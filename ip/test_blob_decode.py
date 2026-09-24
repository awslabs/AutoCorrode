#!/usr/bin/env python3

import os
import sqlite3
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch


HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "..", "ir"))

import heap_info  # noqa: E402
import repl_srv  # noqa: E402


X = "\x05"
Y = "\x06"


def yxml_element(name, properties=None, body=None):
    attributes = "".join(
        Y + key + "=" + str(value)
        for key, value in (properties or {}).items()
    )
    return X + Y + name + attributes + X + "".join(body or []) + X + Y + X


def timing_export():
    sample = yxml_element(
        "fine_grained_timing_entry",
        {
            "name": "step",
            "success": "true",
            "count": 1,
            "elapsed_us": 10,
            "cpu_us": 5,
            "gc_us": 0,
            "min_elapsed_us": 10,
            "max_elapsed_us": 10,
        },
        [yxml_element(
            "fine_grained_timing_bucket",
            {"bucket": 3, "count": 1},
        )],
    )
    report = yxml_element(
        "xml_elem",
        {
            "xml_name": "fine_grained_timing",
            "version": 2,
            "invocation": 1,
            "method": "example",
            "success": "true",
            "elapsed_us": 20,
            "cpu_us": 10,
            "gc_us": 0,
        },
        [yxml_element("xml_body", body=[sample]), "apply"],
    )
    return yxml_element("command_range", body=[report]).encode("utf-8")


class BlobDecodeTest(unittest.TestCase):
    class FakeZstd:
        class ZstdError(Exception):
            pass

        class ZstdDecompressor:
            def decompressobj(self):
                return BlobDecodeTest.IncompleteDecoder()

    class IncompleteDecoder:
        eof = False

        def decompress(self, _blob):
            return b"partial"

    def test_rejects_a_zstd_frame_without_an_end_marker(self):
        blob = b"\x28\xb5\x2f\xfdtruncated"
        with patch.object(heap_info, "HAS_ZSTD", True), patch.object(
            heap_info, "zstandard", self.FakeZstd, create=True
        ):
            with self.assertRaises(heap_info.ZstdDecodeError):
                heap_info.decompress_blob(blob)

    def test_distinguishes_an_absent_decoder(self):
        blob = b"\x28\xb5\x2f\xfdcompressed"
        with patch.object(heap_info, "HAS_ZSTD", False), patch.object(
            heap_info.subprocess,
            "run",
            side_effect=FileNotFoundError("zstd"),
        ):
            with self.assertRaises(heap_info.ZstdDecoderUnavailable):
                heap_info.decompress_blob(blob)

    @unittest.skipUnless(
        heap_info.HAS_ZSTD,
        "Python zstandard module is not installed",
    )
    def test_real_decoder_rejects_a_truncated_frame(self):
        compressed = heap_info.zstandard.ZstdCompressor().compress(
            b"complete frame"
        )
        with self.assertRaises(heap_info.ZstdDecodeError):
            heap_info.decompress_blob(compressed[:-1])


class TimingConsoleTest(unittest.TestCase):
    def test_decode_failure_does_not_escape_the_management_command(self):
        class BrokenHeapInfo:
            def timing_hotspots(self, **_arguments):
                raise heap_info.ZstdDecoderUnavailable("no decoder")

        server = object.__new__(repl_srv.Server)
        server.heap_info = BrokenHeapInfo()

        result = server._cmd_timings("/timings")

        self.assertIn("Command timings unavailable", result)
        self.assertIn("no decoder", result)


class BlobDecodeCLITest(unittest.TestCase):
    def test_corrupt_zstd_is_not_reported_as_a_missing_decoder(self):
        with tempfile.TemporaryDirectory() as directory:
            database = os.path.join(directory, "Example.db")
            connection = sqlite3.connect(database)
            connection.execute(
                "CREATE TABLE isabelle_exports ("
                "session_name TEXT, theory_name TEXT, name TEXT, body BLOB)")
            connection.execute(
                "CREATE TABLE isabelle_sources ("
                "session_name TEXT, name TEXT, digest TEXT)")
            connection.execute(
                "INSERT INTO isabelle_exports VALUES (?, ?, ?, ?)",
                (
                    "Example",
                    "Example.Theory",
                    "PIDE/markup",
                    b"\x28\xb5\x2f\xfdcorrupt",
                ),
            )
            connection.execute(
                "INSERT INTO isabelle_exports VALUES (?, ?, ?, ?)",
                (
                    "Example",
                    "Example.Other",
                    "PIDE/markup1",
                    timing_export(),
                ),
            )
            connection.commit()
            connection.close()

            binaries = os.path.join(directory, "bin")
            os.mkdir(binaries)
            zstd = os.path.join(binaries, "zstd")
            with open(zstd, "w", encoding="utf-8") as stream:
                stream.write("#!/bin/sh\necho corrupt >&2\nexit 1\n")
            os.chmod(zstd, 0o700)
            environment = dict(os.environ)
            environment["PATH"] = binaries

            process = subprocess.run(
                [
                    sys.executable,
                    "-S",
                    os.path.join(HERE, "heap-db-inspect"),
                    database,
                    "--fine-timings",
                ],
                capture_output=True,
                text=True,
                env=environment,
            )

            self.assertEqual(process.returncode, 0)
            self.assertIn(
                "Skipped 1 undecodable PIDE markup export",
                process.stdout,
            )
            self.assertIn("(1 successful, 0 failed)", process.stdout)
            self.assertNotIn("install Python", process.stdout)


if __name__ == "__main__":
    unittest.main()
