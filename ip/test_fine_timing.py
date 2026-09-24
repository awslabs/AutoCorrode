#!/usr/bin/env python3

import json
import os
import sqlite3
import subprocess
import sys
import tempfile
import unittest


HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)

from fine_timing import (  # noqa: E402
    Aggregate, Timing, aggregate_invocations, extract_reports,
    percentile_upper_bound,
)


X = "\x05"
Y = "\x06"


def elem(name, properties=None, body=None):
    attributes = "".join(
        Y + key + "=" + str(value)
        for key, value in (properties or {}).items())
    return (
        X + Y + name + attributes + X +
        "".join(body or []) +
        X + Y + X)


def bucket(index, count):
    return elem(
        "fine_grained_timing_bucket",
        {"bucket": index, "count": count})


def sample(name="step", success=True, count=3):
    return elem(
        "fine_grained_timing_entry",
        {
            "name": name,
            "success": str(success).lower(),
            "count": count,
            "elapsed_us": 120,
            "cpu_us": 100,
            "gc_us": 5,
            "min_elapsed_us": 20,
            "max_elapsed_us": 60,
        },
        [bucket(4, 1), bucket(5, count - 1)])


def transported_report(version=2, invocation=42, success=True,
                       report_body=None):
    properties = {
        "xml_name": "fine_grained_timing",
        "version": version,
        "invocation": invocation,
        "method": "example_method",
        "success": str(success).lower(),
    }
    if version == 1:
        properties.update({
            "elapsed_us": 500,
            "cpu_us": 400,
            "gc_us": 10,
        })
    return elem(
        "xml_elem", properties,
        [elem("xml_body", body=report_body or [sample()]), "apply"])


def export_body(report):
    return elem(
        "command_range", body=[
            elem(
                "command_span",
                {"name": "apply", "kind": "prf_script"},
                [
                    elem(
                        "entity",
                        {"name": "apply", "command_offset": 123}),
                    report,
                ])
        ])


class FineTimingDecodeTest(unittest.TestCase):
    def test_decodes_transport_and_location(self):
        result = extract_reports(
            export_body(transported_report()),
            "Example.Theory", "PIDE/markup")
        self.assertEqual(result.malformed, 0)
        self.assertEqual(len(result.invocations), 1)
        invocation = result.invocations[0]
        self.assertEqual(invocation.invocation, 42)
        self.assertEqual(invocation.command, "apply")
        self.assertEqual(invocation.command_offset, 123)
        self.assertEqual(invocation.samples[0].aggregate.count, 3)

    def test_decodes_legacy_invocation_timing(self):
        result = extract_reports(
            export_body(transported_report(version=1)))
        self.assertEqual(result.invocations[0].timing.elapsed_us, 500)

    def test_rejects_bad_histogram(self):
        bad_sample = sample().replace(Y + "count=3", Y + "count=4", 1)
        result = extract_reports(
            export_body(transported_report(report_body=[bad_sample])))
        self.assertEqual(result.malformed, 1)
        self.assertEqual(result.invocations, [])

    def test_counts_unsupported_versions(self):
        result = extract_reports(
            export_body(transported_report(version=7)))
        self.assertEqual(result.unsupported, 1)
        self.assertEqual(result.invocations, [])

    def test_handles_deep_pide_markup_without_recursion(self):
        report = transported_report()
        for _ in range(1200):
            report = elem("nested", body=[report])
        result = extract_reports(report)
        self.assertEqual(len(result.invocations), 1)

    def test_deduplicates_repeated_transport_records(self):
        report = transported_report()
        result = extract_reports(report + report)
        self.assertEqual(len(result.invocations), 1)
        self.assertEqual(result.duplicates, 1)

    def test_merges_samples_and_preserves_histogram(self):
        first = extract_reports(
            export_body(transported_report(invocation=1))).invocations[0]
        second = extract_reports(
            export_body(transported_report(invocation=2))).invocations[0]
        rows = aggregate_invocations([first, second], lambda _: "")
        aggregate = rows[("", "step", True)]
        self.assertEqual(aggregate.count, 6)
        self.assertEqual(aggregate.timing.elapsed_us, 240)
        self.assertEqual(aggregate.histogram, {4: 2, 5: 4})

    def test_percentiles_are_bucket_upper_bounds(self):
        aggregate = Aggregate(
            count=4,
            timing=Timing(100, 80, 0),
            min_elapsed_us=1,
            max_elapsed_us=40,
            histogram={0: 1, 3: 3})
        self.assertEqual(percentile_upper_bound(aggregate, 0.25), 1)
        self.assertEqual(percentile_upper_bound(aggregate, 0.50), 15)


class FineTimingCLITest(unittest.TestCase):
    def test_json_output_is_machine_readable(self):
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
                ("Example", "Example.Theory", "PIDE/markup",
                 export_body(transported_report()).encode("utf-8")))
            connection.commit()
            connection.close()

            process = subprocess.run(
                [
                    os.path.join(HERE, "heap-db-inspect"),
                    database,
                    "--fine-timings",
                    "--format", "json",
                ],
                check=True, capture_output=True, text=True)
            document = json.loads(process.stdout)
            self.assertEqual(
                document["format"],
                "heap-db-inspect/fine-grained-timing")
            self.assertEqual(document["summary"]["reports"], 1)
            self.assertEqual(document["rows"][0]["sample"], "step")


if __name__ == "__main__":
    unittest.main()
