#!/usr/bin/env python3
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: MIT

import os
import socket
import sys
import unittest

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from iq_bridge import MCPBridgeWithReconnect


class FakeSocket:
    def __init__(self, recv_chunks, timeout_after_chunks=False):
        self.recv_chunks = list(recv_chunks)
        self.sent = []
        self.closed = False
        self.timeout_after_chunks = timeout_after_chunks
        self.timeout = None

    def send(self, data):
        self.sent.append(data)
        return len(data)

    def sendall(self, data):
        self.sent.append(data)

    def settimeout(self, timeout):
        self.timeout = timeout

    def recv(self, _size):
        if self.recv_chunks:
            return self.recv_chunks.pop(0)
        if self.timeout_after_chunks:
            raise socket.timeout("simulated timeout")
        return b""

    def close(self):
        self.closed = True


class IQBridgeFramingTest(unittest.TestCase):
    def make_bridge(self, recv_chunks, timeout_after_chunks=False):
        bridge = MCPBridgeWithReconnect()
        bridge.isabelle_socket = FakeSocket(recv_chunks, timeout_after_chunks=timeout_after_chunks)
        bridge.connected = True
        bridge.response_timeout_sec = 1
        return bridge

    def test_fragmented_response_reads(self):
        bridge = self.make_bridge(
            [
                b'{"jsonrpc":"2.0","id":"1","res',
                b'ult":{"ok":true}}\n',
            ]
        )

        response = bridge.forward_to_isabelle(
            {"jsonrpc": "2.0", "id": "1", "method": "tools/call", "params": {}}
        )

        self.assertEqual(response, {"jsonrpc": "2.0", "id": "1", "result": {"ok": True}})

    def test_back_to_back_responses_are_queued(self):
        bridge = self.make_bridge(
            [
                b'{"jsonrpc":"2.0","id":"1","result":1}\n{"jsonrpc":"2.0","id":"2","result":2}\n',
            ]
        )

        response1 = bridge.forward_to_isabelle(
            {"jsonrpc": "2.0", "id": "1", "method": "tools/call", "params": {}}
        )
        response2 = bridge.forward_to_isabelle(
            {"jsonrpc": "2.0", "id": "2", "method": "tools/call", "params": {}}
        )

        self.assertEqual(response1, {"jsonrpc": "2.0", "id": "1", "result": 1})
        self.assertEqual(response2, {"jsonrpc": "2.0", "id": "2", "result": 2})

    def test_out_of_order_responses_match_request_id(self):
        bridge = self.make_bridge(
            [
                b'{"jsonrpc":"2.0","id":"2","result":2}\n',
                b'{"jsonrpc":"2.0","id":"1","result":1}\n',
            ]
        )

        response1 = bridge.forward_to_isabelle(
            {"jsonrpc": "2.0", "id": "1", "method": "tools/call", "params": {}}
        )
        response2 = bridge.forward_to_isabelle(
            {"jsonrpc": "2.0", "id": "2", "method": "tools/call", "params": {}}
        )

        self.assertEqual(response1, {"jsonrpc": "2.0", "id": "1", "result": 1})
        self.assertEqual(response2, {"jsonrpc": "2.0", "id": "2", "result": 2})

    def test_request_timeout_returns_none_and_marks_disconnected(self):
        bridge = self.make_bridge([], timeout_after_chunks=True)
        bridge.response_timeout_sec = 1

        response = bridge.forward_to_isabelle(
            {"jsonrpc": "2.0", "id": "1", "method": "tools/call", "params": {}}
        )

        self.assertIsNone(response)
        self.assertFalse(bridge.connected)
        self.assertIsNotNone(bridge.last_forward_error)
        self.assertIn("timed out waiting for Isabelle server response", bridge.last_forward_error)

    def test_forward_failure_message_includes_tool_name_and_detail(self):
        bridge = self.make_bridge([], timeout_after_chunks=True)
        bridge.response_timeout_sec = 1
        request = {
            "jsonrpc": "2.0",
            "id": "1",
            "method": "tools/call",
            "params": {"name": "explore", "arguments": {}},
        }

        response = bridge.forward_to_isabelle(request)
        self.assertIsNone(response)

        message = bridge._forward_failure_message(request)
        self.assertIn("tools/call (tool=explore)", message)
        self.assertIn("timed out waiting for Isabelle server response", message)

    def test_effective_timeout_uses_tool_timeout_arguments(self):
        bridge = MCPBridgeWithReconnect()
        bridge.response_timeout_sec = 30
        request = {
            "jsonrpc": "2.0",
            "id": "1",
            "method": "tools/call",
            "params": {
                "name": "write_file",
                "arguments": {
                    "timeout": 120000,
                    "timeout_per_command": 60000,
                },
            },
        }

        effective = bridge._effective_response_timeout_sec(request)
        self.assertGreaterEqual(effective, 125.0)

    def test_effective_timeout_defaults_without_tool_timeout_arguments(self):
        bridge = MCPBridgeWithReconnect()
        bridge.response_timeout_sec = 30
        request = {
            "jsonrpc": "2.0",
            "id": "1",
            "method": "tools/call",
            "params": {"name": "read_file", "arguments": {"mode": "Line"}},
        }

        effective = bridge._effective_response_timeout_sec(request)
        self.assertEqual(effective, 30.0)


if __name__ == "__main__":
    unittest.main()
