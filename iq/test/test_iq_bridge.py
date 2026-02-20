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


if __name__ == "__main__":
    unittest.main()
