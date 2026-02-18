#!/usr/bin/env python3
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: MIT

import os
import sys
import unittest

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from iq_bridge import MCPBridgeWithReconnect


class FakeSocket:
    def __init__(self, recv_chunks):
        self.recv_chunks = list(recv_chunks)
        self.sent = []
        self.closed = False

    def send(self, data):
        self.sent.append(data)
        return len(data)

    def recv(self, _size):
        if self.recv_chunks:
            return self.recv_chunks.pop(0)
        return b""

    def close(self):
        self.closed = True


class IQBridgeFramingTest(unittest.TestCase):
    def make_bridge(self, recv_chunks):
        bridge = MCPBridgeWithReconnect()
        bridge.isabelle_socket = FakeSocket(recv_chunks)
        bridge.connected = True
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


if __name__ == "__main__":
    unittest.main()
