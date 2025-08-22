#!/usr/bin/env python3
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: MIT
"""
MCP Bridge for Isabelle with automatic reconnection.
Reconnects to server when connection is lost and new queries come in.
"""

import sys
import json
import socket
import time
from typing import Dict, Any, Optional

class MCPBridgeWithReconnect:
    def __init__(self):
        self.isabelle_socket = None
        self.connected = False

    def log(self, message: str):
        """Log messages to stderr and file with timestamp."""
        timestamp = time.strftime("%Y-%m-%d %H:%M:%S")
        log_message = f"{timestamp} [MCP-Bridge] {message}"

        # Log to stderr
        print(log_message, file=sys.stderr, flush=True)

        # Also log to file
        try:
            import os
            script_dir = os.path.dirname(os.path.abspath(__file__))
            log_file = os.path.join(script_dir, "bridge_log.txt")
            with open(log_file, "a") as f:
                f.write(log_message + "\n")
                f.flush()
        except Exception:
            pass  # Don't let logging errors break the bridge

    def connect_to_isabelle(self) -> bool:
        """Connect to the Isabelle MCP server."""
        try:
            if self.isabelle_socket:
                try:
                    self.isabelle_socket.close()
                except:
                    pass

            self.isabelle_socket = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
            self.isabelle_socket.connect(('localhost', 8765))
            self.connected = True
            self.log("Connected to Isabelle MCP server")
            return True

        except Exception as e:
            self.log(f"Connection failed: {e}")
            self.connected = False
            if self.isabelle_socket:
                try:
                    self.isabelle_socket.close()
                except:
                    pass
                self.isabelle_socket = None
            return False

    def ensure_connection(self) -> bool:
        """Ensure we have a working connection, reconnecting if necessary."""
        if self.connected and self.isabelle_socket:
            return True

        self.log("Connection lost, attempting to reconnect...")
        return self.connect_to_isabelle()

    def forward_to_isabelle(self, request: Dict[str, Any]) -> Optional[Dict[str, Any]]:
        """Forward request to Isabelle server with automatic reconnection."""
        method = request.get('method', 'unknown')

        # Ensure we have a connection
        if not self.ensure_connection():
            self.log(f"Cannot establish connection - cannot forward {method}")
            return None

        try:
            # Send request
            request_str = json.dumps(request)
            self.isabelle_socket.send((request_str + "\n").encode())

            # Read response as bytes first
            response_bytes = b""

            # Read first chunk
            first_chunk = self.isabelle_socket.recv(4096)
            if not first_chunk:
                self.log(f"No response for {method} - connection closed")
                self.connected = False
                return None

            response_bytes += first_chunk

            # Read remaining chunks with short timeout
            self.isabelle_socket.settimeout(0.1)
            while True:
                try:
                    chunk = self.isabelle_socket.recv(4096)
                    if not chunk:
                        break
                    response_bytes += chunk
                except socket.timeout:
                    break

            # Reset to blocking mode
            self.isabelle_socket.settimeout(None)

            # Decode and parse
            try:
                response_str = response_bytes.decode('utf-8').strip()
                parsed_response = json.loads(response_str)
                self.log(f"Successfully forwarded {method}")
                return parsed_response
            except (UnicodeDecodeError, json.JSONDecodeError) as e:
                self.log(f"Response decode error for {method}: {e}")
                return None

        except Exception as e:
            self.log(f"Error forwarding {method}: {e}")
            self.connected = False
            return None

    def create_error_response(self, request_id: Any, code: int, message: str) -> Dict[str, Any]:
        """Create a standard JSON-RPC error response."""
        return {
            "jsonrpc": "2.0",
            "id": request_id,
            "error": {
                "code": code,
                "message": message
            }
        }

    def run(self):
        """Main bridge loop with automatic reconnection."""
        self.log("Starting MCP bridge for Isabelle with automatic reconnection")

        # Initial connection attempt
        if not self.connect_to_isabelle():
            self.log("Failed to establish initial connection - will retry on first request")
        else:
            self.log("Bridge ready with initial connection")

        try:
            for line in sys.stdin:
                line = line.strip()
                if not line:
                    continue

                try:
                    request = json.loads(line)
                    method = request.get("method", "unknown")
                    request_id = request.get("id")

                    # Forward to Isabelle server (with automatic reconnection)
                    response = self.forward_to_isabelle(request)

                    if response:
                        # Ensure response has correct ID
                        response["id"] = request_id

                        # Send response back to Amazon Q
                        response_str = json.dumps(response)
                        print(response_str, flush=True)
                        self.log(f"Response sent for {method}")
                    else:
                        # Send error if forwarding failed
                        error_response = self.create_error_response(
                            request_id, -32603, f"Failed to forward {method} to Isabelle server"
                        )
                        print(json.dumps(error_response), flush=True)
                        self.log(f"Error response sent for {method}")

                except json.JSONDecodeError as e:
                    self.log(f"JSON parse error: {e}")
                    error_response = self.create_error_response(
                        None, -32700, f"Parse error: {e}"
                    )
                    print(json.dumps(error_response), flush=True)

        except KeyboardInterrupt:
            self.log("Bridge interrupted")
        except Exception as e:
            self.log(f"Unexpected error in bridge: {e}")
        finally:
            if self.isabelle_socket:
                try:
                    self.isabelle_socket.close()
                except:
                    pass
            self.log("Bridge shutdown complete")

if __name__ == "__main__":
    bridge = MCPBridgeWithReconnect()
    bridge.run()
