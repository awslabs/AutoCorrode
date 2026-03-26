#!/usr/bin/env bash
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: MIT
#
# Thin wrapper — all logic lives in test_ic_integration.py
exec python3 "$(dirname "$0")/test_ic_integration.py" "$@"
