#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
python3 scripts/check_imports.py
lake build --wfail
lake env lean Audit.lean
