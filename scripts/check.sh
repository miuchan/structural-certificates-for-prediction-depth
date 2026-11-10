#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
lake build --wfail
lake env python3 scripts/check_imports.py
lake env lean Audit.lean
lake env python3 scripts/check_audit.py
