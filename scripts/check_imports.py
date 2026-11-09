#!/usr/bin/env python3
"""Ensure the default entry point imports every project proof module.

This keeps the axiom audit's imported environment aligned with the full source
tree. It does not infer mathematical correctness from textual proof syntax.
"""
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[1]
files = [ROOT / "PredictionDepth.lean", *(ROOT / "PredictionDepth").rglob("*.lean")]
modules = {str(p.relative_to(ROOT).with_suffix("")).replace("/", "."): p for p in files}
seen = set()


def visit(module):
    if module in seen or module not in modules:
        return
    seen.add(module)
    for dependency in re.findall(r"^(?:public\s+)?import\s+([A-Za-z0-9_.]+)",
                                 modules[module].read_text(), re.MULTILINE):
        visit(dependency)


visit("PredictionDepth")
missing = sorted(modules.keys() - seen)
if missing:
    raise SystemExit("Not covered by the entry point and axiom audit:\n" + "\n".join(missing))
print(f"Entry point covers all {len(modules)} project modules.")
