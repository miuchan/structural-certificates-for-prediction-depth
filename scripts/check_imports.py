#!/usr/bin/env python3
"""Check the compiled entry point's actual import closure.

Run via `lake env python3 scripts/check_imports.py` after building the project.
"""

import os
from pathlib import Path
import subprocess
from tempfile import TemporaryDirectory


ROOT = Path(__file__).resolve().parents[1]
CHECKER = ROOT / "scripts" / "ImportClosure.lean"


def project_modules(root):
    sources = [root / "PredictionDepth.lean", *(root / "PredictionDepth").rglob("*.lean")]
    return {".".join(source.relative_to(root).with_suffix("").parts) for source in sources}


def missing_modules(expected, env=None):
    result = subprocess.run(
        ["lean", str(CHECKER)], cwd=ROOT, env=env, capture_output=True, text=True,
    )
    if result.returncode:
        raise SystemExit(f"Lean could not read the entry point's imports:\n{result.stdout}{result.stderr}")
    return sorted(expected - set(result.stdout.splitlines()))


def check_regression():
    with TemporaryDirectory(prefix="prediction-depth-imports-") as directory:
        scratch = Path(directory)
        env = {**os.environ, "LEAN_PATH": str(scratch)}
        fixtures = scratch / "PredictionDepth"
        fixtures.mkdir()

        def compile_source(path, source):
            path.write_text(source, encoding="utf-8")
            subprocess.run(
                ["lean", "-o", str(path.with_suffix(".olean")), str(path)],
                cwd=scratch, env=env, check=True,
            )

        for name in ("Leaf", "Commented", "NestedCommented"):
            compile_source(fixtures / f"{name}.lean", "")
        compile_source(fixtures / "Bridge.lean", "import PredictionDepth.Leaf\n")

        # Even built modules named in block comments are absent from the audit.
        entry = scratch / "PredictionDepth.lean"
        commented = (
            "import PredictionDepth.Bridge\n"
            "/-\n"
            "import PredictionDepth.Commented\n"
            "-/\n"
            "/-\n"
            "  /-\n"
            "import PredictionDepth.NestedCommented\n"
            "  -/\n"
            "-/\n"
        )
        compile_source(entry, commented)
        modules = project_modules(scratch)
        expected_missing = ["PredictionDepth.Commented", "PredictionDepth.NestedCommented"]
        missing = missing_modules(modules, env)
        if missing != expected_missing:
            raise SystemExit(
                f"Import coverage regression: expected missing {expected_missing}, got {missing}."
            )

        compile_source(
            entry, "import PredictionDepth.Commented\nimport PredictionDepth.NestedCommented\n" + commented,
        )
        missing = missing_modules(modules, env)
        if missing:
            raise SystemExit(f"Import coverage regression: valid import closure is missing {missing}.")
        print("Import coverage regression passed: block comments do not count as imports.")


def main():
    modules = project_modules(ROOT)
    missing = missing_modules(modules)
    if missing:
        raise SystemExit("Not covered by the entry point and axiom audit:\n" + "\n".join(missing))
    print(f"Entry point covers all {len(modules)} project modules.")
    check_regression()


if __name__ == "__main__":
    main()
