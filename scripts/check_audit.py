#!/usr/bin/env python3
"""Run via `lake env python3 scripts/check_audit.py` after building the project."""

import os
from pathlib import Path
import subprocess
from tempfile import TemporaryDirectory


ROOT = Path(__file__).resolve().parents[1]
DIAGNOSTIC = (
    "AuditRegressionExternal.unexpectedTheorem transitively depends on "
    "unapproved axiom AuditRegressionDependency.unexpectedOracle"
)


def main():
    with TemporaryDirectory(prefix="prediction-depth-audit-") as directory:
        scratch = Path(directory).resolve()
        env = os.environ.copy()
        env["LEAN_PATH"] = os.pathsep.join(
            path for path in (str(scratch), env.get("LEAN_PATH")) if path
        )
        lean = ["lean", f"--root={scratch}"]

        # The dependency defines an axiom outside the modules selected by the audit.
        dependency = scratch / "AuditRegressionDependency.lean"
        dependency.write_text(
            "namespace AuditRegressionDependency\n"
            "axiom unexpectedOracle : False\n"
            "theorem intermediate : False := unexpectedOracle\n"
            "end AuditRegressionDependency\n",
            encoding="utf-8",
        )

        # The defining module must be audited even though the theorem's namespace differs.
        fixture = scratch / "PredictionDepth" / "AuditRegression.lean"
        fixture.parent.mkdir()
        fixture.write_text(
            "import AuditRegressionDependency\n"
            "theorem AuditRegressionExternal.unexpectedTheorem : False :=\n"
            "  AuditRegressionDependency.intermediate\n",
            encoding="utf-8",
        )

        # Shadow the project entry point with the fixture so Audit.lean runs unchanged.
        entry_point = scratch / "PredictionDepth.lean"
        entry_point.write_text("import Lean\nimport PredictionDepth.AuditRegression\n", encoding="utf-8")

        for source in (dependency, fixture, entry_point):
            subprocess.run(
                [*lean, "-o", str(source.with_suffix(".olean")), str(source)],
                env=env,
                check=True,
            )

        result = subprocess.run(
            ["lean", f"--root={ROOT}", str(ROOT / "Audit.lean")],
            env=env, stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT, text=True,
        )
        if result.returncode == 0 or DIAGNOSTIC not in result.stdout:
            raise SystemExit(
                f"Expected the audit to reject {DIAGNOSTIC!r}.\n{result.stdout}"
            )
        print(f"Audit regression passed: {DIAGNOSTIC}.")


if __name__ == "__main__":
    main()
