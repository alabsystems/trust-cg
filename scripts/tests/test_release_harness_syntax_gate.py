from __future__ import annotations

import re
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
RELEASE_CHECKS = ROOT / "scripts" / "run_public_release_checks.sh"
HARNESS = ROOT / "benchmarks" / "beat-llvm" / "run.py"

# The release gate must parse the authoritative differential harness with the
# interpreter's own parser (not a regex, not a grep) and must name the harness
# file explicitly: a syntax regression in run.py is otherwise invisible to a
# release smoke, which never runs the harness's timing lanes.
GATE_RE = re.compile(
    r"^python3 -c '(?P<program>import ast, pathlib, sys; ast\.parse\([^']*\))' \\\n"
    r"\s+benchmarks/beat-llvm/run\.py\n",
    re.MULTILINE,
)


def _gate_program() -> str:
    match = GATE_RE.search(RELEASE_CHECKS.read_text())
    if match is None:
        raise AssertionError(
            f"{RELEASE_CHECKS.relative_to(ROOT)} has no ast.parse gate over "
            f"{HARNESS.relative_to(ROOT)}"
        )
    return match.group("program")


def _run_gate(target: Path) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        [sys.executable, "-c", _gate_program(), str(target)],
        cwd=ROOT,
        capture_output=True,
        text=True,
        check=False,
    )


class ReleaseHarnessSyntaxGateTests(unittest.TestCase):
    def test_release_checks_parse_the_differential_harness(self) -> None:
        _gate_program()

    def test_gate_accepts_the_committed_harness(self) -> None:
        result = _run_gate(HARNESS)
        self.assertEqual(result.returncode, 0, result.stderr)

    def test_gate_rejects_a_syntax_regression(self) -> None:
        # A same-quote nested f-string is exactly the shape that once broke the
        # harness on pre-PEP 701 interpreters; an unterminated string is a
        # regression every interpreter rejects, so the gate must fail on it.
        with tempfile.TemporaryDirectory() as tmp:
            broken = Path(tmp) / "run.py"
            broken.write_text(HARNESS.read_text() + '\nrow["reason"] = f"unterminated\n')
            result = _run_gate(broken)
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("SyntaxError", result.stderr)


if __name__ == "__main__":
    unittest.main()
