"""The opcode coverage gate must build without reaching the network."""

from __future__ import annotations

import os
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest


ROOT = Path(__file__).resolve().parents[2]


class OpcodeCoverageGateTests(unittest.TestCase):
    def run_gate(self, cargo_rc: int, features: str | None = None) -> tuple[subprocess.CompletedProcess, list[str]]:
        with tempfile.TemporaryDirectory(prefix="trust-cg-coverage-gate-") as temporary:
            base = Path(temporary)
            scripts = base / "repository" / "scripts"
            scripts.mkdir(parents=True)
            shutil.copy2(ROOT / "scripts/check_opcode_coverage_gate.sh", scripts / "check_opcode_coverage_gate.sh")
            record = base / "argv"
            # The gate runs Cargo only through scripts/trust_cargo.sh (the Trust
            # toolchain's targo); a recording stand-in takes its place.
            cargo = scripts / "trust_cargo.sh"
            cargo.write_text(
                '#!/bin/sh\nfor arg in "$@"; do printf "%s\\n" "$arg"; done > "$GATE_TEST_ARGV"\nexit "$GATE_TEST_RC"\n',
                encoding="utf-8",
            )
            cargo.chmod(0o755)
            env = dict(os.environ, GATE_TEST_ARGV=str(record), GATE_TEST_RC=str(cargo_rc))
            env.pop("COVERAGE_GATE_FEATURES", None)
            if features is not None:
                env["COVERAGE_GATE_FEATURES"] = features
            result = subprocess.run(
                ["bash", str(scripts / "check_opcode_coverage_gate.sh")], cwd=base, env=env,
                capture_output=True, text=True, check=False,
            )
            argv = record.read_text(encoding="utf-8").splitlines() if record.exists() else []
        return result, argv

    def test_targo_runs_locked_and_offline(self):
        for features in (None, "slow-full-database"):
            with self.subTest(features=features):
                result, argv = self.run_gate(0, features)
                self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
                self.assertEqual(argv[:1], ["test"], argv)
                self.assertIn("--locked", argv)
                self.assertIn("--offline", argv)
                self.assertIn("coverage_gate_tests", argv)
                separator = argv.index("--")
                self.assertLess(argv.index("--offline"), separator, "--offline must reach targo, not libtest")
                if features is not None:
                    self.assertEqual(argv[argv.index("--features") + 1], features)

    def test_a_failing_test_run_fails_the_gate(self):
        result, _ = self.run_gate(101)
        self.assertEqual(result.returncode, 1, result.stdout + result.stderr)


if __name__ == "__main__":
    unittest.main()
