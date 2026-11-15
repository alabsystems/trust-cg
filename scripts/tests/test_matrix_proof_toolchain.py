"""Exercise the matrix's actual proof-preflight branch without compiling crates."""

import os
from pathlib import Path
import subprocess
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[2]
SOURCE = (ROOT / "scripts/run_full_test_matrix.sh").read_text()
PREFLIGHT = SOURCE.split("# P0 proof gate:", 1)[1].split(
    'if [ "${DRY_RUN}" -eq 1 ]; then', 1
)[0]
# The split keeps the text following the comment marker; restore that marker
# so bash evaluates only executable source, not the remainder of the comment.
PREFLIGHT = "# P0 proof gate:" + PREFLIGHT


class MatrixProofToolchainTests(unittest.TestCase):
    def run_preflight(self, commands=(), overrides=None):
        with tempfile.TemporaryDirectory() as temporary:
            directory = Path(temporary)
            for name in commands:
                command = directory / name
                command.write_text("#!/bin/sh\nexit 77\n")
                command.chmod(0o755)
            probe = directory / "check_proof_gate.sh"
            probe.write_text("#!/bin/sh\nprintf 'PROBE_RAN\\n'\n")
            probe.chmod(0o755)
            environment = {key: value for key, value in os.environ.items() if key not in {
                "AY_SOLVER_PATH", "TCG_EXTERNAL_CLEAN_CHECKER", "TCG_CLEAN_CHECKER",
                "TRUST_CG_PROOF_GATE", "CI", "GITHUB_ACTIONS", "BASH_ENV", "ENV",
            }}
            environment.update(PATH=str(directory), SCRIPT_DIR=str(directory), DRY_RUN="0")
            environment.update(overrides or {})
            return subprocess.run(
                ["/bin/bash", "-c", PREFLIGHT], env=environment,
                text=True, capture_output=True, check=False,
            )

    def test_aterm_or_ay_advertisement_requires_the_real_gate(self):
        for command in ["aterm", "alab-ay", "ay"]:
            with self.subTest(command=command):
                result = self.run_preflight([command])
                self.assertEqual(result.returncode, 0, result.stderr)
                self.assertIn("PROBE_RAN", result.stdout)

    def test_z3_does_not_advertise_an_authorized_solver(self):
        result = self.run_preflight(["z3"])
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertNotIn("PROBE_RAN", result.stdout)
        self.assertIn("STRICT PROOF GATE SKIPPED", result.stderr)

    def test_empty_explicit_overrides_are_probed_not_silently_skipped(self):
        for variable in ["AY_SOLVER_PATH", "TCG_EXTERNAL_CLEAN_CHECKER", "TCG_CLEAN_CHECKER"]:
            with self.subTest(variable=variable):
                result = self.run_preflight(overrides={variable: ""})
                self.assertEqual(result.returncode, 0, result.stderr)
                self.assertIn("PROBE_RAN", result.stdout)

    def test_required_gate_cannot_pass_without_the_toolchain(self):
        result = self.run_preflight(overrides={"TRUST_CG_PROOF_GATE": "require"})
        self.assertEqual(result.returncode, 1)
        self.assertIn("formal floor UN-RUN", result.stderr)
        self.assertNotIn("Install z3", result.stderr)

    def test_explicit_nonformal_mode_does_not_run_the_probe(self):
        result = self.run_preflight(["aterm"], {"TRUST_CG_PROOF_GATE": "skip"})
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertNotIn("PROBE_RAN", result.stdout)


if __name__ == "__main__":
    unittest.main()
