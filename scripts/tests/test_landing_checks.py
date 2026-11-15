"""Run the real landing_checks.sh against stub gates to pin its exit contract.

Missing evidence (no perf results JSON, a --no-sentinel skip, a stale results
file under --require-current-perf, or an unattested landing base) must be a
nonzero result unless an explicit --allow-missing-* diagnostic opt-in prints a
NON-QUALIFYING banner.
"""

from __future__ import annotations

import os
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest


ROOT = Path(__file__).resolve().parents[2]
LANDING = ROOT / "scripts" / "landing_checks.sh"


class LandingChecksTests(unittest.TestCase):
    def run_landing(self, *args: str, results: bool = True, base: str | None = None,
                    **codes: int) -> tuple[subprocess.CompletedProcess, list[str]]:
        with tempfile.TemporaryDirectory(prefix="trust-cg-landing-") as temporary:
            repo = Path(temporary)
            scripts = repo / "scripts"
            scripts.mkdir()
            shutil.copy2(LANDING, scripts / "landing_checks.sh")
            shutil.copy2(ROOT / "scripts/github_transport.py", scripts / "github_transport.py")
            log = repo / "calls.log"
            for name, key in (
                ("compile_time_canary.sh", "canary"),
                ("compile_determinism_sentinel.sh", "sentinel"),
            ):
                stub = scripts / name
                stub.write_text(f'#!/bin/sh\necho "{key} $*" >>"$STUB_LOG"\nexit {codes.get(key, 0)}\n')
                stub.chmod(0o755)
            (scripts / "check_perf_ratchet.py").write_text(
                "import os, sys\n"
                "with open(os.environ['STUB_LOG'], 'a') as log:\n"
                "    log.write('ratchet ' + ' '.join(sys.argv[1:]) + '\\n')\n"
                f"sys.exit({codes.get('ratchet', 0)})\n"
            )
            # The attestation tool committed at the landing base decides; the
            # candidate's own copy (the working tree's) must never run.
            (scripts / "soundness_attestation.py").write_text(
                "import os, sys\n"
                "with open(os.environ['STUB_LOG'], 'a') as log:\n"
                "    log.write('attest ' + ' '.join(sys.argv[1:]) + '\\n')\n"
                f"sys.exit({codes.get('attest', 0)})\n"
            )
            git_env = {key: value for key, value in os.environ.items() if not key.startswith("GIT_")}
            git_env.update(GIT_CONFIG_NOSYSTEM="1", GIT_CONFIG_GLOBAL=os.devnull, GIT_AUTHOR_NAME="t",
                           GIT_AUTHOR_EMAIL="t@example.invalid", GIT_COMMITTER_NAME="t",
                           GIT_COMMITTER_EMAIL="t@example.invalid")
            def git(*argv: str) -> str:
                return subprocess.run(["git", "-C", str(repo), *argv], check=True, capture_output=True,
                                      text=True, env=git_env).stdout.strip()
            git("init", "-q")
            git("add", "-A")
            git("commit", "-qm", "landing base")
            landed = git("rev-parse", "HEAD")
            git("update-ref", "refs/remotes/origin/main", landed)
            git("update-ref", "refs/remotes/dev/main", landed)
            (scripts / "soundness_attestation.py").write_text(
                "import os, sys\n"
                "with open(os.environ['STUB_LOG'], 'a') as log:\n"
                "    log.write('candidate-tool ' + ' '.join(sys.argv[1:]) + '\\n')\n"
                "sys.exit(0)\n"
            )
            if results:
                directory = repo / "benchmarks" / "beat-llvm" / "results"
                directory.mkdir(parents=True)
                (directory / "run.json").write_text("{}\n")
            environment = {key: value for key, value in os.environ.items()
                           if key != "TCG_LANDING_BASE"}
            environment["STUB_LOG"] = str(log)
            if base is not None:
                environment["TCG_LANDING_BASE"] = base
            result = subprocess.run(
                ["bash", str(scripts / "landing_checks.sh"), *args], env=environment,
                capture_output=True, text=True, timeout=60, check=False,
            )
            calls = log.read_text().splitlines() if log.exists() else []
            calls = [call.replace(landed, "<base>") for call in calls]
        return result, calls

    def test_script_parses(self):
        subprocess.run(["bash", "-n", str(LANDING)], check=True)

    def test_every_gate_green_is_the_only_qualifying_zero(self):
        result, calls = self.run_landing()
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn("landing-checks: ALL GREEN", result.stdout)
        self.assertNotIn("NON-QUALIFYING", result.stdout + result.stderr)
        self.assertEqual(calls[:3], ["canary ", "ratchet ", "sentinel "])
        # The base's committed verifier checks the base; the candidate's tool never runs.
        self.assertEqual([call.split(" --repo ")[0] for call in calls[3:]], ["attest verify <base>"])

    def test_missing_perf_results_are_missing_evidence_not_a_skip(self):
        result, calls = self.run_landing(results=False)
        self.assertEqual(result.returncode, 3, result.stdout + result.stderr)
        self.assertIn("perf ratchet MISSING EVIDENCE", result.stderr)
        self.assertIn("MISSING REQUIRED EVIDENCE: perf", result.stderr)
        self.assertNotIn("ALL GREEN", result.stdout)
        self.assertNotIn("SKIPPED", result.stdout + result.stderr)
        self.assertFalse(any(call.startswith("ratchet") for call in calls))

    def test_no_sentinel_is_missing_evidence_not_a_skip(self):
        result, calls = self.run_landing("--no-sentinel")
        self.assertEqual(result.returncode, 3, result.stdout + result.stderr)
        self.assertIn("MISSING REQUIRED EVIDENCE: sentinel", result.stderr)
        self.assertFalse(any(call.startswith("sentinel") for call in calls))
        result, _ = self.run_landing("--no-sentinel", results=False)
        self.assertEqual(result.returncode, 3)
        self.assertIn("MISSING REQUIRED EVIDENCE: perf sentinel", result.stderr)

    def test_explicit_opt_ins_exit_zero_only_behind_a_non_qualifying_banner(self):
        for args, results, missing in (
            (("--allow-missing-perf",), False, "perf"),
            (("--no-sentinel", "--allow-missing-sentinel"), True, "sentinel"),
            (("--no-sentinel", "--allow-missing-sentinel", "--allow-missing-perf"), False, "perf sentinel"),
        ):
            with self.subTest(args=args):
                result, _ = self.run_landing(*args, results=results)
                self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
                self.assertIn("!!! landing-checks: NON-QUALIFYING RUN", result.stderr)
                self.assertIn(f"NON-QUALIFYING (missing: {missing})", result.stdout)
                self.assertNotIn("ALL GREEN", result.stdout)
        # An opt-in for one gate never excuses the other.
        result, _ = self.run_landing("--allow-missing-perf", "--no-sentinel", results=False)
        self.assertEqual(result.returncode, 3)
        self.assertIn("MISSING REQUIRED EVIDENCE: sentinel", result.stderr)
        # An opt-in does not change a run whose evidence is present.
        result, _ = self.run_landing("--allow-missing-perf", "--allow-missing-sentinel")
        self.assertEqual(result.returncode, 0)
        self.assertIn("landing-checks: ALL GREEN", result.stdout)

    def test_red_and_tooling_outrank_missing_evidence(self):
        result, _ = self.run_landing(results=False, canary=1)
        self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
        result, _ = self.run_landing(results=False, canary=2)
        self.assertEqual(result.returncode, 2, result.stdout + result.stderr)
        result, _ = self.run_landing("--allow-missing-perf", results=False, sentinel=1)
        self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
        self.assertIn("NON-QUALIFYING", result.stderr)

    def test_require_current_perf_forwards_and_stale_results_are_missing_evidence(self):
        result, calls = self.run_landing("--require-current-perf")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn("ratchet --require-current", calls)
        result, _ = self.run_landing("--require-current-perf", ratchet=3)
        self.assertEqual(result.returncode, 3, result.stdout + result.stderr)
        self.assertIn("MISSING CURRENT EVIDENCE", result.stderr)
        self.assertIn("MISSING REQUIRED EVIDENCE: perf-current", result.stderr)
        result, _ = self.run_landing("--require-current-perf", results=False)
        self.assertEqual(result.returncode, 3)

    def test_predecessor_attestation_exit_codes(self):
        # verify: 0 attested, 1 failing/incomplete, 2 malformed, 3 absent.
        for code, expected, text in ((1, 1, "predecessor attestation RED"),
                                     (2, 2, "predecessor attestation TOOLING"),
                                     (3, 3, "MISSING REQUIRED EVIDENCE: attestation"),
                                     (7, 2, "predecessor attestation TOOLING")):
            with self.subTest(code=code):
                result, _ = self.run_landing(attest=code)
                self.assertEqual(result.returncode, expected, result.stdout + result.stderr)
                self.assertIn(text, result.stderr)
                self.assertNotIn("ALL GREEN", result.stdout)
        # No reachable origin is not a verdict; the local records decide.
        result, _ = self.run_landing()
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        # An unresolvable base is tooling, never a pass.
        result, _ = self.run_landing(base="refs/remotes/nowhere/main")
        self.assertEqual(result.returncode, 2, result.stdout + result.stderr)
        # A red gate outranks a missing attestation.
        result, _ = self.run_landing(attest=3, canary=1)
        self.assertEqual(result.returncode, 1)

    def test_landing_base_is_configurable(self):
        result, calls = self.run_landing(base="refs/remotes/dev/main")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn("attest verify <base>", [call.split(" --repo ")[0] for call in calls])

    def test_invalid_or_contradictory_arguments_run_nothing(self):
        for args in (("--skip-perf",), ("--require-current-perf", "--allow-missing-perf")):
            with self.subTest(args=args):
                result, calls = self.run_landing(*args)
                self.assertEqual(result.returncode, 2, result.stdout + result.stderr)
                self.assertEqual(calls, [])


if __name__ == "__main__":
    unittest.main()
