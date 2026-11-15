#!/usr/bin/env python3
"""Exercise lint gate failures with a temporary frontend; no compiler runs."""

from __future__ import annotations

import json
import os
import re
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest


ROOT = Path(__file__).resolve().parents[2]
GATE = ROOT / "scripts" / "check_tippy.sh"


def workspace_packages() -> set[str]:
    """The package names of the root workspace's members."""
    manifest = (ROOT / "Cargo.toml").read_text()
    members = manifest[manifest.index("members = ["):]
    members = members[:members.index("]")]
    names = set()
    for member in re.findall(r'"([^"]+)"', members):
        package = (ROOT / member / "Cargo.toml").read_text()
        package = package[package.index("[package]"):]
        names.add(re.search(r'^name\s*=\s*"([^"]+)"', package, re.M).group(1))
    return names



class TippyGateTests(unittest.TestCase):
    def run_gate(self, mode: str) -> tuple[subprocess.CompletedProcess[str], list[list[str]]]:
        with tempfile.TemporaryDirectory() as scratch:
            directory = Path(scratch)
            frontend = directory / "targo"
            calls = directory / "calls.jsonl"
            frontend.write_text(
                f"#!{sys.executable}\n"
                "import json, os, sys\n"
                "args = sys.argv[1:]\n"
                "with open(os.environ['TEST_TIPPY_CALLS'], 'a') as log:\n"
                "    log.write(json.dumps(args) + '\\n')\n"
                "package = args[args.index('-p') + 1]\n"
                "mode = os.environ['TEST_TIPPY_MODE']\n"
                "if mode == 'tooling' and package == 'trust-cg-cli':\n"
                "    print('frontend terminated without diagnostics', file=sys.stderr)\n"
                "    sys.exit(101)\n"
                "if mode in ('cli', 'both', 'mixed') and package == 'trust-cg-cli':\n"
                "    print('cli/tests/export.rs:7:1: error: a CLI lint finding', file=sys.stderr)\n"
                "    sys.exit(1)\n"
                "if mode == 'both' and package == 'trust-cg-verify':\n"
                "    print('verify/src/lib.rs:9:1: error: a verifier lint finding', file=sys.stderr)\n"
                "    sys.exit(1)\n"
                "if mode == 'mixed' and package == 'trust-cg-codegen':\n"
                "    print('codegen/tests/jit.rs:1:1: error: kernel JIT fixtures require exact compiler', file=sys.stderr)\n"
                "    sys.exit(1)\n"
            )
            frontend.chmod(0o700)
            env = os.environ.copy()
            env.update(
                TRUST_TARGO=str(frontend),
                TEST_TIPPY_CALLS=str(calls),
                TEST_TIPPY_MODE=mode,
            )
            result = subprocess.run(
                ["bash", str(GATE)], env=env, text=True, capture_output=True, check=False
            )
            return result, [json.loads(line) for line in calls.read_text().splitlines()]

    def test_clean_run_covers_cli_binaries_and_tests(self) -> None:
        result, calls = self.run_gate("clean")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        cli = [args for args in calls if "trust-cg-cli" in args]
        self.assertEqual(len(cli), 1)
        for flag in ("--bins", "--tests", "--locked", "--keep-going", "--no-deps"):
            self.assertIn(flag, cli[0])
        self.assertNotIn("--lib", cli[0])

    def test_clean_run_lints_every_workspace_member(self) -> None:
        result, calls = self.run_gate("clean")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        linted = {args[args.index("-p") + 1]: args for args in calls}
        self.assertEqual(len(linted), len(calls), "a package was linted twice")
        self.assertEqual(set(linted), workspace_packages())
        for package, args in linted.items():
            for flag in ("--tests", "--locked", "--keep-going", "--no-deps"):
                self.assertIn(flag, args, package)
            no_library = package in ("trust-cg-cli", "trust-cg-test")
            self.assertEqual("--lib" in args, not no_library, package)
        for package in ("trust-cg-sat-host", "trust-cg-onnx-import", "trust-cg-jit-matrix",
                        "trust-cg-fuzz", "trust-cg-llvm-import", "trust-cg-test", "trust-cg-cli"):
            self.assertIn("--bins", linted[package], package)
        self.assertEqual(
            linted["trust-cg-llvm-import"][linted["trust-cg-llvm-import"].index("--features") + 1],
            "driver",
        )
        self.assertIn(f"{len(calls)} package(s) clean", result.stdout + result.stderr)

    def test_cli_finding_fails_the_gate(self) -> None:
        result, _ = self.run_gate("cli")
        self.assertEqual(result.returncode, 1)
        self.assertIn("trust-cg-cli(1)", result.stdout + result.stderr)

    def test_earlier_finding_does_not_hide_cli_findings(self) -> None:
        result, calls = self.run_gate("both")
        self.assertEqual(result.returncode, 1)
        self.assertTrue(any("trust-cg-cli" in args for args in calls))
        self.assertIn("trust-cg-verify(1) trust-cg-cli(1)", result.stdout + result.stderr)

    def test_fixture_refusal_does_not_hide_a_cli_finding(self) -> None:
        result, _ = self.run_gate("mixed")
        self.assertEqual(result.returncode, 1)
        transcript = result.stdout + result.stderr
        self.assertIn("NOT LINTED", transcript)
        self.assertIn("trust-cg-cli(1)", transcript)

    def test_cli_frontend_failure_is_a_tooling_failure(self) -> None:
        result, _ = self.run_gate("tooling")
        self.assertEqual(result.returncode, 2)
        self.assertIn("TOOLING", result.stdout + result.stderr)
        self.assertNotIn("package(s) clean", result.stdout + result.stderr)


if __name__ == "__main__":
    unittest.main()
