"""run_full_test_matrix.sh probes the package its shards build with, never a PATH shim.

The matrix runs `targo metadata` twice (the auto-shard census and the
shard-policy check that keeps the test denominator complete), reads
`trustc --version` (recorded in the report; it also picks libtest's JSON or
plain format) and asks `trustc --print sysroot` (the proof-gate hint). Each
must run the package scripts/trust_cargo.sh builds the shards with: the file
scripts/trust_toolchain.py resolves for the `workspace` purpose, or
$TRUST_TARGO. The PATH `targo` and `trustc` may be atpkg launcher shims whose
shell prelude the resolver accepts without running
(DR-ATPKG-PRELUDE-SHIM-20261015); a matrix that executed them would measure
whatever such a prelude prints.

The dry runs here use a fake package (scripts/tests/atpkg_prelude_fixture.py)
whose metadata lists exactly the plan's packages and targets. No Cargo or real
toolchain runs.
"""

from __future__ import annotations

import json
import os
from pathlib import Path
import shlex
import subprocess
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parent))
import atpkg_prelude_fixture as FIXTURE  # noqa: E402


ROOT = Path(__file__).resolve().parents[2]
MATRIX = ROOT / "scripts" / "run_full_test_matrix.sh"
SOURCE = MATRIX.read_text()
SCRIPT = ROOT / "scripts" / "trust_toolchain.py"


def plan_metadata() -> dict:
    """`cargo metadata` for a workspace that is exactly the matrix's plan: each
    planned crate, with every integration target a shard names."""
    plan = SOURCE.split("read -r -d '' SHARD_PLAN <<'EOF' || true\n", 1)[1].split("\nEOF\n", 1)[0]
    targets: dict[str, set[str]] = {}
    for line in plan.splitlines():
        if not line.strip():
            continue
        crate, _, arguments = line.split("|")[:3]
        words = shlex.split(arguments)
        named = targets.setdefault(crate, set())
        named.update(words[index + 1] for index, word in enumerate(words[:-1]) if word == "--test")
    packages = [
        {"name": crate, "id": f"path+file:///fixture/{crate}#0.0.0", "features": {},
         "targets": [{"name": name, "kind": ["test"], "test": True, "required-features": []}
                     for name in sorted(names)]}
        for crate, names in sorted(targets.items())
    ]
    return {"packages": packages, "workspace_members": [package["id"] for package in packages]}


def ghost_metadata(metadata: dict) -> dict:
    """`metadata` plus a workspace package the plan does not cover."""
    ghost = {"name": "ghost-package", "id": "ghost 0.0.0", "features": {}, "targets": []}
    return {"packages": metadata["packages"] + [ghost],
            "workspace_members": metadata["workspace_members"] + [ghost["id"]]}


class MatrixRunsThePackageTests(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory(prefix="trust-cg-matrix-package-")
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name).resolve()
        self.metadata = plan_metadata()
        self.package = FIXTURE.make_package(self.root / "pkg", metadata=self.metadata)
        self.log = self.root / "shim-calls.log"
        self.shims = self.root / "atpkg-bin"
        # The preludes answer the questions the matrix asks: a census with a
        # package no shard covers, and a nightly compiler.
        FIXTURE.lying_shim(self.shims / "targo", self.package / "bin" / "targo", self.log,
                           {"metadata*": json.dumps(ghost_metadata(self.metadata),
                                                   separators=(",", ":"))})
        FIXTURE.lying_shim(self.shims / "trustc", self.package / "bin" / "trustc", self.log,
                           {"--version": "rustc 1.99.0-nightly (forged by a prelude)",
                            "--print sysroot": str(self.root)})
        self.sysbin = self.root / "sysbin"
        self.sysbin.mkdir()
        (self.sysbin / "python3").symlink_to(sys.executable)

    def environment(self, *directories: Path, **extra: str) -> dict:
        environment = {key: value for key, value in os.environ.items()
                       if not key.startswith(("TRUST_CG_", "TCG_"))
                       and key not in {"TRUST_TARGO", "RUST_TEST_NOCAPTURE", "BASH_ENV", "ENV", "CI",
                                       "GITHUB_ACTIONS"}}
        environment["PATH"] = ":".join([*(str(path) for path in directories), str(self.sysbin),
                                        "/usr/bin", "/bin"])
        environment.update(extra)
        return environment

    def dry_run(self, environment: dict) -> subprocess.CompletedProcess:
        return subprocess.run(
            ["bash", str(MATRIX), "--dry-run", "--out", str(self.root / "matrix.json")],
            env=environment, text=True, capture_output=True, timeout=120, check=False,
        )

    def test_the_lying_shims_are_accepted_and_would_change_the_verdict(self):
        # Non-vacuity: the resolver follows both shims to the package, and
        # each prelude does answer differently from the package it execs.
        resolved = subprocess.run(
            [sys.executable, "-B", str(SCRIPT), "--purpose", "workspace", "--print", "json"],
            env=self.environment(self.shims), text=True, capture_output=True, timeout=60, check=False,
        )
        self.assertEqual(resolved.returncode, 0, resolved.stderr)
        record = json.loads(resolved.stdout)
        self.assertEqual(record["selection"], "path-launcher")
        self.assertEqual(record["targo"], str(self.package / "bin" / "targo"))
        census = subprocess.run([str(self.shims / "targo"), "metadata"], text=True,
                                capture_output=True, timeout=60, check=True)
        self.assertIn("ghost-package", census.stdout)
        version = subprocess.run([str(self.shims / "trustc"), "--version"], text=True,
                                 capture_output=True, timeout=60, check=True)
        self.assertIn("nightly", version.stdout)
        self.assertEqual(len(FIXTURE.logged(self.log)), 2)

    def test_dry_run_measures_the_resolved_package_not_the_path_shims(self):
        result = self.dry_run(self.environment(self.shims))
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertNotIn("ghost-package", result.stderr)
        self.assertIn(f"Shard policy OK: {len(self.metadata['packages'])} workspace packages covered",
                      result.stdout)
        # The package compiler is stable, so libtest keeps its plain format.
        self.assertNotIn("--format json", result.stdout)
        self.assertEqual(FIXTURE.logged(self.log), [], "the matrix executed a PATH launcher shim")

    def test_the_compiler_version_and_libtest_format_come_from_the_package(self):
        # Only trustc lies here, so the census passes either way and the plan
        # shows which `--version` picked the libtest format.
        FIXTURE.lying_shim(self.shims / "targo", self.package / "bin" / "targo", self.log)
        result = self.dry_run(self.environment(self.shims))
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn("--show-output", result.stdout)
        self.assertNotIn("--format json", result.stdout)
        self.assertEqual(FIXTURE.logged(self.log), [], "the matrix executed a PATH launcher shim")

    def test_trust_targo_is_the_package_when_set(self):
        # scripts/trust_cargo.sh builds with $TRUST_TARGO when it is set, so
        # the census runs it too, with no Trust tool on PATH at all.
        result = self.dry_run(self.environment(TRUST_TARGO=str(self.package / "bin" / "targo")))
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn("Shard policy OK", result.stdout)
        relative = self.dry_run(self.environment(self.shims, TRUST_TARGO="pkg/bin/targo"))
        self.assertEqual(relative.returncode, 1, relative.stdout + relative.stderr)
        self.assertIn("TRUST_TARGO must be an absolute path", relative.stderr)
        self.assertEqual(FIXTURE.logged(self.log), [])

    def test_no_resolvable_package_fails_before_any_census(self):
        result = self.dry_run(self.environment())
        self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
        self.assertIn("no installed Trust toolchain resolves", result.stderr)
        self.assertNotIn("Shard policy OK", result.stdout)


class ProofGateHintTests(unittest.TestCase):
    """The proof-gate hint reads the resolved sysroot, never `trustc` on PATH."""

    PREFLIGHT = "# P0 proof gate:" + SOURCE.split("# P0 proof gate:", 1)[1].split(
        'if [ "${DRY_RUN}" -eq 1 ]; then', 1)[0]
    TRUST_ENV = SOURCE[SOURCE.index("trust_env() {"):SOURCE.index("\n}\n", SOURCE.index("trust_env() {")) + 3]

    def run_preflight(self, directory: Path, **extra: str) -> subprocess.CompletedProcess:
        probe = directory / "check_proof_gate.sh"
        probe.write_text("#!/bin/sh\nprintf 'PROBE_RAN\\n'\n")
        probe.chmod(0o755)
        environment = {key: value for key, value in os.environ.items() if key not in {
            "AY_SOLVER_PATH", "TCG_EXTERNAL_CLEAN_CHECKER", "TCG_CLEAN_CHECKER",
            "TRUST_CG_PROOF_GATE", "CI", "GITHUB_ACTIONS", "BASH_ENV", "ENV", "MATRIX_TRUST_SYSROOT",
        }}
        environment.update(PATH=f"{directory}:/usr/bin:/bin", SCRIPT_DIR=str(directory), DRY_RUN="0")
        environment.update(extra)
        return subprocess.run(["/bin/bash", "-c", self.TRUST_ENV + self.PREFLIGHT], env=environment,
                              text=True, capture_output=True, timeout=60, check=False)

    def test_only_the_resolved_sysroot_advertises_its_ay(self):
        with tempfile.TemporaryDirectory(prefix="trust-cg-matrix-hint-") as temporary:
            directory = Path(temporary).resolve()
            forged = directory / "forged-sysroot"
            (forged / "bin").mkdir(parents=True)
            (forged / "bin" / "ay").write_text("#!/bin/sh\n")
            (forged / "bin" / "ay").chmod(0o755)
            liar = directory / "trustc"
            liar.write_text(f"#!/bin/sh\nprintf '%s\\n' '{forged}'\n")
            liar.chmod(0o755)
            ignored = self.run_preflight(directory)
            self.assertEqual(ignored.returncode, 0, ignored.stderr)
            self.assertNotIn("PROBE_RAN", ignored.stdout)
            self.assertIn("STRICT PROOF GATE SKIPPED", ignored.stderr)
            resolved = self.run_preflight(directory, MATRIX_TRUST_SYSROOT=str(forged))
            self.assertEqual(resolved.returncode, 0, resolved.stderr)
            self.assertIn("PROBE_RAN", resolved.stdout)


if __name__ == "__main__":
    unittest.main()
