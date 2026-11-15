#!/usr/bin/env python3
"""Compile the actual sentinel Clean unit and check same-route proof rejection.

Rust builds use the explicit unverified lane. Clean declaration typing remains
mandatory there; this test makes no Rust, ABI, NoUB or machine-code proof claim.
"""
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "scripts"))
from bump_trust_ir_pin import resource_fds


class SentinelCleanUnitTest(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        selected = os.environ.get("TRUST_TARGO_BIN") or shutil.which("targo")
        if not selected:
            raise RuntimeError("Trust Targo is required for sentinel Clean compilation")
        cls.targo = Path(selected).resolve()
        cls.trustc = cls.targo.with_name("trustc")
        if not cls.trustc.is_file():
            raise RuntimeError("the selected Targo needs its sibling Trust compiler")
        scratch = ROOT / "target" / ".ubd"
        scratch.mkdir(parents=True, exist_ok=True)
        cls.temporary = tempfile.TemporaryDirectory(prefix="sentinel-clean-unit-", dir=scratch)
        cls.addClassCleanup(cls.temporary.cleanup)
        cls.work = Path(cls.temporary.name)
        cls.source = ROOT / "proofs" / "sentinel_decide_spec.lean"
        cls.source_hash = hashlib.sha256(cls.source.read_bytes()).hexdigest()
        names = ["actual_sentinel", "true_theorem", "false_theorem"]
        (cls.work / "Cargo.toml").write_text(
            '[workspace]\nresolver="2"\nmembers=' + json.dumps(names) + "\n"
        )
        for name in names:
            package = cls.work / name
            package.mkdir()
            (package / "Cargo.toml").write_text(
                '[package]\nname=' + json.dumps(name)
                + '\nversion="0.0.0"\nedition="2021"\n[lib]\npath="lib.rs"\n'
            )
            unit = cls.source if name == names[0] else package / "unit.lean"
            if name != names[0]:
                unit.write_text(
                    "theorem arithmetic_probe : (1 : Nat) = "
                    + ("1" if name == names[1] else "2") + " := rfl\n"
                )
            (package / "lib.rs").write_text(
                "#[path = " + json.dumps(str(unit)) + "]\nclean mod sentinel_proofs;\n"
            )
        cls.env = dict(os.environ)
        for key in list(cls.env):
            if key.startswith("GIT_CONFIG") or key in {
                "GIT_DIR", "GIT_WORK_TREE", "GIT_INDEX_FILE", "GIT_COMMON_DIR",
                "SDKROOT", "RUSTC_WRAPPER", "RUSTC_WORKSPACE_WRAPPER",
                "CARGO_BUILD_RUSTC", "RUSTFLAGS", "RUSTDOCFLAGS", "RUSTC_BOOTSTRAP",
                "CARGO_ENCODED_RUSTFLAGS",
            }:
                cls.env.pop(key, None)
        cls.env.update(
            RUSTC=str(cls.trustc), CARGO_TARGET_DIR=str(cls.work / "build"),
            CARGO_HOME=str(cls.work / "cargo-home"), CARGO_NET_OFFLINE="true",
            CARGO_INCREMENTAL="0", CARGO_PROFILE_DEV_DEBUG="0",
        )
        cls.env["PATH"] = str(cls.targo.parent) + os.pathsep + cls.env.get("PATH", "")
        result = cls.run_targo("generate-lockfile", "--offline")
        if result.returncode:
            raise RuntimeError(result.stdout)

    @classmethod
    def run_targo(cls, *args):
        return subprocess.run(
            [str(cls.targo), *args], cwd=cls.work, env=cls.env,
            stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True,
            pass_fds=resource_fds(cls.env),
        )

    def check_package(self, name):
        return self.run_targo("--unverified", "check", "--locked", "--offline", "-p", name)

    def test_complete_actual_unit_is_kernel_checked(self):
        result = self.check_package("actual_sentinel")
        self.assertEqual(result.returncode, 0, result.stdout)
        self.assertRegex(result.stdout, r"Clean island kernel-checked: 170 declaration\(s\) registered")
        self.assertIn("TrustCg.Fnv128Carry.full_step_source_value", result.stdout)
        self.assertEqual(hashlib.sha256(self.source.read_bytes()).hexdigest(), self.source_hash)

    def test_true_theorem_uses_the_same_compiler_route(self):
        result = self.check_package("true_theorem")
        self.assertEqual(result.returncode, 0, result.stdout)
        self.assertIn("Clean island kernel-checked: 1 declaration(s) registered", result.stdout)

    def test_false_theorem_is_a_type_rejection(self):
        result = self.check_package("false_theorem")
        self.assertNotEqual(result.returncode, 0, result.stdout)
        self.assertIn("Type mismatch: expected 1 = 2, got 1 = 1", result.stdout)
        self.assertNotIn("failed to parse", result.stdout)


if __name__ == "__main__":
    if "--admitted" not in sys.argv:
        admission = shutil.which("build-slot")
        if admission is None:
            raise SystemExit("build-slot is required for compiler resource admission")
        result = subprocess.run(
            [admission, "--cpus", "1", "--mem-gb", "4",
             "--", sys.executable, str(Path(__file__).resolve()), "--admitted", *sys.argv[1:]],
            cwd=ROOT, pass_fds=resource_fds(os.environ),
        )
        raise SystemExit(result.returncode)
    sys.argv.remove("--admitted")
    unittest.main()
