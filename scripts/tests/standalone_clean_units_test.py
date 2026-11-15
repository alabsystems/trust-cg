#!/usr/bin/env python3
"""Compile actual production proof modules and refuse same-proof mutations.

Includes the unchanged sentinel controls. Rust uses the explicit unverified
lane; source typing grants no Rust, physical ABI or codegen-license verdict.
"""
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import unittest

import sentinel_clean_unit_test as sentinel

ROOT = Path(__file__).resolve().parents[2]


class StandaloneCleanUnitsTest(sentinel.SentinelCleanUnitTest):
    @classmethod
    def setUpClass(cls):
        super().setUpClass()
        cls.units = {
            "actual_dispatch": (
                ROOT / "crates/rustc-codegen-trust-cg/src/place_resolution_proofs.rs",
                ROOT / "proofs/mir_place_resolution_spec.lean", 42,
                "resolve_other_is_reject", "2021",
            ),
            "actual_bounds": (
                ROOT / "crates/trust-cg-opt/src/dec_iv_proofs.rs",
                ROOT / "benchmarks/step0-oracles/revloop/proof/dec_iv_bound.lean", 10,
                "dec_exact", "2024",
            ),
        }
        cls.input_hashes = {
            str(path): hashlib.sha256(path.read_bytes()).hexdigest()
            for unit in cls.units.values() for path in unit[:2]
        }
        mutations = {
            "wrong_dispatch": (
                cls.units["actual_dispatch"][1],
                "= Resolution.reject RejectReason.placeProjection :=",
                "= Resolution.reject RejectReason.borrowedScalarNoDeref :=",
            ),
            "wrong_bounds": (
                cls.units["actual_bounds"][1],
                "theorem guard_pos2 (p : Nat) (hg : 1 + 1 ≤ p) : 2 ≤ p := hg",
                "theorem guard_pos2 (p : Nat) (hg : 1 + 1 ≤ p) : 3 ≤ p := hg",
            ),
        }
        names = ["actual_sentinel", "true_theorem", "false_theorem", *cls.units, *mutations]
        (cls.work / "Cargo.toml").write_text(
            '[workspace]\nresolver="2"\nmembers=' + json.dumps(names) + "\n"
        )
        for name in [*cls.units, *mutations]:
            package = cls.work / name
            package.mkdir()
            edition = cls.units[name][4] if name in cls.units else "2021"
            (package / "Cargo.toml").write_text(
                '[package]\nname=' + json.dumps(name)
                + '\nversion="0.0.0"\nedition=' + json.dumps(edition)
                + '\n[lib]\npath="lib.rs"\n'
            )
            if name in cls.units:
                # Compile the actual complete Rust module, including its real
                # relative Lean path, rather than reconstructing that hook.
                module = cls.units[name][0]
                rust = "#[path = " + json.dumps(str(module)) + "]\nmod production_proofs;\n"
            else:
                source, old, new = mutations[name]
                text = source.read_text()
                if old not in text:
                    raise RuntimeError(f"missing mutation target in {source}")
                module = package / "unit.lean"
                module.write_text(text.replace(old, new, 1))
                rust = "#[path = " + json.dumps(str(module)) + "]\nclean mod mutated;\n"
            (package / "lib.rs").write_text(rust)
        lock = cls.run_targo("generate-lockfile", "--offline")
        if lock.returncode:
            raise RuntimeError(lock.stdout)

    def check_actual(self, name):
        result = self.check_package(name)
        self.assertEqual(result.returncode, 0, result.stdout)
        unit = self.units[name]
        self.assertIn(f"Clean island kernel-checked: {unit[2]} declaration(s) registered", result.stdout)
        self.assertIn(unit[3], result.stdout)
        for path in unit[:2]:
            self.assertEqual(hashlib.sha256(path.read_bytes()).hexdigest(), self.input_hashes[str(path)])

    def test_complete_dispatch_production_module(self):
        self.check_actual("actual_dispatch")

    def test_complete_reverse_induction_production_module(self):
        self.check_actual("actual_bounds")

    def check_mutation(self, name, theorem):
        result = self.check_package(name)
        self.assertNotEqual(result.returncode, 0, result.stdout)
        self.assertIn(theorem, result.stdout)
        self.assertIn("Type mismatch", result.stdout)
        self.assertNotIn("failed to parse", result.stdout)

    def test_same_dispatch_proof_refuses_changed_rejection(self):
        self.check_mutation("wrong_dispatch", "resolve_other_is_reject")

    def test_same_reverse_induction_proof_refuses_stronger_bound(self):
        self.check_mutation("wrong_bounds", "guard_pos2")


if __name__ == "__main__":
    if "--admitted" not in sys.argv:
        gate = shutil.which("build-slot")
        if gate is None:
            raise SystemExit("build-slot is required for compiler resource admission")
        raise SystemExit(subprocess.run(
            [gate, "--cpus", "1", "--mem-gb", "4", "--", sys.executable,
             str(Path(__file__).resolve()), "--admitted", *sys.argv[1:]],
            cwd=ROOT, pass_fds=sentinel.resource_fds(os.environ),
        ).returncode)
    sys.argv.remove("--admitted")
    unittest.main()
