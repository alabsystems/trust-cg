"""Cargo.lock and the tree-wide tuple must name one tuple.

Every case but the real-tree one builds a synthetic repository; that one only
checks that the real tree's report is complete and that its exit status follows
it. scripts/bump_trust_ir_pin.py is read only for its owned-file constants.
"""

from __future__ import annotations

import ast
import contextlib
import importlib.util
import io
import json
from pathlib import Path
import tempfile
import unittest


ROOT = Path(__file__).resolve().parents[2]
SPEC = importlib.util.spec_from_file_location("check_companion_coherence", ROOT / "scripts/check_companion_coherence.py")
assert SPEC is not None and SPEC.loader is not None
COHERENCE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(COHERENCE)

IR, CLEAN, AY = "1" * 40, "2" * 40, "3" * 40
OLD = "4" * 40
ORG = "https://github.com/example"
SCHEME = "git" + "+"


def lock_source(repository: str, revision: str) -> str:
    return f"{SCHEME}{ORG}/{repository}.git?rev={revision}#{revision}"


def package(name: str, identity: str = "") -> str:
    text = f'\n[[package]]\nname = "{name}"\nversion = "0.1.0"\n'
    return text + (f'source = "{identity}"\n' if identity else "")


def lock(ir: str = IR, clean: str = CLEAN, ay: str = AY, with_ay: bool = True, extra: str = "") -> str:
    text = "version = 4\n" + package("serde")
    text += package("trust-ir", lock_source("trust-ir", ir))
    text += package("clean-kernel", lock_source("clean", clean))
    if with_ay:
        text += package("ay-pb", lock_source("ay", ay)) + package("ay-sat", lock_source("ay", ay))
    return text + extra


class CompanionCoherenceTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory(prefix="trust-cg-coherence-")
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)
        dep = f'git = "{ORG}/trust-ir.git", rev = "{IR}"'
        self.write("Cargo.toml", f"[workspace.dependencies]\ntrust-ir = {{ {dep} }}\n")
        self.write("crates/rustc-codegen-trust-cg/Cargo.toml", f"[dependencies]\ntrust-ir = {{ {dep} }}\n")
        self.write(
            "crates/trust-cg-regalloc/Cargo.toml",
            f'[dependencies]\nay-pb = {{ version = "0.26.0", git = "{ORG}/ay.git", rev = "{AY}", optional = true }}\n',
        )
        self.write(
            "crates/trust-cg-codegen/src/compile_artifact_cache_profile.rs",
            f'pub const COMPILE_ARTIFACT_DEFAULT_TRUST_IR_IDENTITY: &str =\n    "trust_ir:{IR}";\n'
            f'pub const COMPILE_ARTIFACT_DEFAULT_AY_IDENTITY: &str =\n    "ay:{AY}";\n',
        )
        for relative in COHERENCE.LOCKS:
            self.write(relative, lock(with_ay=relative in COHERENCE.AY_LOCKS))

    def write(self, relative: str, text: str) -> None:
        path = self.root / relative
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text)

    def run_check(self, *extra: str) -> tuple[int, str, str]:
        stdout, stderr = io.StringIO(), io.StringIO()
        with contextlib.redirect_stdout(stdout), contextlib.redirect_stderr(stderr):
            code = COHERENCE.main(["--root", str(self.root), *extra])
        return code, stdout.getvalue(), stderr.getvalue()

    def assertDisagreement(self, fragment: str) -> dict:
        code, stdout, _ = self.run_check()
        self.assertEqual(code, 1, stdout)
        self.assertIn(f"DISAGREEMENT: {fragment}", stdout)
        report = COHERENCE.coherence(self.root)
        self.assertEqual(report["status"], "incoherent")
        self.assertTrue(any(fragment in item for item in report["disagreements"]), report["disagreements"])
        return report

    def test_coherent_tuple_passes_and_reports_every_source(self):
        code, stdout, _ = self.run_check()
        self.assertEqual(code, 0, stdout)
        self.assertIn("companion identities: COHERENT", stdout)
        report = COHERENCE.coherence(self.root)
        self.assertEqual((report["disagreements"], report["errors"]), ([], []))
        self.assertEqual(set(report["companions"]), {"TrustIr", "Clean", "AY"})
        clean = report["companions"]["Clean"]["sources"]
        self.assertEqual(clean["Cargo.lock"]["revision"], CLEAN)
        self.assertEqual(clean[COHERENCE.TREE]["revision"], CLEAN)
        self.assertNotIn("soundness_revs.lock", clean)
        code, stdout, _ = self.run_check("--json")
        self.assertEqual((code, json.loads(stdout)["status"]), (0, "coherent"))

    def test_split_tree_and_split_root_lock_are_reported(self):
        self.write("fuzz/Cargo.lock", lock(clean=OLD, with_ay=False))
        self.assertDisagreement(f"{COHERENCE.TREE}: tree resolves split Clean revisions")
        self.write("fuzz/Cargo.lock", lock(with_ay=False))
        self.write("Cargo.lock", lock(extra=package("ay-extra", lock_source("ay", OLD))))
        report = self.assertDisagreement("AY: Cargo.lock pins 2 revisions")
        self.assertIsNone(report["companions"]["AY"]["sources"][COHERENCE.TREE])

    def test_malformed_sources_fail_closed(self):
        self.write("Cargo.lock", lock(with_ay=False))
        code, stdout, _ = self.run_check()
        self.assertEqual(code, 1)
        self.assertIn("AY: Cargo.lock pins no ay source", stdout)

    def test_unreadable_required_file_exits_two(self):
        (self.root / COHERENCE.CACHE).unlink()
        code, _, stderr = self.run_check()
        self.assertEqual(code, 2)
        self.assertIn("companion coherence check failed", stderr)

    def test_real_tree_report_is_complete_and_its_status_decides_the_exit(self):
        report = COHERENCE.coherence(ROOT)
        self.assertEqual(set(report["companions"]), {"TrustIr", "Clean", "AY"})
        for label, companion in report["companions"].items():
            self.assertIsNotNone(companion["sources"]["Cargo.lock"], label)
        self.assertEqual(report["status"] == "coherent", not report["disagreements"] and not report["errors"])
        stdout = io.StringIO()
        with contextlib.redirect_stdout(stdout):
            code = COHERENCE.main(["--root", str(ROOT)])
        self.assertEqual(code, 0 if report["status"] == "coherent" else 1)


class TreeTupleTests(unittest.TestCase):
    """The tree-split detection: every manifest, lock and cache identity names one revision."""

    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory(prefix="trust-cg-tree-tuple-")
        self.root = Path(self.temporary.name)
        dep = f'git = "{ORG}/trust-ir.git", rev = "{IR}"'
        self.write(
            "Cargo.toml",
            "[workspace.dependencies]\n"
            f'#     [patch."{ORG}/trust-ir.git"] stays uncommitted\n'
            f"trust-ir = {{ {dep}, features = [\"serde\"] }}\n"
            f"trust-ir-build = {{ {dep} }}\n",
        )
        self.write(
            "crates/rustc-codegen-trust-cg/Cargo.toml",
            f"[dependencies]\ntrust-ir = {{ {dep} }}\n",
        )
        self.write(
            "crates/trust-cg-regalloc/Cargo.toml",
            "[dependencies]\n"
            f'ay-pb = {{ version = "0.26.0", git = "{ORG}/ay.git", rev = "{AY}", optional = true }}\n'
            f'ay-sat = {{ version = "0.26.0", git = "{ORG}/ay.git", rev = "{AY}", optional = true }}\n',
        )
        self.write(
            "crates/trust-cg-codegen/src/compile_artifact_cache_profile.rs",
            f'pub const COMPILE_ARTIFACT_DEFAULT_TRUST_IR_IDENTITY: &str =\n    "trust_ir:{IR}";\n'
            f'pub const COMPILE_ARTIFACT_DEFAULT_AY_IDENTITY: &str =\n    "ay:{AY}";\n',
        )
        for relative in COHERENCE.LOCKS:
            self.write(relative, self.lock(with_ay=relative in COHERENCE.AY_LOCKS))

    def tearDown(self):
        self.temporary.cleanup()

    def write(self, relative: str, text: str) -> None:
        path = self.root / relative
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text)

    def read(self, relative: str) -> str:
        return (self.root / relative).read_text()

    def lock(self, ir: str = IR, clean: str = CLEAN, ay: str = AY, with_ay: bool = True) -> str:
        text = "version = 4\n" + package("serde")
        text += package("trust-ir", lock_source("trust-ir", ir))
        text += package("trust-ir-build", lock_source("trust-ir", ir))
        text += package("clean-kernel", lock_source("clean", clean))
        if with_ay:
            text += package("ay-pb", lock_source("ay", ay)) + package("ay-sat", lock_source("ay", ay))
        return text

    def assertRefused(self, fragment: str) -> None:
        errors = COHERENCE.tree_tuple(self.root)[1]
        self.assertTrue(any(fragment in error for error in errors), errors)
        stdout = io.StringIO()
        with contextlib.redirect_stdout(stdout):
            self.assertEqual(COHERENCE.main(["--root", str(self.root)]), 1)
        self.assertIn(fragment, stdout.getvalue())

    def test_matching_tree_resolves_one_revision_per_companion(self):
        self.assertEqual(COHERENCE.tree_tuple(self.root), ({"TrustIr": IR, "Clean": CLEAN, "AY": AY}, []))

    def test_fuzz_lock_may_resolve_the_same_ay_but_not_another(self):
        self.write("fuzz/Cargo.lock", self.lock())
        self.assertEqual(COHERENCE.tree_tuple(self.root)[1], [])
        self.write("fuzz/Cargo.lock", self.lock(ay=OLD))
        self.assertRefused("tree resolves split AY revisions")

    def test_split_or_mutable_tree_is_refused_before_comparison(self):
        bridge_lock = "crates/rustc-codegen-trust-cg/Cargo.lock"
        cases = [
            ("tree resolves split TrustIr revisions",
             lambda: self.write(bridge_lock, self.lock(ir=OLD))),
            ("tree resolves split Clean revisions",
             lambda: self.write("fuzz/Cargo.lock", self.lock(clean=OLD, with_ay=False))),
            ("not an exact rev#rev identity",
             lambda: self.write("Cargo.lock", self.read("Cargo.lock").replace(
                 f"clean.git?rev={CLEAN}#{CLEAN}", "clean.git?branch=main#" + CLEAN))),
            ("Cargo.lock: resolves no ay package",
             lambda: self.write("Cargo.lock", self.lock(with_ay=False))),
            ("mutable or local selector",
             lambda: self.write("crates/rustc-codegen-trust-cg/Cargo.toml",
                                f'trust-ir = {{ git = "{ORG}/trust-ir.git", branch = "main" }}\n')),
            ("lacks an exact 40-hex rev",
             lambda: self.write("crates/trust-cg-regalloc/Cargo.toml",
                                f'ay-pb = {{ git = "{ORG}/ay.git", rev = "849c19fa" }}\n')),
            ("no pinned trust-ir dependency",
             lambda: self.write("crates/rustc-codegen-trust-cg/Cargo.toml", "[dependencies]\n")),
            ("COMPILE_ARTIFACT_DEFAULT_AY_IDENTITY must be defined once",
             lambda: self.write("crates/trust-cg-codegen/src/compile_artifact_cache_profile.rs",
                                f'pub const COMPILE_ARTIFACT_DEFAULT_TRUST_IR_IDENTITY: &str = "trust_ir:{IR}";\n')),
            ("tree resolves split AY revisions",
             lambda: self.write("crates/trust-cg-codegen/src/compile_artifact_cache_profile.rs",
                                self.read("crates/trust-cg-codegen/src/compile_artifact_cache_profile.rs")
                                .replace(f"ay:{AY}", f"ay:{OLD}"))),
        ]
        for fragment, mutate in cases:
            with self.subTest(fragment):
                self.tearDown()
                self.setUp()
                mutate()
                self.assertRefused(fragment)

    def test_owned_files_mirror_the_pin_bump_transaction(self):
        tree = ast.parse((ROOT / "scripts/bump_trust_ir_pin.py").read_text())
        constants = {}
        for node in tree.body:
            if isinstance(node, ast.Assign) and len(node.targets) == 1 and isinstance(node.targets[0], ast.Name):
                try:
                    constants[node.targets[0].id] = ast.literal_eval(node.value)
                except ValueError:
                    continue
        self.assertEqual(tuple(constants["MANIFESTS"]), COHERENCE.MANIFESTS)
        self.assertEqual(tuple(constants["LOCKS"]), COHERENCE.LOCKS)
        self.assertEqual(constants["REGALLOC"], COHERENCE.REGALLOC)
        self.assertEqual(constants["CACHE"], COHERENCE.CACHE)
        self.assertEqual(
            {constants["CACHE_NAME"], constants["AY_CACHE_NAME"]},
            {name for name, _ in COHERENCE.CACHE_CONSTANTS.values()},
        )


if __name__ == "__main__":
    unittest.main()
