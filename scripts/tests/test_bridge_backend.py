"""Pin scripts/bridge_backend.py: the host suffix, newest-candidate resolution,
and the fail-closed freshness rule the measurement entry points share."""

from __future__ import annotations

import importlib.util
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest


ROOT = Path(__file__).resolve().parents[2]
SCRIPT = ROOT / "scripts" / "bridge_backend.py"
SPEC = importlib.util.spec_from_file_location("bridge_backend", SCRIPT)
backend = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(backend)


class BridgeBackendTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory(prefix="trust-cg-backend-")
        self.addCleanup(self.temporary.cleanup)
        # Resolved: on macOS the temporary root is behind the /var -> /private/var
        # symlink, and stale_source reports include_str!/include_bytes! inputs by
        # their resolved path but manifests by their repo-relative one.
        self.repo = Path(self.temporary.name).resolve()
        self.source = self.repo / "crates" / "trust-cg-core" / "src" / "lib.rs"
        self.source.parent.mkdir(parents=True)
        self.source.write_text("// backend source\n")
        os.utime(self.source, (1_000_000_000, 1_000_000_000))

    def build(self, index: int, mtime: int) -> Path:
        path = backend.candidates(self.repo)[index]
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(b"backend")
        os.utime(path, (mtime, mtime))
        return path

    def cli(self, *arguments: str) -> subprocess.CompletedProcess:
        return subprocess.run([sys.executable, str(SCRIPT), "--repo", str(self.repo), *arguments],
                              capture_output=True, text=True, timeout=60, check=False)

    def test_suffix_follows_the_platform(self):
        self.assertEqual(backend.suffix("darwin"), ".dylib")
        self.assertEqual(backend.suffix("linux"), ".so")
        self.assertEqual(backend.file_name("linux"), "librustc_codegen_trust_cg.so")
        self.assertTrue(all(path.name == "librustc_codegen_trust_cg.dylib"
                            for path in backend.candidates(self.repo, "darwin")))
        self.assertEqual(backend.candidates(self.repo, "linux")[0],
                         self.repo / "crates/rustc-codegen-trust-cg/target-bridge/release"
                         / "librustc_codegen_trust_cg.so")

    def test_the_newest_candidate_wins_and_ties_keep_preference_order(self):
        self.assertIsNone(backend.newest(self.repo))
        old = self.build(0, 2_000_000_000)
        new = self.build(2, 2_000_000_100)
        self.assertEqual(backend.newest(self.repo), new)
        os.utime(new, (2_000_000_000, 2_000_000_000))
        self.assertEqual(backend.newest(self.repo), old)

    def test_a_backend_older_than_a_backend_source_is_stale(self):
        path = self.build(0, 2_000_000_000)
        self.assertIsNone(backend.stale_source(self.repo, path))
        for relative in ("crates/trust-cg-core/tests/t.rs", "crates/trust-cg-core/benches/b.rs",
                         "crates/trust-cg-core/examples/e.rs", "crates/x/target/debug/build/g.rs"):
            ignored = self.repo / relative
            ignored.parent.mkdir(parents=True, exist_ok=True)
            ignored.write_text("// not in the cdylib\n")
            with self.subTest(ignored=relative):
                self.assertIsNone(backend.stale_source(self.repo, path))
        os.utime(self.source, (2_000_000_100, 2_000_000_100))
        self.assertEqual(backend.stale_source(self.repo, path), self.source)
        with self.assertRaises(backend.BackendError):
            backend.resolve(self.repo)
        self.assertEqual(backend.resolve(self.repo, allow_stale=True), (path, self.source))

    def test_sources_are_matched_by_path_components_not_substrings(self):
        path = self.build(0, 2_000_000_000)
        cases = (
            "crates/trust-cg-codegen/src/target.rs",            # "/target" substring
            "crates/trust-cg-ir/src/target_info.rs",
            "crates/trust-cg-codegen/src/target/mod.rs",       # a module directory named target
            "crates/trust-cg-core/src/testsuite.rs",
        )
        for relative in cases:
            source = self.repo / relative
            source.parent.mkdir(parents=True, exist_ok=True)
            source.write_text("// compiled into the backend\n")
            os.utime(source, (2_000_000_100, 2_000_000_100))
            with self.subTest(source=relative):
                self.assertEqual(backend.stale_source(self.repo, path), source)
            source.unlink()
        # Ignored: a unit-test module directory and a nested Cargo build directory.
        for relative, marker in (("crates/trust-cg-opt/src/vectorize/tests/t.rs", None),
                                 ("crates/trust-cg-core/fuzz/out/build/g.rs", "crates/trust-cg-core/fuzz/out")):
            source = self.repo / relative
            source.parent.mkdir(parents=True, exist_ok=True)
            source.write_text("// not in the cdylib\n")
            os.utime(source, (2_000_000_100, 2_000_000_100))
            if marker:
                (self.repo / marker / "CACHEDIR.TAG").write_text("Signature: 8a477f597d28d172789f06886806bc55\n")
            with self.subTest(ignored=relative):
                self.assertIsNone(backend.stale_source(self.repo, path))

    def test_non_rust_build_inputs_make_the_backend_stale(self):
        """Embedded data, manifests, the lock (trust-ir pin) and the toolchain pin
        are build inputs too; documentation and test fixtures are not."""
        path = self.build(0, 2_000_000_000)
        verify = self.repo / "crates" / "trust-cg-verify"
        (verify / "src").mkdir(parents=True)
        (verify / "src" / "lib.rs").write_text(
            'const DB: &str = include_str!("../verdict_db/tier0.vdb");\n'
            'const BIN: &[u8] = include_bytes!("../tests/fixtures/blob.bin");\n')
        os.utime(verify / "src" / "lib.rs", (1_000_000_000, 1_000_000_000))
        inputs = {
            "crates/trust-cg-verify/verdict_db/tier0.vdb": True,
            "crates/trust-cg-verify/tests/fixtures/blob.bin": True,   # named by include_bytes!
            "crates/trust-cg-verify/Cargo.toml": True,
            "crates/rustc-codegen-trust-cg/Cargo.lock": True,
            "crates/rustc-codegen-trust-cg/rust-toolchain.toml": True,
            "crates/trust-cg-sat-host/src/solver.c": True,
            "Cargo.toml": True,                                        # workspace inheritance
            ".cargo/config.toml": True,
            "crates/trust-cg-verify/README.md": False,
            "crates/rustc-codegen-trust-cg/fixtures/crate/Cargo.toml": False,
            "crates/trust-cg-verify/tests/fixtures/unused.bin": False,
            "crates/trust-cg-verify/src/.lib.rs.swp": False,
        }
        for relative in inputs:
            target = self.repo / relative
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_text("x\n")
            os.utime(target, (1_000_000_000, 1_000_000_000))
        self.assertIsNone(backend.stale_source(self.repo, path))
        for relative, is_input in inputs.items():
            target = self.repo / relative
            os.utime(target, (2_000_000_100, 2_000_000_100))
            with self.subTest(input=relative):
                found = backend.stale_source(self.repo, path)
                self.assertEqual(found, target.resolve() if is_input else None)
            os.utime(target, (1_000_000_000, 1_000_000_000))

    def write(self, relative: str, text: str, mtime: int = 1_000_000_000) -> Path:
        path = self.repo / relative
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text)
        os.utime(path, (mtime, mtime))
        return path

    def bridge_lock(self, *path_packages: str, extra: str = "") -> None:
        blocks = ["version = 4\n"]
        blocks += [f'[[package]]\nname = "{name}"\nversion = "0.7.0"\n' for name in path_packages]
        blocks.append('[[package]]\nname = "serde"\nversion = "1.0.0"\n'
                      'source = "registry+https://github.com/rust-lang/crates.io-index"\n')
        self.write("crates/rustc-codegen-trust-cg/Cargo.lock", "\n".join(blocks) + extra)

    def test_only_crates_the_bridge_lock_compiles_are_inputs(self):
        """A crate outside the bridge's path packages (the CLI here) cannot make
        a just-built backend stale; one inside it still does."""
        self.write("crates/rustc-codegen-trust-cg/Cargo.toml", '[package]\nname = "rustc_codegen_trust_cg"\n')
        self.write("crates/trust-cg-core/Cargo.toml", '[package]\nname = "trust-cg-core"\nversion = "0.7.0"\n')
        self.write("crates/trust-cg-cli/Cargo.toml", '[package]\nname = "trust-cg-cli"\n\n[dependencies]\nx = "1"\n')
        cli = self.write("crates/trust-cg-cli/src/main.rs", "fn main() {}\n")
        self.bridge_lock("rustc_codegen_trust_cg", "trust-cg-core")
        self.assertEqual(backend.bridge_crate_directories(self.repo), {"rustc-codegen-trust-cg", "trust-cg-core"})
        path = self.build(0, 2_000_000_000)
        os.utime(cli, (2_000_000_100, 2_000_000_100))
        self.assertIsNone(backend.stale_source(self.repo, path))
        os.utime(self.source, (2_000_000_100, 2_000_000_100))
        self.assertEqual(backend.stale_source(self.repo, path), self.source)
        os.utime(self.source, (1_000_000_000, 1_000_000_000))
        # A path package no crate manifest names: the set is unknown, so every crate is scanned.
        self.bridge_lock("rustc_codegen_trust_cg", "trust-cg-core", "trust-cg-moved")
        os.utime(self.repo / "crates/rustc-codegen-trust-cg/Cargo.lock", (1_000_000_000, 1_000_000_000))
        self.assertIsNone(backend.bridge_crate_directories(self.repo))
        self.assertEqual(backend.stale_source(self.repo, path), cli)
        # No lock, or one without path packages: every crate is scanned.
        (self.repo / "crates/rustc-codegen-trust-cg/Cargo.lock").unlink()
        self.assertIsNone(backend.bridge_crate_directories(self.repo))
        self.bridge_lock()
        self.assertIsNone(backend.bridge_crate_directories(self.repo))

    def test_shared_path_modules_are_inputs_unless_test_only(self):
        self.write("crates/rustc-codegen-trust-cg/Cargo.toml", '[package]\nname = "rustc_codegen_trust_cg"\n')
        self.write("crates/trust-cg-core/Cargo.toml", '[package]\nname = "trust-cg-core"\n')
        self.bridge_lock("rustc_codegen_trust_cg", "trust-cg-core")
        shared = self.write("crates/test_support/shared.rs", "// shared source\n")
        self.write("crates/trust-cg-core/src/lib.rs",
                   '#[cfg(test)]\n#[path = "../../test_support/shared.rs"]\nmod shared;\n'
                   '#[cfg(all(test, target_os = "macos"))]\n#[path = "../tests/common/run.rs"]\nmod run;\n')
        runner = self.write("crates/trust-cg-core/tests/common/run.rs", "// test runner\n")
        path = self.build(0, 2_000_000_000)
        for source in (shared, runner):
            os.utime(source, (2_000_000_100, 2_000_000_100))
        self.assertIsNone(backend.stale_source(self.repo, path))
        # The same module compiled into the library is an input of the backend.
        self.write("crates/trust-cg-core/src/lib.rs",
                   '#[doc(hidden)]\n#[path = "../../test_support/shared.rs"]\nmod shared;\n')
        self.assertEqual(backend.stale_source(self.repo, path), shared.resolve())

    def test_a_checkout_path_cannot_switch_the_check_off(self):
        for parent in ("tests", "target-checkouts", "examples"):
            repo = self.repo / parent / "checkout"
            source = repo / "crates" / "trust-cg-core" / "src" / "lib.rs"
            source.parent.mkdir(parents=True)
            source.write_text("// backend source\n")
            path = backend.candidates(repo)[0]
            path.parent.mkdir(parents=True)
            path.write_bytes(b"backend")
            os.utime(path, (2_000_000_000, 2_000_000_000))
            os.utime(source, (2_000_000_100, 2_000_000_100))
            with self.subTest(parent=parent):
                self.assertEqual(backend.stale_source(repo, path), source)

    def test_missing_backends_are_refused(self):
        with self.assertRaisesRegex(backend.BackendError, "no bridge backend is built"):
            backend.resolve(self.repo)
        with self.assertRaisesRegex(backend.BackendError, "bridge backend missing"):
            backend.resolve(self.repo, self.repo / "absent.so")

    def test_cli_exit_codes(self):
        self.assertEqual(self.cli("--print", "path").returncode, 2)
        path = self.build(0, 2_000_000_000)
        result = self.cli("--print", "path")
        self.assertEqual((result.returncode, result.stdout.strip()), (0, str(path)))
        explicit = self.cli("--print", "path", "--backend", str(path))
        self.assertEqual(explicit.stdout.strip(), str(path))
        os.utime(self.source, (2_000_000_100, 2_000_000_100))
        stale = self.cli("--print", "path")
        self.assertEqual(stale.returncode, 2)
        self.assertIn("STALE", stale.stderr)
        allowed = self.cli("--print", "path", "--allow-stale")
        self.assertEqual((allowed.returncode, allowed.stdout.strip()), (0, str(path)))
        self.assertIn("not evidence", allowed.stderr)
        self.assertEqual(self.cli("--print", "suffix").stdout.strip(), backend.suffix())


if __name__ == "__main__":
    unittest.main()
