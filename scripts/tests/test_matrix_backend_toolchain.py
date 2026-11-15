"""Exercise the installed Trust package's backend availability probe."""

import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest


SCRIPT = Path(__file__).resolve().parents[1] / "run_full_test_matrix.sh"
SOURCE = SCRIPT.read_text()
START = SOURCE.index("rustc_backend_toolchain_field() {")
END = SOURCE.index("\n}\n\n", SOURCE.index("check_rustc_backend_env() {", START)) + 2
FUNCTIONS = SOURCE[START:END]


class BackendToolchainTests(unittest.TestCase):
    def probe(self, channel="trust", failure="", launchers=False):
        with tempfile.TemporaryDirectory(prefix="tcg-backend-gate-") as directory:
            root = Path(directory).resolve()
            bridge = root / "crates/rustc-codegen-trust-cg"
            bridge.mkdir(parents=True)
            components = '' if channel == "trust" else '\ncomponents = ["rustc-dev"]'
            (bridge / "rust-toolchain.toml").write_text(
                f'[toolchain]\nchannel = "{channel}"{components}\n'
            )
            (bridge / "Cargo.toml").write_text("[package]\nname = 'fixture'\n")
            deps = root / "sysroot/lib/rustlib/aarch64-apple-darwin/lib"
            deps.mkdir(parents=True)
            for name in ("rustc_middle", "rustc_codegen_ssa"):
                if failure != "missing-private" or name != "rustc_middle":
                    (deps / f"lib{name}-fixture.rlib").touch()
            bindir = root / "bin"
            bindir.mkdir()
            (bindir / "python3").symlink_to(sys.executable)
            package_bin = root / "sysroot/bin"
            package_bin.mkdir()
            program = f"#!{sys.executable}\n" + '''import os
from pathlib import Path
import sys
a = sys.argv[1:]
failure = os.environ['PROBE_FAILURE']
channel = os.environ['PROBE_CHANNEL']
driver = Path(sys.argv[0]).name
assert driver != 'rustup', 'the bridge probe must never run rustup'
if driver == 'targo':
    assert a.pop(0) == '--unverified', a
    assert os.environ['RUSTC'] == os.environ['REPO_ROOT'] + '/sysroot/bin/trustc'
    assert a[0] == 'build' and '--locked' in a and '--release' in a, a
    sys.exit(13 if failure == 'build' else 0)
assert driver == 'trustc', a
if a == ['--version']:
    print('fixture compiler')
elif a == ['--print', 'sysroot']:
    print(os.environ['REPO_ROOT'] + ('/other' if failure in ('wrong-sysroot', 'optimized-wrong-sysroot') else '/sysroot'))
elif a == ['-vV']:
    print('binary: ' + ('rustc' if failure == 'wrong-driver' else driver))
    if failure != 'missing-commit': print('commit-hash: ' + 'a' * 40)
    print('host: aarch64-apple-darwin')
else:
    assert a.pop(0) == '-Ztrust-verify=off', a
    assert a[:2] == ['--crate-name', 'trust_cg_rustc_private_probe'], a
    sys.exit(17 if failure == 'compile' else 0)
'''
            for name in ("trustc", "targo"):
                location = package_bin / name
                location.write_text(program)
                location.chmod(0o755)
                if name == "targo" and failure == "missing-tool":
                    continue
                if name == "targo" and failure == "wrong-pair":
                    location = root / "other/bin/targo"
                    location.parent.mkdir(parents=True)
                    location.write_text(program)
                    location.chmod(0o755)
                if launchers:
                    shim = bindir / name
                    shim.write_text(f"#!/bin/sh\n# atpkg shim\nexec '{location}' \"$@\"\n")
                    shim.chmod(0o755)
                else:
                    (bindir / name).symlink_to(location)
            (root / "other").mkdir(exist_ok=True)
            (bindir / "rustup").write_text(program)
            (bindir / "rustup").chmod(0o755)
            # SCRIPT_DIR is the script's own variable: the probe imports the
            # launcher-shim rule from scripts/trust_toolchain.py beside it.
            env = dict(os.environ, REPO_ROOT=str(root), PROBE_CHANNEL=channel,
                       PROBE_FAILURE=failure, PATH=str(bindir) + os.pathsep + "/usr/bin:/bin",
                       SCRIPT_DIR=str(SCRIPT.parent))
            for name in ("RUSTC", "RUSTC_WRAPPER", "RUSTC_WORKSPACE_WRAPPER", "CARGO_BUILD_RUSTC",
                         "CARGO_BUILD_RUSTC_WRAPPER", "CARGO_BUILD_RUSTC_WORKSPACE_WRAPPER"):
                env.pop(name, None)
            if failure == "override":
                env["RUSTC"] = "/unexpected/compiler"
            if failure == "optimized-wrong-sysroot":
                env["PYTHONOPTIMIZE"] = "1"
            return subprocess.run(["bash", "-c", FUNCTIONS + "\ncheck_rustc_backend_env"],
                                  env=env, text=True, capture_output=True, timeout=30)

    def test_installed_trust_binds_path_pair_and_ignores_stale_rustup(self):
        result = self.probe()
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn("/sysroot/bin/trustc", result.stdout)
        self.assertIn("commit-hash: " + "a" * 40, result.stdout)

    def test_atpkg_launchers_are_followed_to_the_package(self):
        result = self.probe(launchers=True)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn("/sysroot/bin/trustc", result.stdout)

    def test_a_stock_or_retired_nightly_channel_is_refused(self):
        for channel in ("nightly-2026-04-20", "1.97.1"):
            with self.subTest(channel=channel):
                result = self.probe(channel)
                self.assertNotEqual(result.returncode, 0)
                self.assertIn('must pin channel = "trust"', result.stderr)

    def test_missing_or_mismatched_installed_tools_refuse_gate(self):
        for failure, message in (("missing-tool", "missing from PATH"),
                                 ("wrong-pair", "same installed package"),
                                 ("wrong-sysroot", "package mismatch"),
                                 ("optimized-wrong-sysroot", "package mismatch"),
                                 ("wrong-driver", "branded trustc"),
                                 ("missing-commit", "commit identity"),
                                 ("override", "ambient compiler override")):
            with self.subTest(failure=failure):
                result = self.probe(failure=failure)
                self.assertNotEqual(result.returncode, 0)
                self.assertIn(message, result.stderr)

    def test_missing_private_library_refuses_gate(self):
        result = self.probe(failure="missing-private")
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("private crate missing", result.stderr)

    def test_private_compile_failure_refuses_gate(self):
        result = self.probe(failure="compile")
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("cannot compile a rustc_private probe", result.stderr)

    def test_backend_build_failure_refuses_gate(self):
        result = self.probe(failure="build")
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("release build failed", result.stderr)


if __name__ == "__main__":
    unittest.main()
