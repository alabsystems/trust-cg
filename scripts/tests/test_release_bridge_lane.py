"""Execute the release gate's rustc-backend lane against controlled Trust packs."""

from __future__ import annotations

import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest


ROOT = Path(__file__).resolve().parents[2]
RELEASE = ROOT / "scripts" / "run_public_release_checks.sh"
SOURCE = RELEASE.read_text()
RETIRED = "nightly-2026-04-20"


def _function(name: str) -> str:
    start = SOURCE.index(f"{name}() {{")
    return SOURCE[start:SOURCE.index("\n}\n", start) + 3]


def _assignment(name: str) -> str:
    start = SOURCE.index(f"\n{name}=") + 1
    return SOURCE[start:SOURCE.index("\n", start) + 1]


# The gate runs the bridge as three accounted lanes, in this order:
# bridge-toolchain-pin, bridge-env and bridge-tests. The harness below executes
# the gate's own lane functions and variable definitions in that order; only
# REPO_ROOT (the gate's script-relative root) is supplied by the test.
FUNCTION = (
    "REPO_ROOT=$(pwd)\n"
    + _assignment("BRIDGE_TOOLCHAIN_FILE")
    + _assignment("EXPECTED_BRIDGE_CHANNEL")
    + _assignment("BRIDGE_CHANNEL")
    + _assignment("BRIDGE_TARGET_DIR")
    + _function("bridge_toolchain_pin")
    + _function("bridge_release_tests")
    + "bridge_backend_release_tests() {\n"
    + "    bridge_toolchain_pin || return 1\n"
    + "    scripts/run_full_test_matrix.sh --check-rustc-backend-env || return 1\n"
    + "    bridge_release_tests\n"
    + "}\n"
)

FAKE_TOOL = f"#!{sys.executable}\n" + r'''import json
import os
from pathlib import Path
import sys

name = Path(sys.argv[0]).name
arguments = sys.argv[1:]
package = Path(sys.argv[0]).resolve().parent.parent
if name == "targo":
    if arguments == ["--version"]:
        print("targo 1.99.0-dev (5555555 2026-09-17) (targo 0.1.0)")
        sys.exit(0)
    with open(os.environ["RELEASE_LANE_LOG"], "a") as log:
        log.write(json.dumps({
            "argv": arguments, "cwd": os.getcwd(), "rustc": os.environ.get("RUSTC"),
            "target_dir": os.environ.get("CARGO_TARGET_DIR"),
        }) + "\n")
    sys.exit(int(os.environ.get("RELEASE_LANE_TEST_STATUS", "0")))
if arguments == ["-vV"]:
    print("rustc 1.99.0-dev (555555555 2026-09-17) (trustc 0.1.0)")
    print("binary: trustc")
    print("commit-hash: " + "5" * 40)
    print("host: aarch64-apple-darwin")
    sys.exit(0)
if arguments == ["--print", "sysroot"]:
    print(package)
    sys.exit(0)
sys.exit(64)
'''

FAKE_MATRIX = """#!/bin/sh
printf 'matrix %s\\n' "$*" >> "$RELEASE_LANE_MATRIX_LOG"
exit "${RELEASE_LANE_MATRIX_STATUS:-0}"
"""


class ReleaseBridgeLaneTests(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory(prefix="trust-cg-release-lane-")
        self.addCleanup(temporary.cleanup)
        self.repo = Path(temporary.name).resolve() / "repo"
        scripts = self.repo / "scripts"
        scripts.mkdir(parents=True)
        shutil.copy2(ROOT / "scripts" / "trust_toolchain.py", scripts / "trust_toolchain.py")
        matrix = scripts / "run_full_test_matrix.sh"
        matrix.write_text(FAKE_MATRIX)
        matrix.chmod(0o755)
        self.bridge = self.repo / "crates" / "rustc-codegen-trust-cg"
        self.bridge.mkdir(parents=True)
        self.set_pin("trust")
        self.package = self.repo.parent / "trust-pack"
        bindir = self.package / "bin"
        bindir.mkdir(parents=True)
        for name in ("trustc", "targo"):
            tool = bindir / name
            tool.write_text(FAKE_TOOL)
            tool.chmod(0o755)
        libdir = self.package / "lib" / "rustlib" / "aarch64-apple-darwin" / "lib"
        libdir.mkdir(parents=True)
        for component in ("rustc_middle", "rustc_codegen_ssa"):
            (libdir / f"lib{component}-fixture.rmeta").touch()
        self.tools = self.repo.parent / "tools"
        self.tools.mkdir()
        (self.tools / "python3").symlink_to(sys.executable)
        self.log = self.repo.parent / "targo.jsonl"
        self.matrix_log = self.repo.parent / "matrix.log"

    def set_pin(self, channel):
        (self.bridge / "rust-toolchain.toml").write_text(f'[toolchain]\nchannel = "{channel}"\n')

    def run_lane(self, *, path=None, **extra):
        environment = {
            key: value for key, value in os.environ.items()
            if key not in {"RUSTC", "CARGO_TARGET_DIR", "RUST_TEST_THREADS"}
        }
        environment.update(
            PATH=path or os.pathsep.join([str(self.package / "bin"), str(self.tools), "/usr/bin", "/bin"]),
            RELEASE_LANE_LOG=str(self.log), RELEASE_LANE_MATRIX_LOG=str(self.matrix_log),
            RUST_TEST_THREADS="1", **extra,
        )
        return subprocess.run(
            ["sh", "-c", "set -eu\n" + FUNCTION + "\nbridge_backend_release_tests\n"],
            cwd=self.repo, env=environment, text=True, capture_output=True, timeout=60,
        )

    def targo_calls(self):
        if not self.log.exists():
            return []
        return [json.loads(line) for line in self.log.read_text().splitlines()]

    def test_release_lane_runs_the_complete_suite_under_the_resolved_package(self):
        result = self.run_lane()
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertEqual(self.matrix_log.read_text(), "matrix --check-rustc-backend-env\n")
        self.assertIn("5" * 40, result.stdout)
        self.assertIn("no Trust-verified compilation claim", result.stdout)
        calls = self.targo_calls()
        self.assertEqual(len(calls), 1)
        call = calls[0]
        self.assertEqual(call["argv"], [
            "--unverified", "test", "--release", "--locked", "--all-features",
            "--all-targets", "--no-fail-fast", "--", "--test-threads=1",
        ])
        self.assertEqual(call["rustc"], str(self.package / "bin" / "trustc"))
        self.assertEqual(Path(call["cwd"]).resolve(), self.bridge)
        self.assertEqual(call["target_dir"], str(self.repo / "target" / "rustc-codegen-trust-cg-trust"))

    def test_package_path_with_spaces_reaches_the_suite_intact(self):
        spaced = self.repo.parent / "Application Support" / "trust-pack"
        spaced.parent.mkdir()
        self.package.rename(spaced)
        self.package = spaced
        result = self.run_lane()
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        calls = self.targo_calls()
        self.assertEqual(len(calls), 1)
        self.assertEqual(calls[0]["rustc"], str(spaced / "bin" / "trustc"))

    def test_retired_nightly_or_other_pin_is_refused_before_any_build(self):
        for channel in (RETIRED, "nightly-2026-09-01", "1.97.1"):
            with self.subTest(channel=channel):
                self.set_pin(channel)
                result = self.run_lane()
                self.assertNotEqual(result.returncode, 0)
                self.assertIn('must pin exactly channel = "trust"', result.stderr)
                self.assertFalse(self.matrix_log.exists())
                self.assertEqual(self.targo_calls(), [])

    def test_failed_availability_probe_stops_the_lane(self):
        result = self.run_lane(RELEASE_LANE_MATRIX_STATUS="1")
        self.assertNotEqual(result.returncode, 0)
        self.assertEqual(self.targo_calls(), [])

    def test_atpkg_launcher_shims_resolve_to_the_package_they_exec(self):
        # aterm puts `#!/bin/sh` launchers ending in `exec '<package>/bin/<tool>'
        # "$@"` on PATH; scripts/trust_toolchain.py follows that shape
        # (`launcher_target`).
        shims = self.repo.parent / "shims"
        shims.mkdir()
        for name in ("trustc", "targo"):
            shim = shims / name
            shim.write_text(f"#!/bin/sh\nexec '{self.package / 'bin' / name}' \"$@\"\n")
            shim.chmod(0o755)
        result = self.run_lane(path=os.pathsep.join([str(shims), str(self.tools), "/usr/bin", "/bin"]))
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        calls = self.targo_calls()
        self.assertEqual(len(calls), 1)
        self.assertEqual(calls[0]["rustc"], str(self.package / "bin" / "trustc"))

    def test_unresolvable_package_stops_the_lane(self):
        # A wrapper whose last command is not its one exec is not a launcher.
        wrappers = self.repo.parent / "wrappers"
        wrappers.mkdir()
        for name in ("trustc", "targo"):
            wrapper = wrappers / name
            wrapper.write_text(
                f"#!/bin/sh\nexec '{self.package / 'bin' / name}' \"$@\"\n: after\n")
            wrapper.chmod(0o755)
        for path, message in (
            (os.pathsep.join([str(self.tools), "/usr/bin", "/bin"]), "missing from PATH: trustc"),
            (os.pathsep.join([str(wrappers), str(self.tools), "/usr/bin", "/bin"]), "package mismatch"),
        ):
            with self.subTest(message=message):
                result = self.run_lane(path=path)
                self.assertNotEqual(result.returncode, 0)
                self.assertIn(message, result.stderr)
                self.assertEqual(self.targo_calls(), [])

    def test_backend_suite_failure_fails_the_gate(self):
        result = self.run_lane(RELEASE_LANE_TEST_STATUS="101")
        self.assertEqual(result.returncode, 101, result.stdout + result.stderr)
        self.assertEqual(len(self.targo_calls()), 1)

    def test_release_gate_invokes_the_lanes_in_order_and_names_no_stock_nightly(self):
        lanes = SOURCE[SOURCE.index("gate_lanes() {"):]
        pin = lanes.index("described_lane bridge-toolchain-pin")
        env = lanes.index("lane bridge-env scripts/run_full_test_matrix.sh --check-rustc-backend-env")
        tests = lanes.index("described_lane bridge-tests")
        self.assertLess(pin, env)
        self.assertLess(env, tests)
        self.assertIn("bridge_toolchain_pin", lanes[pin:env])
        self.assertIn("bridge_release_tests", lanes[tests:tests + 400])
        for retired in (RETIRED, "rustup run", "rustup which"):
            with self.subTest(retired=retired):
                self.assertNotIn(retired, _function("bridge_toolchain_pin"))
                self.assertNotIn(retired, _function("bridge_release_tests"))
        self.assertNotIn(f'channel = ["]{RETIRED}', SOURCE)


if __name__ == "__main__":
    unittest.main()
