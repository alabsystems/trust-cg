"""Timing harnesses drive the bridge's pinned Trust compiler, never a stock nightly.

Each harness resolves its compiler through scripts/trust_toolchain.py. A fake
installed Trust pack records every compile so these tests check the selected
driver, the explicit unverified frontend lane flag and the stamped identity,
and that an absent or stock driver stops the harness before any compile.
"""

from __future__ import annotations

import importlib.util
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest
from unittest import mock


ROOT = Path(__file__).resolve().parents[2]
COMMIT = "9" * 40
LANE = "-Ztrust-verify=off"
FAKE_TOOL = f"#!{sys.executable}\n" + r'''import json
import os
from pathlib import Path
import sys

name = Path(sys.argv[0]).name
arguments = sys.argv[1:]
package = Path(sys.argv[0]).resolve().parent.parent
if name == "targo":
    if arguments == ["--version"]:
        print("targo 1.99.0-dev (999999999 2026-09-17) (targo 0.1.0)")
        sys.exit(0)
    sys.exit(64)
if arguments == ["-vV"]:
    print("rustc 1.99.0-dev (999999999 2026-09-17) (trustc 0.1.0)")
    print("binary: " + name)
    print("commit-hash: " + "9" * 40)
    print("host: aarch64-apple-darwin")
    print("release: 1.99.0-dev")
    sys.exit(0)
if arguments == ["--version"]:
    print("rustc 1.99.0-dev (999999999 2026-09-17) (trustc 0.1.0)")
    sys.exit(0)
if arguments == ["--print", "sysroot"]:
    print(package)
    sys.exit(0)
with open(os.environ["HARNESS_TEST_ARGV"], "a") as log:
    log.write(json.dumps({"compiler": sys.argv[0], "arguments": arguments}) + "\n")
sys.exit(int(os.environ.get("HARNESS_TEST_COMPILE_STATUS", "1")))
'''


def make_pack(root: Path, compiler_name: str = "trustc") -> Path:
    bindir = root / "bin"
    bindir.mkdir(parents=True)
    for name in (compiler_name, "targo"):
        tool = bindir / name
        tool.write_text(FAKE_TOOL)
        tool.chmod(0o755)
    libdir = root / "lib/rustlib/aarch64-apple-darwin/lib"
    libdir.mkdir(parents=True)
    for component in ("rustc_middle", "rustc_codegen_ssa"):
        (libdir / f"lib{component}-fixture.rmeta").touch()
    return bindir / compiler_name


class HarnessFixture(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory(prefix="trust-cg-harness-driver-")
        self.addCleanup(temporary.cleanup)
        self.directory = Path(temporary.name).resolve()
        self.compiler = make_pack(self.directory / "trust-pack")
        self.stock = make_pack(self.directory / "stock", compiler_name="rustc")
        # Created after every source file, so no harness treats it as stale.
        self.dylib = self.directory / "librustc_codegen_trust_cg.dylib"
        self.dylib.write_bytes(b"fixture backend\n")
        self.argv = self.directory / "argv.jsonl"
        self.out = self.directory / "out"
        self.base_path = os.pathsep.join(["/usr/bin", "/bin", "/usr/sbin", "/sbin"])
        self.environment = {key: value for key, value in os.environ.items()
                            if not key.startswith(("TCG_", "TRUST_CG_"))}
        self.environment.update(HARNESS_TEST_ARGV=str(self.argv), PATH=self.base_path)

    def compiles(self):
        if not self.argv.exists():
            return []
        return [json.loads(line) for line in self.argv.read_text().splitlines()]

    def run_harness(self, relative, *arguments, path=None):
        environment = dict(self.environment)
        if path is not None:
            environment["PATH"] = path
        return subprocess.run([sys.executable, str(ROOT / relative), *arguments], cwd=self.directory,
                              env=environment, capture_output=True, text=True, timeout=120)

    def assert_trust_lane(self, calls, expected_count, backend_count):
        self.assertEqual(len(calls), expected_count)
        for call in calls:
            self.assertEqual(Path(call["compiler"]), self.compiler)
            self.assertIn(LANE, call["arguments"])
            self.assertNotIn("nightly", " ".join(call["arguments"]))
        with_backend = [call for call in calls
                        if f"-Zcodegen-backend={self.dylib}" in call["arguments"]]
        self.assertEqual(len(with_backend), backend_count)


class ScriptHarnessDriverTests(HarnessFixture):
    CASES = (
        ("benchmarks/beat-llvm/compile_gate.py",
         ("--progs", "p3_gcd"), 1, 3, 3),
        ("benchmarks/beat-llvm/scale_gate.py",
         ("--sizes", "small", "--n", "1"), 0, 1, 0),
        ("benchmarks/compile-scaling/run.py",
         ("--shapes", "blocks", "--sizes", "100", "-n", "1"), 1, 2, 1),
        ("benchmarks/compile-apples/run.py",
         ("--progs", "p3_gcd", "-n", "1", "--allow-loaded"), 1, 4, 2),
    )

    def common(self, relative):
        arguments = ["--dylib", str(self.dylib)]
        if relative.startswith("benchmarks/compile-"):
            arguments += ["--out-dir", str(self.out)]
        return arguments

    def test_explicit_driver_compiles_every_lane_with_the_trust_pack(self):
        for relative, arguments, code, count, backend in self.CASES:
            with self.subTest(harness=relative):
                if self.argv.exists():
                    self.argv.unlink()
                result = self.run_harness(relative, *self.common(relative), "--driver", str(self.compiler),
                                          *arguments)
                self.assertEqual(result.returncode, code, result.stdout + result.stderr)
                self.assertIn(COMMIT, result.stdout + result.stderr)
                self.assertIn("unverified", result.stdout + result.stderr)
                self.assert_trust_lane(self.compiles(), count, backend)

    def test_path_package_is_the_default_driver(self):
        relative, arguments, code, count, backend = self.CASES[0]
        result = self.run_harness(relative, *self.common(relative), *arguments,
                                  path=os.pathsep.join([str(self.compiler.parent), self.base_path]))
        self.assertEqual(result.returncode, code, result.stdout + result.stderr)
        self.assert_trust_lane(self.compiles(), count, backend)

    def test_missing_or_stock_driver_stops_before_any_compile(self):
        for relative, arguments, _, _, _ in self.CASES:
            for driver, message in ((None, "missing from PATH: trustc"),
                                    (str(self.stock), "branded trustc driver")):
                with self.subTest(harness=relative, driver=driver):
                    extra = [] if driver is None else ["--driver", driver]
                    result = self.run_harness(relative, *self.common(relative), *extra, *arguments)
                    self.assertNotEqual(result.returncode, 0, result.stdout + result.stderr)
                    self.assertIn(message, result.stdout + result.stderr)
                    self.assertEqual(self.compiles(), [])


class AttributionToolDriverTests(HarnessFixture):
    TOOLS = ROOT / "benchmarks/compile-apples/tools"

    def test_positional_and_option_tools_select_the_trust_pack(self):
        program = ROOT / "benchmarks/beat-llvm/progs/p3_gcd.rs"
        for tool, arguments, count, backend in (
            ("fixed_charge.py", ["--driver", str(self.compiler), "1", str(self.dylib)], 1, 0),
            ("ab.py", ["--driver", str(self.compiler), "--a", str(self.dylib), "--n", "1", str(program)], 4, 2),
        ):
            with self.subTest(tool=tool):
                if self.argv.exists():
                    self.argv.unlink()
                result = self.run_harness(str(self.TOOLS / tool), *arguments)
                self.assertNotEqual(result.returncode, 0, result.stdout + result.stderr)
                self.assertIn(COMMIT, result.stderr)
                self.assert_trust_lane(self.compiles(), count, backend)

    def test_tools_refuse_an_absent_or_stock_driver_before_any_compile(self):
        for arguments, message in ((["1", str(self.dylib)], "missing from PATH: trustc"),
                                   (["--driver", str(self.stock), "1", str(self.dylib)], "branded trustc"),
                                   (["1", str(self.dylib), "--driver"], "--driver needs")):
            with self.subTest(arguments=arguments):
                result = self.run_harness(str(self.TOOLS / "fixed_charge.py"), *arguments)
                self.assertNotEqual(result.returncode, 0)
                self.assertIn(message, result.stderr)
        self.assertEqual(self.compiles(), [])


SHELL_TOOL = """#!/bin/sh
name=$(basename "$0")
package=$(cd "$(dirname "$0")/.." && pwd -P)
if [ "$name" = targo ]; then
  if [ "$*" = --version ]; then echo "targo 1.99.0-dev (999999999 2026-09-17) (targo 0.1.0)"; exit 0; fi
  exit 64
fi
case "$*" in
  -vV) printf 'rustc 1.99.0-dev (999999999 2026-09-17) (trustc 0.1.0)\\nbinary: %s\\ncommit-hash: %s\\nhost: aarch64-apple-darwin\\n' "$name" "COMMIT"; exit 0 ;;
  --version) echo "rustc 1.99.0-dev (999999999 2026-09-17) (trustc 0.1.0)"; exit 0 ;;
  "--print sysroot") echo "$package"; exit 0 ;;
esac
printf '%s\\n' "$0 $*" >> "$HARNESS_TEST_ARGV_TEXT"
exit 1
""".replace("COMMIT", COMMIT)


class DifferentialScriptDriverTests(HarnessFixture):
    """The whole-program and cross-backend differentials share the resolver."""

    def setUp(self):
        super().setUp()
        package = self.directory / "shell-pack"
        (package / "bin").mkdir(parents=True)
        # Match the fixture's OS to the host linker. A fake Darwin compiler
        # on Linux is correctly refused before compiling because GNU ld is
        # not Apple ld64; that cannot test compiler-argument forwarding.
        fixture_host = ("aarch64-apple-darwin" if sys.platform == "darwin"
                        else "aarch64-unknown-linux-gnu")
        for name in ("trustc", "targo"):
            tool = package / "bin" / name
            tool.write_text(SHELL_TOOL.replace("aarch64-apple-darwin", fixture_host))
            tool.chmod(0o755)
        libdir = package / f"lib/rustlib/{fixture_host}/lib"
        libdir.mkdir(parents=True)
        for component in ("rustc_middle", "rustc_codegen_ssa"):
            (libdir / f"lib{component}-fixture.rmeta").touch()
        self.shell_compiler = package / "bin" / "trustc"
        self.log = self.directory / "argv.txt"
        self.environment.update(
            HARNESS_TEST_ARGV_TEXT=str(self.log), BRIDGE_FUZZ_DYLIB=str(self.dylib),
            BRIDGE_FUZZ_OUT=str(self.directory / "fuzz"), ABI_XBACK_DYLIB=str(self.dylib),
            ABI_XBACK_OUT=str(self.directory / "abi"), DECLINE_DYLIB=str(self.dylib),
            DECLINE_OUT=str(self.directory / "decline"),
        )

    def run_script(self, relative, *arguments):
        return subprocess.run(["bash", str(ROOT / relative), *arguments], cwd=self.directory,
                              env=self.environment, capture_output=True, text=True, timeout=300)

    def logged(self):
        return self.log.read_text().splitlines() if self.log.exists() else []

    CASES = (
        ("benchmarks/bridge-fuzz/run.sh", ("1", "1"), 0, 2),
        ("benchmarks/decline-shapes/run.sh", (), 0, 2),
        ("benchmarks/shape-coverage/run.sh", (), 1, 2),
        ("benchmarks/abi-xback/run.sh", ("1", "1"), 1, 1),
    )

    def arguments(self, relative, driver, extra):
        head = ["--driver", str(driver)] if driver is not None else []
        tail = [str(self.dylib)] if relative.endswith("shape-coverage/run.sh") else []
        return [*head, *tail, *extra]

    def test_explicit_driver_reaches_every_compile_with_the_unverified_lane(self):
        for relative, extra, code, _ in self.CASES:
            with self.subTest(script=relative):
                if self.log.exists():
                    self.log.unlink()
                result = self.run_script(relative, *self.arguments(relative, self.shell_compiler, extra))
                self.assertEqual(result.returncode, code, result.stdout + result.stderr)
                self.assertIn(COMMIT, result.stdout)
                calls = self.logged()
                self.assertTrue(calls)
                for call in calls:
                    self.assertTrue(call.startswith(f"{self.shell_compiler} -Ztrust-verify=off "), call)

    def test_absent_or_stock_driver_fails_before_any_compile(self):
        for relative, extra, _, refusal in self.CASES:
            for driver in (None, self.stock):
                with self.subTest(script=relative, driver=driver):
                    result = self.run_script(relative, *self.arguments(relative, driver, extra))
                    self.assertEqual(result.returncode, refusal, result.stdout + result.stderr)
                    self.assertIn("pinned Trust compiler", result.stderr)
                    self.assertEqual(self.logged(), [])

    def test_selftests_need_no_compiler(self):
        for relative in ("benchmarks/shape-coverage/run.sh", "benchmarks/abi-xback/run.sh"):
            with self.subTest(script=relative):
                result = self.run_script(relative, "--selftest")
                self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
                self.assertIn("selftest", result.stdout)


class BeatLlvmHarnessDriverTests(HarnessFixture):
    def setUp(self):
        super().setUp()
        spec = importlib.util.spec_from_file_location("beat_llvm_run_under_test",
                                                      ROOT / "benchmarks/beat-llvm/run.py")
        self.module = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(self.module)
        patcher = mock.patch.dict(os.environ, self.environment, clear=True)
        patcher.start()
        self.addCleanup(patcher.stop)

    def harness(self, *extra):
        argv = ["run.py", "--dylib", str(self.dylib), "--progs", "p3_gcd", "--allow-loaded",
                "--out-dir", str(self.out), *extra]
        with mock.patch.object(sys, "argv", argv):
            args = self.module.parse_args()
        harness = self.module.Harness(args)
        self.addCleanup(shutil.rmtree, harness.workdir, True)
        return harness

    def test_lanes_share_the_trust_driver_and_its_unverified_frontend_flag(self):
        harness = self.harness("--driver", str(self.compiler))
        llvm = harness.compile_cmd(Path("p.rs"), Path("p"), "3", bridge=False)
        bridge = harness.compile_cmd(Path("p.rs"), Path("p"), "3", bridge=True)
        self.assertEqual(llvm[:3], [str(self.compiler), LANE, "--edition=2021"])
        self.assertEqual(bridge[:3], [str(self.compiler), f"-Zcodegen-backend={self.dylib}", LANE])
        self.assertEqual([item for item in bridge if not item.startswith("-Zcodegen-backend=")], llvm)

    def test_provenance_stamps_the_exact_driver_identity(self):
        harness = self.harness("--driver", str(self.compiler))
        provenance = harness.provenance()
        driver = provenance["driver"]
        self.assertEqual(provenance["rustc_path"], str(self.compiler))
        self.assertEqual(driver["compiler"], str(self.compiler))
        self.assertEqual(driver["commit"], COMMIT)
        self.assertEqual(driver["selection"], "explicit-driver")
        self.assertEqual(driver["lane"], "unverified")
        self.assertEqual(driver["compiler_flags"], [LANE])
        self.assertEqual(driver["bridge_pin"]["channel"], "trust")
        self.assertIn(f"{self.compiler.parent / 'targo'} --unverified build --release",
                      provenance["dylib_build_command"])
        self.assertNotIn("<trust-package>", provenance["dylib_build_command"])
        # Provenance may ask the resolved driver informational --print queries
        # (the CPU-policy probe); it must never compile, and never ask another
        # compiler.
        calls = self.compiles()
        self.assertTrue(all(call["arguments"][:1] == ["--print"] for call in calls), calls)
        self.assertTrue(all(call["compiler"] == str(self.compiler.resolve()) or
                            call["compiler"] == str(self.compiler) for call in calls), calls)

    def test_absent_or_stock_driver_exits_as_a_tooling_error(self):
        for extra in ((), ("--driver", str(self.stock))):
            with self.subTest(extra=extra):
                with self.assertRaises(SystemExit) as caught:
                    self.harness(*extra)
                self.assertEqual(caught.exception.code, 2)
        self.assertEqual(self.compiles(), [])


if __name__ == "__main__":
    unittest.main()
