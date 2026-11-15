"""Run the benchmark entry points against controlled toolchain prerequisites.

Every entry point resolves the Trust compiler the bridge pin names through
scripts/trust_toolchain.py. These fixtures supply a fake installed Trust pack so
the prerequisite, driver-selection and refusal paths run without a real
compiler or backend.
"""

import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest


ROOT = Path(__file__).resolve().parents[2]
COMMIT = "7" * 40
FAKE_TOOL = f"#!{sys.executable}\n" + r'''import json
import os
from pathlib import Path
import sys

name = Path(sys.argv[0]).name
arguments = sys.argv[1:]
package = Path(sys.argv[0]).resolve().parent.parent
if name == "targo":
    if arguments == ["--version"]:
        print("targo 1.99.0-dev (7777777 2026-09-17) (targo 0.1.0)")
        sys.exit(0)
    sys.exit(64)
if arguments == ["-vV"]:
    print("rustc 1.99.0-dev (777777777 2026-09-17) (trustc 0.1.0)")
    print("binary: trustc")
    print("commit-hash: " + "7" * 40)
    print("host: aarch64-apple-darwin")
    sys.exit(0)
if arguments == ["--version"]:
    print("rustc 1.99.0-dev (777777777 2026-09-17) (trustc 0.1.0)")
    sys.exit(0)
if arguments == ["--print", "sysroot"]:
    print(package)
    sys.exit(0)
if arguments[:2] == ["--print", "target-libdir"]:
    print(os.environ["BENCHMARK_TEST_LIBDIR"])
    sys.exit(0)
with open(os.environ["BENCHMARK_TEST_COMPILES"], "a") as marker:
    marker.write("compile\n")
with open(os.environ["BENCHMARK_TEST_ARGV"], "a") as log:
    log.write(json.dumps({"compiler": sys.argv[0], "arguments": arguments,
                          "xdg_cache_home": os.environ.get("XDG_CACHE_HOME"),
                          "tcg": sorted(k for k in os.environ
                                        if k.startswith(("TCG_", "TRUST_CG_")))}) + "\n")
backend = any(argument.startswith("-Zcodegen-backend=") for argument in arguments)
sys.stderr.write(os.environ.get("BENCHMARK_TEST_BACKEND_STDERR", "") if backend else "")
status = int(os.environ.get("BENCHMARK_TEST_COMPILE_STATUS", "23"))
if backend and "BENCHMARK_TEST_BACKEND_STATUS" in os.environ:
    status = int(os.environ["BENCHMARK_TEST_BACKEND_STATUS"])
if status == 0 and "-o" in arguments:
    # A runnable artifact whose exit code stands in for the program's checksum.
    artifact = Path(arguments[arguments.index("-o") + 1])
    artifact.write_text("#!/bin/sh\nexit " + os.environ.get("BENCHMARK_TEST_PROGRAM_EXIT", "51") + "\n")
    artifact.chmod(0o755)
sys.exit(status)
'''


class FakePackFixture:
    """A throwaway checkout holding copies of the entry points, a fake installed
    Trust pack and a placeholder bridge backend."""

    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory(prefix="trust-cg-bench-preflight-")
        self.addCleanup(self.temporary.cleanup)
        self.directory = Path(self.temporary.name).resolve()
        self.scripts = self.directory / "scripts"
        self.scripts.mkdir()
        for name in ["compile_time_canary.sh", "compile_determinism_sentinel.sh",
                     "check_benchmark_target.sh", "run_with_timeout.py", "gate_env.sh",
                     "trust_toolchain.py", "bridge_backend.py"]:
            shutil.copy2(ROOT / "scripts" / name, self.scripts / name)
        self.bridge = self.directory / "crates/rustc-codegen-trust-cg"
        # The backend carries this host's shared-library suffix (scripts/bridge_backend.py).
        suffix = ".dylib" if sys.platform == "darwin" else ".so"
        self.dylib = self.bridge / f"target/release/librustc_codegen_trust_cg{suffix}"
        self.dylib.parent.mkdir(parents=True)
        self.dylib.touch()
        self.set_pin("trust")
        # The backend is newer than every build input (the pin file is one):
        # a far-future mtime keeps it current however the tests edit the pin.
        os.utime(self.dylib, (4_000_000_000, 4_000_000_000))
        self.package = self.directory / "trust-pack"
        bindir = self.package / "bin"
        bindir.mkdir(parents=True)
        for name in ("trustc", "targo"):
            tool = bindir / name
            tool.write_text(FAKE_TOOL)
            tool.chmod(0o755)
        self.compiler = bindir / "trustc"
        private = self.package / "lib/rustlib/aarch64-apple-darwin/lib"
        private.mkdir(parents=True)
        for component in ("rustc_middle", "rustc_codegen_ssa"):
            (private / f"lib{component}-fixture.rmeta").touch()
        tools = self.directory / "tools"
        tools.mkdir()
        (tools / "python3").symlink_to(sys.executable)
        self.library = self.directory / "target-libraries"
        self.marker = self.directory / "compiles"
        self.argv = self.directory / "argv.jsonl"
        # Independent of the runner's environment: no ambient cache root, no
        # TCG_* control (trustc would refuse it), no shell start-up file.
        self.environment = {key: value for key, value in os.environ.items()
                            if key not in {"BASH_ENV", "ENV", "XDG_CACHE_HOME"}
                            and not key.startswith(("TCG_", "TRUST_CG_"))}
        self.base_path = os.pathsep.join([str(tools), "/usr/bin", "/bin", "/usr/sbin", "/sbin"])
        self.environment.update(
            PATH=os.pathsep.join([str(bindir), self.base_path]),
            BENCHMARK_TEST_LIBDIR=str(self.library), BENCHMARK_TEST_COMPILES=str(self.marker),
            BENCHMARK_TEST_ARGV=str(self.argv), SCRATCH=str(self.directory / "scratch"),
        )

    def set_pin(self, channel):
        (self.bridge / "rust-toolchain.toml").write_text(f'[toolchain]\nchannel = "{channel}"\n')

    def install_target(self):
        self.library.mkdir()
        for name in ["libstd-test.rlib", "libcore-test.rlib"]:
            (self.library / name).touch()

    def run_script(self, name, *arguments, **environment):
        return subprocess.run(
            ["bash", str(self.scripts / name), *arguments], env={**self.environment, **environment},
            text=True, capture_output=True, timeout=30, check=False,
        )

    def compiles(self):
        if not self.argv.exists():
            return []
        return [json.loads(line) for line in self.argv.read_text().splitlines()]


class BenchmarkPrerequisiteTests(FakePackFixture, unittest.TestCase):
    def test_missing_target_stops_both_scripts_before_any_compile(self):
        for name, code in [("compile_time_canary.sh", 2), ("compile_determinism_sentinel.sh", 3)]:
            with self.subTest(script=name):
                result = self.run_script(name)
                self.assertEqual(result.returncode, code, result.stdout + result.stderr)
                self.assertIn("standard libraries missing for aarch64-apple-darwin", result.stderr)
                self.assertNotIn("regressed", result.stderr)
                self.assertFalse(self.marker.exists())

    def test_both_scripts_keep_the_inherited_path(self):
        # The compiler comes from scripts/trust_toolchain.py (the installed
        # Trust package), so neither script puts rustup's stock proxies first:
        # the PATH in force when the Trust compiler is resolved is the caller's.
        home = self.directory / "home"
        proxies = home / ".cargo" / "bin"
        proxies.mkdir(parents=True)
        seen = self.directory / "path-seen"
        for tool in ("rustup", "trustc", "targo"):
            (proxies / tool).write_text(
                '#!/bin/sh\nprintf "%s\\n" "$PATH" > "$BENCHMARK_TEST_PATH_SEEN"\nexit 1\n'
            )
            (proxies / tool).chmod(0o755)
        self.environment.pop("BASH_ENV", None)
        self.environment.update(HOME=str(home), BENCHMARK_TEST_PATH_SEEN=str(seen),
                                PATH=f"/usr/bin:/bin:{proxies}")
        for name, code in [("compile_time_canary.sh", 2), ("compile_determinism_sentinel.sh", 3)]:
            with self.subTest(script=name):
                result = self.run_script(name)
                self.assertEqual(result.returncode, code, result.stdout + result.stderr)
                self.assertIn("cannot resolve the pinned Trust compiler", result.stderr)
                self.assertEqual(seen.read_text().strip().split(":"), ["/usr/bin", "/bin", str(proxies)])
                self.assertFalse(self.marker.exists())
                seen.unlink()

    def test_partial_target_installation_is_not_ready(self):
        self.library.mkdir()
        (self.library / "libstd-test.rlib").touch()
        result = self.run_script("compile_determinism_sentinel.sh")
        self.assertEqual(result.returncode, 3, result.stderr)
        self.assertFalse(self.marker.exists())

    def test_reference_failure_is_tooling_not_a_backend_verdict(self):
        self.install_target()
        result = self.run_script("compile_determinism_sentinel.sh")
        self.assertEqual(result.returncode, 3, result.stdout + result.stderr)
        self.assertIn("reference compilation failed", result.stderr)
        self.assertNotIn("FAILCLOSED", result.stdout + result.stderr)
        self.assertEqual(self.marker.read_text().splitlines(), ["compile"])

    def test_zero_malformed_and_unrepresentable_attempt_counts_are_rejected(self):
        for count in ["0", "00", "1garbage", "-1", "99999999999999999999999"]:
            with self.subTest(count=count):
                result = self.run_script("compile_determinism_sentinel.sh", count)
                self.assertEqual(result.returncode, 3, result.stdout + result.stderr)
                self.assertNotIn("DETERMINISTIC —", result.stdout)
                self.assertFalse(self.marker.exists())

    def test_compiles_use_the_resolved_package_compiler_in_the_unverified_lane(self):
        self.install_target()
        for name, code, message in [
            ("compile_time_canary.sh", 2, "LLVM lane failed"),
            ("compile_determinism_sentinel.sh", 3, "reference compilation failed"),
        ]:
            with self.subTest(script=name):
                if self.argv.exists():
                    self.argv.unlink()
                result = self.run_script(name)
                self.assertEqual(result.returncode, code, result.stdout + result.stderr)
                self.assertIn(message, result.stderr)
                calls = self.compiles()
                self.assertEqual(len(calls), 1)
                self.assertEqual(Path(calls[0]["compiler"]), self.compiler)
                self.assertEqual(calls[0]["arguments"][0], "-Ztrust-verify=off")
                # The target is the resolved compiler's host triple by default.
                self.assertIn("aarch64-apple-darwin", calls[0]["arguments"])

    def test_explicit_driver_selects_the_package_when_path_has_none(self):
        without_trust = {"PATH": self.base_path}
        for name, code in [("compile_time_canary.sh", 2), ("compile_determinism_sentinel.sh", 3)]:
            with self.subTest(script=name, driver=False):
                result = self.run_script(name, **without_trust)
                self.assertEqual(result.returncode, code, result.stdout + result.stderr)
                self.assertIn("missing from PATH: trustc", result.stderr)
                self.assertNotIn("standard libraries missing", result.stderr)
            with self.subTest(script=name, driver=True):
                result = self.run_script(name, "--driver", str(self.compiler), **without_trust)
                self.assertEqual(result.returncode, code, result.stdout + result.stderr)
                self.assertIn("standard libraries missing for aarch64-apple-darwin", result.stderr)
            self.assertFalse(self.marker.exists())
        result = self.run_script("compile_time_canary.sh", "--driver")
        self.assertEqual(result.returncode, 3, result.stderr)
        result = self.run_script("compile_time_canary.sh", "--bogus")
        self.assertEqual(result.returncode, 3, result.stderr)

    def test_retired_nightly_or_unidentified_compiler_is_refused_before_any_compile(self):
        self.install_target()
        self.set_pin("nightly-2026-04-20")
        for name, code in [("compile_time_canary.sh", 2), ("compile_determinism_sentinel.sh", 3)]:
            with self.subTest(script=name, pin="retired"):
                result = self.run_script(name)
                self.assertEqual(result.returncode, code, result.stdout + result.stderr)
                self.assertIn("retired stock nightly lane", result.stderr)
        self.set_pin("trust")
        stock = self.directory / "stock/bin/rustc"
        stock.parent.mkdir(parents=True)
        stock.write_text(FAKE_TOOL)
        stock.chmod(0o755)
        for name, code in [("compile_time_canary.sh", 2), ("compile_determinism_sentinel.sh", 3)]:
            with self.subTest(script=name, driver="stock rustc"):
                result = self.run_script(name, "--driver", str(stock))
                self.assertEqual(result.returncode, code, result.stdout + result.stderr)
                self.assertIn("branded trustc driver", result.stderr)
        self.assertFalse(self.marker.exists())

class PortableGateTests(FakePackFixture, unittest.TestCase):
    """The canary and the sentinel end to end on a fake Trust pack: no Darwin-only
    probe, the host's backend suffix and target, fresh caches without TCG_*
    environment, and fail-closed refusals."""

    def setUp(self):
        super().setUp()
        self.install_target()
        self.environment["BENCHMARK_TEST_COMPILE_STATUS"] = "0"

    def test_canary_runs_end_to_end_with_portable_probes(self):
        result = self.run_script("compile_time_canary.sh")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn("canary: OK", result.stdout)
        self.assertIn("target:         aarch64-apple-darwin", result.stdout)
        self.assertIn(f"dylib:          {self.dylib}", result.stdout)
        self.assertRegex(result.stdout, r"loadavg_1min:   [0-9]+\.[0-9]{2} \(ncpu=[0-9]+\)")
        self.assertRegex(result.stdout, r"dylib_sha256:   [0-9a-f]{64}")
        calls = self.compiles()
        self.assertEqual(len(calls), 5)  # LLVM, bridge warmup, three timed
        self.assertTrue(all("aarch64-apple-darwin" in call["arguments"] for call in calls))
        self.assertTrue(all(call["tcg"] == [] for call in calls))

    def test_explicit_target_and_backend_are_honored(self):
        other = self.directory / "elsewhere" / self.dylib.name
        other.parent.mkdir()
        other.touch()
        result = self.run_script("compile_time_canary.sh", "--target", "x86_64-apple-darwin",
                                 "--dylib", str(other))
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        calls = self.compiles()
        self.assertTrue(all("x86_64-apple-darwin" in call["arguments"] for call in calls))
        bridge = [call for call in calls if f"-Zcodegen-backend={other}" in call["arguments"]]
        self.assertEqual(len(bridge), 4)
        self.argv.unlink()
        for name, code in (("compile_time_canary.sh", 2), ("compile_determinism_sentinel.sh", 3)):
            with self.subTest(script=name):
                result = self.run_script(name, "--dylib", str(self.directory / "absent.so"))
                self.assertEqual(result.returncode, code, result.stdout + result.stderr)
                self.assertIn("bridge backend missing", result.stderr)
                result = self.run_script(name, "--target")
                self.assertEqual(result.returncode, 3, result.stdout + result.stderr)
        self.assertEqual(self.compiles(), [])

    def test_a_stale_or_absent_backend_is_refused_before_any_compile(self):
        source = self.directory / "crates/trust-cg-core/src/lib.rs"
        source.parent.mkdir(parents=True)
        source.write_text("// newer than the backend\n")
        os.utime(self.bridge / "rust-toolchain.toml", (900_000_000, 900_000_000))
        os.utime(self.dylib, (1_000_000_000, 1_000_000_000))
        for name, code in (("compile_time_canary.sh", 2), ("compile_determinism_sentinel.sh", 3)):
            with self.subTest(script=name):
                result = self.run_script(name)
                self.assertEqual(result.returncode, code, result.stdout + result.stderr)
                self.assertIn("is STALE", result.stderr)
        # A test source is not compiled into the backend and cannot make it stale.
        source.unlink()
        test_source = self.directory / "crates/trust-cg-core/tests/t.rs"
        test_source.parent.mkdir(parents=True)
        test_source.write_text("// test only\n")
        self.assertEqual(self.run_script("compile_time_canary.sh").returncode, 0)
        self.dylib.unlink()
        result = self.run_script("compile_time_canary.sh")
        self.assertEqual(result.returncode, 2, result.stdout + result.stderr)
        self.assertIn("no bridge backend is built", result.stderr)

    def test_degraded_proof_checker_is_a_config_error_not_a_green(self):
        banner = "[trust-cg] INDEPENDENT PROOF CHECKER UNUSABLE — verification is DEGRADED\n"
        for name, arguments in (("compile_time_canary.sh", ()), ("compile_determinism_sentinel.sh", ("2",))):
            for status in ("0", "1"):  # a degraded lane neither passes nor fails the gate
                with self.subTest(script=name, backend_status=status):
                    result = self.run_script(name, *arguments, BENCHMARK_TEST_BACKEND_STDERR=banner,
                                             BENCHMARK_TEST_BACKEND_STATUS=status)
                    self.assertEqual(result.returncode, 3, result.stdout + result.stderr)
                    self.assertIn("verification DEGRADED", result.stderr)
                    self.assertNotIn("GATE RED", result.stderr)

    def test_a_mismatch_is_p0_even_with_a_degraded_checker(self):
        banner = "[trust-cg] INDEPENDENT PROOF CHECKER UNUSABLE — verification is DEGRADED\n"
        result = self.run_script("compile_time_canary.sh", BENCHMARK_TEST_BACKEND_STDERR=banner,
                                 BENCHMARK_TEST_PROGRAM_EXIT="7")
        self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
        self.assertIn("exit-code MISMATCH", result.stderr)
        self.assertIn("verification DEGRADED", result.stderr)
        self.assertIn("compile-time canary provenance", result.stdout)

    def test_canary_mismatch_and_fail_closed_are_red(self):
        result = self.run_script("compile_time_canary.sh", BENCHMARK_TEST_PROGRAM_EXIT="7")
        self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
        self.assertIn("MISMATCH", result.stderr)
        result = self.run_script("compile_time_canary.sh", BENCHMARK_TEST_BACKEND_STATUS="1")
        self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
        self.assertIn("bridge failed to compile", result.stderr)

    def test_sentinel_cold_attempts_use_fresh_caches_without_tcg_env(self):
        result = self.run_script("compile_determinism_sentinel.sh", "3")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn("DETERMINISTIC — all 3 compiles succeeded", result.stdout)
        attempts = [call for call in self.compiles()
                    if any(a.startswith("-Zcodegen-backend=") for a in call["arguments"])]
        self.assertEqual(len(attempts), 3)
        roots = [call["xdg_cache_home"] for call in attempts]
        self.assertEqual(len(set(roots)), 3)
        self.assertTrue(all(root and "cache" in Path(root).name for root in roots))
        self.assertTrue(all(call["tcg"] == [] for call in self.compiles()))
        warm = self.run_script("compile_determinism_sentinel.sh", "2", "--warm")
        self.assertEqual(warm.returncode, 0, warm.stdout + warm.stderr)
        self.assertIsNone(self.compiles()[-1]["xdg_cache_home"])
        # An ambient cache root is overridden by cold attempts and kept by warm ones.
        ambient = str(self.directory / "ambient-cache")
        self.argv.unlink()
        cold = self.run_script("compile_determinism_sentinel.sh", "2", XDG_CACHE_HOME=ambient)
        self.assertEqual(cold.returncode, 0, cold.stdout + cold.stderr)
        roots = [c["xdg_cache_home"] for c in self.compiles()
                 if any(a.startswith("-Zcodegen-backend=") for a in c["arguments"])]
        self.assertEqual(len(roots), 2)
        self.assertNotIn(ambient, roots)
        warm = self.run_script("compile_determinism_sentinel.sh", "2", "--warm", XDG_CACHE_HOME=ambient)
        self.assertEqual(warm.returncode, 0, warm.stdout + warm.stderr)
        self.assertEqual(self.compiles()[-1]["xdg_cache_home"], ambient)
        failed = self.run_script("compile_determinism_sentinel.sh", "2", BENCHMARK_TEST_BACKEND_STATUS="1")
        self.assertEqual(failed.returncode, 2, failed.stdout + failed.stderr)


if __name__ == "__main__":
    unittest.main()
