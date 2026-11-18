#!/usr/bin/env python3
"""Regression tests for the beat-llvm harnesses' RSS, CPU-provenance and
retention machinery (peak_rss.py, hostinfo.py, run.py, scale_gate.py).

No benchmark runs here: every compiler and program is a small stand-in script.
Run with `python3 benchmarks/beat-llvm/test_run_provenance.py` or
`python3 -m unittest benchmarks/beat-llvm/test_run_provenance.py`.
"""

import argparse
import hashlib
import importlib.util
import json
import os
import re
import shlex
import statistics
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path
from unittest import mock

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent.parent
if str(HERE) not in sys.path:
    sys.path.insert(0, str(HERE))

import emitted_size  # noqa: E402
import hostinfo  # noqa: E402
import peak_rss  # noqa: E402
import scale_gate  # noqa: E402

_SPEC = importlib.util.spec_from_file_location("beat_llvm_run", HERE / "run.py")
harness = importlib.util.module_from_spec(_SPEC)
_SPEC.loader.exec_module(harness)

MIB = 1 << 20


def allocate(mib):
    """A command whose peak RSS is at least `mib` MiB (every page is written)."""
    return [sys.executable, "-c", f'x = b"\\x01" * ({mib} << 20)']


def write_executable(path, text):
    path.write_text(text)
    path.chmod(0o755)
    return path


def write_python_executable(path, body):
    # A kernel shebang cannot quote an interpreter path containing spaces.
    # exec preserves the stand-in's PID, signals and argument list.
    entry = ("#!/bin/sh\n'''exec' " + shlex.quote(sys.executable)
             + ' "$0" "$@"\n\' \'\'\'\n')
    return write_executable(path, entry + body)


# ---------------------------------------------------------------- peak_rss.py

def fake_driver(compiler, compiler_flags=()):
    """A resolved-driver record shaped like scripts/trust_toolchain.py's output,
    for harness objects built without resolve_rustc()."""
    return {
        "schema": "trust-cg-trust-toolchain-v1", "selection": "test", "requested_driver": None,
        "compiler": str(compiler), "targo": str(Path(compiler).with_name("targo")),
        "sysroot": str(Path(compiler).parent.parent), "host": "aarch64-unknown-linux-gnu",
        "commit": "5" * 40, "release": "1.99.0-dev", "version": "test", "targo_version": None,
        "lane": "unverified", "lane_label": "test stand-in driver (no verification claim)",
        "compiler_flags": list(compiler_flags), "bridge_pin": "trust",
    }

class PeakRssUnitTests(unittest.TestCase):
    def test_units_are_normalised_to_bytes(self):
        self.assertEqual(peak_rss.maxrss_unit("darwin"), "bytes")
        self.assertEqual(peak_rss.maxrss_unit("linux"), "KiB")
        self.assertEqual(peak_rss.normalize_maxrss(4096, "darwin"), 4096)
        self.assertEqual(peak_rss.normalize_maxrss(4096, "linux"), 4096 * 1024)
        for empty in (None, 0, -1):
            with self.subTest(value=empty):
                self.assertIsNone(peak_rss.normalize_maxrss(empty, "linux"))

    def test_wrapper_record_names_raw_unit_and_bytes(self):
        record = peak_rss.wrapper_record(2048, 0, "ok", 0.5, platform="linux")
        self.assertEqual(record["ru_maxrss_raw"], 2048)
        self.assertEqual(record["ru_maxrss_unit"], "KiB")
        self.assertEqual(record["ru_maxrss_bytes"], 2048 * 1024)
        self.assertEqual(record["wall_s"], 0.5)

    def test_time_output_parsers_cover_bsd_and_gnu(self):
        bsd = "        0.01 real  0.00 user\n   1261568  maximum resident set size\n"
        gnu = "\tCommand being timed: \"true\"\n\tMaximum resident set size (kbytes): 1800\n"
        self.assertEqual(peak_rss.parse_time_output(bsd), 1261568)
        self.assertEqual(peak_rss.parse_time_output(gnu), 1800 * 1024)
        self.assertIsNone(peak_rss.parse_time_output("0.00user 0.00system"))
        self.assertEqual(peak_rss.time_wrapper_flag("darwin"), "-l")
        self.assertEqual(peak_rss.time_wrapper_flag("linux"), "-v")

    def test_missing_time_binary_is_no_cross_check_not_a_zero(self):
        self.assertIsNone(peak_rss.time_wrapper_peak_rss(["true"], time_bin="/nonexistent/time"))
        self.assertIsNone(peak_rss.relative_difference(None, 5))
        self.assertEqual(peak_rss.relative_difference(100, 95), 0.05)


class PeakRssMeasurementTests(unittest.TestCase):
    def test_measures_a_known_allocation(self):
        sample = peak_rss.measure(allocate(48), timeout=60)
        self.assertEqual((sample.returncode, sample.status), (0, "ok"))
        self.assertGreaterEqual(sample.peak_rss_bytes, 48 * MIB)
        self.assertGreater(sample.wall_s, 0)

    def test_each_measurement_starts_from_zero(self):
        # The reason for the wrapper: RUSAGE_CHILDREN in one long-lived process
        # is a high-water mark over every child, so a small child measured after
        # a big one would inherit the big one's peak.
        big = peak_rss.measure(allocate(96), timeout=60)
        small = peak_rss.measure([sys.executable, "-c", "pass"], timeout=60)
        self.assertGreaterEqual(big.peak_rss_bytes, 96 * MIB)
        self.assertLess(small.peak_rss_bytes, big.peak_rss_bytes / 2)

    def test_nonzero_exit_keeps_its_peak(self):
        # A beat-llvm program's exit code IS its checksum, so a nonzero status
        # is a normal run with a meaningful peak.
        sample = peak_rss.measure([sys.executable, "-c", "raise SystemExit(7)"], timeout=60)
        self.assertEqual((sample.returncode, sample.status), (7, "ok"))
        self.assertIsNotNone(sample.peak_rss_bytes)

    def test_killed_unexecutable_and_timed_out_children_have_no_peak(self):
        cases = (
            ([sys.executable, "-c", "import os, signal; os.kill(os.getpid(), signal.SIGKILL)"],
             None, 128 + 9, "signaled"),
            (["/nonexistent/compiler"], None, peak_rss.EXEC_FAILED_EXIT, "exec-failed"),
            ([sys.executable, "-c", "import time; time.sleep(30)"], 0.5,
             peak_rss.TIMEOUT_EXIT, "timeout"),
        )
        for cmd, timeout, code, status in cases:
            with self.subTest(status=status):
                sample = peak_rss.measure(cmd, timeout=timeout)
                self.assertEqual((sample.returncode, sample.status), (code, status))
                self.assertIsNone(sample.peak_rss_bytes)
                self.assertIsNone(sample.wall_s)

    def test_missing_record_is_not_a_measurement(self):
        broken = peak_rss.measure(["true"], python="/nonexistent/python")
        self.assertIsNone(broken.peak_rss_bytes)
        self.assertNotEqual(broken.status, "ok")

    @unittest.skipUnless(sys.platform == "linux", "native Linux sampler")
    def test_native_floor_is_below_a_python_child_image(self):
        floor = peak_rss.measure(peak_rss.trivial_command(), timeout=60)
        python = peak_rss.measure([sys.executable, "-c", "pass"], timeout=60)
        self.assertEqual((floor.status, python.status), ("ok", "ok"))
        self.assertGreater(floor.peak_rss_bytes, 0)
        self.assertLess(floor.peak_rss_bytes, python.peak_rss_bytes / 2)
        directory, binary, identity = peak_rss.native_sampler()
        self.assertEqual(binary.read_bytes()[:4], b"\x7fELF")
        self.assertEqual(Path(directory.name).stat().st_mode & 0o777, 0o700)
        self.assertEqual(identity, peak_rss.sampler_identity())

    @unittest.skipUnless(sys.platform == "linux", "native Linux sampler")
    def test_native_build_failure_keeps_no_measurement(self):
        env = dict(os.environ, CC="/nonexistent/native-rss-compiler")
        sample = peak_rss.measure(peak_rss.trivial_command(), env=env)
        self.assertEqual(sample.status, "wrapper-failed")
        self.assertIsNone(sample.peak_rss_bytes)
        self.assertIsNone(sample.wall_s)
        self.assertEqual(peak_rss.sampler_identity(env)["status"], "wrapper-failed")

    @unittest.skipUnless(sys.platform == "linux", "native Linux sampler")
    def test_native_exec_error_is_distinct_from_a_real_exit_127(self):
        real = peak_rss.measure([sys.executable, "-c", "raise SystemExit(127)"])
        failed = peak_rss.measure(["/nonexistent/program"])
        self.assertEqual((real.returncode, failed.returncode), (127, 127))
        self.assertEqual((real.status, failed.status), ("ok", "exec-failed"))
        self.assertIsNotNone(real.peak_rss_bytes)
        self.assertIsNone(failed.peak_rss_bytes)

    @unittest.skipUnless(sys.platform == "linux", "native Linux sampler")
    def test_timeout_stops_the_owned_descendant_group_and_drains_output(self):
        # The descendant deliberately inherits the output pipes. Killing only
        # its parent would leave communicate() blocked and a live child behind.
        code = ("import subprocess,sys,time; "
                "p=subprocess.Popen([sys.executable,'-c','import time;time.sleep(30)']); "
                "print(p.pid,flush=True);time.sleep(30)")
        sample = peak_rss.measure([sys.executable, "-c", code], timeout=1)
        self.assertEqual((sample.returncode, sample.status), (124, "timeout"))
        self.assertIsNone(sample.peak_rss_bytes)
        child = Path('/proc') / str(int(sample.stdout.strip())) / 'stat'
        if child.exists():
            # An orphaned zombie awaits the host's init, but cannot run or keep
            # the output pipes open. The sampler reaps its own direct child.
            self.assertIn(child.read_text().split(') ', 1)[1].split()[0], ('Z', 'X'))

    @unittest.skipUnless(sys.platform == "linux", "native Linux sampler")
    def test_cli_uses_the_same_native_measurement_and_forwards_output(self):
        with tempfile.TemporaryDirectory() as temporary:
            out = Path(temporary) / "sample.json"
            result = subprocess.run([sys.executable, str(peak_rss.WRAPPER), "--out", str(out),
                                     "--timeout", "60", "--", sys.executable, "-c",
                                     "import sys;print('out');print('err',file=sys.stderr);sys.exit(7)"],
                                    capture_output=True, text=True, timeout=90)
            self.assertEqual((result.returncode, result.stdout, result.stderr), (7, "out\n", "err\n"))
            record = json.loads(out.read_text())
            self.assertEqual((record["status"], record["returncode"]), ("ok", 7))
            self.assertGreater(record["ru_maxrss_bytes"], 0)

    def test_cross_check_records_floor_and_calibration(self):
        check = peak_rss.cross_check()
        self.assertTrue(check["rusage_covers_allocation"], check)
        self.assertEqual(check["allocation_bytes"], peak_rss.CALIBRATION_MIB * MIB)
        if peak_rss.trivial_command():
            self.assertIsNotNone(check["sampler_floor_bytes"])
            self.assertLess(check["sampler_floor_bytes"], check["rusage_bytes"])
        if check["time_wrapper_bytes"] is None:
            self.assertIsNone(check["agree"])
        else:
            self.assertIsInstance(check["agree"], bool)


# ---------------------------------------------------------------- hostinfo.py
X86_CPUINFO = """processor\t: 0
vendor_id\t: GenuineIntel
model name\t: Intel(R) Xeon(R) Platinum 8375C CPU @ 2.90GHz
flags\t\t: fpu sse2 avx2 avx512f

processor\t: 1
vendor_id\t: GenuineIntel
model name\t: Intel(R) Xeon(R) Platinum 8375C CPU @ 2.90GHz
flags\t\t: fpu sse2 avx2 avx512f
"""

# A heterogeneous arm64 host: /proc/cpuinfo names no model, only MIDR ids.
ARM_CPUINFO = """processor\t: 0
BogoMIPS\t: 2000.00
Features\t: fp asimd atomics sve2 sme
CPU implementer\t: 0x41
CPU architecture: 8
CPU variant\t: 0x0
CPU part\t: 0xd85
CPU revision\t: 1

processor\t: 1
BogoMIPS\t: 2000.00
Features\t: fp asimd atomics sve2
CPU implementer\t: 0x41
CPU architecture: 8
CPU variant\t: 0x0
CPU part\t: 0xd87
CPU revision\t: 1

processor\t: 2
Features\t: fp asimd atomics sve2 sme
CPU implementer\t: 0x41
CPU part\t: 0xd85
"""

LSCPU = """Architecture:             aarch64
Vendor ID:                ARM
  Model name:             Cortex-X925
    Model:                1
  Model name:             Cortex-A725
    Model:                1
"""

SYSCTL = """hw.optional.floatingpoint: 1
hw.optional.watchpoint: 4
hw.optional.arm.FEAT_LSE: 1
hw.optional.arm.FEAT_SME: 0
machdep.cpu.brand_string: Apple M4 Max
"""


class CpuIdentityTests(unittest.TestCase):
    def test_x86_model_name(self):
        self.assertEqual(hostinfo.cpu_model_from_cpuinfo(X86_CPUINFO),
                         ("Intel(R) Xeon(R) Platinum 8375C CPU @ 2.90GHz", "/proc/cpuinfo model name"))

    def test_arm64_lists_every_core_type_with_raw_ids(self):
        model, source = hostinfo.cpu_model_from_cpuinfo(ARM_CPUINFO)
        self.assertEqual(model, "ARM Cortex-X925 [0x41:0xd85] + ARM Cortex-A725 [0x41:0xd87]")
        self.assertEqual(source, "/proc/cpuinfo CPU implementer/part")

    def test_unknown_parts_are_raw_ids_never_guesses(self):
        text = "CPU implementer\t: 0x61\nCPU part\t: 0x39\n\nCPU implementer\t: 0x41\nCPU part\t: 0xfff\n"
        model, _ = hostinfo.cpu_model_from_cpuinfo(text)
        self.assertEqual(model, "Apple part 0x39 [0x61:0x39] + ARM part 0xfff [0x41:0xfff]")

    def test_board_model_line_is_not_a_cpu_model(self):
        self.assertIsNone(hostinfo.cpu_model_from_cpuinfo("Model\t: Raspberry Pi 4 Model B\n"))

    def test_lscpu_names_every_cluster(self):
        self.assertEqual(hostinfo.cpu_model_from_lscpu(LSCPU),
                         ("Cortex-X925 + Cortex-A725", "lscpu Model name"))
        self.assertIsNone(hostinfo.cpu_model_from_lscpu("Model name:  -\n"))

    def test_linux_preference_order(self):
        self.assertEqual(hostinfo.cpu_model("Linux", cpuinfo=X86_CPUINFO, lscpu=LSCPU)[1],
                         "/proc/cpuinfo model name")
        self.assertEqual(hostinfo.cpu_model("Linux", cpuinfo=ARM_CPUINFO, lscpu=LSCPU)[0],
                         "Cortex-X925 + Cortex-A725")
        self.assertEqual(hostinfo.cpu_model("Linux", cpuinfo=ARM_CPUINFO, lscpu="")[1],
                         "/proc/cpuinfo CPU implementer/part")

    def test_undetectable_model_is_empty_never_a_hostname(self):
        import platform
        model, source = hostinfo.cpu_model("Linux", cpuinfo="", lscpu="")
        self.assertEqual((model, source), ("", "unavailable"))
        self.assertNotEqual(model, platform.node())
        self.assertEqual(hostinfo.cpu_model("Darwin", sysctl=lambda name: ""), ("", "unavailable"))
        self.assertEqual(hostinfo.cpu_model("Darwin", sysctl=lambda name: "Apple M4 Max"),
                         ("Apple M4 Max", "sysctl machdep.cpu.brand_string"))
        self.assertEqual(hostinfo.cpu_model("Plan9"), ("", "unavailable"))

    def test_linux_features_are_common_to_every_core(self):
        self.assertEqual(hostinfo.cpu_features("Linux", cpuinfo=ARM_CPUINFO),
                         (["asimd", "atomics", "fp", "sve2"],
                          "/proc/cpuinfo flags/Features (common to all cores)"))
        self.assertEqual(hostinfo.cpu_features_from_cpuinfo(X86_CPUINFO),
                         ["avx2", "avx512f", "fpu", "sse2"])
        self.assertEqual(hostinfo.cpu_features("Linux", cpuinfo=""), ([], "unavailable"))

    def test_sysctl_features_are_enabled_flags_only(self):
        self.assertEqual(hostinfo.cpu_features_from_sysctl(SYSCTL), ["arm.FEAT_LSE", "floatingpoint"])
        x86 = "machdep.cpu.features: FPU SSE2\nmachdep.cpu.leaf7_features: AVX2\n"
        self.assertEqual(hostinfo.cpu_features_from_sysctl(x86), ["AVX2", "FPU", "SSE2"])
        self.assertEqual(hostinfo.cpu_features("Darwin", sysctl_text="")[1], "unavailable")

    def test_feature_digest_is_order_independent(self):
        self.assertEqual(hostinfo.features_digest(["b", "a"]), hostinfo.features_digest(["a", "b"]))
        self.assertEqual(hostinfo.features_digest(["a", "b"]),
                         hashlib.sha256(b"a\nb").hexdigest())
        self.assertEqual(hostinfo.features_digest([]), "")

    def test_host_provenance_on_this_host(self):
        host = hostinfo.host_provenance()
        for key in ("host_model", "host_model_source", "host_name", "machine_model",
                    "legacy_host_model", "cpu_features", "cpu_features_source",
                    "cpu_features_sha256"):
            self.assertIn(key, host)
        if host["host_model"]:
            self.assertNotEqual(host["host_model"], host["host_name"])

    def test_legacy_identity_is_the_pre_cpu_model_stamp(self):
        """The ratchet matches older baselines on what the harness stamped as
        host_model before it named the CPU: `sysctl -n hw.model`, else the
        hostname."""
        with mock.patch.object(hostinfo, "_sysctl", return_value="Mac16,5"):
            self.assertEqual(hostinfo.legacy_host_identity(), "Mac16,5")
        with mock.patch.object(hostinfo, "_sysctl", return_value=""), \
                mock.patch.object(hostinfo.platform, "node", return_value="spark-d5a4"):
            self.assertEqual(hostinfo.legacy_host_identity(), "spark-d5a4")
        self.assertNotIn("legacy_host_model", harness.REQUIRED_PROVENANCE)


def fake_sysfs(root, capacities, extras=("cpufreq", "cpuidle")):
    for cpu, cap in capacities.items():
        d = Path(root) / f"cpu{cpu}"
        d.mkdir(parents=True)
        if cap is not None:
            (d / "cpu_capacity").write_text(f"{cap}\n")
    for extra in extras:
        (Path(root) / extra).mkdir(parents=True, exist_ok=True)


def shell_pick_core(sysfs):
    """reports/perf/run_scaling.sh's own pick_core, pointed at a fake sysfs."""
    script = (ROOT / "reports/perf/run_scaling.sh").read_text()
    match = re.search(r"^pick_core\(\) \{\n.*?^\}\n", script, re.S | re.M)
    assert match, "pick_core() not found in reports/perf/run_scaling.sh"
    body = match.group(0).replace("/sys/devices/system/cpu", str(sysfs))
    out = subprocess.run(["bash", "-c", body + "pick_core\n"], capture_output=True, text=True,
                         check=True)
    return int(out.stdout.strip())


class AffinityTests(unittest.TestCase):
    def test_pick_core_matches_run_scaling_sh(self):
        layouts = (
            {0: 512, 1: 512, 2: 1024, 3: 1024},        # big cores last
            {0: 1024, 1: 512},                         # big core first
            {0: 512, 2: 1024, 10: 1024, 11: 512},      # tie: glob order puts cpu10 first
            {0: 1024, 1: 1024},                        # homogeneous
            {0: None, 1: None},                        # no cpu_capacity at all
            {0: None, 5: 700, 6: 900},                 # partial exposure
        )
        for layout in layouts:
            with self.subTest(layout=layout), tempfile.TemporaryDirectory() as tmp:
                fake_sysfs(tmp, layout)
                caps = hostinfo.read_cpu_capacities(tmp)
                self.assertEqual(caps, {c: v for c, v in layout.items() if v is not None})
                core, note = hostinfo.pick_core(caps)
                self.assertEqual(core, shell_pick_core(tmp))
                self.assertIn("run_scaling.sh", note)

    def test_pick_core_selection_notes(self):
        self.assertEqual(hostinfo.pick_core({})[0], 0)
        self.assertIn("heterogeneous", hostinfo.pick_core({0: 512, 1: 1024})[1])
        self.assertIn("homogeneous", hostinfo.pick_core({0: 1024, 1: 1024})[1])

    def test_pinning_fails_closed(self):
        # No affinity API (macOS): refuse rather than record a pin that never happened.
        with mock.patch.object(hostinfo.os, "sched_setaffinity", None, create=True), \
                self.assertRaisesRegex(RuntimeError, "unsupported"):
            hostinfo.pin_core("auto", capacities={})

        def refuse(pid, cpus):
            raise OSError(22, "Invalid argument")

        with self.assertRaisesRegex(RuntimeError, "cannot pin to core 7"):
            hostinfo.pin_core("7", capacities={}, setaffinity=refuse, getaffinity=lambda pid: {0})
        with self.assertRaisesRegex(RuntimeError, "kernel reports affinity"):
            hostinfo.pin_core("1", capacities={}, setaffinity=lambda pid, cpus: None,
                              getaffinity=lambda pid: {0, 1})
        for bad in ("-1", "big", ""):
            with self.subTest(requested=bad), self.assertRaises(RuntimeError):
                hostinfo.pin_core(bad, capacities={}, setaffinity=lambda pid, cpus: None,
                                  getaffinity=lambda pid: {0})

    def test_pinned_record(self):
        mask = {}

        def setaffinity(pid, cpus):
            mask["cpus"] = set(cpus)

        record = hostinfo.pin_core("auto", capacities={0: 512, 1: 1024, 2: 1024},
                                   setaffinity=setaffinity, getaffinity=lambda pid: mask["cpus"])
        self.assertEqual(mask["cpus"], {1})
        self.assertEqual((record["policy"], record["core"], record["cpu_capacity"]),
                         ("pinned", 1, 1024))
        self.assertTrue(record["heterogeneous"])
        explicit = hostinfo.pin_core("2", capacities={}, setaffinity=setaffinity,
                                     getaffinity=lambda pid: mask["cpus"])
        self.assertEqual((explicit["core"], explicit["selection"]), (2, "explicit --pin-core"))
        self.assertIsNone(explicit["heterogeneous"])

    def test_unpinned_record_states_the_policy(self):
        record = hostinfo.unpinned_record({"heterogeneous": True, "source": "sysctl hw.nperflevels 2"})
        self.assertEqual((record["policy"], record["core"]), ("none", None))
        self.assertTrue(record["heterogeneous"])
        self.assertTrue(record)  # a stated "none" is present provenance

    def test_core_topology(self):
        self.assertTrue(hostinfo.core_topology("Linux", capacities={0: 1, 1: 2})["heterogeneous"])
        self.assertFalse(hostinfo.core_topology("Linux", capacities={0: 2, 1: 2})["heterogeneous"])
        self.assertIsNone(hostinfo.core_topology("Linux", capacities={})["heterogeneous"])
        self.assertTrue(hostinfo.core_topology("Darwin", sysctl=lambda n: "2")["heterogeneous"])
        self.assertIsNone(hostinfo.core_topology("Darwin", sysctl=lambda n: "")["heterogeneous"])


class CpuPolicyTests(unittest.TestCase):
    LLVM = ["rustc", "--edition=2021", "--target", "aarch64-unknown-linux-gnu",
            "-Copt-level=3", "-o", "out", "src.rs"]

    def test_default_policy_and_parity(self):
        bridge = [self.LLVM[0], "-Zcodegen-backend=/x/lib.so"] + self.LLVM[1:]
        policy = hostinfo.cpu_policy_from_cmds(self.LLVM, bridge)
        self.assertEqual((policy["target_cpu"], policy["target_feature"]), ("default", "default"))
        self.assertTrue(policy["lane_parity"])
        self.assertEqual(policy["bridge_extra_flags"], ["-Zcodegen-backend=/x/lib.so"])
        self.assertIn("identical trustc command", policy["statement"])

    def test_explicit_cpu_in_both_spellings(self):
        llvm = self.LLVM + ["-C", "target-cpu=neoverse-v2", "-Ctarget-feature=+lse"]
        bridge = llvm + ["-Zcodegen-backend=/x/lib.so"]
        policy = hostinfo.cpu_policy_from_cmds(llvm, bridge)
        self.assertEqual((policy["target_cpu"], policy["target_feature"]), ("neoverse-v2", "+lse"))
        self.assertTrue(policy["lane_parity"])
        self.assertIn("not established", policy["statement"])

    def test_lane_drift_breaks_parity(self):
        bridge = self.LLVM + ["-Zcodegen-backend=/x/lib.so", "-Ctarget-cpu=native"]
        policy = hostinfo.cpu_policy_from_cmds(self.LLVM, bridge)
        self.assertFalse(policy["lane_parity"])
        self.assertIn("DIFFER", policy["statement"])
        dropped = hostinfo.cpu_policy_from_cmds(self.LLVM, self.LLVM[:-1])
        self.assertFalse(dropped["lane_parity"])
        self.assertEqual(dropped["llvm_only_flags"], ["src.rs"])

    def test_rustc_print_parsers(self):
        cpus = ("Available CPUs for this target:\n"
                "    native   - Select the CPU of the current host (currently apple-m4).\n"
                "    a64fx\n"
                "    generic  - This is the default target CPU for the current build target "
                "(currently aarch64-unknown-linux-gnu).\n")
        self.assertEqual(hostinfo.parse_default_target_cpu(cpus), "generic")
        self.assertIsNone(hostinfo.parse_default_target_cpu("Available CPUs for this target:\n"))
        cfg = 'target_arch="aarch64"\ntarget_feature="neon"\ntarget_feature="fp-armv8"\n'
        self.assertEqual(hostinfo.parse_cfg_target_features(cfg), ["fp-armv8", "neon"])
        self.assertIsNone(hostinfo.parse_cfg_target_features('target_arch="x"\n'))


# ---------------------------------------------------------------- run.py
def complete_provenance():
    prov = {key: "recorded" for key in harness.REQUIRED_PROVENANCE}
    prov.update(
        git_sha="0123456789abcdef0123456789abcdef01234567", git_dirty=False,
        timestamp_utc="2026-09-18T12:34:56+00:00", host_arch="arm64",
        host_model="Apple M4 Max", host_model_source="sysctl machdep.cpu.brand_string",
        host_name="some-box.local", machine_model="Mac16,5",
        cpu_features=["arm.FEAT_LSE"], cpu_features_sha256="aa" * 32,
        cpu_policy={"target_cpu": "default", "target_feature": "default", "lane_parity": True,
                    "bridge_extra_flags": ["-Zcodegen-backend=/x"]},
        affinity=hostinfo.unpinned_record({"heterogeneous": True, "source": "stub"}),
        rss_sampling={"method": peak_rss.METHOD, "ru_maxrss_unit": "bytes",
                      "cross_check": {"agree": True, "sampler_floor_bytes": 1261568,
                                      "rusage_bytes": 70 * MIB, "time_wrapper_bytes": 70 * MIB,
                                      "time_wrapper": "/usr/bin/time -l"}},
        dylib_sha256="bb" * 32, rustc_version="rustc 1.0", target="aarch64-apple-darwin",
        loadavg_before=0.5, loadavg_after=0.6, load_threshold=8.0, quiet=True,
        load_status="QUIET", cache={"mode": "warm", "verdict_count": 1, "verdict_count_after": 1},
        n_compile=3, n_run=5, n_rss=5, tcg_env={}, os="Darwin", provenance_complete=True,
        size_definition=emitted_size.DEFINITION,
        missing_required_provenance=[],
        proof_checker={"tool": "clean", "candidates": [
            {"path": "/pkg/store/clean/current/bin/clean", "route": "aterm-packaged",
             "sha256": "cc" * 32, "runs": True, "probe": "--version", "version": "clean 0.9.0"}]},
    )
    return prov


def sample_results():
    return {
        "schema": harness.SCHEMA,
        "provenance": complete_provenance(),
        "headline_eligible": False,
        "programs": {
            "p1": {"category": "scalar", "expected_bridge": "MATCH", "verdict": "MATCH",
                   "reason": "", "label": None,
                   "compile": {"llvm_o3": {"times_s": [0.1, 0.11, 0.12], "median_s": 0.11},
                               "bridge_warm": {"times_s": [0.2, 0.21, 0.22], "median_s": 0.21}},
                   "run": {"llvm_o3": {"exit": 3, "nondet_exit": None, "times_s": [0.01] * 5,
                                       "median_s": 0.01, "rel_spread": 0.0},
                           "bridge": {"exit": 3, "nondet_exit": None, "times_s": [0.02] * 5,
                                      "median_s": 0.02, "rel_spread": 0.0}},
                   "size_bytes": {"llvm_o3": 1000, "bridge": 1100},
                   "peak_rss_bytes": {"llvm_o3": 2 * MIB, "bridge": 3 * MIB},
                   "compile_peak_rss_bytes": {"llvm_o2": 90 * MIB, "llvm_o3": 95 * MIB,
                                              "bridge": 120 * MIB},
                   "ratios": {"runtime_vs_llvm_o3": 2.0, "rss_vs_llvm_o3": 1.5}},
            "h3": {"category": "heap", "expected_bridge": "INCOMPLETE", "verdict": "INCOMPLETE",
                   "reason": "bridge fail-closed (quiet machine): x", "label": None,
                   "compile": {"bridge_warm": {"times_s": [], "median_s": None}}, "run": {},
                   "size_bytes": {}, "peak_rss_bytes": {}, "compile_peak_rss_bytes": {},
                   "ratios": {}},
        },
        "aggregates": {"total_programs": 2, "match_count": 1, "incomplete_count": 1,
                       "mismatch_count": 0, "nondet_failclosed_count": 0,
                       "nondet_candidate_count": 0, "coverage_pct": 50.0,
                       "runtime_geomean_vs_llvm_o3": 2.0, "runtime_worst_vs_llvm_o3": 2.0,
                       "compile_warm_geomean_vs_llvm_o2": 1.9,
                       "compile_warm_geomean_vs_llvm_o3": 1.8,
                       "rss_geomean_vs_llvm_o3": 1.5, "size_geomean_vs_llvm_o3": 1.1,
                       "by_category": {}},
    }


class RequiredProvenanceTests(unittest.TestCase):
    def test_complete_provenance_passes(self):
        self.assertEqual(harness.missing_required_provenance(complete_provenance()), [])

    def test_parity_fields_are_required(self):
        for field, empty in (("host_model", ""), ("cpu_features", []), ("cpu_policy", {}),
                             ("affinity", None), ("rss_sampling", None)):
            prov = complete_provenance()
            prov[field] = empty
            with self.subTest(field=field):
                self.assertEqual(harness.missing_required_provenance(prov), [field])
            del prov[field]
            with self.subTest(absent=field):
                self.assertEqual(harness.missing_required_provenance(prov), [field])

    def test_hostname_is_not_required_provenance(self):
        prov = complete_provenance()
        prov["host_name"] = ""
        self.assertEqual(harness.missing_required_provenance(prov), [])


class RetentionTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory(prefix="beat-llvm-retain-")
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        self.res = sample_results()
        self.jpath = self.root / "results" / "0123456789ab-20260918T123456Z.json"
        self.mpath = self.jpath.with_suffix(".md")
        self.jpath.parent.mkdir()
        self.jpath.write_text(json.dumps(self.res))
        self.mpath.write_text("# table\n")

    def test_directory_is_date_and_revision_and_never_collides(self):
        prov = self.res["provenance"]
        first = harness.plan_retention_dir(self.root / "perf", prov)
        self.assertEqual(first.name, "2026-09-18-0123456789ab")
        first.mkdir(parents=True)
        second = harness.plan_retention_dir(self.root / "perf", prov)
        self.assertEqual(second.name, "2026-09-18-0123456789ab-123456Z")
        second.mkdir()
        third = harness.plan_retention_dir(self.root / "perf", prov)
        self.assertEqual(third.name, "2026-09-18-0123456789ab-123456Z-2")
        prov["git_dirty"] = True
        self.assertEqual(harness.plan_retention_dir(self.root / "other", prov).name,
                         "2026-09-18-0123456789ab-dirty")

    def test_retained_record_holds_samples_outcomes_and_hashes(self):
        dest = harness.plan_retention_dir(self.root / "perf", self.res["provenance"])
        harness.write_retention(dest, self.res, self.jpath, self.mpath)
        names = sorted(p.name for p in dest.iterdir())
        self.assertEqual(names, sorted([self.jpath.name, self.mpath.name, "README.md",
                                        "inventory.json", "outcomes.json", "raw_samples.json"]))
        outcomes = json.loads((dest / "outcomes.json").read_text())
        self.assertEqual(outcomes["h3"]["verdict"], "INCOMPLETE")  # intent-to-treat row kept
        raw = json.loads((dest / "raw_samples.json").read_text())
        self.assertEqual(raw["p1"]["compile"]["bridge_warm"], [0.2, 0.21, 0.22])
        self.assertEqual(raw["p1"]["run"]["llvm_o3"]["times_s"], [0.01] * 5)
        self.assertEqual(raw["p1"]["compile_peak_rss_bytes"]["bridge"], 120 * MIB)
        inventory = json.loads((dest / "inventory.json").read_text())
        self.assertEqual(inventory["git_sha"], self.res["provenance"]["git_sha"])
        self.assertFalse(inventory["headline_eligible"])
        for name, entry in inventory["files"].items():
            with self.subTest(file=name):
                data = (dest / name).read_bytes()
                self.assertEqual(entry["sha256"], hashlib.sha256(data).hexdigest())
                self.assertEqual(entry["bytes"], len(data))
        self.assertNotIn("inventory.json", inventory["files"])
        readme = (dest / "README.md").read_text()
        self.assertIn("NOT EVIDENCE", readme)
        self.assertIn("Apple M4 Max", readme)
        self.assertIn("sampler floor 1261568", readme)
        self.assertIn("| compile cold geomean vs -O2 | — (not measured) |", readme)
        self.assertNotIn("](", readme)  # no links for the documentation link gate to chase

    def test_eligible_readme_and_no_overwrite(self):
        self.res["headline_eligible"] = True
        dest = self.root / "perf" / "x"
        harness.write_retention(dest, self.res, self.jpath, self.mpath)
        self.assertIn("**headline_eligible: YES**", (dest / "README.md").read_text())
        with self.assertRaises(FileExistsError):
            harness.write_retention(dest, self.res, self.jpath, self.mpath)

    def test_markdown_reports_cpu_identity_and_rss_method(self):
        text = harness.Harness.markdown(object.__new__(harness.Harness), self.res)
        self.assertIn("host: Apple M4 Max", text)
        self.assertIn("-C target-cpu default", text)
        self.assertIn("affinity none", text)
        self.assertIn("sampler floor 1261568 B", text)
        self.assertIn("gated by contract/gates.json v4 (S1/S2 linked size, S3/S4 emitted size, "
                      "R1/R2 RSS)", text)
        self.assertIn("peak RSS is the median of 5 samples per lane", text)
        self.assertIn("None→None certificates", text)  # no cert store stamped: shown, not guessed
        self.res["provenance"]["cache"]["cert_store"] = {"cert_count": 5, "cert_count_after": 7}
        text = harness.Harness.markdown(object.__new__(harness.Harness), self.res)
        self.assertIn("1→1 verdicts, 5→7 certificates", text)


class HarnessRssTests(unittest.TestCase):
    """Harness.compile_peak_rss / peak_rss through the portable sampler, with a
    stand-in compiler (no trustc, no benchmark)."""

    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory(prefix="beat-llvm-rss-")
        self.addCleanup(self.tmp.cleanup)
        self.dir = Path(self.tmp.name)
        self.h = object.__new__(harness.Harness)
        self.h.env = dict(os.environ)
        self.h.args = argparse.Namespace(target="aarch64-unknown-linux-gnu")
        self.h.dylib = self.dir / "lib.so"
        self.h.driver = fake_driver(self.dir / "fake-rustc")

    def compiler(self, body):
        return write_python_executable(self.dir / "fake-rustc", f"{body}\n")

    def test_compiler_peak_is_measured_in_bytes(self):
        self.h.rustc = str(self.compiler('x = b"\\x01" * (40 << 20)'))
        peak = self.h.compile_peak_rss(self.dir / "p.rs", self.dir / "p", "3", bridge=True)
        self.assertGreaterEqual(peak, 40 * MIB)

    def test_failed_compile_has_no_peak(self):
        self.h.rustc = str(self.compiler("raise SystemExit(1)"))
        self.assertIsNone(self.h.compile_peak_rss(self.dir / "p.rs", self.dir / "p", "3", bridge=False))

    def test_program_peak_survives_checksum_exit(self):
        program = write_python_executable(self.dir / "prog",
                                          'x = b"\\x01" * (24 << 20)\nraise SystemExit(42)\n')
        self.assertGreaterEqual(self.h.peak_rss(program), 24 * MIB)
        crash = write_python_executable(self.dir / "crash",
                                        "import os, signal\nos.kill(os.getpid(), signal.SIGKILL)\n")
        self.assertIsNone(self.h.peak_rss(crash))

    def test_rss_sampling_names_program_compiler_and_unit(self):
        with mock.patch.object(harness.rss_capture, "cross_check", return_value={"agree": None}):
            record = self.h.rss_sampling()
        self.assertEqual(record["method"], peak_rss.METHOD)
        self.assertEqual(record["reported_unit"], "bytes")
        self.assertIn(record["ru_maxrss_unit"], ("bytes", "KiB"))
        self.assertIn("compiled program", record["peak_rss_bytes"])
        self.assertIn("compiler", record["compile_peak_rss_bytes"])
        self.assertIn("gates.json version 3", record["gate"])
        self.assertIn("R1", record["gate"])
        self.assertIn("median of N", record["peak_rss_bytes"])
        self.assertIn("median of N", record["compile_peak_rss_bytes"])
        self.assertIn("max(5%, 2 x", record["noise_policy"])
        self.assertIn("2x sampler_floor_bytes", record["floor_rule"])


FAKE_RUSTC = """#!/bin/sh
case "$*" in
  --version) echo "rustc 1.0.0-fake" ;;
  *target-cpus*) printf '%s\\n' "Available CPUs for this target:" \\
      "    generic - This is the default target CPU for the current build target (currently $4)." ;;
  *cfg*) printf '%s\\n' 'target_arch="aarch64"' 'target_feature="neon"' ;;
  *) exit 1 ;;
esac
"""


class HarnessRuntimeTests(unittest.TestCase):
    def harness(self):
        return harness.Harness.__new__(harness.Harness)

    def test_checksum_exits_include_normal_nonzero_results(self):
        for code in (0, 7, 125):
            with self.subTest(code=code):
                h = self.harness()
                h.run_bin = mock.Mock(return_value=(code, 0.125))
                record = h.runtime_lane(Path("program"), 3)
                self.assertEqual(record["exit"], code)
                self.assertEqual(record["times_s"], [0.125] * 3)
                self.assertEqual(record["median_s"], 0.125)
                self.assertIsNone(record.get("error"))
                self.assertEqual(h.run_bin.call_count, 4)

    def test_signal_termination_is_not_a_stable_checksum(self):
        import signal
        with tempfile.TemporaryDirectory() as td:
            program = write_python_executable(Path(td) / "program",
                                                    "import os, signal\nos.kill(os.getpid(), signal.SIGTERM)\n")
            record = self.harness().runtime_lane(program, 3)
        self.assertIsNone(record["median_s"])
        self.assertEqual(record["times_s"], [])
        self.assertEqual(record["error"]["returncode"], -signal.SIGTERM)
        self.assertEqual(record["error"]["kind"], "signal")
        self.assertEqual(record["error"]["sample"], 0)

    def test_failed_measured_run_preserves_samples_without_a_median(self):
        h = self.harness()
        h.run_bin = mock.Mock(side_effect=[(7, 0.2), (7, 0.125), (-9, 0.1)])
        record = h.runtime_lane(Path("program"), 3)
        self.assertEqual(record["times_s"], [0.125])
        self.assertIsNone(record["median_s"])
        self.assertEqual(record["error"]["returncode"], -9)
        self.assertEqual(record["error"]["phase"], "measured")
        self.assertEqual(record["error"]["sample"], 2)
        self.assertEqual(h.run_bin.call_count, 3)

    def test_reserved_exit_statuses_are_not_benchmark_results(self):
        for code in (126, 127, 255):
            with self.subTest(code=code):
                h = self.harness()
                h.run_bin = mock.Mock(return_value=(code, 0.1))
                record = h.runtime_lane(Path("program"), 3)
                self.assertIsNone(record["median_s"])
                self.assertEqual(record["error"]["kind"], "invalid_exit")
                self.assertEqual(record["error"]["returncode"], code)
                self.assertEqual(h.run_bin.call_count, 1)

    def test_timeout_retains_only_completed_samples(self):
        h = self.harness()
        h.run_bin = mock.Mock(side_effect=[(7, 0.2), (7, 0.125),
                                          subprocess.TimeoutExpired("program", 1)])
        record = h.runtime_lane(Path("program"), 3)
        self.assertEqual(record["times_s"], [0.125])
        self.assertIsNone(record["median_s"])
        self.assertEqual(record["error"]["kind"], "timeout")
        self.assertEqual(record["error"]["sample"], 2)

    def test_missing_executable_is_a_retained_launch_failure(self):
        with tempfile.TemporaryDirectory() as td:
            record = self.harness().runtime_lane(Path(td) / "missing", 3)
        self.assertIsNone(record["median_s"])
        self.assertEqual(record["error"]["kind"], "launch_error")
        self.assertEqual(record["error"]["phase"], "warmup")

    def test_both_lanes_crashing_after_the_oracle_cannot_be_match(self):
        with tempfile.TemporaryDirectory() as td:
            h = self.harness()
            h.repo = h.workdir = Path(td)
            h.args = argparse.Namespace(n_compile=3, n_run=2, n_rss=5, cold=False)
            h.manifest = {"p1": {"expected_exit": 0, "expected_bridge": "MATCH"}}
            source = h.repo / "p1.rs"
            source.write_text("fn main() {}\n")

            def compile_lane(src, out, *args, **kwargs):
                out.write_bytes(b"stand-in")
                return {"ok": True, "times_s": [0.1] * 3, "median_s": 0.1}

            h.compile_lane = compile_lane
            h.emitted_size_lane = mock.Mock(return_value={"bytes": 1})
            h.rss_lanes = mock.Mock(return_value=({}, {}))
            # The pinned LLVM oracle succeeds first; every timing run then
            # terminates identically in both lanes, as during a runtime fault.
            h.run_bin = mock.Mock(side_effect=[(0, 0.1)] + [(-15, 0.1)] * 6)
            row = h.bench_program(source)
        self.assertEqual(row["verdict"], "INCOMPLETE")
        self.assertIn("runtime", row["reason"])
        self.assertEqual(row["ratios"], {})
        h.rss_lanes.assert_not_called()


class HarnessProvenanceTests(unittest.TestCase):
    """Harness.provenance() end to end on a throwaway repository with a stand-in
    trustc: the stamp carries the CPU identity, lane policy, affinity and RSS
    sampling this host yields (no program is compiled or timed)."""

    def test_provenance_stamps_parity_and_sampling(self):
        with tempfile.TemporaryDirectory(prefix="beat-llvm-prov-") as tmp:
            repo = Path(tmp)
            env = {**os.environ, "GIT_AUTHOR_NAME": "t", "GIT_AUTHOR_EMAIL": "t@example.invalid",
                   "GIT_COMMITTER_NAME": "t", "GIT_COMMITTER_EMAIL": "t@example.invalid"}
            (repo / "README").write_text("x\n")
            for cmd in (["init", "-q"], ["add", "README"], ["commit", "-q", "-m", "x"]):
                subprocess.run(["git", "-C", str(repo), *cmd], env=env, check=True,
                               capture_output=True)
            h = object.__new__(harness.Harness)
            h.args = argparse.Namespace(target="aarch64-unknown-linux-gnu", load_threshold=None,
                                        allow_stale_dylib=False, n_compile=3, n_run=5, n_rss=5)
            h.repo, h.workdir, h.env = repo, repo, dict(os.environ)
            h.dylib = repo / "librustc_codegen_trust_cg.so"
            h.dylib.write_bytes(b"\0")
            h.rustc = str(write_executable(repo / "rustc", FAKE_RUSTC))
            h.driver = fake_driver(h.rustc, ("-Ztrust-verify=off",))
            h.affinity = hostinfo.unpinned_record({"heterogeneous": True, "source": "stub"})
            with mock.patch("sys.stderr") as stderr:
                prov = h.provenance()
            warned = "".join(str(c.args[0]) for c in stderr.write.call_args_list)
        self.assertIn("mixes core types", warned)
        host = hostinfo.host_provenance()
        self.assertEqual(prov["host_model"], host["host_model"])
        self.assertEqual(prov["legacy_host_model"], hostinfo.legacy_host_identity())
        self.assertEqual(prov["cpu_features_sha256"], host["cpu_features_sha256"])
        policy = prov["cpu_policy"]
        self.assertEqual((policy["target_cpu"], policy["lane_parity"]), ("default", True))
        self.assertEqual(policy["llvm_default_target_cpu"], "generic")
        self.assertEqual(policy["llvm_default_target_features"], ["neon"])
        self.assertEqual(prov["affinity"]["policy"], "none")
        self.assertEqual(prov["rss_sampling"]["method"], peak_rss.METHOD)
        self.assertTrue(prov["rss_sampling"]["cross_check"]["rusage_covers_allocation"])
        missing = harness.missing_required_provenance(prov)
        detected = [k for k in ("host_model", "cpu_features") if host[k]]
        for field in ("cpu_policy", "affinity", "rss_sampling", *detected):
            self.assertNotIn(field, missing)
        json.dumps(prov)  # the stamp is serialisable into the results JSON


class HarnessOptionTests(unittest.TestCase):
    def parse(self, *argv):
        with mock.patch.object(sys, "argv", ["run.py", *argv]):
            return harness.parse_args()

    def test_options(self):
        self.assertIsNone(self.parse().pin_core)
        self.assertEqual(self.parse("--pin-core").pin_core, "auto")
        self.assertEqual(self.parse("--pin-core", "3").pin_core, "3")
        self.assertEqual(self.parse("--retain-dir", "reports/perf").retain_dir, "reports/perf")

    def test_unpinnable_host_is_a_tooling_error(self):
        args = self.parse("--pin-core", "--repo", str(ROOT))
        failure = RuntimeError("core pinning is unsupported here")
        with mock.patch.object(harness.hostinfo, "pin_core", side_effect=failure), \
                mock.patch.object(harness.Harness, "resolve_rustc") as resolve, \
                mock.patch("sys.stderr"):
            with self.assertRaises(SystemExit) as stop:
                harness.Harness(args)
        self.assertEqual(stop.exception.code, 2)
        resolve.assert_not_called()


def lane(times, ok=None):
    record = {"times_s": list(times), "median_s": statistics.median(times) if times else None}
    if ok is not None:
        record["ok"] = ok
    else:
        record.update(exit=0, nondet_exit=None)  # successful runtime stand-in
    return record


def rss_records(value, n=5):
    """N sampler records that all read VALUE, as bench_program retains them."""
    return [{"bytes": value, "status": "ok" if value else "signaled", "returncode": 0,
             "wall_s": 0.1} for _ in range(n)]


def match_row(category="scalar", runtime=1.0, warm=1.0, cold=None, size=(1000, 1000),
              rss=(40 * MIB, 40 * MIB), compile_rss=(200 * MIB, 200 * MIB, 200 * MIB),
              emitted=(400, 400)):
    """A MATCH row as bench_program leaves it: raw samples per lane (the
    aggregates are computed from these), the size readings and N retained
    samples behind each peak-RSS reading. `runtime`, `warm` and `cold` are the
    bridge/LLVM ratios the samples encode; None leaves that lane without
    samples, and cold=False records a failed cold lane."""
    run = {"llvm_o3": lane([0.2] * 5),
           "bridge": lane([] if runtime is None else [0.2 * runtime] * 5)}
    compile_rec = {f"llvm_o{opt}": lane([0.5] * 3, ok=True) for opt in "023"}
    compile_rec["bridge_warm"] = lane([0.5 * warm] * 3, ok=True)
    if cold is False:
        compile_rec["bridge_cold"] = lane([0.4], ok=False)
    elif cold is not None:
        compile_rec["bridge_cold"] = lane([0.5 * cold] * 3, ok=True)
    peak = dict(zip(("llvm_o3", "bridge"), rss))
    compiler = dict(zip(("llvm_o2", "llvm_o3", "bridge"), compile_rss))
    return {"category": category, "verdict": "MATCH", "label": None, "ratios": {},
            "compile": compile_rec, "run": run,
            "size_bytes": dict(zip(("llvm_o3", "bridge"), size)),
            "emitted_size_bytes": dict(zip(("llvm_o3", "bridge"), emitted)),
            "peak_rss_bytes": peak, "compile_peak_rss_bytes": compiler,
            "rss_samples": {"program": {k: rss_records(v) for k, v in peak.items()},
                            "compiler": {k: rss_records(v) for k, v in compiler.items()}}}


FLOOR_CHECK = {"sampler_floor_bytes": 10 * MIB, "rusage_covers_allocation": True, "agree": True,
               "time_wrapper_present": True}


class AggregateFailClosedTests(unittest.TestCase):
    """Harness.aggregates never averages a subset of the MATCH rows."""

    def aggregates(self, programs, cross_check=FLOOR_CHECK):
        return harness.Harness.aggregates(object.__new__(harness.Harness), programs, cross_check)

    def test_complete_rows_give_every_aggregate(self):
        agg = self.aggregates({"a": match_row(runtime=0.5, size=(1000, 1100)),
                               "b": match_row(runtime=2.0, category="vectorizable")})
        self.assertAlmostEqual(agg["runtime_geomean_vs_llvm_o3"], 1.0, places=12)
        self.assertAlmostEqual(agg["runtime_worst_vs_llvm_o3"], 2.0, places=12)
        self.assertAlmostEqual(agg["vectorizable_worst_runtime_vs_llvm_o3"], 2.0, places=12)
        self.assertAlmostEqual(agg["size_geomean_vs_llvm_o3"], (1.1 * 1.0) ** 0.5, places=12)
        self.assertAlmostEqual(agg["size_worst_vs_llvm_o3"], 1.1, places=12)
        self.assertEqual(agg["rss_geomean_vs_llvm_o3"], 1.0)
        self.assertEqual(agg["compile_rss_geomean_vs_llvm_o2"], 1.0)
        self.assertEqual(agg["program_rss_resolved_loss_count"], 0)
        self.assertTrue(agg["resource_measurement_complete"])
        self.assertEqual(agg["ratio_missing"], {})
        self.assertEqual(agg["coverage_pct"], 100.0)
        self.assertIsNone(agg["compile_cold_geomean_vs_llvm_o2"])  # --cold not requested
        # Stamped values are exact: the harness never rounds what a gate reads.
        agg = self.aggregates({"a": match_row(runtime=1.0004)})
        self.assertGreater(agg["runtime_geomean_vs_llvm_o3"], 1.0)

    def test_failed_or_disagreeing_runtime_outcomes_cannot_supply_a_ratio(self):
        changes = [{"exit": -9}, {"exit": 126}, {"exit": 255}, {"exit": True},
                   {"exit": "0"}, {"exit": None}, {"exit": 7},
                   {"nondet_exit": 7}, {"error": {}},
                   {"error": {"kind": "timeout"}}]
        for change in changes:
            with self.subTest(change=change):
                row = match_row()
                row["run"]["bridge"].update(change)
                agg = self.aggregates({"bad": row})
                self.assertIsNone(agg["runtime_geomean_vs_llvm_o3"])
                self.assertEqual(agg["ratio_missing"]["runtime_vs_llvm_o3"], ["bad"])
        row = match_row()
        del row["run"]["bridge"]["nondet_exit"]
        self.assertIsNone(self.aggregates({"bad": row})["runtime_geomean_vs_llvm_o3"])
        for code in (0, 7, 125):
            row = match_row(runtime=0.5)
            for record in row["run"].values():
                record["exit"] = code
            self.assertEqual(self.aggregates({"ok": row})["runtime_geomean_vs_llvm_o3"], 0.5)

    def test_a_missing_runtime_ratio_is_named_not_dropped(self):
        rows = {"a": match_row(runtime=0.5), "b": match_row(runtime=None)}
        agg = self.aggregates(rows)
        self.assertIsNone(agg["runtime_geomean_vs_llvm_o3"])
        self.assertIsNone(agg["runtime_worst_vs_llvm_o3"])
        self.assertIsNone(agg["scalar_runtime_geomean_vs_llvm_o3"])
        self.assertIsNone(agg["by_category"]["scalar"]["runtime_geomean_vs_llvm_o3"])
        self.assertEqual(agg["ratio_missing"]["runtime_vs_llvm_o3"], ["b"])
        reasons = harness.ineligibility_reasons(complete_provenance(), agg, 3, 5)
        self.assertEqual(reasons, ["runtime/compile samples missing "
                                   "({'runtime_vs_llvm_o3': ['b']})"])

    def test_the_cold_lane_is_unmeasured_until_requested_then_complete_or_null(self):
        agg = self.aggregates({"a": match_row(cold=1.5), "b": match_row(cold=2.0)})
        self.assertAlmostEqual(agg["compile_cold_geomean_vs_llvm_o2"], (1.5 * 2.0) ** 0.5, places=12)
        agg = self.aggregates({"a": match_row(cold=1.5), "b": match_row(cold=False)})
        self.assertIsNone(agg["compile_cold_geomean_vs_llvm_o2"])
        self.assertEqual(agg["ratio_missing"]["compile_cold_vs_llvm_o2"], ["b"])

    def test_a_floor_bound_program_nulls_the_program_rss_geomean(self):
        # gates.json version 4 (ruling OD-32): a reading at or below twice the
        # sampler floor is an upper bound, so no geomean is reported over it,
        # and an uncalibrated sampler qualifies no reading at all.
        agg = self.aggregates({"a": match_row(), "b": match_row(rss=(15 * MIB, 15 * MIB))})
        self.assertEqual(agg["program_rss_floor_bound_count"], 1)
        self.assertIsNone(agg["rss_geomean_vs_llvm_o3"])
        self.assertEqual(agg["compile_rss_geomean_vs_llvm_o2"], 1.0)  # compiler peaks are not floor-bound
        agg = self.aggregates({"a": match_row()}, cross_check=None)
        self.assertIsNone(agg["program_rss_floor_bound_count"])
        self.assertIsNone(agg["rss_geomean_vs_llvm_o3"])

    def test_a_missing_rss_reading_nulls_rss_and_makes_the_row_ineligible(self):
        rows = {"a": match_row(), "b": match_row(rss=(40 * MIB, None))}
        agg = self.aggregates(rows)
        self.assertIsNone(agg["rss_geomean_vs_llvm_o3"])
        self.assertIsNone(agg["program_rss_resolved_loss_count"])
        self.assertEqual(agg["resource_missing"], ["b.peak_rss_bytes.bridge"])
        self.assertFalse(agg["resource_measurement_complete"])
        self.assertEqual(agg["size_geomean_vs_llvm_o3"], 1.0)  # its own readings are complete
        reasons = harness.ineligibility_reasons(complete_provenance(), dict(agg, mismatch_count=0), 3, 5)
        self.assertEqual(len(reasons), 1)
        self.assertIn("size/RSS measurement incomplete", reasons[0])
        self.assertIn("b.peak_rss_bytes.bridge", reasons[0])

    def test_a_progs_subset_is_never_evidence(self):
        corpus = harness.check_gates.corpus_programs()
        self.assertEqual(len(corpus), 18)
        agg = dict(self.aggregates({"a": match_row()}), mismatch_count=0)
        full = {name: match_row() for name in corpus}
        self.assertEqual(harness.ineligibility_reasons(complete_provenance(), agg, 3, 5, full), [])
        subset = {corpus[0]: match_row()}
        reasons = harness.ineligibility_reasons(complete_provenance(), agg, 3, 5, subset)
        self.assertEqual(len(reasons), 1)
        self.assertIn("program subset: 1 of the 18-program contract corpus", reasons[0])

    def test_eligibility_reasons_cover_knobs_degraded_checker_and_sampler(self):
        agg = dict(self.aggregates({"a": match_row()}), mismatch_count=0)
        self.assertEqual(harness.ineligibility_reasons(complete_provenance(), agg, 3, 5), [])
        for change, expected in (({"bridge_cg_args": ["no-proof-certs"]}, "non-default backend knobs"),
                                 ({"proof_checker_degraded": ["a:O3"]}, "verification DEGRADED"),
                                 ({"quiet": False}, "LOADED")):
            prov = dict(complete_provenance(), **change)
            with self.subTest(change=change):
                reasons = harness.ineligibility_reasons(prov, agg, 3, 5)
                self.assertEqual(len(reasons), 1, reasons)
                self.assertIn(expected, reasons[0])
        uncalibrated = dict(self.aggregates({"a": match_row()}, {"agree": False}), mismatch_count=0)
        self.assertIn("RSS sampler calibration",
                      " ".join(harness.ineligibility_reasons(complete_provenance(), uncalibrated, 3, 5)))
        self.assertIn("below contract-default N",
                      " ".join(harness.ineligibility_reasons(complete_provenance(), agg, 1, 5)))


class ProofCheckerTests(unittest.TestCase):
    """proof_checker_record names the Clean candidates in the backend's order."""

    def test_packaged_then_sysroot_candidates_are_stamped_with_digests(self):
        with tempfile.TemporaryDirectory(prefix="beat-llvm-clean-") as tmp:
            root = Path(tmp)
            packaged = root / "pkg" / "store" / "clean" / "current" / "bin" / "clean"
            packaged.parent.mkdir(parents=True)
            write_executable(packaged, "#!/bin/sh\necho 'clean 0.9.0'\n")
            (root / "pkg" / "bin").mkdir()
            sysroot = root / "trust"
            (sysroot / "bin").mkdir(parents=True)
            shipped = write_executable(sysroot / "bin" / "clean", "#!/bin/sh\necho 'clean 0.8.0'\n")
            env = {"PATH": f"{root / 'pkg' / 'bin'}:/usr/bin:/bin", "HOME": str(root / "home")}
            record = harness.proof_checker_record(env, sysroot, "linux")
            self.assertEqual([c["route"] for c in record["candidates"]],
                             ["aterm-packaged", "toolchain-sysroot"])
            self.assertEqual(record["candidates"][0]["path"], str(packaged.resolve()))
            self.assertEqual([c["runs"] for c in record["candidates"]], [True, True])
            self.assertEqual(record["candidates"][0]["version"], "clean 0.9.0")
            self.assertEqual(record["candidates"][1]["sha256"],
                             hashlib.sha256(shipped.read_bytes()).hexdigest())
            prov = dict(complete_provenance(), proof_checker=record)
            agg = dict(AggregateFailClosedTests().aggregates({"a": match_row()}), mismatch_count=0)
            self.assertEqual(harness.ineligibility_reasons(prov, agg, 3, 5), [])
            # An executable-bit text file cannot be exec'd (ENOEXEC), and a
            # failing one is not a checker either: neither counts as runnable.
            packaged.write_text("not a program\n")
            shipped.write_text("#!/bin/sh\nexit 3\n")
            record = harness.proof_checker_record(env, sysroot, "linux")
            self.assertEqual([c["runs"] for c in record["candidates"]], [False, False])
            self.assertIn("cannot execute", record["candidates"][0]["error"])
            self.assertEqual(record["candidates"][1]["returncode"], 3)
            reasons = harness.ineligibility_reasons(dict(prov, proof_checker=record), agg, 3, 5)
            self.assertEqual(reasons, ["no independent proof checker (Clean) candidate ran when probed"])
            none = harness.proof_checker_record({"PATH": "/usr/bin", "HOME": str(root / "home")},
                                                root / "no-sysroot", "linux")
            self.assertEqual(none["candidates"], [])
        reasons = harness.ineligibility_reasons(dict(prov, proof_checker=none), agg, 3, 5)
        self.assertEqual(reasons, ["no independent proof checker (Clean) resolvable for the backend"])

    def test_a_checker_that_hangs_is_not_runnable(self):
        with tempfile.TemporaryDirectory(prefix="beat-llvm-clean-") as tmp:
            hang = write_executable(Path(tmp) / "clean", "#!/bin/sh\nexec sleep 30\n")
            with mock.patch.object(harness, "CHECKER_PROBE_TIMEOUT", 0.5):
                probe = harness.probe_checker(hang, {"PATH": "/usr/bin:/bin"})
        self.assertFalse(probe["runs"])
        self.assertIn("timed out", probe["error"])



class BridgeLaneTests(unittest.TestCase):
    """The bridge lanes' knobs, cold cache, degraded-checker detection and
    fail-closed diagnostics, with a stand-in compiler."""

    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory(prefix="beat-llvm-lane-")
        self.addCleanup(self.tmp.cleanup)
        self.dir = Path(self.tmp.name)
        self.log = self.dir / "calls.jsonl"
        self.h = object.__new__(harness.Harness)
        self.h.env = {k: v for k, v in os.environ.items()
                      if not k.startswith(("TCG_", "TRUST_CG_", "XDG_CACHE_HOME"))}
        self.h.env["LANE_LOG"] = str(self.log)
        self.h.args = argparse.Namespace(target="aarch64-unknown-linux-gnu", bridge_cg_arg=None)
        self.h.dylib = self.dir / "librustc_codegen_trust_cg.so"
        self.h.workdir = self.dir / "work"
        self.h.workdir.mkdir()
        self.src = self.dir / "p.rs"
        self.src.write_text("fn main() {}\n")

    def compiler(self, body=""):
        script = write_python_executable(self.dir / "fake-rustc", f"""import json, os, pathlib, sys
xdg = os.environ.get("XDG_CACHE_HOME")
with open(os.environ["LANE_LOG"], "a") as log:
    log.write(json.dumps({{"argv": sys.argv[1:], "xdg": xdg,
                          "tcg": sorted(k for k in os.environ if k.startswith(("TCG_", "TRUST_CG_")))}}) + "\\n")
if xdg:
    cache = pathlib.Path(xdg, "trust-cg")
    cache.mkdir()
    (cache / "cert").write_text("x")
{body}
""")
        self.h.rustc = str(script)
        self.h.driver = fake_driver(script, ("-Ztrust-verify=off",))
        return script

    def calls(self):
        return [json.loads(line) for line in self.log.read_text().splitlines()]

    def test_knobs_reach_only_the_bridge_as_the_tracked_option(self):
        self.compiler()
        self.h.args.bridge_cg_arg = ["no-proof-certs", "time"]
        bridge = self.h.compile_cmd(self.src, self.dir / "o", "3", bridge=True)
        self.assertEqual(bridge[1:4], [f"-Zcodegen-backend={self.h.dylib}",
                                       "-Ztrust-ir-cg-args=no-proof-certs", "-Ztrust-ir-cg-args=time"])
        llvm = self.h.compile_cmd(self.src, self.dir / "o", "3", bridge=False)
        self.assertFalse([arg for arg in llvm if arg.startswith(("-Ztrust-ir-cg-args", "-Zcodegen"))])

    def test_native_and_cross_target_policy_matches_both_lanes(self):
        self.compiler()
        for target in (self.h.driver["host"], "x86_64-apple-darwin"):
            with self.subTest(target=target):
                self.h.args.target = target
                llvm = self.h.compile_cmd(self.src, self.dir / "o", "3", bridge=False)
                bridge = self.h.compile_cmd(self.src, self.dir / "o", "3", bridge=True)
                self.assertEqual([a for a in bridge if a not in llvm],
                                 [f"-Zcodegen-backend={self.h.dylib}"])
                for command in (llvm, bridge):
                    self.assertIn("-Ztrust-verify=off", command)
                    if target == self.h.driver["host"]:
                        self.assertNotIn("--target", command)
                    else:
                        self.assertEqual(command[command.index("--target") + 1], target)

    def test_cold_compiles_start_from_fresh_private_caches_without_tcg_env(self):
        self.compiler()
        rec = self.h.compile_cold(self.src, self.dir / "o", 2)
        self.assertTrue(rec["ok"], rec)
        self.assertEqual(len(rec["times_s"]), 2)
        self.assertEqual(rec["cache_entries_after"], [2, 2])  # trust-cg/ and its entry
        calls = self.calls()
        roots = [Path(call["xdg"]) for call in calls]
        self.assertEqual(len(set(roots)), 2)
        for root in roots:
            self.assertEqual(root.parent, self.h.workdir)
            self.assertFalse(root.exists())  # removed after its compile
        self.assertEqual([call["tcg"] for call in calls], [[], []])
        self.assertTrue(all(f"-Zcodegen-backend={self.h.dylib}" in call["argv"] for call in calls))

    def test_a_failed_cold_compile_is_recorded_not_timed(self):
        self.compiler("sys.exit(1)")
        rec = self.h.compile_cold(self.src, self.dir / "o", 3)
        self.assertFalse(rec["ok"])
        self.assertEqual(rec["times_s"], [])
        self.assertEqual(len(self.calls()), 1)

    def test_a_degraded_proof_checker_is_recorded_for_bridge_compiles_only(self):
        self.compiler('sys.stderr.write("[trust-cg] INDEPENDENT PROOF CHECKER UNUSABLE — '
                      'verification is DEGRADED\\n")')
        self.assertTrue(self.h.compile_once(self.src, self.dir / "o", "3", bridge=False)[0])
        self.assertFalse(getattr(self.h, "proof_degraded", set()))
        self.assertTrue(self.h.compile_once(self.src, self.dir / "o", "3", bridge=True)[0])
        sample = self.h.compile_rss_sample(self.src, self.dir / "o", "3", bridge=True)
        self.assertEqual(sample["status"], "ok")
        self.assertEqual(self.h.proof_degraded, {"p:O3", "p:rss-O3"})

    def test_fail_closed_errors_keep_their_cause_codes(self):
        self.compiler('sys.stderr.write("error: [TCG-MIR-UNSUPPORTED] cannot compile\\n'
                      '  - f: [TCG-PROOF-465] promotion rejected\\n'
                      '  - g: [TCG-PROOF-465] again\\n"); sys.exit(1)')
        ok, _, err = self.h.compile_once(self.src, self.dir / "o", "3", bridge=True)
        self.assertFalse(ok)
        self.assertTrue(err.startswith("error: [TCG-MIR-UNSUPPORTED]"), err)
        self.assertTrue(err.endswith("causes=[TCG-PROOF-465]"), err)

    def test_compiler_launches_forward_only_advertised_descriptors(self):
        read_fd, write_fd = os.pipe()
        self.addCleanup(os.close, write_fd)
        self.addCleanup(os.close, read_fd)
        with tempfile.TemporaryFile() as lease, tempfile.TemporaryFile() as unrelated:
            descriptors = {}
            for fd in (read_fd, write_fd, lease.fileno()):
                info = os.fstat(fd)
                descriptors[fd] = (info.st_dev, info.st_ino)
            other = os.fstat(unrelated.fileno())
            compiler = self.compiler(f"""
for fd, identity in {descriptors!r}.items():
    try:
        info = os.fstat(fd)
    except OSError:
        raise SystemExit(71)
    assert (info.st_dev, info.st_ino) == identity
try:
    info = os.fstat({unrelated.fileno()})
except OSError:
    pass
else:
    assert (info.st_dev, info.st_ino) != {(other.st_dev, other.st_ino)!r}
""")
            self.h.env = {"PATH": os.defpath, "LANE_LOG": str(self.log)}
            env = {"MAKEFLAGS": f"-j2 --jobserver-auth={read_fd},{write_fd}",
                   "ATERM_SDK_LEASE_V3": str(lease.fileno())}
            out = self.dir / "o"
            ok, _, error = self.h.compile_once(self.src, out, "3", bridge=False, extra_env=env)
            self.assertTrue(ok, error)
            rss = self.h.compile_rss_sample(self.src, out, "3", bridge=False, extra_env=env)
            self.assertEqual((rss["status"], rss["returncode"]), ("ok", 0))
            sample = peak_rss.measure([str(compiler)], env={**self.h.env, **env},
                                      python=sys.executable, inherit_resources=True)
            self.assertEqual((sample.status, sample.returncode), ("ok", 0), sample.stderr)
            sample = peak_rss.measure([str(compiler)], env={**self.h.env, **env})
            self.assertEqual((sample.status, sample.returncode), ("ok", 71))

    def test_invalid_compiler_transport_refuses_before_running(self):
        self.compiler()
        env = {"MAKEFLAGS": "--jobserver-auth=0,1"}
        with self.assertRaisesRegex(peak_rss.ResourceRefusal, "malformed MAKEFLAGS descriptor"):
            self.h.compile_once(self.src, self.dir / "o", "3", bridge=False, extra_env=env)
        sample = peak_rss.measure([self.h.rustc], env={**self.h.env, **env}, inherit_resources=True)
        self.assertEqual((sample.status, sample.returncode), ("wrapper-failed", 127))
        self.assertIn("malformed MAKEFLAGS descriptor", sample.stderr)
        self.assertFalse(self.log.exists())

    def test_rss_samples_keep_status_and_bytes(self):
        program = write_python_executable(self.dir / "prog",
                                          'x = b"\\x01" * (24 << 20)\nraise SystemExit(7)\n')
        sample = self.h.program_rss_sample(program)
        self.assertEqual((sample["status"], sample["returncode"]), ("ok", 7))
        self.assertGreaterEqual(sample["bytes"], 24 * MIB)
        crash = write_python_executable(self.dir / "crash",
                                        "import os, signal\nos.kill(os.getpid(), signal.SIGKILL)\n")
        sample = self.h.program_rss_sample(crash)
        self.assertEqual(sample["status"], "signaled")
        self.assertIsNone(sample["bytes"])


class TargetAndBackendTests(unittest.TestCase):
    def build(self, *argv):
        with mock.patch.object(sys, "argv", ["run.py", "--repo", str(ROOT), *argv]):
            args = harness.parse_args()

        def resolve(h):
            h.driver = fake_driver("/pack/bin/trustc")
            return "/pack/bin/trustc"

        with mock.patch.object(harness.Harness, "resolve_rustc", autospec=True, side_effect=resolve):
            return harness.Harness(args)

    def test_temporary_root_is_never_registered_for_recursive_cleanup(self):
        # Even a regressed guard cannot delete shared data: use a private
        # sandbox and intercept cleanup registration while injecting the fault.
        with tempfile.TemporaryDirectory(prefix="scratch-cleanup-control-") as temporary:
            root = Path(temporary)
            sentinel = root / "keep"
            sentinel.write_text("retained")
            with mock.patch.object(harness.tempfile, "gettempdir", return_value=temporary), \
                    mock.patch.object(harness.tempfile, "mkdtemp", return_value=temporary), \
                    mock.patch.object(harness.atexit, "register") as register, \
                    mock.patch("sys.stderr"):
                with self.assertRaises(SystemExit):
                    self.build()
            register.assert_not_called()
            self.assertEqual(sentinel.read_text(), "retained")

    def test_target_defaults_to_the_driver_host(self):
        h = self.build()
        self.assertEqual(h.args.target, "aarch64-unknown-linux-gnu")
        self.assertEqual(h.target_selection, "driver host")
        h = self.build("--target", "x86_64-apple-darwin")
        self.assertEqual(h.args.target, "x86_64-apple-darwin")
        self.assertEqual(h.target_selection, "explicit --target")

    def test_default_backend_has_this_hosts_suffix(self):
        h = self.build()
        suffix = ".dylib" if sys.platform == "darwin" else ".so"
        self.assertEqual(h.dylib.name, "librustc_codegen_trust_cg" + suffix)
        self.assertEqual(Path(self.build("--dylib", "/x/lib.so").dylib), Path("/x/lib.so"))

    def test_retention_keeps_rss_samples_and_cold_cache_population(self):
        res = sample_results()
        res["programs"]["p1"]["rss_samples"] = {"program": {"bridge": {"bytes": 3 * MIB, "status": "ok"}}}
        res["programs"]["p1"]["compile"]["bridge_cold"] = {"times_s": [0.3], "cache_entries_after": [5]}
        with tempfile.TemporaryDirectory(prefix="beat-llvm-retain-") as tmp:
            jpath, mpath = Path(tmp) / "r.json", Path(tmp) / "r.md"
            jpath.write_text(json.dumps(res))
            mpath.write_text("# t\n")
            dest = harness.write_retention(Path(tmp) / "keep", res, jpath, mpath)
            raw = json.loads((dest / "raw_samples.json").read_text())
        self.assertEqual(raw["p1"]["rss_samples"]["program"]["bridge"]["bytes"], 3 * MIB)
        self.assertEqual(raw["p1"]["cold_cache_entries_after"], [5])
        self.assertIsNone(raw["h3"]["cold_cache_entries_after"])

# ---------------------------------------------------------------- scale_gate.py
class ScaleGateTests(unittest.TestCase):
    def test_rss_reps_use_the_wrapper_wall_and_peak(self):
        sample = peak_rss.Sample(0, "ok", 123 * MIB, 0.75, "", "")
        self.assertEqual(scale_gate.run_once(["rustc"], {}, True, measure=lambda c, env: sample),
                         (0.75, 123 * MIB))
        for bad in (peak_rss.Sample(1, "ok", 5, 0.1, "", ""),
                    peak_rss.Sample(137, "signaled", None, None, "", "")):
            with self.subTest(sample=bad):
                self.assertIsNone(scale_gate.run_once(["rustc"], {}, True,
                                                      measure=lambda c, env, s=bad: s))

    def test_rss_rep_measures_a_real_child(self):
        wall, peak = scale_gate.run_once(allocate(32), dict(os.environ), True)
        self.assertGreater(wall, 0)
        self.assertGreaterEqual(peak, 32 * MIB)

    def test_provenance_header(self):
        host = {"host_model": "", "host_model_source": "unavailable", "machine_model": "",
                "cpu_features": [], "cpu_features_sha256": ""}
        target = {"target": "aarch64-apple-darwin", "target_selection": "driver host"}
        lines = scale_gate.provenance_lines(
            "/x/rustc", "/x/lib.so", hostinfo.unpinned_record(), {"sampler_floor_bytes": 7,
                                                                  "agree": None,
                                                                  "relative_difference": None},
            host=host, **target)
        text = "\n".join(lines)
        self.assertIn("target: aarch64-apple-darwin (driver host)", text)
        self.assertIn("CPU model UNAVAILABLE", text)
        self.assertIn("-C target-cpu default", text)
        self.assertIn("lane parity True", text)
        self.assertIn("affinity: none", text)
        self.assertIn("sampler floor 7 B", text)
        self.assertNotIn("peak RSS", "\n".join(scale_gate.provenance_lines(
            "/x/rustc", "/x/lib.so", hostinfo.unpinned_record(), None, host=host, **target)))

    def test_target_defaults_to_the_driver_host(self):
        # The gate used to fix x86_64-apple-darwin for both lanes, so on Apple
        # silicon it cross-compiled against a host-built backend (X-DARWIN-P8).
        self.assertFalse(hasattr(scale_gate, "TARGET"))
        for host in ("aarch64-apple-darwin", "aarch64-unknown-linux-gnu"):
            with self.subTest(host=host):
                self.assertEqual(scale_gate.resolve_target(None, {"host": host}),
                                 (host, "driver host"))
        self.assertEqual(scale_gate.resolve_target("x86_64-apple-darwin",
                                                   {"host": "aarch64-apple-darwin"}),
                         ("x86_64-apple-darwin", "explicit --target"))
        with self.assertRaises(SystemExit):
            scale_gate.resolve_target(None, {"host": ""})

    def test_both_lanes_compile_for_the_resolved_target(self):
        llvm = scale_gate.lane_cmd("/x/rustc", [], "small", "llvm", "s.rs", "/w",
                                   ("-Ztrust-verify=off",), target="aarch64-apple-darwin")
        tcg = scale_gate.lane_cmd("/x/rustc", ["-Zcodegen-backend=/x/lib.dylib"], "small", "tcg",
                                  "s.rs", "/w", ("-Ztrust-verify=off",),
                                  target="aarch64-apple-darwin")
        for cmd in (llvm, tcg):
            self.assertEqual(cmd[cmd.index("--target") + 1], "aarch64-apple-darwin")
            self.assertEqual(cmd.count("--target"), 1)
        self.assertEqual([a for a in tcg if a not in llvm], ["-Zcodegen-backend=/x/lib.dylib",
                                                             "/w/small.tcg"])
        with self.assertRaises(ValueError):
            scale_gate.lane_cmd("/x/rustc", [], "small", "llvm", "s.rs", "/w")



# ---------------------------------------------------------------- emitted_size.py
def macho_image(sections, uuid=b"\x11" * 16):
    """A minimal 64-bit Mach-O executable: one __TEXT segment holding SECTIONS
    ((name, bytes) pairs, a None body is zero-fill) plus an LC_UUID."""
    import struct
    nsects = len(sections)
    seg_size = 72 + 80 * nsects
    header = 32
    data_at = header + seg_size + 24
    body, cursor, sect_cmds = b"", data_at, b""
    for name, content in sections:
        zerofill = content is None
        size = 16 if zerofill else len(content)
        sect_cmds += struct.pack("<16s16sQQIIIIIIII", name.encode(), b"__TEXT", 0x1000 + cursor,
                                 size, 0 if zerofill else cursor, 0, 0, 0,
                                 0x1 if zerofill else 0, 0, 0, 0)
        if not zerofill:
            body += content
            cursor += len(content)
    segment = struct.pack("<II16sQQQQiiII", 0x19, seg_size, b"__TEXT", 0x1000, cursor, 0, cursor,
                          5, 5, nsects, 0) + sect_cmds
    uuid_cmd = struct.pack("<II16s", 0x1B, 24, uuid)
    mach = struct.pack("<IiiIIIII", 0xFEEDFACF, 0x0100000C, 0, 2, 2, seg_size + 24, 0, 0)
    return mach + segment + uuid_cmd + body


def elf_image(sections):
    """A minimal 64-bit ELF: SECTIONS are (name, bytes, flags) triples."""
    import struct
    names = b"\0" + b"".join(n.encode() + b"\0" for n, _, _ in sections) + b".shstrtab\0"
    body, offsets = b"", []
    for _, content, _ in sections:
        offsets.append(64 + len(body))
        body += content
    strtab_off = 64 + len(body)
    body += names
    shoff = 64 + len(body)
    headers = struct.pack("<IIQQQQIIQQ", 0, 0, 0, 0, 0, 0, 0, 0, 0, 0)
    at = 1
    for (name, content, flags), offset in zip(sections, offsets):
        headers += struct.pack("<IIQQQQIIQQ", at, 1, flags, 0, offset, len(content), 0, 0, 1, 0)
        at += len(name) + 1
    headers += struct.pack("<IIQQQQIIQQ", at, 3, 0, 0, strtab_off, len(names), 0, 0, 1, 0)
    ident = b"\x7fELF" + bytes([2, 1, 1]) + b"\0" * 9
    ehdr = ident + struct.pack("<HHIQQQIHHHHHH", 2, 0xB7, 1, 0, 0, shoff, 0, 64, 0, 0, 64,
                               len(sections) + 2, len(sections) + 1)
    return ehdr + body + headers


LD64_MAP = """# Path: {dir}/p_bridge
# Arch: arm64
# Object files:
[  0] linker synthesized
[  1] {dir}/rustcAbc123/symbols.o
[  2] {dir}/p_bridge.p.123-cgu.0.rcgu.o
[  3] {dir}/p_bridge.allocator_shim.rcgu.o
[  4] /sysroot/lib/libstd-1.rlib(std-1.std.9-cgu.0.rcgu.o)
[  5] /usr/lib/crt1.o
[  6] /SDK/usr/lib/libSystem.tbd
[  7] p_bridge.p.123-cgu.1.rcgu.o
# Sections:
# Address\tSize    \tSegment\tSection
0x100000400\t0x00000200\t__TEXT\t__text
0x100000600\t0x0000000C\t__TEXT\t__stubs
0x10000060C\t0x00000020\t__TEXT\t__const
0x10000062C\t0x00000010\t__TEXT\t__cstring
0x10000063C\t0x00000040\t__TEXT\t__unwind_info
0x100004000\t0x00000030\t__DATA_CONST\t__const
0x100008000\t0x00000010\t__DATA\t__data
0x100008010\t0x00000020\t__DATA\t__bss
# Symbols:
# Address\tSize    \tFile  Name
0x100000400\t0x00000040\t[  2] _main_body
0x100000440\t0x00000020\t[  3] ___rust_alloc
0x100000460\t0x00000180\t[  4] _std_thing
0x1000005E0\t0x00000010\t[  5] _start
0x1000005F0\t0x00000010\t[  7] _second_cgu
0x100000600\t0x0000000C\t[  0] stub
0x10000060C\t0x00000010\t[  2] l_anon.1
0x10000061C\t0x00000010\t[  4] l_anon.std
0x10000062C\t0x00000008\t[  2] cstring1
0x10000063C\t0x00000040\t[  0] compact unwind info
0x100004000\t0x00000018\t[  2] vtable
0x100008000\t0x00000008\t[  2] _STATIC
0x100008010\t0x00000010\t[  2] _BSS
# Dead Stripped Symbols:
#        \tSize    \tFile  Name
<<dead>> \t0x00000100\t[  2] _dead_fn
"""

GNU_LD_MAP = """Archive member included to satisfy reference by file (symbol)

/sysroot/libstd.rlib(std.o)
                              {dir}/p.p.1-cgu.0.rcgu.o (_ZN3std2rt10lang_start17h1E)

Discarded input sections

 .text          0x0000000000000000        0x0 {dir}/p.p.1-cgu.0.rcgu.o
 .text._ZN4dead17h0123456789abcdefE
                0x0000000000000000       0x40 {dir}/p.p.1-cgu.0.rcgu.o

Memory Configuration

Name             Origin             Length             Attributes
*default*        0x0000000000000000 0xffffffffffffffff

Linker script and memory map

LOAD /usr/lib/aarch64-linux-gnu/Scrt1.o
LOAD {dir}/p.p.1-cgu.0.rcgu.o
                [!provide]                        PROVIDE (__executable_start = SEGMENT_START ("text-segment", 0x0))
                0x0000000000000238                . = (SEGMENT_START ("text-segment", 0x0) + SIZEOF_HEADERS)

.text           0x0000000000001000      0x200
 *(.text.unlikely .text.*_unlikely .text.unlikely.*)
 *(.text .stub .text.* .gnu.linkonce.t.*)
 .text          0x0000000000001000       0x34 /usr/lib/aarch64-linux-gnu/Scrt1.o
                0x0000000000001000                _start
 .text._ZN1p4main17h0123456789abcdefE
                0x0000000000001040       0x54 {dir}/p.p.1-cgu.0.rcgu.o
                0x0000000000001040                _ZN1p4main17h0123456789abcdefE
 *fill*         0x0000000000001094        0xc
 .text.main     0x00000000000010a0       0x30 {dir}/p.p.1-cgu.0.rcgu.o
                0x00000000000010a0                main
 .text          0x00000000000010d0       0x80 /sysroot/libstd.rlib(std.o)

.rodata         0x0000000000002000       0x60
 *(.rodata .rodata.* .gnu.linkonce.r.*)
 .rodata..Lanon.1
                0x0000000000002000       0x18 {dir}/p.p.1-cgu.0.rcgu.o
 .rodata.cst16  0x0000000000002020       0x10 {dir}/p.p.1-cgu.0.rcgu.o
 .rodata        0x0000000000002030       0x30 /sysroot/libstd.rlib(std.o)

.eh_frame       0x0000000000002060       0x40
 .eh_frame      0x0000000000002060       0x28 {dir}/p.p.1-cgu.0.rcgu.o

.data.rel.ro    0x0000000000003000       0x20
 .data.rel.ro..Lanon.2
                0x0000000000003000       0x20 {dir}/p.p.1-cgu.0.rcgu.o

.data           0x0000000000004000        0x8
 .data          0x0000000000004000        0x8 {dir}/p.p.1-cgu.0.rcgu.o

.bss            0x0000000000004008       0x10
 .bss           0x0000000000004008       0x10 {dir}/p.p.1-cgu.0.rcgu.o

/DISCARD/
 *(.note.GNU-stack)

.comment        0x0000000000000000       0x2b
 .comment       0x0000000000000000       0x2b {dir}/p.p.1-cgu.0.rcgu.o
                                         0x2c (size before relaxing)
"""


class EmittedSizeTests(unittest.TestCase):
    """emitted_size.py: the program's own bytes from the linker's map (no link runs)."""

    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory(prefix="beat-llvm-size-")
        self.addCleanup(self.tmp.cleanup)
        self.dir = Path(self.tmp.name)

    def measure(self, text):
        path = self.dir / "link.map"
        path.write_text(text.format(dir=self.dir))
        return emitted_size.measure_map(path, self.dir, cwd=self.dir)

    def test_ld64_map_counts_only_the_programs_code_and_read_only_data(self):
        record = self.measure(LD64_MAP)
        self.assertIsNone(record["error"])
        self.assertEqual(record["format"], "ld64")
        # text: _main_body 0x40 + ___rust_alloc 0x20 + the relative cgu.1 0x10 (std, crt1,
        # the linker's stub and the dead-stripped _dead_fn are not the program's).
        self.assertEqual(record["classes"]["text"], 0x40 + 0x20 + 0x10)
        # read-only data: __TEXT,__const 0x10 + __cstring 0x8 + __DATA_CONST,__const 0x18.
        self.assertEqual(record["classes"]["rodata"], 0x10 + 0x8 + 0x18)
        self.assertEqual((record["classes"]["data"], record["classes"]["zerofill"]), (8, 16))
        self.assertEqual(record["classes"]["unwind"], 0)  # compact unwind is the linker's
        self.assertEqual(record["bytes"], 0x70 + 0x30)
        self.assertEqual(record["sections"]["__TEXT,__text"], 0x70)
        self.assertEqual(record["program_objects"],
                         ["p_bridge.allocator_shim.rcgu.o", "p_bridge.p.123-cgu.0.rcgu.o",
                          "p_bridge.p.123-cgu.1.rcgu.o", "symbols.o"])
        self.assertEqual(len(record["map_sha256"]), 64)

    def test_gnu_ld_map_counts_only_the_programs_code_and_read_only_data(self):
        record = self.measure(GNU_LD_MAP)
        self.assertIsNone(record["error"])
        self.assertEqual(record["format"], "gnu-ld")
        self.assertEqual(record["classes"]["text"], 0x54 + 0x30)  # discarded _dead not counted
        self.assertEqual(record["classes"]["rodata"], 0x18 + 0x10 + 0x20)  # incl. .data.rel.ro
        self.assertEqual(record["classes"]["unwind"], 0x28)
        self.assertEqual((record["classes"]["data"], record["classes"]["zerofill"]), (8, 16))
        self.assertEqual(record["classes"]["other"], 0x2b)  # .comment: not loaded, not counted
        self.assertEqual(record["bytes"], 0x84 + 0x48)
        self.assertEqual(record["program_objects"], ["p.p.1-cgu.0.rcgu.o"])

    def test_unreadable_unknown_or_empty_maps_are_unmeasured_never_zero(self):
        head, symbols = LD64_MAP.split("# Symbols:")
        std_only = head + "# Symbols:" + "".join(
            line.replace(line[line.index("["):line.index("]") + 1], "[  4]") + "\n"
            if line.startswith("0x") else line + "\n" for line in symbols.splitlines())
        for name, text in (("unknown", "VMA LMA Size Align Out In Symbol\n"),
                           ("no program bytes", std_only)):
            with self.subTest(name):
                record = self.measure(text)
                self.assertIsNone(record["bytes"])
                self.assertTrue(record["error"])
        record = emitted_size.measure_map(self.dir / "absent.map", self.dir)
        self.assertIsNone(record["bytes"])
        self.assertIn("unreadable", record["error"])

    def test_a_program_atom_outside_every_mapped_section_refuses_the_reading(self):
        # Before the first section, in the gap after __TEXT, and past the last
        # section: the atom's bytes cannot be classified, so the whole reading
        # is refused rather than undercounted by skipping them.
        head, dead = LD64_MAP.split("# Dead Stripped Symbols:")
        for address in ("0x100000000", "0x100000700", "0x200000000"):
            with self.subTest(address=address):
                text = (head + f"{address}\t0x00000010\t[  2] _stray\n"
                        + "# Dead Stripped Symbols:" + dead)
                record = self.measure(text)
                self.assertIsNone(record["bytes"])
                self.assertIn("lies in no mapped section", record["error"])
                self.assertIn(address[2:].lstrip("0").lower(), record["error"])
        # A stray atom from a sysroot archive member is not the program's: no refusal.
        text = head + "0x200000000\t0x00000010\t[  4] _std_stray\n# Dead Stripped Symbols:" + dead
        self.assertEqual(self.measure(text)["bytes"], 0x70 + 0x30)

    def test_program_objects_are_this_compiles_relocatable_objects(self):
        inside = self.dir / "a.rcgu.o"
        self.assertTrue(emitted_size.program_object(str(inside), self.dir))
        self.assertTrue(emitted_size.program_object("a.rcgu.o", self.dir))  # relative to cwd
        self.assertFalse(emitted_size.program_object("/elsewhere/a.rcgu.o", self.dir))
        self.assertFalse(emitted_size.program_object(f"{self.dir}/lib.rlib(a.o)", self.dir))
        self.assertFalse(emitted_size.program_object("linker synthesized", self.dir))
        self.assertFalse(emitted_size.program_object(f"{self.dir}/libfoo.dylib", self.dir))

    def test_link_map_arguments_per_platform(self):
        self.assertEqual(emitted_size.link_map_args("/m", "darwin"),
                         ["-C", "link-arg=-Wl,-map,/m"])
        self.assertEqual(emitted_size.link_map_args("/m", "linux"),
                         ["-C", "link-arg=-Wl,-Map=/m"])

    def test_image_digest_ignores_link_identity_but_not_code(self):
        a = self.dir / "a"
        b = self.dir / "b"
        c = self.dir / "c"
        sections = [("__text", b"\x1f\x20\x03\xd5" * 4), ("__const", b"k" * 8), ("__bss", None)]
        a.write_bytes(macho_image(sections, uuid=b"\x01" * 16))
        b.write_bytes(macho_image(sections, uuid=b"\x02" * 16))
        c.write_bytes(macho_image([("__text", b"\x1f\x20\x03\xd5" * 3 + b"\0\0\0\0"),
                                   ("__const", b"k" * 8), ("__bss", None)]))
        self.assertEqual(emitted_size.image_digest(a), emitted_size.image_digest(b))
        self.assertNotEqual(emitted_size.image_digest(a), emitted_size.image_digest(c))
        e1, e2, e3 = self.dir / "e1", self.dir / "e2", self.dir / "e3"
        e1.write_bytes(elf_image([(".text", b"code", 6), (".note.gnu.build-id", b"id-1", 2),
                                  (".comment", b"GCC 1", 0)]))
        e2.write_bytes(elf_image([(".text", b"code", 6), (".note.gnu.build-id", b"id-2", 2),
                                  (".comment", b"GCC 2", 0)]))
        e3.write_bytes(elf_image([(".text", b"edoc", 6), (".note.gnu.build-id", b"id-1", 2),
                                  (".comment", b"GCC 1", 0)]))
        self.assertEqual(emitted_size.image_digest(e1), emitted_size.image_digest(e2))
        self.assertNotEqual(emitted_size.image_digest(e1), emitted_size.image_digest(e3))
        (self.dir / "junk").write_bytes(b"not an image")
        with self.assertRaises(ValueError):
            emitted_size.image_digest(self.dir / "junk")


FAKE_SIZE_RUSTC = """import sys
from pathlib import Path
sys.path.insert(0, {tests!r})
import test_run_provenance as t
args = sys.argv[1:]
out = Path(args[args.index("-o") + 1])
link = [a for a in args if a.startswith("link-arg=")]
code = {code!r}
out.write_bytes(t.macho_image([("__text", code), ("__const", b"k" * 8)]))
(out.parent / "fake.p-cgu.0.rcgu.o").write_bytes(b"")
if link:
    path = link[0].split(",", 2)[2] if ",-map," in link[0] else link[0].split("-Map=", 1)[1]
    Path(path).write_text(t.LD64_MAP.format(dir=out.parent)
                          .replace("p_bridge.p.123-cgu.0.rcgu.o", "fake.p-cgu.0.rcgu.o"))
"""


class HarnessEmittedSizeTests(unittest.TestCase):
    """Harness.emitted_size_lane with a stand-in compiler that links an image and
    writes an Apple-format map (no trustc, no linker)."""

    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory(prefix="beat-llvm-esize-")
        self.addCleanup(self.tmp.cleanup)
        self.dir = Path(self.tmp.name)
        self.h = object.__new__(harness.Harness)
        self.h.env = dict(os.environ)
        self.h.args = argparse.Namespace(target="aarch64-apple-darwin")
        self.h.workdir = self.dir
        self.h.dylib = self.dir / "lib.dylib"
        self.timed = self.dir / "timed"
        self.timed.write_bytes(macho_image([("__text", b"\x1f\x20\x03\xd5" * 4),
                                            ("__const", b"k" * 8)], uuid=b"\x09" * 16))

    def compiler(self, code):
        script = FAKE_SIZE_RUSTC.format(tests=str(HERE), code=code)
        self.h.rustc = str(write_python_executable(self.dir / "fake-rustc", script))
        self.h.driver = fake_driver(self.h.rustc)

    def test_the_map_linked_twin_of_the_timed_binary_is_measured(self):
        self.compiler(b"\x1f\x20\x03\xd5" * 4)
        with mock.patch.object(harness.emitted_size, "link_map_args",
                               lambda path, platform=None: ["-C", f"link-arg=-Wl,-map,{path}"]):
            record = self.h.emitted_size_lane(self.dir / "p.rs", "p", "llvm_o3", "3", False,
                                              self.timed)
        self.assertIsNone(record["error"], record)
        self.assertEqual(record["bytes"], 0x70 + 0x30)
        self.assertEqual(record["image_sha256"], record["timed_image_sha256"])
        self.assertIn("fake.p-cgu.0.rcgu.o", record["program_objects"])
        self.assertEqual([p.name for p in self.dir.iterdir() if p.name.startswith("size-")], [])

    def test_a_twin_whose_code_differs_is_refused(self):
        self.compiler(b"\x00" * 16)
        record = self.h.emitted_size_lane(self.dir / "p.rs", "p", "llvm_o3", "3", False, self.timed)
        self.assertIsNone(record["bytes"])
        self.assertIn("differ from the timed compile's binary", record["error"])

    def test_a_failed_size_compile_is_unmeasured(self):
        self.h.rustc = str(write_executable(self.dir / "fail-rustc",
                                            "#!/bin/sh\necho 'error: boom' >&2\nexit 1\n"))
        self.h.driver = fake_driver(self.h.rustc)
        record = self.h.emitted_size_lane(self.dir / "p.rs", "p", "bridge", "3", True, self.timed)
        self.assertIsNone(record["bytes"])
        self.assertIn("size compile failed: error: boom", record["error"])


class HarnessMedianRssTests(unittest.TestCase):
    """Harness.rss_lanes: N interleaved samples per lane and their exact median."""

    def test_samples_interleave_lanes_and_report_the_median(self):
        h = object.__new__(harness.Harness)
        order = []
        readings = {"a": iter([30, 10, 20]), "b": iter([5, 5, 7])}

        def sample(lane):
            order.append(lane)
            return {"bytes": next(readings[lane]), "status": "ok"}

        samples, medians = h.rss_lanes(3, ("a", "b"), sample)
        self.assertEqual(order, ["a", "b", "a", "b", "a", "b"])
        self.assertEqual(medians, {"a": 20, "b": 5})
        self.assertEqual([s["bytes"] for s in samples["a"]], [30, 10, 20])

    def test_a_failed_sample_leaves_the_lane_without_a_reading(self):
        h = object.__new__(harness.Harness)
        values = iter([10, None, 12])
        _, medians = h.rss_lanes(3, ("a",), lambda lane: {"bytes": next(values)})
        self.assertEqual(medians, {"a": None})

    def test_n_rss_is_an_odd_positive_count(self):
        self.assertEqual(harness.odd_positive_int("5"), 5)
        for bad in ("4", "0", "-3"):
            with self.subTest(bad=bad), self.assertRaises(argparse.ArgumentTypeError):
                harness.odd_positive_int(bad)
        with mock.patch.object(sys, "argv", ["run.py"]):
            self.assertEqual(harness.parse_args().n_rss, 5)
        with mock.patch.object(sys, "argv", ["run.py", "--n-rss", "3"]):
            self.assertEqual(harness.parse_args().n_rss, 3)

    def test_fewer_rss_samples_than_the_contract_is_not_evidence(self):
        agg = dict(harness.Harness.aggregates(object.__new__(harness.Harness),
                                              {"a": match_row()}, FLOOR_CHECK), mismatch_count=0)
        self.assertEqual(harness.ineligibility_reasons(complete_provenance(), agg, 3, 5, n_rss=5), [])
        reasons = harness.ineligibility_reasons(complete_provenance(), agg, 3, 5, n_rss=3)
        self.assertEqual(reasons, ["below contract-default N (peak RSS 3 < 5)"])

    def test_the_harness_and_the_checker_agree_on_the_retained_sample_count(self):
        # No MATCH row (the Darwin production lane today): no retained reading,
        # so only the provenance N applies, in the harness as in check_gates.
        incomplete = dict(match_row(), verdict="INCOMPLETE")
        agg = dict(harness.Harness.aggregates(object.__new__(harness.Harness),
                                              {"a": incomplete}, FLOOR_CHECK), mismatch_count=0)
        self.assertIsNone(agg["rss_min_samples"])
        self.assertTrue(harness.check_gates.rss_samples_meet_contract({"a": incomplete}, agg))
        self.assertEqual(harness.ineligibility_reasons(complete_provenance(), agg, 3, 5, n_rss=5), [])
        # A MATCH row whose retained lanes hold fewer samples than the contract
        # N is ineligible in both, whatever provenance says.
        short = match_row()
        for kind in short["rss_samples"].values():
            for lane_name in kind:
                kind[lane_name] = kind[lane_name][:3]
        agg = dict(harness.Harness.aggregates(object.__new__(harness.Harness),
                                              {"a": short}, FLOOR_CHECK), mismatch_count=0)
        self.assertEqual(agg["rss_min_samples"], 3)
        self.assertFalse(harness.check_gates.rss_samples_meet_contract({"a": short}, agg))
        self.assertEqual(harness.ineligibility_reasons(complete_provenance(), agg, 3, 5, n_rss=5),
                         ["retained peak-RSS samples below the contract N (fewest 3 < 5)"])


if __name__ == "__main__":
    unittest.main()
