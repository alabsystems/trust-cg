# Author: Andrew Yates | Copyright 2026 Andrew Yates | License: Apache-2.0
"""CPU receipt admission and profile-only/floor scope boundaries."""
import contextlib
import io
from pathlib import Path
import sys
import tempfile
import unittest
from unittest import mock

SCRIPTS = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(SCRIPTS))
try:
    import check_aarch64_cpu_profiles as profiles
finally:
    sys.path.pop(0)


def baseline_receipt():
    return ("AARCH64_CPU_PROFILE checks=5 profile=aarch64-isa-v1 CPU_FEATURES "
            "hwcap=8fb hwcap2=0 lse=0 fp16_scalar=0 fp16_simd=0 dotprod=0\n"
            "AARCH64_JIT_CPU_PROFILE cells=16 matched=4 refused=12\n"
            "AARCH64_EMULATION_CONTRACT controls=8\n")


class CpuProfileReceiptTests(unittest.TestCase):
    def test_baseline_requires_actual_flags_and_complete_jit_outcomes(self):
        row = profiles.feature_census(baseline_receipt(), "cortex-a53")
        self.assertEqual((row["jit_matched"], row["jit_refused"]), (4, 12))
        self.assertEqual(row["cpu_flags"]["hwcap"], "8fb")

    def test_missing_flags_duplicate_receipts_and_truncated_denominators_refuse(self):
        text = baseline_receipt()
        controls = (
            text.replace(" hwcap2=0", ""), text.replace(" dotprod=0", ""), text + text,
            text.replace("matched=4 refused=12", "matched=4 refused=8"),
            text.replace("AARCH64_EMULATION_CONTRACT controls=8", ""),
        )
        for control in controls:
            with self.subTest(control=control), self.assertRaises(RuntimeError):
                profiles.feature_census(control, "cortex-a53")

    def test_mislabelled_cpu_cannot_reuse_baseline_receipt(self):
        with self.assertRaisesRegex(RuntimeError, "requested max"):
            profiles.feature_census(baseline_receipt(), "max")
        with self.assertRaisesRegex(RuntimeError, "requested cortex-a53"):
            profiles.feature_census(baseline_receipt().replace("lse=0", "lse=1"), "cortex-a53")

    def test_filtered_positive_target_cannot_pass_summary_admission(self):
        full = "test result: ok. 3 passed; 0 failed; 0 ignored; 0 measured; 0 filtered out;"
        self.assertEqual(profiles.SUMMARY.findall(full), ["3"])
        self.assertEqual(profiles.SUMMARY.findall(full.replace("0 filtered out", "1 filtered out")), [])


class CpuProfileScopeTests(unittest.TestCase):
    def test_native_floor_removes_and_records_ambient_child_emulation(self):
        environment = {"TCG_TEST_AARCH64_EMULATOR": "/private/qemu", "TCG_TEST_AARCH64_CPU": "max"}
        self.assertEqual(profiles.floor.scrubbed_environment(environment), sorted(environment))

    def test_profile_only_propagates_failure_without_writing_floor_report(self):
        with tempfile.TemporaryDirectory() as temp:
            output = Path(temp) / "matrix"
            with mock.patch.object(profiles.floor.subprocess, "call", return_value=1) as call:
                result = profiles.floor.main([
                    "--cpu-profile", "host+baseline-emulation", "--cpu-profile-only",
                    "--aarch64-emulator", "/private/qemu-aarch64", "--out", str(output),
                    "--cpu-profile-driver", "/private/trust/bin/trustc",
                ])
            self.assertEqual(result, 1)
            self.assertFalse(output.exists())
            self.assertIn("check_aarch64_cpu_profiles.py", call.call_args.args[0][1])
            self.assertIn("/private/trust/bin/trustc", call.call_args.args[0])

    def test_profile_controls_need_explicit_matrix_and_executor(self):
        for args in (["--cpu-profile-only"], ["--aarch64-emulator", "/private/qemu"],
                     ["--cpu-profile", "host+baseline-emulation"]):
            with self.subTest(args=args), contextlib.redirect_stderr(io.StringIO()), self.assertRaises(SystemExit):
                profiles.floor.main(args)

    def test_matrix_listing_does_not_rename_or_delete_native_floor_targets(self):
        original = profiles.floor.TARGETS
        stream = io.StringIO()
        with contextlib.redirect_stdout(stream):
            result = profiles.floor.main(["--list", "--cpu-profile", "host+baseline-emulation",
                                          "--aarch64-emulator", "/private/qemu"])
        self.assertEqual(result, 0)
        text = stream.getvalue()
        for package, target in original:
            self.assertIn(f"{package} {target}", text)
        self.assertIn("cpu-profile-matrix native-host qemu-max qemu-cortex-a53", text)
        self.assertEqual(profiles.floor.TARGETS, original)


if __name__ == "__main__":
    unittest.main()
