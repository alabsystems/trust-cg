"""scripts/check_linux_x86_64.py: the x86-64 floor's minimums, its bridge lane and its
decided-absent record (the last shared with the AArch64 floor)."""

from __future__ import annotations

import contextlib
import importlib.util
import io
import json
from pathlib import Path
import sys
import shlex
import tempfile
import types
import unittest
from unittest import mock


# The selected interpreter can live below "Application Support". A kernel
# shebang splits such a path; this shell/Python header execs the exact quoted
# interpreter and preserves the fixture argv. Python sees the exec as a string.
PYTHON_FIXTURE_HEADER = (
    "#!/bin/sh\n'''exec' " + shlex.quote(sys.executable) + ' "$0" "$@"\n' + "' '''\n"
)

ROOT = Path(__file__).resolve().parents[2]


def load(name: str):
    spec = importlib.util.spec_from_file_location(name, ROOT / "scripts" / f"{name}.py")
    assert spec is not None and spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


GATE = load("check_linux_x86_64")
SHARED = GATE.SHARED
SWIFTCC = ("trust-cg-codegen", "e2e_x86_64_swiftcc")
BRIDGE_LANE = ("rustc-codegen-trust-cg", "m143_x86_vectorize_trace")

PINNED_MINIMUMS = {
    ("trust-cg-codegen", "e2e_x86_64_aggregate_abi"): 18,
    ("trust-cg-codegen", "e2e_x86_64_aggregate_byval_arg"): 6,
    # All twelve, because two of them EXECUTE the internal multi-result
    # convention (the link-run and JIT lanes) and are the only native evidence
    # for it.
    ("trust-cg-codegen", "e2e_x86_64_internal_multi_result"): 12,
    # All three, because the run leg is the only one that EXECUTES the
    # split-copy replay kernels; the provenance and compile legs alone would
    # let the row pass on a host where nothing ran.
    ("trust-cg-codegen", "e2e_x86_64_split_copy_replay"): 3,
    ("rustc-codegen-trust-cg", "m143_x86_vectorize_trace"): 2,
    # All nine, because four of them LINK and EXECUTE the TY BFS kernel and are
    # the only evidence that x86-64 TY code runs at all; the default minimum of
    # 1 would let the five compile-only tests satisfy the row on a host where
    # nothing executed.
    ("trust-cg-codegen", "ty_bfs_minimal"): 9,
    # All five, so the three cheap structural guards cannot satisfy the row on a
    # host where neither the O0 nor the O1 lowering sweep actually ran.
    ("trust-cg-codegen", "clean_fixture_host_lowering"): 5,
}
# The floor's target count, asserted so a lane cannot leave it silently; the
# floor has no source census that would catch a dropped row. Move it only
# together with the lane that was added or removed.
REQUIRED_TARGET_COUNT = 73  # Includes the required e2e_x86_64_sib_rmw target.


def trust_lane_provenance(build_command: list[str], trust: dict | None = None) -> dict:
    """The keys main() and the target commands require of preflight's
    provenance, the Trust development lane being the floor's only lane (a
    missing key must raise, not pass), with the resolved bridge package or none.
    """
    record = {
        "lane": "trust-unverified", "build_command": list(build_command), "tools": {"env": "/usr/bin/env"},
        "runtime_checker_environment": {}, "compiler_environment": {}, "compiler_tool_identities": {},
    }
    if trust is not None:
        record["trust_bridge"] = trust
    return record


# The root workspace's build command in the target-command fixtures.
ROOT_LANE = ["/root-lane/bin/targo", "--unverified"]


def cargo_config_record(problems: tuple[str, ...] = (), sha: str = "c" * 64) -> dict:
    """A cargo_config audit record: the committed repository config, and any problems."""
    return {
        "cwd": "/fixture", "cargo_home": "/fixture/.cargo", "environment": {},
        "files": [{"path": "/fixture/.cargo/config.toml", "sha256": sha, "bytes": 1,
                   "exempt": "the repository's committed config"}],
        "problems": list(problems),
    }


def transcript(passed: int) -> str:
    return (
        f"running {passed} tests\n"
        f"test result: ok. {passed} passed; 0 failed; 0 ignored; "
        "0 measured; 0 filtered out; finished in 0.01s\n"
    )


class LinuxX86FloorEvidenceTests(unittest.TestCase):
    def test_x86_minimums_are_source_bound_and_not_inherited_from_aarch64(self) -> None:
        self.assertEqual(GATE.HOST, "x86_64-unknown-linux-gnu")
        self.assertEqual(SHARED.HOST, GATE.HOST)
        self.assertEqual(SHARED.TARGET_MINIMUM_PASSES, PINNED_MINIMUMS)
        self.assertEqual(SHARED.minimum_problems(), [])
        for row, minimum in PINNED_MINIMUMS.items():
            with self.subTest(row=row):
                self.assertIn(row, GATE.TARGETS)
                self.assertEqual(SHARED.target_minimum_passes(*row), minimum)
                self.assertEqual(SHARED.classify_result(0, transcript(minimum), minimum)["status"], "pass")
                shrunk = SHARED.classify_result(0, transcript(minimum - 1), minimum)
                self.assertEqual(shrunk["status"], "fail")
                self.assertIn("below the required minimum", " ".join(shrunk["errors"]))

    def test_source_inventory_shrinkage_is_refused_before_cargo(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            tests = Path(temporary) / "crates" / "trust-cg-codegen" / "tests"
            tests.mkdir(parents=True)
            (tests / "e2e_x86_64_aggregate_abi.rs").write_text(
                "#[test]\nfn case() {}\n" * 17
            )
            problems = SHARED.minimum_problems(
                rows=(("trust-cg-codegen", "e2e_x86_64_aggregate_abi"),),
                root=Path(temporary), stale_entries=False,
            )
        self.assertTrue(any("minimum 18 exceeds its #[test] functions" in p for p in problems), problems)

    def test_failed_preflight_report_still_names_host_and_required_minima(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            output = Path(temporary) / "evidence"
            with mock.patch.object(SHARED, "preflight", side_effect=RuntimeError("controlled stop before Cargo")), \
                 contextlib.redirect_stdout(io.StringIO()), contextlib.redirect_stderr(io.StringIO()):
                status = GATE.main(["--out", str(output)])
            report = json.loads((output / "report.json").read_text())
        self.assertEqual(status, 1)
        self.assertEqual(report["status"], "fail")
        self.assertEqual(report["host"], GATE.HOST)
        self.assertEqual(report["schema"], SHARED.SCHEMA)
        self.assertEqual(len(report["required_target_minimum_passes"]), len(GATE.TARGETS))
        self.assertEqual(
            report["required_minimum_passes"],
            sum(report["required_target_minimum_passes"].values()),
        )
        for (package, target), minimum in PINNED_MINIMUMS.items():
            self.assertEqual(report["required_target_minimum_passes"][f"{package}/{target}"], minimum)
        self.assertEqual(report["targets"], [])
        # Even a run that never reached Cargo records the decided-absent rows.
        self.assertEqual(report["decided_absent"], SHARED.decided_absent_records())


class LinuxX86TargetInventoryTests(unittest.TestCase):
    def test_target_count_is_pinned_so_a_lane_cannot_leave_silently(self) -> None:
        self.assertEqual(len(GATE.TARGETS), REQUIRED_TARGET_COUNT)
        self.assertEqual(len(set(GATE.TARGETS)), len(GATE.TARGETS))
        self.assertIn(BRIDGE_LANE, GATE.TARGETS)
        self.assertEqual(
            [row for row in GATE.TARGETS if row[0] == SHARED.BRIDGE_PACKAGE], [BRIDGE_LANE]
        )
        for package, target in GATE.TARGETS:
            with self.subTest(target=f"{package}/{target}"):
                self.assertTrue((ROOT / "crates" / package / "tests" / f"{target}.rs").is_file())

    def test_bridge_lane_runs_in_the_bridge_workspace_under_the_pinned_package(self) -> None:
        trust = {"targo": "/pkg/bin/targo", "compiler": "/pkg/bin/trustc"}
        command, root, overrides = SHARED.target_command(
            *BRIDGE_LANE, trust_lane_provenance(ROOT_LANE, trust=trust), 4, False,
        )
        self.assertEqual(root, SHARED.BRIDGE_DIR)
        self.assertEqual(overrides, {"RUSTC": "/pkg/bin/trustc"})
        self.assertEqual(command[:6], [
            "/pkg/bin/targo", "--unverified", "test", "--release", "--locked", "--color",
        ])
        self.assertEqual(command[-7:], [
            "-j", "4", "--test", BRIDGE_LANE[1], "--", "--nocapture", "--test-threads=1",
        ])
        # The bridge is its own workspace: `-p` does not name it, and the root
        # workspace's build command is never the program.
        self.assertNotIn("-p", command)
        self.assertNotIn(ROOT_LANE[0], command)

    def test_bridge_lane_without_a_resolved_package_refuses_instead_of_using_path(self) -> None:
        with self.assertRaises(RuntimeError) as raised:
            SHARED.target_command(*BRIDGE_LANE, trust_lane_provenance(ROOT_LANE), 4, False)
        self.assertIn("no pinned Trust package was resolved", str(raised.exception))

    def test_bridge_lane_refuses_a_row_whose_environment_it_cannot_deliver(self) -> None:
        # `trustc` refuses TCG_* variables on the process and this runner does
        # not write the bridge workspace's target runner, so a TARGET_ENVIRONMENT
        # row on a bridge target must refuse rather than be dropped. No bridge
        # row declares one; the rule is asserted here so adding one cannot pass
        # silently.
        trust = {"targo": "/pkg/bin/targo", "compiler": "/pkg/bin/trustc"}
        with mock.patch.object(SHARED, "TARGET_ENVIRONMENT", {BRIDGE_LANE: {"TCG_REQUIRE_LLD": "1"}}):
            with self.assertRaises(RuntimeError) as raised:
                SHARED.target_command(*BRIDGE_LANE, trust_lane_provenance(ROOT_LANE, trust=trust), 4, False)
        self.assertIn("no TARGET_ENVIRONMENT delivery route", str(raised.exception))

    def test_bridge_lane_runs_without_the_checker_selections_trustc_refuses(self) -> None:
        self.assertEqual(
            SHARED.target_unset_environment(*BRIDGE_LANE), SHARED.RUNTIME_CHECKER_ENVIRONMENT,
        )

    def test_root_workspace_lane_is_unchanged_and_keeps_features_beside_its_target(self) -> None:
        row = ("trust-cg-codegen", "e2e_x86_64_aggregate_abi")
        command, root, overrides = SHARED.target_command(*row, trust_lane_provenance(ROOT_LANE), 2, True)
        self.assertEqual((root, overrides), (SHARED.ROOT, {}))
        self.assertEqual(command, [
            *ROOT_LANE, "test", "--locked", "--offline", "--color", "never", "-j", "2",
            "-p", row[0], "--test", row[1], "--", "--nocapture", "--test-threads=1",
        ])

    def test_set_environment_applies_after_the_unset_list(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            log = Path(temporary) / "probe.log"
            result = SHARED.run_target(
                [sys.executable, "-c", "import os; print(os.environ.get('TCG_PROBE_NAME', 'absent'))"],
                log, 60.0, unset_environment=("TCG_PROBE_NAME",),
                set_environment={"TCG_PROBE_NAME": "override"},
            )
            transcript_text = log.read_text()
        self.assertEqual(result["set_environment"], {"TCG_PROBE_NAME": "override"})
        self.assertEqual(result["cwd"], str(SHARED.ROOT))
        self.assertIn("override", transcript_text)


class DecidedAbsentTests(unittest.TestCase):
    def test_swiftcc_lane_is_required_under_xd03(self) -> None:
        # Ruling XD-03 (docs/decision-record.md, 2026-10-02): swiftcc is a
        # required Linux x86-64 convention, so its target is a TARGETS row and no
        # ruling holds any target out of this floor.
        self.assertIn(SWIFTCC, GATE.TARGETS)
        self.assertEqual(GATE.DECIDED_ABSENT, ())
        self.assertIn(("trust-cg-codegen", "e2e_x86_64_calling_conv"), GATE.TARGETS)
        self.assertTrue((ROOT / "crates" / SWIFTCC[0] / "tests" / f"{SWIFTCC[1]}.rs").is_file())
        self.assertEqual(SHARED.decided_absent_problems(), [])
        self.assertEqual(SHARED.DECIDED_ABSENT, GATE.DECIDED_ABSENT)

    def test_aarch64_floor_declares_no_decided_absent_target(self) -> None:
        self.assertEqual(load("check_linux_aarch64").DECIDED_ABSENT, ())

    def test_list_prints_decided_absent_rows_after_the_required_targets(self) -> None:
        out = io.StringIO()
        with contextlib.redirect_stdout(out):
            self.assertEqual(GATE.main(["--list"]), 0)
        lines = out.getvalue().splitlines()
        required = len(GATE.TARGETS)
        self.assertEqual(lines[:required], [f"{package} {target}" for package, target in GATE.TARGETS])
        self.assertEqual(
            lines[required:],
            [f"decided-absent {p} {t} ({d}): {r}" for p, t, d, r in GATE.DECIDED_ABSENT],
        )

    def test_overlap_and_missing_test_file_are_inventory_problems(self) -> None:
        rows = (("fixture", "first", "XD-99", "overlap"), ("fixture", "missing", "XD-98", "no file"))
        with mock.patch.object(SHARED, "TARGETS", (("fixture", "first"),)):
            with mock.patch.object(SHARED, "DECIDED_ABSENT", rows):
                problems = SHARED.decided_absent_problems()
                err = io.StringIO()
                with contextlib.redirect_stdout(io.StringIO()), contextlib.redirect_stderr(err):
                    self.assertEqual(GATE.main(["--list"]), 1)
        self.assertTrue(any("fixture/first (XD-99) is also a required target" in p for p in problems), problems)
        self.assertTrue(any("fixture/missing (XD-98) has no test file" in p for p in problems), problems)
        self.assertIn("is also a required target", err.getvalue())

    def run_with_fixture(self, temp: str, absent: tuple, problems: list[str]) -> tuple[int, dict, str, Path]:
        arguments = Path(temp) / "cargo-arguments"
        fixture = Path(temp) / "cargo-fixture"
        fixture.write_text(
            PYTHON_FIXTURE_HEADER +
            "import sys\n"
            f"open({str(arguments)!r}, 'a').write(' '.join(sys.argv[1:]) + '\\n')\n"
            f"print({transcript(1)!r})\n"
        )
        fixture.chmod(0o700)
        output = Path(temp) / "results"
        provenance = {
            "source_sha": "fixture-source", "dirty": True,
            "host": SHARED.HOST, "source_fingerprint": "fixture-fingerprint",
            **trust_lane_provenance([str(fixture)]),
            "tools": {"targo": str(fixture), "env": "/usr/bin/env", "git": "fixture-git"},
        }
        recorder = types.SimpleNamespace(
            offline_problems=lambda identity: [], identity_changes=lambda before, after: [],
        )
        stdout = io.StringIO()
        with contextlib.ExitStack() as stack:
            stack.enter_context(mock.patch.object(SHARED, "cargo_config_record", return_value=cargo_config_record()))
            stack.enter_context(mock.patch.object(SHARED, "selected_build_tool", return_value="/fixture/pkg/bin/targo"))
            stack.enter_context(mock.patch.object(SHARED, "TARGETS", (("fixture", "first"),)))
            stack.enter_context(mock.patch.object(SHARED, "DECIDED_ABSENT", absent))
            stack.enter_context(mock.patch.object(SHARED, "decided_absent_problems", return_value=problems))
            stack.enter_context(mock.patch.object(SHARED, "preflight", return_value=provenance))
            stack.enter_context(mock.patch.object(SHARED, "source_provenance", return_value=provenance))
            stack.enter_context(mock.patch.object(SHARED, "dependency_identity", return_value={}))
            stack.enter_context(mock.patch.object(SHARED, "dependency_recorder", return_value=recorder))
            stack.enter_context(mock.patch.object(SHARED, "proof_tool_identities", return_value={}))
            stack.enter_context(mock.patch.object(SHARED, "proof_tool_problems", return_value=[]))
            stack.enter_context(mock.patch.object(SHARED, "proof_tool_changes", return_value=[]))
            stack.enter_context(contextlib.redirect_stdout(stdout))
            stack.enter_context(contextlib.redirect_stderr(io.StringIO()))
            code = GATE.main(["--out", str(output), "--timeout-seconds", "60"])
        report = json.loads((output / "report.json").read_text())
        return code, report, stdout.getvalue(), arguments

    def test_run_records_and_prints_decided_absent_without_running_it(self) -> None:
        absent = (("fixture", "absent", "XD-99", "fixture reason"),)
        with tempfile.TemporaryDirectory() as temp:
            code, report, stdout, arguments = self.run_with_fixture(temp, absent, [])
            argv = arguments.read_text()
        self.assertEqual((code, report["status"]), (0, "pass"), report)
        self.assertEqual(
            report["decided_absent"],
            [{"package": "fixture", "target": "absent", "decision": "XD-99", "reason": "fixture reason"}],
        )
        self.assertEqual(report["required_targets"], [["fixture", "first"]])
        self.assertEqual([row["target"] for row in report["targets"]], ["first"])
        self.assertIn("--test first", argv)
        self.assertNotIn("absent", argv)
        self.assertEqual(
            stdout.count("decided absent, not run: fixture/absent (XD-99): fixture reason"), 2,
            stdout,
        )
        # No bridge row in this fixture inventory, so no Trust package is resolved.
        self.assertNotIn("trust_bridge", report["provenance"])
        self.assertIsNone(report["controls"]["trust_driver"])

    def test_inventory_problems_refuse_the_run_before_any_target(self) -> None:
        absent = (("fixture", "first", "XD-99", "overlap"),)
        with tempfile.TemporaryDirectory() as temp:
            code, report, _stdout, arguments = self.run_with_fixture(
                temp, absent, ["decided-absent target fixture/first (XD-99) is also a required target"],
            )
            ran = arguments.exists()
        self.assertEqual((code, report["status"]), (1, "fail"), report)
        self.assertEqual(report["targets"], [])
        self.assertFalse(ran)
        self.assertIn("decided-absent target fixture/first (XD-99) is also a required target", report["errors"])


if __name__ == "__main__":
    unittest.main()
