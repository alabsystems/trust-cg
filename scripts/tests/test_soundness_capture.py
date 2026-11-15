"""Exercise the actual soundness Cargo wrapper and Clean proof legs with controlled output."""

import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest


ROOT = Path(__file__).resolve().parents[2]
SOURCE = (ROOT / "scripts/soundness_check.sh").read_text()
# The production functions start every python3 by the gate's pinned
# interpreter (OD-XHOST-GATE-CWD-20261025, repair round 3), which the gate
# exports before any of them runs; the harness gives them this one.
GATE_ENVIRONMENT = dict(os.environ, SOUNDNESS_PYTHON3=os.path.realpath(sys.executable))
CARGO_GATE = "run_cargo_gate() {" + SOURCE.split("run_cargo_gate() {", 1)[1].split(
    "\nrun_trust_cg_cargo_gates() {", 1
)[0]


def between(start, end):
    """The production source from `start` up to (not including) `end`, exactly once."""
    assert SOURCE.count(start) == 1, start
    body = SOURCE.split(start, 1)[1]
    assert end in body, end
    return start + body.split(end, 1)[0]


def bash_array(name):
    text = between(f"{name}=(", ")\n") + ")\n"
    stems = [line.strip() for line in text.splitlines()[1:-1] if line.strip()]
    return text, stems


PROOF_INVENTORY = between(
    "check_trust_cg_proof_inventory() {", "\nrun_trust_cg_clean_check() {"
)
TRUST_CG_CLEAN_CHECK = between("run_trust_cg_clean_check() {", "\nrun_lean_formal_gate() {")
CLEAN_SUMMARY_VALIDATOR = between(
    "validate_clean_check_summary() {", '\nif [ -n "$MODE_VALIDATE_CLEAN_SUMMARY" ]'
)
# The Clean checkout's proof section through the repository-proof section: the
# rebuild decision that gates both is executed as production code below.
CLEAN_PROOF_SECTIONS = between(
    'section "Clean checkout: clean-check (B-def', '\n  section "Clean checkout: kernel diversity gate"'
)
# The production summary: finish_run is the only exit of a constellation run.
SUMMARY = between("# Summary. finish_run", "# End of summary.")
CLEAN_LEAN_ARRAY, CLEAN_LEAN_STEMS = bash_array("CLEAN_LEAN")
TRUST_CG_LEAN_ARRAY, TRUST_CG_LEAN_STEMS = bash_array("TRUST_CG_LEAN")
# run_cargo_gate reads the release-mode set under `set -u`, so the extracted
# function needs the production array beside it.
RELEASE_GATES_ARRAY, RELEASE_GATES = bash_array("TRUST_CG_RELEASE_INCLUDE_IGNORED_GATES")


def clean_summary(declarations, failed=0):
    return (
        f"Checked {declarations} declarations\n"
        f"{declarations - failed} passed, {failed} failed\n"
    )


def transcript(*, output="", ignored=0, filtered=0, failed=False):
    outcome = "FAILED" if failed else "ok"
    text = f"running {1 + ignored} tests\ntest witness ... {outcome}\n"
    if ignored:
        text += "test deferred ... ignored\n"
    if output:
        text += f"---- witness stdout ----\n{output}\n"
    text += (
        f"test result: {outcome}. {int(not failed)} passed; {int(failed)} failed; "
        f"{ignored} ignored; 0 measured; {filtered} filtered out; finished in 0.01s\n"
    )
    return text


class SoundnessCaptureTests(unittest.TestCase):
    def run_gate(self, text, *, code=0, lane="repo", nocapture="0",
                 package="test-package", target="witness", selector="integration"):
        with tempfile.TemporaryDirectory() as temporary:
            directory = Path(temporary)
            log = directory / "fixture.log"
            args = directory / "args.log"
            log.write_text(text)
            # Only the workload is stubbed. Dispatch, capture flags, result
            # validation and PASS/FAIL decisions are the production function.
            program = r'''
set -u
run_bounded() {
    printf '%s\n' "$@" > "$ARGS_LOG"
    cat "$TRANSCRIPT"
    return "$FAKE_RC"
}
run_clean_cargo_bounded() { run_bounded "$@"; }
TRUST_CARGO="$TRUST_CG_DIR/scripts/trust_cargo.sh"
record() { printf '%s|%s|%s\n' "$1" "$2" "$3"; }
leg_class_runs_here() { [ "$1" = host-independent ]; }
''' + RELEASE_GATES_ARRAY + CARGO_GATE + '\nrun_cargo_gate "$TRUST_CG_DIR" "$PACKAGE" "$TARGET" "$LANE" "$SELECTOR"\n'
            result = subprocess.run(
                ["bash", "-c", program], text=True, capture_output=True, timeout=30,
                env=dict(GATE_ENVIRONMENT, TRUST_CG_DIR=str(ROOT), LOGDIR=str(directory),
                         TRANSCRIPT=str(log), ARGS_LOG=str(args), FAKE_RC=str(code),
                         PACKAGE=package, TARGET=target,
                         LANE=lane, SELECTOR=selector, RUST_TEST_NOCAPTURE=nocapture,
                         SOUNDNESS_COMMAND_TIMEOUT_SECONDS="30"),
            )
            return result, args.read_text().splitlines()

    def test_both_cargo_lanes_request_successful_test_capture(self):
        for lane in ("repo", "clean"):
            with self.subTest(lane=lane):
                result, args = self.run_gate(transcript(), lane=lane)
                self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
                self.assertIn("|PASS|", result.stdout)
                self.assertEqual(args[-2:], ["--", "--show-output"])

    def test_explicit_library_filter_keeps_capture_and_nonvacuity_guards(self):
        result, args = self.run_gate(transcript(filtered=7), selector="lib")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn("--lib", args)
        self.assertIn("--show-output", args)
        self.assertIn("--test-threads=1", args)
        for text in ("", transcript(filtered=7, output="SKIP: missing checker")):
            result, _ = self.run_gate(text, selector="lib")
            self.assertNotEqual(result.returncode, 0, result.stdout)

    def test_x86_aot_routing_controls_are_canonical_legs(self):
        result = subprocess.run(
            ["bash", str(ROOT / "scripts/soundness_check.sh"), "--list-json"],
            text=True, capture_output=True, timeout=30,
        )
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        legs = json.loads(result.stdout)["legs"]
        for leg_id in (
            "trust-cg-verify --lib x86_source_bound_body::tests::slice16::",
            "trust-cg-codegen --test x86_source_bound_body",
        ):
            with self.subTest(leg=leg_id):
                self.assertEqual(
                    [leg for leg in legs if leg["id"] == leg_id],
                    [{"id": leg_id, "class": "host-independent"}],
                )

    def test_x86_aot_whole_target_refuses_filtered_or_skipped_execution(self):
        for text, succeeds in (
            (transcript(), True),
            (transcript(filtered=3), False),
            (transcript(output="SKIP: replay tools unavailable"), False),
        ):
            with self.subTest(transcript=text):
                result, args = self.run_gate(
                    text, package="trust-cg-codegen", target="x86_source_bound_body"
                )
                self.assertEqual(result.returncode == 0, succeeds, result.stdout + result.stderr)
                self.assertEqual(args[args.index("--test") + 1], "x86_source_bound_body")
                self.assertIn("--show-output", args)

    def test_runtime_skip_cannot_be_credited_as_a_pass(self):
        result, _ = self.run_gate(transcript(output="SKIP: required oracle unavailable"))
        self.assertNotEqual(result.returncode, 0, result.stdout)
        self.assertIn("|FAIL|", result.stdout)

    def test_formal_campaign_opt_out_cannot_be_credited_as_a_pass(self):
        result, _ = self.run_gate(transcript(output=(
            "witness: external-solver campaign not requested; "
            "set TRUST_CG_RUN_FORMAL_PROOF_TESTS=1 to run"
        )))
        self.assertNotEqual(result.returncode, 0, result.stdout)
        self.assertIn("|FAIL|", result.stdout)
        self.assertIn("1 runtime SKIPs", result.stdout)

    def test_encoding_gate_executes_its_full_domain_control_in_release(self):
        self.assertIn("wasm_encoding_gate", RELEASE_GATES)
        result, args = self.run_gate(
            transcript(), package="trust-cg-verify", target="wasm_encoding_gate"
        )
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn("--release", args[:args.index("--")])
        self.assertIn("--include-ignored", args[args.index("--") + 1:])

    def test_x86_native_gate_is_not_run_where_that_class_does_not_run(self):
        with tempfile.TemporaryDirectory() as temporary:
            directory = Path(temporary)
            args = directory / "args.log"
            program = r'''
set -u
run_bounded() { printf '%s\n' "$@" > "$ARGS_LOG"; }
record() { printf '%s|%s|%s\n' "$1" "$2" "$3"; }
leg_class_runs_here() { [ "$1" = host-independent ]; }
''' + CARGO_GATE + '\nrun_cargo_gate "$TRUST_CG_DIR" trust-cg-codegen e2e_x86_64_swiftcc repo integration x86_64-native\n'
            result = subprocess.run(
                ["bash", "-c", program], text=True, capture_output=True, timeout=30,
                env=dict(GATE_ENVIRONMENT, TRUST_CG_DIR=str(ROOT), LOGDIR=str(directory), ARGS_LOG=str(args)),
            )
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertEqual(result.stdout, "")
            self.assertFalse(args.exists())

    def test_package_qualified_leg_names_keep_two_targets_apart(self):
        result, _ = self.run_gate(transcript(), package="trust-cg-cli", target="must_refuse_corpus")
        self.assertIn("trust-cg-cli --test must_refuse_corpus|PASS|", result.stdout)
        result, _ = self.run_gate(transcript(), package="trust-cg-verify", target="witness")
        self.assertIn("witness|PASS|", result.stdout.splitlines()[0])

    def test_ignored_case_cannot_hide_beside_a_passing_case(self):
        result, _ = self.run_gate(transcript(ignored=1))
        self.assertNotEqual(result.returncode, 0, result.stdout)

    def test_filtered_cases_make_a_named_gate_incomplete(self):
        result, _ = self.run_gate(transcript(filtered=1))
        self.assertNotEqual(result.returncode, 0, result.stdout)

    def test_rollup_without_named_results_is_not_evidence(self):
        result, _ = self.run_gate(
            "test result: ok. 12 passed; 0 failed; 0 ignored; 0 measured; 0 filtered out;\n"
        )
        self.assertNotEqual(result.returncode, 0, result.stdout)

    def test_later_rollup_cannot_hide_an_incomplete_suite(self):
        result, _ = self.run_gate("running 1 test\ntest lost ... ok\n" + transcript())
        self.assertNotEqual(result.returncode, 0, result.stdout)

    def test_test_failure_is_not_mislabeled_as_a_compile_error(self):
        result, _ = self.run_gate(
            transcript(failed=True) + "error: test failed, to rerun pass --test witness\n",
            code=101,
        )
        self.assertNotEqual(result.returncode, 0, result.stdout)
        self.assertNotIn("BUILD/COMPILE ERROR", result.stdout)

    def test_nonzero_exit_cannot_be_hidden_by_a_passing_suite(self):
        result, _ = self.run_gate(transcript(), code=101)
        self.assertNotEqual(result.returncode, 0, result.stdout)

    def test_nocapture_environment_cannot_claim_captured_evidence(self):
        result, _ = self.run_gate(transcript(), nocapture="1")
        self.assertNotEqual(result.returncode, 0, result.stdout)

    def test_timeout_and_empty_output_fail_closed(self):
        for code in (0, 124):
            with self.subTest(code=code):
                result, _ = self.run_gate("", code=code)
                self.assertNotEqual(result.returncode, 0, result.stdout)


class SoundnessCompletionTests(unittest.TestCase):
    def test_skipped_constellation_cannot_be_green_or_attested(self):
        for failures, skips, expected in ((0, 0, 0), (1, 0, 1), (0, 1, 1)):
            with self.subTest(failures=failures, skips=skips):
                program = ("set -u\nsection() { :; }\nhr() { :; }\n" + SUMMARY
                           + '\nFAIL_COUNT="$F" SKIP_COUNT="$S" PASS_COUNT=1\nfinish_run\n')
                result = subprocess.run(
                    ["bash", "-c", program],
                    text=True, capture_output=True, timeout=10,
                    env=dict(GATE_ENVIRONMENT, F=str(failures), S=str(skips), MODE_ATTEST="1",
                             MODE_PREFLIGHT_ONLY="0", RUN_SCOPE="full",
                             ATTESTATION_TOOL="/nonexistent/attestation-tool", TRUST_CG_DIR=str(ROOT),
                             CLEAN_BIN="/nonexistent/clean", RUN_STARTED_AT="fixture",
                             C_GRN="", C_BLD="", C_RST="", C_RED="", C_YEL="",
                             LOGDIR="controlled-log-directory"),
                )
                # A green run reaches the attestation writer (absent here, so it
                # fails closed); a failing or skipping one never does.
                self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
                if skips or failures:
                    self.assertNotIn("ALL SOUNDNESS GATES GREEN", result.stdout)
                    self.assertIn("no attestation record", result.stdout)
                else:
                    self.assertIn("ALL SOUNDNESS GATES GREEN", result.stdout)
                    self.assertIn("refusing to write an attestation record", result.stdout)

    def test_wasm_only_lane_cannot_pass_with_missing_required_tables(self):
        decision = 'if [ "$MODE_RUN_WASM_ORACLES" -eq 1 ]; then' + SOURCE.split(
            'if [ "$MODE_RUN_WASM_ORACLES" -eq 1 ]; then', 1
        )[1].split(
            "# ----------------------------------------------------------------------------\n# Banner + preflight.", 1
        )[0]
        program = r'''
set -u
section() { :; }
hr() { :; }
run_wasm_oracle_gate() { :; }
run_island_gates() { :; }
''' + decision
        result = subprocess.run(
            ["bash", "-c", program], text=True, capture_output=True, timeout=10,
            env=dict(GATE_ENVIRONMENT, MODE_RUN_WASM_ORACLES="1", WASM_CFG_FUZZ_FUNCS="200",
                     PASS_COUNT="8", FAIL_COUNT="0", SKIP_COUNT="1", C_YEL="", C_RST=""),
        )
        self.assertEqual(result.returncode, 1, result.stdout + result.stderr)


class TrustCgProofCleanCheckTests(unittest.TestCase):
    """The repository's own proofs/*.lean are gated by the production leg."""

    # Stubs shared by every fixture: only the workload and output are replaced.
    # Dispatch, file/checker preconditions, summary validation and every
    # PASS/FAIL/SKIP decision are the production functions extracted above.
    PRELUDE = r"""
set -u
record() { printf '%s|%s|%s\n' "$1" "$2" "$3"; }
# A census run's proof tree: the checkout itself (an --attest run's private
# export is held by test_private_cache.py's gate cases).
CANDIDATE_PROOF_DIR="$TRUST_CG_DIR"
CANDIDATE_PROOF_SOURCE="the working tree"
CANDIDATE_PROOF_REFUSAL=""
export_candidate_proofs() { return 0; }
run_bounded() {
    printf '%s\n' "$@" >> "$ARGS_LOG"
    cat "$TRANSCRIPT"
    return "$FAKE_RC"
}
"""

    @staticmethod
    def make_checker(directory, present):
        clean_bin = directory / "clean"
        if present:
            # Never executed: run_bounded is the stubbed workload.
            clean_bin.write_text("#!/bin/sh\nexit 97\n")
            clean_bin.chmod(0o755)
        return clean_bin

    def run_bash(self, program, directory, *, clean_bin, transcript="", code=0,
                 trust_cg_dir=ROOT, **extra):
        args = directory / "args.log"
        log = directory / "fixture.log"
        log.write_text(transcript)
        result = subprocess.run(
            ["bash", "-c", program], text=True, capture_output=True, timeout=30,
            env=dict(GATE_ENVIRONMENT, TRUST_CG_DIR=str(trust_cg_dir), LOGDIR=str(directory),
                     CLEAN_BIN=str(clean_bin), TRANSCRIPT=str(log), ARGS_LOG=str(args),
                     FAKE_RC=str(code), SOUNDNESS_COMMAND_TIMEOUT_SECONDS="30", **extra),
        )
        invoked = args.read_text().splitlines() if args.exists() else None
        return result, invoked

    def run_leg(self, transcript, *, code=0, stem="abi_clobber_spec", checker=True):
        with tempfile.TemporaryDirectory() as temporary:
            directory = Path(temporary)
            clean_bin = self.make_checker(directory, checker)
            program = (self.PRELUDE + CLEAN_SUMMARY_VALIDATOR + "\n" + TRUST_CG_CLEAN_CHECK
                       + '\nrun_trust_cg_clean_check "$STEM"\n')
            result, invoked = self.run_bash(program, directory, clean_bin=clean_bin,
                                            transcript=transcript, code=code, STEM=stem)
            return result, invoked, clean_bin

    def run_inventory(self, stems_on_disk=None):
        """Run the production inventory leg; `None` inspects this checkout."""
        with tempfile.TemporaryDirectory() as temporary:
            directory = Path(temporary)
            checkout = ROOT
            if stems_on_disk is not None:
                checkout = directory / "checkout"
                (checkout / "proofs").mkdir(parents=True)
                for stem in stems_on_disk:
                    (checkout / "proofs" / f"{stem}.lean").write_text("-- fixture\n")
            program = (self.PRELUDE + TRUST_CG_LEAN_ARRAY + PROOF_INVENTORY
                       + "\ncheck_trust_cg_proof_inventory\n")
            result, _ = self.run_bash(program, directory, clean_bin=directory / "clean",
                                      trust_cg_dir=checkout)
            return result

    def run_sections(self, *, build_ok, checker, transcript=""):
        """Run the production Clean and repository-proof sections end to end."""
        with tempfile.TemporaryDirectory() as temporary:
            directory = Path(temporary)
            clean_bin = self.make_checker(directory, checker)
            program = self.PRELUDE + r"""
section() { :; }
poll_remote_dispatch() { :; }
build_clean_binary() { [ "$FAKE_BUILD_OK" = 1 ]; }
run_clean_check() { printf 'sibling %s\n' "$1"; }
""" + CLEAN_LEAN_ARRAY + TRUST_CG_LEAN_ARRAY + CLEAN_SUMMARY_VALIDATOR + "\n" \
                + PROOF_INVENTORY + "\n" + TRUST_CG_CLEAN_CHECK + "\n" + CLEAN_PROOF_SECTIONS + "\n"
            return self.run_bash(program, directory, clean_bin=clean_bin,
                                 transcript=transcript,
                                 FAKE_BUILD_OK="1" if build_ok else "0")

    @staticmethod
    def rows(result, status):
        prefix = "clean-check trust-cg proofs/"
        return sorted(
            line.split("|", 1)[0][len(prefix):] for line in result.stdout.splitlines()
            if line.startswith(prefix) and line.split("|")[1] == status
        )

    def test_inventory_is_exactly_the_repository_proof_files(self):
        on_disk = sorted(path.stem for path in (ROOT / "proofs").glob("*.lean"))
        self.assertTrue(on_disk, "proofs/ must hold the Clean specs this leg gates")
        self.assertEqual(sorted(TRUST_CG_LEAN_STEMS), on_disk)
        self.assertEqual(len(TRUST_CG_LEAN_STEMS), len(set(TRUST_CG_LEAN_STEMS)))
        for stem in ("abi_clobber_spec", "sentinel_decide_spec", "mir_place_resolution_spec"):
            self.assertIn(stem, TRUST_CG_LEAN_STEMS)

    def test_runtime_inventory_passes_on_this_checkout(self):
        result = self.run_inventory()
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn("|PASS|", result.stdout)

    def test_runtime_inventory_accepts_exactly_the_listed_files(self):
        result = self.run_inventory(TRUST_CG_LEAN_STEMS)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn("|PASS|", result.stdout)

    def test_runtime_inventory_fails_closed_on_an_unlisted_proof_file(self):
        result = self.run_inventory(TRUST_CG_LEAN_STEMS + ["new_unwired_spec"])
        self.assertNotEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn("|FAIL|", result.stdout)
        self.assertIn("new_unwired_spec", result.stdout)
        self.assertNotIn("|PASS|", result.stdout)

    def test_list_mode_names_the_leg_and_every_repository_proof(self):
        result = subprocess.run(
            ["bash", str(ROOT / "scripts/soundness_check.sh"), "--list"],
            text=True, capture_output=True, timeout=30,
        )
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        lines = result.stdout.splitlines()
        heading = [
            index for index, line in enumerate(lines)
            if line.startswith("trust-cg checkout: clean-check repository proofs")
        ]
        self.assertEqual(len(heading), 1, result.stdout)
        listed = []
        for line in lines[heading[0] + 1:]:
            if line.startswith("  - "):
                listed.append(line[4:])
            elif listed:
                break
        self.assertEqual(listed, TRUST_CG_LEAN_STEMS)

    def test_checked_proof_with_coherent_summary_passes(self):
        result, invoked, clean_bin = self.run_leg(clean_summary(42))
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn("|PASS|", result.stdout)
        self.assertEqual(
            invoked,
            [str(ROOT), str(clean_bin), "check", str(ROOT / "proofs/abi_clobber_spec.lean")],
        )

    def test_every_listed_proof_is_checked_from_its_repository_path(self):
        for stem in TRUST_CG_LEAN_STEMS:
            with self.subTest(stem=stem):
                result, invoked, _ = self.run_leg(clean_summary(3), stem=stem)
                self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
                self.assertEqual(invoked[-1], str(ROOT / "proofs" / f"{stem}.lean"))

    def test_absent_checker_is_a_loud_skip_never_a_pass(self):
        result, invoked, _ = self.run_leg(clean_summary(42), checker=False)
        self.assertNotEqual(result.returncode, 0, result.stdout)
        self.assertIn("|SKIP|", result.stdout)
        self.assertNotIn("|PASS|", result.stdout)
        self.assertIsNone(invoked)

    def test_missing_proof_source_fails_before_the_checker_is_consulted(self):
        for checker in (True, False):
            with self.subTest(checker=checker):
                result, invoked, _ = self.run_leg(
                    clean_summary(42), stem="no_such_spec", checker=checker
                )
                self.assertNotEqual(result.returncode, 0, result.stdout)
                self.assertIn("|FAIL|", result.stdout)
                self.assertIn("missing .lean file", result.stdout)
                self.assertNotIn("|SKIP|", result.stdout)
                self.assertIsNone(invoked)

    def test_rejected_proof_fails_closed(self):
        result, _, _ = self.run_leg(clean_summary(42, failed=1), code=1)
        self.assertNotEqual(result.returncode, 0, result.stdout)
        self.assertIn("|FAIL|", result.stdout)
        self.assertIn("41 passed, 1 failed", result.stdout)

    def test_success_status_with_incoherent_summary_is_not_evidence(self):
        for transcript in (
            "",
            clean_summary(42, failed=1),
            "Checked 0 declarations\n0 passed, 0 failed\n",
            "Checked 42 declarations\n",
            clean_summary(3) + clean_summary(3),
        ):
            with self.subTest(transcript=transcript):
                result, _, _ = self.run_leg(transcript, code=0)
                self.assertNotEqual(result.returncode, 0, result.stdout)
                self.assertIn("|FAIL|", result.stdout)
                self.assertNotIn("|PASS|", result.stdout)

    def test_timeout_fails_closed(self):
        result, _, _ = self.run_leg("", code=124)
        self.assertNotEqual(result.returncode, 0, result.stdout)
        self.assertIn("|FAIL|", result.stdout)
        self.assertIn("TIMEOUT", result.stdout)

    def test_rebuilt_checker_checks_every_repository_proof(self):
        result, invoked = self.run_sections(
            build_ok=True, checker=True, transcript=clean_summary(5)
        )
        self.assertEqual(result.stderr, "")
        self.assertEqual(self.rows(result, "PASS"), sorted(TRUST_CG_LEAN_STEMS), result.stdout)
        self.assertEqual(self.rows(result, "FAIL") + self.rows(result, "SKIP"), [])
        self.assertIn("trust-cg proofs/*.lean inventory|PASS|", result.stdout)
        checked = [line for line in invoked if line.endswith(".lean")]
        self.assertEqual(
            checked, [str(ROOT / "proofs" / f"{stem}.lean") for stem in TRUST_CG_LEAN_STEMS]
        )
        for stem in CLEAN_LEAN_STEMS:
            self.assertIn(f"sibling {stem}\n", result.stdout)

    def test_failed_clean_rebuild_blocks_the_repository_proofs(self):
        # A stale binary left behind by a failed rebuild must not check them.
        result, invoked = self.run_sections(
            build_ok=False, checker=True, transcript=clean_summary(5)
        )
        self.assertIsNone(invoked)
        self.assertEqual(self.rows(result, "FAIL"), sorted(TRUST_CG_LEAN_STEMS), result.stdout)
        self.assertEqual(self.rows(result, "PASS") + self.rows(result, "SKIP"), [])
        self.assertEqual(result.stdout.count("|FAIL|BLOCKED"),
                         len(TRUST_CG_LEAN_STEMS) + len(CLEAN_LEAN_STEMS))

    def test_absent_checker_after_failed_build_skips_every_repository_proof(self):
        result, invoked = self.run_sections(
            build_ok=False, checker=False, transcript=clean_summary(5)
        )
        self.assertIsNone(invoked)
        self.assertEqual(self.rows(result, "SKIP"), sorted(TRUST_CG_LEAN_STEMS), result.stdout)
        self.assertEqual(self.rows(result, "PASS"), [])
        # The inventory leg needs no checker and still runs.
        self.assertIn("trust-cg proofs/*.lean inventory|PASS|", result.stdout)


if __name__ == "__main__":
    unittest.main()
