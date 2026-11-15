"""Gate tests for the Darwin downstream-consumer lane (scripts/check_darwin_consumers.py, L13-P8).

Every test here is offline: the classifiers are fed literal transcripts and
documents, and the source and pin logic runs against throwaway Git
repositories under a temporary directory that is removed afterwards.
"""

from __future__ import annotations

import contextlib
import importlib.util
import io
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import tempfile
from types import SimpleNamespace
import unittest
from unittest import mock


ROOT = Path(__file__).resolve().parents[2]
SCRIPT = ROOT / "scripts" / "check_darwin_consumers.py"
SPEC = importlib.util.spec_from_file_location("_test_check_darwin_consumers", SCRIPT)
assert SPEC is not None and SPEC.loader is not None
LANE = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = LANE
SPEC.loader.exec_module(LANE)

TRUST_IR_OLD = "1" * 40
TRUST_IR_NEW = "2" * 40
CLEAN_OLD = "3" * 40
CLEAN_NEW = "4" * 40
COHORT = {"trust_ir_rev": TRUST_IR_NEW, "clean_rev": CLEAN_NEW}


def lock_text(packages) -> str:
    blocks = ["version = 4\n"]
    for name, version, source in packages:
        block = f'[[package]]\nname = "{name}"\nversion = "{version}"\n'
        if source:
            block += f'source = "{source}"\n'
        blocks.append(block)
    return "\n".join(blocks)


def git_source(url: str, rev: str) -> str:
    return f"git+{url}?rev={rev}#{rev}"


def transcript(passed=(), failed=(), ignored=(), filtered=0, outputs=None, extra=()) -> str:
    """A libtest --show-output transcript with named results and captured sections."""
    outputs = outputs or {}
    lines = [f"running {len(passed) + len(failed) + len(ignored)} tests"]
    lines += [f"test {name} ... ok" for name in passed]
    lines += [f"test {name} ... FAILED" for name in failed]
    lines += [f"test {name} ... ignored" for name in ignored]
    lines += ["", "successes:", ""]
    for name in passed:
        if name in outputs:
            lines += [f"---- {name} stdout ----", outputs[name], ""]
    lines += ["", "successes:", *[f"    {name}" for name in passed], ""]
    if failed:
        lines += ["failures:", ""]
        for name in failed:
            lines += [f"---- {name} stdout ----", outputs.get(name, "assertion failed"), ""]
        lines += ["", "failures:", *[f"    {name}" for name in failed], ""]
    lines += list(extra)
    state = "FAILED" if failed else "ok"
    lines.append(f"test result: {state}. {len(passed)} passed; {len(failed)} failed; {len(ignored)} ignored; "
                 f"0 measured; {filtered} filtered out; finished in 0.01s")
    return "\n".join(lines) + "\n"


def classify(text, returncode=0, *, minimum=1, known=None, ignored=frozenset(), filtered=frozenset(),
             broad=False):
    return LANE.classify_consumer_target("t", returncode, text, minimum=minimum, known=known or {},
                                         ignored=ignored, substitutions=COHORT, filtered=filtered,
                                         broad_skips=broad)


def workload_document(*, status="ok", code=None, states=5, transitions=5,
                      tier="trust-cg native-fused (compiled BFS)", route="compiled_bfs_fused", accepted=5):
    """A `ty check --output json` result document."""
    return {
        "result": {"status": status, "error_type": "invariant_violation" if code else None, "error_code": code,
                   "violated_property": {"name": "Inv", "type": "invariant"} if code else None},
        "statistics": {"states_found": states, "states_distinct": states, "states_initial": 1,
                       "transitions": transitions},
        "engine_provenance": {"tier": tier, "successor_authority": {
            "primary": route, "routes": {route: {"accepted_results": accepted}}}},
    }


def git(*arguments, cwd=None):
    environment = {**os.environ, "GIT_AUTHOR_NAME": "t", "GIT_AUTHOR_EMAIL": "t@example.invalid",
                   "GIT_COMMITTER_NAME": "t", "GIT_COMMITTER_EMAIL": "t@example.invalid"}
    return subprocess.run(["git", *arguments], cwd=cwd, check=True, capture_output=True, text=True,
                          env=environment).stdout.strip()


class InventoryTests(unittest.TestCase):
    def shard_targets(self, shard: str) -> set[str]:
        text = (ROOT / "scripts" / "run_full_test_matrix.sh").read_text()
        row = next(line for line in text.splitlines() if line.startswith(f"trust-cg-codegen|{shard}|"))
        return set(re.findall(r"--test ([A-Za-z0-9_]+)", row))

    def test_every_contract_target_exists_and_its_listed_names_are_real_tests(self):
        for row in LANE.CG_CONTRACT_TARGETS:
            with self.subTest(target=row.target):
                path = ROOT / "crates" / row.package / "tests" / f"{row.target}.rs"
                self.assertTrue(path.is_file(), path)
                source = path.read_text()
                for name, reason in row.filtered + tuple((n, f.reason) for n, f in row.known_failures):
                    self.assertRegex(source, rf"\bfn {re.escape(name)}\(")
                    self.assertTrue(reason)
                self.assertGreaterEqual(row.minimum, 0)
                if row.minimum == 0:
                    self.assertTrue(row.known_failures, "a zero minimum needs its failures listed")
                for _, failure in row.known_failures:
                    # Every CG-side listed failure is trust-cg's own, so it is a
                    # residual with a declared class of its own.
                    self.assertTrue(failure.residual, failure)
                    self.assertIn(failure.klass, LANE.FAILURE_CLASSES)
                    self.assertNotEqual(failure.klass, "cg-contract-failed")

    def test_the_matrix_ty_and_ay_contract_shards_are_inside_the_lane(self):
        lane = {row.target for row in LANE.CG_CONTRACT_TARGETS}
        self.assertLessEqual(self.shard_targets("integration-ty"), lane)
        # x86_64_sysv_ay_abi checks the x86-64 SysV ABI only.
        self.assertLessEqual(self.shard_targets("integration-ay-contracts") - {"x86_64_sysv_ay_abi"}, lane)
        self.assertIn("o3_ty_materialized_return", lane)
        # ty_bfs_minimal is required by the Darwin floor and runs there.
        floor = (ROOT / "scripts" / "check_darwin_aarch64.py").read_text()
        self.assertIn('("trust-cg-codegen", "ty_bfs_minimal", 9)', floor)
        self.assertNotIn("ty_bfs_minimal", lane)

    def test_the_ty_pin_and_inventory_are_exact(self):
        self.assertRegex(LANE.TY.commit, r"^[0-9a-f]{40}$")
        self.assertTrue(LANE.TY.url.startswith("https://"))
        self.assertIn("reports", LANE.TY.export_exclude)
        self.assertFalse(set(LANE.TY_TARGETS) & set(LANE.TY_COMPILED_OUT))
        for (target, name), failure in LANE.TY_KNOWN_FAILURES.items():
            self.assertIn(target, LANE.TY_TARGETS)
            self.assertTrue(failure.klass and failure.reason and failure.output, name)
            self.assertFalse(failure.residual, "TY's listed failures are TY's own")
        for target, rows in LANE.TY_FILTERED.items():
            self.assertIn(target, LANE.TY_TARGETS)
            for name, reason in rows:
                self.assertTrue(name and reason)
                self.assertNotIn((target, name), LANE.TY_KNOWN_FAILURES)
        self.assertIn("compile::tests::test_linked_trust_ir_probe_publication_allocation_from_env",
                      dict(LANE.TY_FILTERED["lib"]))
        self.assertIn("child_tla_ops_malformed_handle_abort_entry",
                      dict(LANE.TY_FILTERED["tla_ops_ffi_abort_subprocess"]))
        self.assertFalse(set(LANE.TY_LANE_TARGETS) & (set(LANE.TY_TARGETS) | set(LANE.TY_COMPILED_OUT)))
        for target, (path, minimum) in LANE.TY_LANE_TARGETS.items():
            source = path.read_text()
            self.assertTrue(path.is_relative_to(ROOT / "scripts"), path)
            self.assertIn('#![cfg(feature = "native")]', source)
            self.assertEqual(len(re.findall(r"^#\[test\]$", source, flags=re.MULTILINE)), minimum)
        # The lane-owned PowInt target checks TY's 0^0 TypeMismatch and every
        # assertion TY's own test never reaches.
        pow_source = LANE.TY_LANE_TARGETS["trust_cg_lane_pow_int_semantics"][0].read_text()
        for needle in ('"zero to the zero power"', "i64::MIN", "max_exponent + 1", "ArithmeticOverflow",
                       "JitRuntimeErrorKind::TypeMismatch"):
            self.assertIn(needle, pow_source)
        self.assertIn(LANE.TY_REPLAY_TEST, LANE.TY_IGNORED["lib"])
        for row in LANE.TY_WORKLOADS:
            spec, cfg, status, code, states, transitions = row
            self.assertIn(status, ("ok", "error"))
            self.assertEqual(code is None, status == "ok")
            self.assertGreater(states, 0)
        self.assertEqual(LANE.ABI_SEEDS, (1, 40))
        self.assertEqual(LANE.ABI_OPT_LEVELS, ("0", "1", "2", "3"))

    def test_every_named_class_is_declared(self):
        source = SCRIPT.read_text()
        used = set(re.findall(r'LaneError\(\s*"([a-z-]+)"', source))
        used |= set(re.findall(r'classes\.add\("([a-z-]+)"\)', source))
        used |= set(re.findall(r'regression_class="([a-z-]+)"', source))
        self.assertTrue(used)
        self.assertLessEqual(used, set(LANE.FAILURE_CLASSES))

    def test_the_absent_consumers_are_named_never_counted(self):
        self.assertEqual(LANE.ABSENT_CONSUMERS["aterm"]["status"], "absent")
        self.assertEqual(LANE.ABSENT_CONSUMERS["ay"]["status"], "not-in-lane")
        self.assertNotIn("aterm", LANE.STEPS)
        self.assertLessEqual({"tla-check", "tla-cli", "tla-model-native", "tla-model-normalizer", "tla-petri",
                              "tla-shape-ops"}, set(LANE.TY_CRATES_NOT_IN_LANE))

    def test_list_prints_the_plan_without_probing(self):
        stream = io.StringIO()
        with contextlib.redirect_stdout(stream):
            self.assertEqual(LANE.main(["--list"]), 0)
        text = stream.getvalue()
        self.assertIn("abi-xback seeds=1-40 opt=0,1,2,3 directions=2 required_match=320", text)
        self.assertIn(f"ty pin={LANE.TY.commit}", text)
        self.assertIn("absent aterm: absent", text)
        self.assertIn("ty not-in-lane tla-check: ", text)
        self.assertIn("ty tla-trust-cg/lib minimum=1339 filtered=compile::tests::"
                      "test_linked_trust_ir_probe_publication_allocation_from_env", text)
        self.assertIn("ty tla-trust-cg/trust_cg_lane_pow_int_semantics minimum=1 lane-owned="
                      "scripts/consumer_lane_ty_pow_int_semantics.rs", text)
        self.assertIn("host-residual=sat_bcp_gate_fails_closed_for_missing_wrong_and_unrunnable_artifact_routes",
                      text)

    def test_output_inside_the_source_tree_is_refused(self):
        stream = io.StringIO()
        with contextlib.redirect_stderr(stream):
            self.assertEqual(LANE.main(["--out", str(ROOT / "target" / "consumer-lane-report")]), 1)
        self.assertIn("outside the source tree", stream.getvalue())
        self.assertFalse((ROOT / "target" / "consumer-lane-report").exists())


class CohortTests(unittest.TestCase):
    def fixture_root(self, directory: Path, trust_ir=(TRUST_IR_NEW,), clean=(CLEAN_NEW,)) -> Path:
        manifest = ["[workspace.dependencies]"]
        for index, rev in enumerate(trust_ir):
            name = ("trust-ir", "trust-ir-build", "trust-ir-conformance")[index]
            manifest.append(f'{name} = {{ git = "{LANE.TRUST_IR_URL}", rev = "{rev}", features = ["serde"] }}')
        (directory / "Cargo.toml").write_text("\n".join(manifest) + "\n")
        packages = [("clean-kernel" if index == 0 else f"clean-x{index}", "0.9.0", git_source(LANE.CLEAN_URL, rev))
                    for index, rev in enumerate(clean)]
        packages.append(("serde", "1.0.0", "registry+https://github.com/rust-lang/crates.io-index"))
        (directory / "Cargo.lock").write_text(lock_text(packages))
        return directory

    def test_the_cohort_is_one_trust_ir_pin_and_one_clean_revision(self):
        with tempfile.TemporaryDirectory(prefix="tcg-consumer-cohort-") as temporary:
            root = self.fixture_root(Path(temporary))
            self.assertEqual(LANE.cohort(root), COHORT)
        for kwargs in ({"trust_ir": (TRUST_IR_NEW, TRUST_IR_OLD)}, {"clean": (CLEAN_NEW, CLEAN_OLD)},
                       {"trust_ir": ()}, {"clean": ()}):
            with self.subTest(**{key: len(value) for key, value in kwargs.items()}):
                with tempfile.TemporaryDirectory(prefix="tcg-consumer-cohort-") as temporary:
                    root = self.fixture_root(Path(temporary), **kwargs)
                    with self.assertRaises(ValueError):
                        LANE.cohort(root)

    def test_this_checkouts_cohort_is_the_pinned_trust_ir(self):
        observed = LANE.cohort()
        manifest = (ROOT / "Cargo.toml").read_text()
        self.assertIn(f'rev = "{observed["trust_ir_rev"]}"', manifest)
        self.assertRegex(observed["clean_rev"], r"^[0-9a-f]{40}$")

    def test_the_manifest_rewrite_moves_only_trust_ir_and_clean_revisions(self):
        manifest = "\n".join([
            f'ay = {{ version = "0.27.0", git = "https://github.com/alabsystems/ay.git", rev = "{"5" * 40}" }}',
            f'clean-kernel = {{ git = "{LANE.CLEAN_URL}", rev = "{CLEAN_OLD}" }}',
            f'trust-ir = {{ git = "{LANE.TRUST_IR_URL}", rev = "{TRUST_IR_OLD}" }}',
            f'trust-ir-build = {{ git = "{LANE.TRUST_IR_URL}", rev = "{TRUST_IR_NEW}" }}',
            f'trust-cg-codegen = {{ git = "{LANE.TRUST_CG_URL}", rev = "{"6" * 40}" }}',
        ]) + "\n"
        rewritten, changes = LANE.rewrite_manifest(manifest, COHORT)
        self.assertEqual([(change["line"], change["from"], change["to"]) for change in changes],
                         [(2, CLEAN_OLD, CLEAN_NEW), (3, TRUST_IR_OLD, TRUST_IR_NEW)])
        self.assertEqual(rewritten.splitlines()[0], manifest.splitlines()[0])
        self.assertEqual(rewritten.splitlines()[4], manifest.splitlines()[4])
        self.assertNotIn(TRUST_IR_OLD, rewritten)
        self.assertNotIn(CLEAN_OLD, rewritten)
        self.assertEqual(LANE.trust_cg_dependencies(manifest), ["trust-cg-codegen"])
        self.assertEqual(LANE.rewrite_manifest(rewritten, COHORT), (rewritten, []))

    def test_patches_name_this_checkouts_crates_and_refuse_a_missing_one(self):
        arguments = LANE.patch_configuration(["trust-cg-codegen"])
        self.assertEqual(arguments, ["--config", f'patch."{LANE.TRUST_CG_URL}".trust-cg-codegen.path='
                                                 f'"{ROOT / "crates" / "trust-cg-codegen"}"'])
        with self.assertRaises(ValueError):
            LANE.patch_configuration(["trust-cg-not-a-crate"])


class LockTests(unittest.TestCase):
    REGISTRY = "registry+https://github.com/rust-lang/crates.io-index"

    def before(self):
        return {
            ("serde", "1.0.0", self.REGISTRY), ("tla-check", "0.15.0", None),
            ("trust-cg-codegen", "0.7.0", git_source(LANE.TRUST_CG_URL, "6" * 40)),
            ("trust-ir", "0.14.0", git_source(LANE.TRUST_IR_URL, TRUST_IR_OLD)),
            ("clean-kernel", "0.9.0", git_source(LANE.CLEAN_URL, CLEAN_OLD)),
        }

    def substituted(self):
        return {
            ("serde", "1.0.0", self.REGISTRY), ("tla-check", "0.15.0", None),
            ("trust-cg-codegen", "0.7.0", None), ("trust-cg-verify", "0.7.0", None),
            ("trust-ir", "0.14.0", git_source(LANE.TRUST_IR_URL, TRUST_IR_NEW)),
            ("clean-kernel", "0.9.0", git_source(LANE.CLEAN_URL, CLEAN_NEW)),
        }

    def test_the_lock_text_parser_reads_every_package(self):
        packages = self.before()
        self.assertEqual(LANE.lock_packages(lock_text(packages)), packages)
        with self.assertRaises(ValueError):
            LANE.lock_packages('[[package]]\nname = "x"\n')

    def test_an_exact_cohort_substitution_is_accepted(self):
        self.assertEqual(LANE.lock_problems(self.before(), self.substituted(), set(), COHORT), [])

    def test_a_third_party_move_is_drift_unless_this_checkout_pins_it(self):
        after = (self.substituted() - {("serde", "1.0.0", self.REGISTRY)}) | {("serde", "1.0.9", self.REGISTRY)}
        problems = LANE.lock_problems(self.before(), after, set(), COHORT)
        self.assertEqual(len(problems), 1)
        self.assertTrue(problems[0].startswith("consumer-lock-drift: added serde 1.0.9"))
        self.assertEqual(LANE.lock_problems(self.before(), after, {("serde", "1.0.9", self.REGISTRY)}, COHORT), [])

    def test_a_cohort_family_left_at_another_source_is_a_split(self):
        for stale in (("trust-ir", "0.14.0", git_source(LANE.TRUST_IR_URL, TRUST_IR_OLD)),
                      ("clean-ck0", "0.9.0", git_source(LANE.CLEAN_URL, CLEAN_OLD)),
                      ("trust-cg-ir", "0.7.0", git_source(LANE.TRUST_CG_URL, "6" * 40))):
            with self.subTest(package=stale[0]):
                problems = LANE.lock_problems(self.before(), self.substituted() | {stale}, set(), COHORT)
                self.assertEqual(len(problems), 1, problems)
                self.assertTrue(problems[0].startswith(f"consumer-cohort-split: {stale[0]} "), problems)


class TargetClassificationTests(unittest.TestCase):
    POW = LANE.KnownFailure(klass="consumer-test-contradiction", reason="r",
                            output=("zero to the zero power", "err_kind: TypeMismatch"))
    AUDIT = LANE.KnownFailure(klass="consumer-own-pin-audit", reason="r", output=('left: "{trust_ir_rev}"',))

    def test_a_clean_target_passes_with_its_minimum(self):
        verdict = classify(transcript(passed=("a", "b")), minimum=2)
        self.assertEqual((verdict["status"], verdict["passed"], verdict["classes"]), ("pass", 2, []))
        below = classify(transcript(passed=("a",)), minimum=2)
        self.assertEqual((below["status"], below["classes"]), ("fail", ["consumer-inventory-drift"]))

    def test_a_listed_failure_passes_only_with_its_identifying_output(self):
        text = transcript(passed=("a",), failed=("pow",),
                          outputs={"pow": "zero to the zero power: JitCallOut { err_kind: TypeMismatch }"})
        self.assertEqual(classify(text, 101, known={"pow": self.POW})["status"], "pass")
        other = transcript(passed=("a",), failed=("pow",), outputs={"pow": "index out of bounds"})
        verdict = classify(other, 101, known={"pow": self.POW})
        self.assertEqual((verdict["status"], verdict["classes"]), ("fail", ["consumer-known-failure-changed"]))
        # A listed failure that now passes must leave the list.
        fixed = classify(transcript(passed=("a", "pow")), 0, known={"pow": self.POW})
        self.assertEqual((fixed["status"], fixed["classes"]), ("fail", ["consumer-known-failure-changed"]))

    def test_identifying_output_is_formatted_with_the_cohort(self):
        text = transcript(passed=("a",), failed=("audit",),
                          outputs={"audit": f'  left: "{TRUST_IR_NEW}"\n right: "{TRUST_IR_OLD}"'})
        self.assertEqual(classify(text, 101, known={"audit": self.AUDIT})["status"], "pass")
        wrong = transcript(passed=("a",), failed=("audit",), outputs={"audit": f'  left: "{TRUST_IR_OLD}"'})
        self.assertEqual(classify(wrong, 101, known={"audit": self.AUDIT})["status"], "fail")

    def test_an_unrecorded_failure_is_a_regression(self):
        verdict = classify(transcript(passed=("a",), failed=("b",)), 101)
        self.assertEqual((verdict["status"], verdict["classes"]), ("fail", ["consumer-test-regression"]))
        contract = LANE.classify_consumer_target("t", 101, transcript(passed=("a",), failed=("b",)), minimum=1,
                                                 known={}, ignored=frozenset(), substitutions={},
                                                 regression_class="cg-contract-failed")
        self.assertEqual(contract["classes"], ["cg-contract-failed"])

    def test_ignored_and_filtered_tests_must_be_exactly_the_pinned_ones(self):
        text = transcript(passed=("a",), ignored=("corpus",))
        self.assertEqual(classify(text, ignored=frozenset({"corpus"}))["status"], "pass")
        self.assertEqual(classify(text)["classes"], ["consumer-inventory-drift"])
        filtered = transcript(passed=("a",), filtered=2)
        self.assertEqual(classify(filtered, filtered=frozenset({"x", "y"}))["status"], "pass")
        self.assertEqual(classify(filtered, filtered=frozenset({"x"}))["status"], "fail")
        ran = transcript(passed=("a", "x"), filtered=1)
        self.assertEqual(classify(ran, filtered=frozenset({"x"}))["status"], "fail")

    def test_runtime_skips_fail_and_contract_targets_use_the_floors_broad_spelling(self):
        explicit = transcript(passed=("a",), outputs={"a": "SKIP: host tool missing"})
        self.assertEqual(classify(explicit)["status"], "fail")
        broad = transcript(passed=("a",), outputs={"a": "skipping real TY replay bundle reducer: not set"})
        self.assertEqual(classify(broad)["status"], "pass")
        self.assertEqual(classify(broad, broad=True)["status"], "fail")
        # TY's env-gated probe prints exactly this and returns; the broad spelling catches it.
        probe = transcript(passed=("compile::tests::probe",), outputs={
            "compile::tests::probe": "skipping linked trust-ir native allocation probe: "
                                     "TY_TRUST_CG_LINKED_TRUST_IR_PROBE_JSON unset"})
        self.assertEqual(classify(probe, broad=True)["classes"], ["consumer-inventory-drift"])
        # A test or module named "skip" is libtest's own line, never a skip notice.
        for name in ("cache_hit_skips_recompilation", "skip", "skip::cases", "skipped::cases::one"):
            with self.subTest(name=name):
                self.assertEqual(classify(transcript(passed=(name,)), broad=True)["status"], "pass")

    def test_a_listed_host_residual_matches_exactly_and_stays_red_under_its_class(self):
        residual = LANE.KnownFailure(klass="host-proof-promotion-residual", reason="r",
                                     output=("proof promotion rejected", "[AArch64::StpPreIndex]"), residual=True)
        output = "proof promotion rejected for target Aarch64: ... [AArch64::StpPreIndex]"
        verdict = classify(transcript(failed=("bcp",), outputs={"bcp": output}), 101, minimum=0,
                           known={"bcp": residual})
        self.assertEqual((verdict["status"], verdict["classes"]), ("fail", ["host-proof-promotion-residual"]))
        self.assertTrue(verdict["known_failures"][0]["residual"])
        # Another opcode set is a changed failure, not this residual.
        other = classify(transcript(failed=("bcp",), outputs={"bcp": "proof promotion rejected [AArch64::Movz]"}),
                         101, minimum=0, known={"bcp": residual})
        self.assertEqual(other["classes"], ["consumer-known-failure-changed"])
        fixed = classify(transcript(passed=("bcp",)), 0, minimum=0, known={"bcp": residual})
        self.assertEqual(fixed["classes"], ["consumer-known-failure-changed"])

    def test_build_failures_timeouts_and_missing_rollups_are_named(self):
        self.assertEqual(classify("error[E0308]: mismatched types\n", 101)["classes"],
                         ["consumer-build-failed", "consumer-inventory-drift"])
        timed_out = classify(transcript(passed=("a",)), 124)
        self.assertIn("timeout", timed_out["classes"])
        nested = transcript(passed=("a",), outputs={"a": "test result: ok. 9 passed; 0 failed; 0 ignored; "
                                                         "0 measured; 0 filtered out; finished in 0.01s"})
        # A child binary's rollup inside captured output is output, not a suite.
        self.assertEqual(classify(nested)["status"], "pass")


class AbiAndWorkloadTests(unittest.TestCase):
    LINKER = ("abi-xback: host aarch64-apple-darwin; linker /usr/bin/cc (ld64 /usr/bin/ld: "
              "@(#)PROGRAM:ld PROJECT:ld-1); no gcc-ld shim\n")
    PROBE = "abi-xback: link probe: rustc links with /usr/bin/cc\n"

    def run_text(self, match=320, mismatch=0, declined=0, skipped=0, callee=160, caller=160, linker=True,
                 probe=PROBE, lines=()):
        return ((self.LINKER if linker else "") + probe + "".join(f"{line}\n" for line in lines)
                + f"abi-xback: {match} MATCH, {mismatch} MISMATCH, {declined} declined, {skipped} skipped\n"
                + f"abi-xback: directions: llvm-caller x tcg-callee {callee} MATCH; tcg-caller x llvm-callee "
                + f"{caller} MATCH; opt levels 0 1 2 3; seeds 1..40\n")

    def test_the_full_domain_in_both_directions_passes(self):
        verdict = LANE.classify_abi_run(0, self.run_text(), 160)
        self.assertEqual((verdict["status"], verdict["linker"]), ("pass", "/usr/bin/cc"))
        self.assertEqual(verdict["counts"]["tcg_caller_x_llvm_callee"], 160)

    def test_each_failure_is_named(self):
        cases = (
            (dict(match=319, mismatch=1, callee=159, lines=("MISMATCH llvm-caller x tcg-callee seed=3 O2: want 1 got 2",)),
             ["abi-mismatch"]),
            (dict(match=318, declined=2, caller=158), ["abi-backend-decline"]),
            (dict(match=270, declined=50, caller=110), ["abi-backend-decline"]),
            (dict(match=316, skipped=4, callee=158, caller=158,
                  lines=("SKIPPED tcg-caller x llvm-callee seed=3 O0: link failed: error: linking with `cc` failed",)),
             ["abi-skip"]),
            (dict(match=160, callee=160, caller=0), ["abi-incomplete"]),
            (dict(linker=False), ["abi-incomplete"]),
            (dict(probe=""), ["abi-incomplete"]),
            (dict(probe="abi-xback: link probe: rustc links with /opt/other/cc\n"), ["abi-incomplete"]),
        )
        for kwargs, classes in cases:
            with self.subTest(**{key: value for key, value in kwargs.items() if key not in ("lines", "probe")},
                              probe=kwargs.get("probe")):
                exit_code = 0 if kwargs.keys() & {"linker", "probe"} else 1
                verdict = LANE.classify_abi_run(exit_code, self.run_text(**kwargs), 160)
                self.assertEqual(verdict["status"], "fail")
                self.assertTrue(set(classes) <= set(verdict["classes"]), verdict)
                # Every named outcome line, a link-failure skip included, is kept.
                self.assertEqual(verdict["named_failures"], list(kwargs.get("lines", ())))
        self.assertEqual(LANE.classify_abi_run(0, "abi-xback: 0 MATCH\n", 160)["classes"], ["abi-incomplete"])
        # run.sh's own failure exit is explained by the named outcome, never "incomplete" on top.
        declined = LANE.classify_abi_run(1, self.run_text(match=270, declined=50, caller=110), 160)
        self.assertEqual(declined["classes"], ["abi-backend-decline"])
        self.assertEqual(LANE.classify_abi_run(124, self.run_text(), 160)["classes"], ["timeout"])

    def test_the_parsed_lines_are_the_ones_run_sh_prints(self):
        source = LANE.ABI_XBACK.read_text()
        self.assertIn('echo "abi-xback: $match MATCH, $mismatch MISMATCH, $declined declined, $skipped skipped"', source)
        self.assertIn('echo "abi-xback: directions: llvm-caller x tcg-callee $match_tcg_callee MATCH; '
                      'tcg-caller x llvm-callee $match_tcg_caller MATCH;', source)
        self.assertIn("linker $LINKER (ld64 $LD64: $LD64_ID); no gcc-ld shim", source)
        self.assertIn('echo "abi-xback: link probe: rustc links with $LINKER"', source)
        # The probe links with the exact BIN flags, which carry the resolved
        # linker, and requires rustc's link line to invoke that path.
        self.assertRegex(source, r'BIN=\([^\n]*\$\{LINK\[@\]\+"\$\{LINK\[@\]\}"\}\)')
        self.assertIn('"$RUSTC" "${BIN[@]}" --print link-args', source)
        self.assertIn('*"\\"$LINKER\\" "*) ;;', source)
        # A link failure is a skip that keeps the linker's diagnostic, never a decline.
        self.assertIn('2>"$dir/llvm_x_tcg_link.err"', source)
        self.assertNotIn("-l static=xt 2>/dev/null", source)
        self.assertIn("grep -q '^error: linking with `' \"$dir/caller_tcg.err\"", source)
        self.assertEqual(source.count('echo "SKIPPED '), 2)
        self.assertIn(LANE.ABI_SELFTEST_LINE.split(":")[0], source)
        # Darwin never puts a gcc-ld shim on PATH; the Linux fallback is the marked stock exception.
        self.assertIn("STOCK EXCEPTION", source)
        self.assertIn("bridge_backend.py", source)

    def document(self, **kwargs):
        return workload_document(**kwargs)

    def oracle(self, **kwargs):
        return self.document(tier="interpreter", route="eval_per_action", **kwargs)

    ROW = ("AddTwoTest", "AddTwoTest", "ok", None, 5, 5)

    def test_agreeing_backends_on_the_native_tier_pass(self):
        verdict = LANE.classify_workload(self.ROW, self.document(), self.oracle())
        self.assertEqual((verdict["status"], verdict["native_accepted_results"]), ("pass", 5))
        violation = ("Pow", "Pow", "error", "TLC_INVARIANT_VIOLATED", 5, 4)
        self.assertEqual(LANE.classify_workload(
            violation, self.document(status="error", code="TLC_INVARIANT_VIOLATED", transitions=4),
            self.oracle(status="error", code="TLC_INVARIANT_VIOLATED", transitions=4))["status"], "pass")

    def test_disagreement_a_moved_pin_and_a_non_native_run_are_named(self):
        cases = (
            (self.document(states=6), self.oracle(), "workload-mismatch"),
            (self.document(states=6), self.oracle(states=6), "workload-mismatch"),
            (self.document(tier="interpreter", route="eval_whole_parent"), self.oracle(), "workload-not-native"),
            (self.document(accepted=0), self.oracle(), "workload-not-native"),
            (self.document(), self.document(), "workload-mismatch"),
        )
        for native, oracle, klass in cases:
            with self.subTest(klass=klass):
                verdict = LANE.classify_workload(self.ROW, native, oracle)
                self.assertEqual(verdict["status"], "fail")
                self.assertIn(klass, verdict["classes"])
        self.assertEqual(LANE.classify_workload(self.ROW, None, self.oracle())["classes"], ["workload-failed"])

    def test_the_replay_corpus_must_compare_every_dumped_module(self):
        passed = transcript(passed=(LANE.TY_REPLAY_TEST,), filtered=1341)
        summary = json.dumps({"summary": True, "compared": 13, "refused": 0, "sealed_mismatch": 0,
                              "step_changed_image": 0})
        self.assertEqual(LANE.classify_replay(0, passed, ["{}", summary], 13)["status"], "pass")
        for lines, modules in (([summary], 14), ([], 13), ([summary.replace('"refused": 0', '"refused": 1')], 13),
                               ([summary.replace('"sealed_mismatch": 0', '"sealed_mismatch": 2')], 13),
                               ([json.dumps({"summary": True, "compared": 0, "refused": 0,
                                             "sealed_mismatch": 0})], 0)):
            with self.subTest(modules=modules, lines=lines):
                verdict = LANE.classify_replay(0, passed, lines, modules)
                self.assertEqual((verdict["status"], verdict["classes"]), ("fail", ["consumer-replay-failed"]))
        failed = transcript(failed=(LANE.TY_REPLAY_TEST,))
        self.assertEqual(LANE.classify_replay(101, failed, [summary], 13)["status"], "fail")

    def test_replay_modules_are_the_pre_jit_records_of_the_dump(self):
        with tempfile.TemporaryDirectory(prefix="tcg-consumer-replay-") as temporary:
            root = Path(temporary)
            modules = root / "Spec" / "trust-ir-modules"
            modules.mkdir(parents=True)
            (modules / "000001-pre.metadata.json").write_text(json.dumps({"stage": LANE.TY_REPLAY_STAGE}))
            (modules / "000002-linked.metadata.json").write_text(json.dumps({"stage": "compile_module_native.linked"}))
            (modules / "000003-bad.metadata.json").write_text("{")
            self.assertEqual([path.name for path in LANE.replay_modules(root)], ["000001-pre.metadata.json"])
            self.assertEqual(LANE.replay_modules(root / "absent"), [])


class SourceTests(unittest.TestCase):
    """The pinned commit is exported from Git objects, never from a working tree."""

    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory(prefix="tcg-consumer-source-")
        self.base = Path(self.temporary.name)
        self.upstream = self.base / "upstream"
        self.upstream.mkdir()
        git("init", "--quiet", "-b", "main", cwd=self.upstream)
        (self.upstream / "Cargo.toml").write_text("[workspace]\n")
        (self.upstream / "reports").mkdir()
        (self.upstream / "reports" / "big.log").write_text("evidence\n")
        git("add", "-A", cwd=self.upstream)
        git("commit", "--quiet", "-m", "pin", cwd=self.upstream)
        self.commit = git("rev-parse", "HEAD", cwd=self.upstream)
        (self.upstream / "Cargo.toml").write_text("[workspace]\n# uncommitted edit\n")

    def tearDown(self):
        self.temporary.cleanup()

    def pin(self, sibling: Path):
        return LANE.ConsumerPin(name="fixture", url=self.upstream.as_uri(), commit=self.commit, sibling=sibling,
                                export_exclude=("reports",))

    def test_a_sibling_holding_the_pin_is_used_and_its_working_tree_is_not(self):
        pin = self.pin(self.upstream)
        repository, origin = LANE.pin_source(pin, self.base / "cache.git", fetch=False)
        self.assertEqual((repository, origin), (self.upstream, "sibling"))
        record = LANE.export_commit(repository, pin, self.base / "export")
        self.assertEqual((self.base / "export" / "Cargo.toml").read_text(), "[workspace]\n")
        self.assertFalse((self.base / "export" / "reports").exists())
        self.assertEqual(record["tree"], git("rev-parse", f"{self.commit}^{{tree}}", cwd=self.upstream))
        sibling = LANE.sibling_record(self.upstream, self.commit)
        self.assertEqual((sibling["head"], sibling["dirty_tracked"], sibling["holds_pin"]), (self.commit, True, True))

    def test_a_pin_nowhere_is_refused_unless_fetching_is_allowed(self):
        pin = self.pin(self.base / "no-sibling")
        cache = self.base / "cache.git"
        with self.assertRaises(LANE.LaneError) as raised:
            LANE.pin_source(pin, cache, fetch=False)
        self.assertEqual(raised.exception.klass, "consumer-pin-unavailable")
        self.assertFalse(cache.exists())
        repository, origin = LANE.pin_source(pin, cache, fetch=True)
        self.assertEqual((repository, origin), (cache, "fetched"))
        self.assertEqual(LANE.pin_source(pin, cache, fetch=False), (cache, "lane-cache"))
        moved = LANE.ConsumerPin(name="fixture", url=self.upstream.as_uri(), commit="0" * 40,
                                 sibling=self.base / "no-sibling", export_exclude=())
        with self.assertRaises(LANE.LaneError) as raised:
            LANE.pin_source(moved, cache, fetch=True)
        self.assertEqual(raised.exception.klass, "consumer-pin-unavailable")


class ConsumerCacheTests(unittest.TestCase):
    def test_exports_default_to_a_per_user_cache_outside_this_checkout(self):
        mac = LANE.default_consumer_cache(Path("/home/u"), {}, "darwin")
        self.assertEqual(mac.parent, Path("/home/u/Library/Caches/trust-cg-consumer-lane"))
        linux = LANE.default_consumer_cache(Path("/home/u"), {"XDG_CACHE_HOME": "/x"}, "linux")
        self.assertEqual(linux.parent, Path("/x/trust-cg-consumer-lane"))
        self.assertEqual(LANE.default_consumer_cache(Path("/home/u"), {}, "linux").parent,
                         Path("/home/u/.cache/trust-cg-consumer-lane"))
        self.assertEqual(mac.name, linux.name)
        self.assertFalse(mac.is_relative_to(ROOT))

    def test_an_enclosing_cargo_configuration_is_found(self):
        with tempfile.TemporaryDirectory(prefix="tcg-consumer-config-") as temporary:
            base = Path(temporary)
            home = base / "cargo-home"
            home.mkdir()
            (home / "config.toml").write_text("")
            (base / "repo" / ".cargo").mkdir(parents=True)
            (base / "repo" / ".cargo" / "config.toml").write_text("[env]\n")
            inner = base / "repo" / "target" / "consumer"
            inner.mkdir(parents=True)
            outside = base / "cache"
            outside.mkdir()
            found = [path for path in LANE.enclosing_cargo_configs(inner, home) if path.is_relative_to(base)]
            self.assertEqual(found, [base / "repo" / ".cargo" / "config.toml"])
            self.assertEqual([path for path in LANE.enclosing_cargo_configs(outside, home)
                              if path.is_relative_to(base)], [])
            self.assertEqual([path for path in LANE.enclosing_cargo_configs(home, home)
                              if path.is_relative_to(base)], [])


class LeftoverTests(unittest.TestCase):
    ALLOWANCE = (r"\.tmp[A-Za-z0-9]{6}", r"[0-9a-f]{64}\.meta\.json", 1)

    def test_a_listed_consumer_leak_is_tolerated_only_in_its_listed_shape(self):
        leak = {"temporary_leftovers": [".tmpAb12Cd"],
                "temporary_leftover_files": {".tmpAb12Cd": ["a" * 64 + ".meta.json"]}}
        self.assertEqual(LANE.leftover_errors(dict(leak), self.ALLOWANCE), ([], set()))
        self.assertEqual(LANE.leftover_errors(dict(leak))[1], {"temporary-leftovers"})
        other_file = {"temporary_leftovers": [".tmpAb12Cd"],
                      "temporary_leftover_files": {".tmpAb12Cd": ["core.dump"]}}
        self.assertEqual(LANE.leftover_errors(other_file, self.ALLOWANCE)[1], {"temporary-leftovers"})
        two = {"temporary_leftovers": [".tmpAb12Cd", ".tmpEf34Gh"],
               "temporary_leftover_files": {".tmpAb12Cd": ["a" * 64 + ".meta.json"],
                                            ".tmpEf34Gh": ["b" * 64 + ".meta.json"]}}
        self.assertEqual(LANE.leftover_errors(two, self.ALLOWANCE)[1], {"temporary-leftovers"})
        # The leak is a race in the consumer's tests: its absence is recorded, not a failure.
        absent = {"temporary_leftovers": []}
        self.assertEqual(LANE.leftover_errors(absent, self.ALLOWANCE), ([], set()))
        self.assertEqual(absent["listed_consumer_leaks"], [])
        self.assertEqual(LANE.leftover_errors({"temporary_leftovers": []}), ([], set()))
        self.assertEqual(LANE.TY_TEMPORARY_LEAKS["lib"], self.ALLOWANCE)

    def test_the_runner_records_and_removes_a_steps_tmpdir(self):
        with tempfile.TemporaryDirectory(prefix="tcg-consumer-runner-") as temporary:
            output = Path(temporary)
            runner = LANE.Runner(output, dict(os.environ))
            script = ("import os, tempfile; d = tempfile.mkdtemp(prefix='.tmp', dir=os.environ['TMPDIR']); "
                      "open(os.path.join(d, 'x.meta.json'), 'w').close(); print('done')")
            record = runner.run([sys.executable, "-c", script], "leak.log", 30)
            self.assertEqual(record["returncode"], 0)
            self.assertEqual(len(record["temporary_leftovers"]), 1)
            name = record["temporary_leftovers"][0]
            self.assertEqual(record["temporary_leftover_files"][name], ["x.meta.json"])
            self.assertIn("done", (output / "leak.log").read_text())
            slow = runner.run([sys.executable, "-c", "import time; time.sleep(30)"], "slow.log", 0.3)
            self.assertEqual(slow["returncode"], 124)
            with self.assertRaises(FileExistsError):
                runner.run([sys.executable, "-c", "pass"], "leak.log", 30)


class ArchiveTests(unittest.TestCase):
    def test_archive_keeps_the_report_failing_logs_and_inputs_in_a_verifiable_inventory(self):
        spec = importlib.util.spec_from_file_location("_test_lane_evidence_archive",
                                                      ROOT / "scripts" / "check_evidence_archive.py")
        evidence = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(evidence)
        with tempfile.TemporaryDirectory(prefix="tcg-consumer-archive-") as temporary:
            base = Path(temporary)
            run = base / "run"
            run.mkdir()
            for name in ("cg-contracts--red.log", "cg-contracts--green.log", "abi-xback--run.log",
                         "ty--Cargo.lock", "ty--workload--Spec--trust-cg.json", "ty--metadata.json",
                         "abi-xback/fail/caller3_O0_tcg.err", "abi-xback/caller3.rs"):
                (run / name).parent.mkdir(parents=True, exist_ok=True)
                (run / name).write_text(name)
            report = {
                "schema": LANE.SCHEMA, "status": "fail", "provenance": {"source_sha": "a" * 40},
                "steps": {"cg-contracts": {"status": "fail", "targets": [
                    {"log": "cg-contracts--red.log", "status": "fail"},
                    {"log": "cg-contracts--green.log", "status": "pass"}]}},
            }
            (run / "report.json").write_text(json.dumps(report))
            destination = base / "record"
            destination.mkdir()
            with self.assertRaises(ValueError):
                LANE.archive(run, destination)
            (destination / "README.md").write_text("# Record\n")
            with contextlib.redirect_stdout(io.StringIO()):
                self.assertEqual(LANE.archive(run, destination), 0)
            stored = sorted(path.relative_to(destination).as_posix() for path in destination.rglob("*")
                            if path.is_file())
            self.assertEqual(stored, [
                "README.md", "inventory.json", "logs/abi-xback--run.log.gz",
                "logs/abi-xback/fail/caller3_O0_tcg.err.gz", "logs/cg-contracts--red.log.gz",
                "logs/ty--Cargo.lock.gz", "logs/ty--workload--Spec--trust-cg.json.gz", "report.json"])
            self.assertEqual(evidence.archive_errors(destination), [])
            with self.assertRaises(ValueError):
                LANE.archive(run, destination)
            (run / "report.json").write_text(json.dumps({**report, "status": "incomplete"}))
            other = base / "other"
            other.mkdir()
            (other / "README.md").write_text("# Record\n")
            with self.assertRaises(ValueError):
                LANE.archive(run, other)


class FakeRunner:
    """Stands in for Runner: answers each command with a scripted transcript."""

    def __init__(self, output: Path, answer):
        self.output = output
        self.answer = answer
        self.calls: list[str] = []
        self.environment = {"TRUST_TARGO": "/fixture/targo"}

    def run(self, command, log_name, timeout, **_kwargs):
        self.calls.append(log_name)
        returncode, text, leftovers = self.answer(list(command), log_name)
        (self.output / log_name).write_text(text)
        return {"command": list(command), "returncode": returncode, "log": log_name,
                "temporary_leftovers": list(leftovers),
                "temporary_leftover_files": {name: [] for name in leftovers}}


ARGS = SimpleNamespace(offline=False, jobs=1, timeout_seconds=1, build_timeout_seconds=1, abi_timeout_seconds=1,
                       workload_timeout_seconds=1)


class StepTests(unittest.TestCase):
    """The steps' own wiring, driven through FakeRunner (no Cargo, no compiler)."""

    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory(prefix="tcg-consumer-steps-")
        self.addCleanup(self.temporary.cleanup)
        self.output = Path(self.temporary.name)

    def contract_answer(self, opcodes="[AArch64::StpPreIndex, AArch64::AddRI, AArch64::Movz, AArch64::LdpPostIndex]"):
        rows = {f"cg-contracts--{row.target}.log": row for row in LANE.CG_CONTRACT_TARGETS}

        def answer(command, log_name):
            row = rows[log_name]
            failed = tuple(name for name, _ in row.known_failures)
            output = ("compile-only SAT BCP observation diagnostics: proof promotion rejected for target Aarch64: "
                      "non_verified proof entry opcode_inventory_instruction_0 in ay_sat_watch_bcp_status_probe: "
                      "emitted opcode inventory found 4 uncovered non-pseudo opcode(s) across 4 distinct "
                      f"opcode(s) {opcodes}; first in ...")
            text = transcript(passed=tuple(f"t{index}" for index in range(row.minimum)), failed=failed,
                              filtered=len(row.filtered), outputs={name: output for name in failed})
            return (101 if failed else 0), text, ()
        return answer

    def test_cg_contracts_keep_a_listed_host_residual_red_under_its_own_class(self):
        with contextlib.redirect_stdout(io.StringIO()):
            result = LANE.step_cg_contracts(FakeRunner(self.output, self.contract_answer()), ARGS)
        self.assertEqual((result["status"], result["classes"]), ("fail", ["host-proof-promotion-residual"]))
        self.assertEqual(sorted(result["host_residuals"]), sorted(
            name for row in LANE.CG_CONTRACT_TARGETS for name, failure in row.known_failures if failure.residual))
        failing = [row["target"] for row in result["targets"] if row["status"] != "pass"]
        self.assertEqual(failing, ["ay_sat_bcp_install_gate"])
        self.assertEqual(result["executed_passes"], sum(row.minimum for row in LANE.CG_CONTRACT_TARGETS))

    def test_cg_contracts_name_a_changed_residual_as_a_failed_contract(self):
        answer = self.contract_answer(opcodes="[AArch64::StpPreIndex, AArch64::AddRI, AArch64::Movz, "
                                              "AArch64::LdpPostIndex, AArch64::Bl]")
        with contextlib.redirect_stdout(io.StringIO()):
            result = LANE.step_cg_contracts(FakeRunner(self.output, answer), ARGS)
        self.assertEqual(result["classes"], ["cg-contract-failed", "consumer-known-failure-changed"])
        self.assertEqual(result["host_residuals"], [])

    def abi_answer(self, *, selftest_leftovers=(), build_code=0):
        def answer(command, log_name):
            if log_name == "abi-xback--selftest.log":
                return 0, LANE.ABI_SELFTEST_LINE + "\n", selftest_leftovers
            if log_name == "abi-xback--bridge-build.log":
                return build_code, "Finished\n", ()
            linker = "/usr/bin/cc"
            return 0, (f"abi-xback: host aarch64-apple-darwin; linker {linker} (ld64 /usr/bin/ld: PROGRAM:ld)\n"
                       f"abi-xback: link probe: rustc links with {linker}\n"
                       "abi-xback: 320 MATCH, 0 MISMATCH, 0 declined, 0 skipped\n"
                       "abi-xback: directions: llvm-caller x tcg-callee 160 MATCH; tcg-caller x llvm-callee "
                       "160 MATCH; opt levels 0 1 2 3; seeds 1..40\n"), ()
        return answer

    def run_abi(self, runner, stale=None):
        target = self.output / "target-bridge"
        (target / "release").mkdir(parents=True)
        fake_bridge = SimpleNamespace(file_name=lambda: "libbridge.dylib", stale_source=lambda root, path: stale)
        (target / "release" / "libbridge.dylib").write_bytes(b"backend")
        package = {"targo": "/fixture/targo", "compiler": "/fixture/trustc"}
        with mock.patch.object(LANE, "BRIDGE_TARGET", target), \
                mock.patch.object(LANE, "_load", return_value=fake_bridge), \
                contextlib.redirect_stdout(io.StringIO()):
            return LANE.step_abi_xback(runner, ARGS, package)

    def test_abi_xback_runs_the_full_domain_against_a_fresh_bridge(self):
        runner = FakeRunner(self.output, self.abi_answer())
        result = self.run_abi(runner)
        self.assertEqual((result["status"], result["classes"]), ("pass", []), result["errors"])
        self.assertEqual(runner.calls, ["abi-xback--selftest.log", "abi-xback--bridge-build.log",
                                        "abi-xback--run.log"])

    def test_abi_xback_refuses_a_stale_bridge_before_running(self):
        runner = FakeRunner(self.output, self.abi_answer())
        result = self.run_abi(runner, stale=Path("crates/trust-cg-codegen/src/lib.rs"))
        self.assertEqual((result["status"], result["classes"]), ("fail", ["bridge-backend-stale"]))
        self.assertNotIn("abi-xback--run.log", runner.calls)
        self.assertEqual(result["backend"]["stale_input"], "crates/trust-cg-codegen/src/lib.rs")

    def test_abi_xback_judges_the_selftest_and_bridge_build_tmpdirs(self):
        runner = FakeRunner(self.output, self.abi_answer(selftest_leftovers=("core.1",)))
        result = self.run_abi(runner)
        self.assertEqual((result["status"], result["classes"]), ("fail", ["temporary-leftovers"]))
        self.assertIn("abi-xback--run.log", runner.calls)
        self.assertEqual(result["selftest"]["status"], "fail")
        failed = self.run_abi_build_failure()
        self.assertEqual(failed["classes"], ["bridge-build-failed"])

    def run_abi_build_failure(self):
        with tempfile.TemporaryDirectory(prefix="tcg-consumer-steps-") as temporary:
            self.output = Path(temporary)
            runner = FakeRunner(self.output, self.abi_answer(build_code=101))
            target = self.output / "target-bridge"
            fake_bridge = SimpleNamespace(file_name=lambda: "libbridge.dylib", stale_source=lambda root, path: None)
            with mock.patch.object(LANE, "BRIDGE_TARGET", target), \
                    mock.patch.object(LANE, "_load", return_value=fake_bridge), \
                    contextlib.redirect_stdout(io.StringIO()):
                return LANE.step_abi_xback(runner, ARGS, {"targo": "/fixture/targo", "compiler": "/fixture/trustc"})

    def ty_answer(self, context, calls, *, skip_notice_in=None, build_leftovers=()):
        """Scripted TY: every target meets its minimum with its listed failures, ignores and filters."""
        targets = {**LANE.TY_TARGETS, **{name: minimum for name, (_, minimum) in LANE.TY_LANE_TARGETS.items()}}

        def answer(command, log_name, stdout_path=None, extra_environment=None):
            calls[log_name] = command
            if log_name in ("ty--build-tests.log", "ty--build-binary.log"):
                return 0, "Finished\n", (build_leftovers if log_name == "ty--build-tests.log" else ())
            if log_name == "ty--canary.log":
                return 0, LANE.TY_CANARY_LINE + "\n", ()
            if log_name == "ty--replay.log":
                summary = {"summary": True, "compared": 1, "refused": 0, "sealed_mismatch": 0}
                Path(extra_environment["TY_ADOPTION_IDENTITY_OUT"]).write_text(json.dumps(summary) + "\n")
                return 0, transcript(passed=(LANE.TY_REPLAY_TEST,), filtered=1), ()
            if log_name.startswith("ty--workload--"):
                spec, backend = log_name[len("ty--workload--"):-len(".log")].split("--")
                row = next(row for row in LANE.TY_WORKLOADS if row[0] == spec)
                _, _, status, code, states, transitions = row
                tier, route = (("trust-cg native-fused (compiled BFS)", "compiled_bfs_fused") if backend == "trust-cg"
                               else ("interpreter", "eval_per_action"))
                document = workload_document(status=status, code=code, states=states, transitions=transitions,
                                             tier=tier, route=route)
                stdout_path.write_text(json.dumps(document))
                return (0 if status == "ok" else 1), "", ()
            target = log_name[len("ty--"):-len(".log")]
            known = [name for (key, name), _ in LANE.TY_KNOWN_FAILURES.items() if key == target]
            outputs = {name: "\n".join(failure.output).format(**COHORT)
                       for (key, name), failure in LANE.TY_KNOWN_FAILURES.items() if key == target}
            if target == skip_notice_in:
                outputs["t0"] = "skipping native probe: TY_SOME_PROBE unset"
            text = transcript(passed=tuple(f"t{index}" for index in range(targets[target])), failed=tuple(known),
                              ignored=tuple(sorted(LANE.TY_IGNORED.get(target, ()))),
                              filtered=len(LANE.TY_FILTERED.get(target, ())), outputs=outputs)
            return (101 if known else 0), text, ()
        return answer

    def run_ty(self, **answer_options):
        base = Path(tempfile.mkdtemp(prefix="ty-", dir=self.output))
        context = {"source": base / "export", "target_dir": base / "ty-target",
                   "patches": [], "cache_dir": base / "cache", "replay_dir": base / "dump"}
        (context["target_dir"] / "debug").mkdir(parents=True)
        (context["target_dir"] / "debug" / LANE.TY_BINARY).write_bytes(b"ty")
        module = context["replay_dir"] / "AddTwoTest" / "trust-ir-modules"
        module.mkdir(parents=True)
        (module / "000001.metadata.json").write_text(json.dumps({"stage": LANE.TY_REPLAY_STAGE}))
        calls: dict = {}
        answer = self.ty_answer(context, calls, **answer_options)

        class Runner(FakeRunner):
            def run(self, command, log_name, timeout, **kwargs):
                self.calls.append(log_name)
                returncode, text, leftovers = answer(list(command), log_name, kwargs.get("stdout_path"),
                                                     kwargs.get("extra_environment"))
                (self.output / log_name).write_text(text)
                return {"command": list(command), "returncode": returncode, "log": log_name,
                        "temporary_leftovers": list(leftovers), "temporary_leftover_files": {}}

        result: dict = {"classes": [], "errors": []}
        output = base / "logs"
        output.mkdir()
        with contextlib.redirect_stdout(io.StringIO()):
            LANE.run_ty_targets(Runner(output, None), ARGS, context, result, COHORT)
        return LANE.summarize_ty(result), calls

    def test_ty_targets_run_with_their_filters_and_count_only_ty_passes(self):
        result, calls = self.run_ty()
        self.assertEqual((result["status"], result["classes"]), ("pass", []), result["errors"][:3])
        self.assertEqual([row["target"] for row in result["targets"] if row["status"] != "pass"], [])
        self.assertEqual(result["executed_passes"], sum(LANE.TY_TARGETS.values()))
        self.assertEqual(result["lane_target_passes"], sum(minimum for _, minimum in LANE.TY_LANE_TARGETS.values()))
        self.assertEqual(set(result["not_in_lane"]), set(LANE.TY_CRATES_NOT_IN_LANE))
        self.assertEqual(result["build"]["status"], "pass")
        self.assertEqual(result["canary"]["status"], "pass")
        self.assertTrue(all(row["status"] == "pass" for row in result["workloads"]), result["workloads"][0])
        self.assertEqual(result["replay"]["status"], "pass", result["replay"]["errors"])
        # Each env-gated test is skipped by exact name, never run and never counted.
        for target, rows in LANE.TY_FILTERED.items():
            command = calls[f"ty--{target}.log"]
            tail = command[command.index("--") + 1:]
            self.assertIn("--exact", tail)
            for name, _ in rows:
                self.assertIn(name, tail[tail.index("--skip") :])
            row = next(row for row in result["targets"] if row["target"] == target)
            self.assertEqual(row["filtered"], sorted(name for name, _ in rows))
        self.assertNotIn("--exact", calls["ty--valueref_set_union_source_compile_only.log"])
        owners = {row["target"]: row["owner"] for row in result["targets"]}
        self.assertEqual({name for name, owner in owners.items() if owner == "lane"}, set(LANE.TY_LANE_TARGETS))
        self.assertEqual(set(owners) - set(LANE.TY_LANE_TARGETS), set(LANE.TY_TARGETS))

    def test_ty_skip_notices_and_build_leftovers_fail_the_step(self):
        result, _ = self.run_ty(skip_notice_in="value_ref_native")
        failing = {row["target"]: row["classes"] for row in result["targets"] if row["status"] != "pass"}
        self.assertEqual(failing, {"value_ref_native": ["consumer-inventory-drift"]})
        self.assertEqual(result["status"], "fail")
        leaked, _ = self.run_ty(build_leftovers=("core.1",))
        self.assertEqual((leaked["build"]["status"], leaked["build"]["classes"]), ("fail", ["temporary-leftovers"]))
        # A leftover is judged, not a reason to stop: every target still ran.
        self.assertEqual(len(leaked["targets"]), len(LANE.TY_TARGETS) + len(LANE.TY_LANE_TARGETS))
        self.assertEqual(leaked["classes"], ["temporary-leftovers"])

    def test_lane_targets_are_copied_into_the_export_only(self):
        source = self.output / "export"
        tests = source / LANE.TY_PACKAGE_DIR / "tests"
        with self.assertRaises(LANE.LaneError) as raised:
            LANE.inject_lane_targets(source)
        self.assertEqual(raised.exception.klass, "consumer-inventory-drift")
        tests.mkdir(parents=True)
        injected = LANE.inject_lane_targets(source)
        self.assertEqual([row["target"] for row in injected], list(LANE.TY_LANE_TARGETS))
        for row in injected:
            path, _ = LANE.TY_LANE_TARGETS[row["target"]]
            self.assertEqual((source / row["path"]).read_bytes(), path.read_bytes())
            self.assertEqual(row["sha256"], LANE.sha256_file(path))
        # A pin that already carries the name is drift, never overwritten.
        with self.assertRaises(LANE.LaneError) as raised:
            LANE.inject_lane_targets(source)
        self.assertEqual(raised.exception.klass, "consumer-inventory-drift")


class MatrixWiringTests(unittest.TestCase):
    def test_the_darwin_matrix_requires_this_lanes_pass_line(self):
        source = (ROOT / "scripts" / "run_darwin_full_test_matrix.py").read_text()
        self.assertIn('CONSUMER_LANE = SCRIPTS / "check_darwin_consumers.py"', source)
        self.assertIn(f'"{LANE.SUCCESS_LINE}"', source)


if __name__ == "__main__":
    unittest.main()
