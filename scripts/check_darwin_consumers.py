#!/usr/bin/env python3
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Copyright 2026 Andrew Yates | License: Apache-2.0
"""Run the required Darwin downstream-consumer lane (ledger L13-P8).

The lane executes trust-cg's downstream consumers at this checkout's source on
an aarch64-apple-darwin host, with the installed Trust package
(`scripts/trust_cargo.sh`, `targo --unverified`; no proof claim about any
build), and writes report.json plus one log per step:

1. preflight: the Darwin floor's identity record (`check_darwin_aarch64.py`:
   host, Trust package, host tools, source fingerprint), this checkout's
   trust-ir/Clean cohort, and every sibling checkout's HEAD.
2. cg-contracts: trust-cg-codegen's TY and AY consumer-contract targets (the
   full matrix's integration-ty and integration-ay-contracts shards plus
   `o3_ty_materialized_return`), each a bounded `trust_cargo.sh test` judged
   like a Darwin floor target, with a minimum of executed passes.
3. abi-xback: `benchmarks/abi-xback/run.sh --selftest`, a release build of the
   rustc bridge backend from this checkout (refused when older than any build
   input), then the generated cross-backend run, seeds 1-40 at O0-O3 in both
   directions (LLVM caller x trust-cg callee, trust-cg caller x LLVM callee),
   linked by ld64 through the host-resolved `cc` (run.sh proves the link
   line invokes that `cc` before the first combination).
4. ty: the TY repository at a pinned commit, re-pointed at this checkout:
   a. source: the pinned commit is exported with `git archive` (never a
      working tree) from the sibling checkout when it holds that commit, else
      from the lane's object cache; `--fetch-consumers` fetches exactly that
      commit into the cache. A pin that resolves nowhere is refused.
   b. cohort: TY's trust-cg crates are patched (`--config patch`) to this
      checkout's crates, and TY's trust-ir and Clean revisions are rewritten to
      the trust-ir revision this checkout pins and the Clean revision its lock
      carries (one universe of each, as TY's manifest requires).
   c. lock: resolution starts from TY's committed Cargo.lock. Every package it
      adds must belong to a substituted family or, if third-party, be the
      version this checkout's own lock pins, and no cohort family may remain
      at another source; removals are recorded. Anything else is lock drift.
   d. build and run every `tla-trust-cg` (features `native`) test target with
      `--locked --offline`, plus the lane's own amended copy of TY's PowInt
      test (TY_LANE_TARGETS), the `native_bfs_mcl_canary` example, and a
      TLC-style workload: `ty check` of pinned specs on TY's trust-cg backend
      and on its interpreter, which must agree on verdict and state counts,
      with the trust-cg run on TY's native tier.
5. absent consumers: aterm has no trust-cg workload on this host (named,
   never counted); the AY repository's consumer suites and TY's other
   trust-cg-consuming crates are not in this lane (named in the report).

Failures carry a named class (FAILURE_CLASSES). Consumer-owned failures are
listed by exact test name with the output that identifies them; a listed
failure that passes or fails differently fails the lane, so the list only
shrinks. A failure owned by trust-cg itself on this host (a host residual) is
listed the same way but never passes: it keeps the lane red under its own
class, distinct from an unlisted regression. A test whose body returns early
unless an environment variable is set is filtered by exact name with its
reason, so it is never counted as an executed pass. Every bounded step's own
TMPDIR must be empty afterwards (TY's library suite may leave its one listed
cache record). `--only STEP` runs selected steps and is never a lane pass.

This is testing evidence for the consumers' current domains. It is not proof,
not a Trust-verified build, not a performance measurement and not a Linux
result; the Linux half of L13-P8 stays open.
"""

from __future__ import annotations

import argparse
import hashlib
import importlib.util
import json
import os
from dataclasses import dataclass
from datetime import datetime, timezone
from pathlib import Path
import re
import shutil
import signal
import subprocess
import sys
import tempfile
import time
from typing import Iterable, Sequence


ROOT = Path(__file__).resolve().parents[1]
SCRIPTS = ROOT / "scripts"
SCHEMA = "trust-cg-darwin-consumer-lane-v1"
FLOOR_SCRIPT = SCRIPTS / "check_darwin_aarch64.py"
TRUST_CARGO = SCRIPTS / "trust_cargo.sh"
TIMEOUT_RUNNER = SCRIPTS / "run_with_timeout.py"
BRIDGE_BACKEND = SCRIPTS / "bridge_backend.py"
ABI_XBACK = ROOT / "benchmarks" / "abi-xback" / "run.sh"
BRIDGE_DIR = ROOT / "crates" / "rustc-codegen-trust-cg"
BRIDGE_TARGET = BRIDGE_DIR / "target-bridge"
# Consumer builds and the pinned-commit object cache live under this
# checkout's own target directory and are reused across runs. Exported
# consumer sources may not: Cargo reads every .cargo/config.toml above the
# directory it runs in, so a consumer exported under this checkout would build
# with trust-cg's own Cargo configuration. Exports go to a cache directory
# outside it (default_consumer_cache), keyed by this checkout's path so
# worktrees do not share one, at a stable path so Cargo's fingerprints survive
# re-exports.
LANE_CACHE = ROOT / "target" / "consumer-lane"
SUCCESS_LINE = "Darwin consumer lane: PASS"
OUTPUT_PREFIX = "trust-cg-darwin-consumers-"
STEPS = ("cg-contracts", "abi-xback", "ty")

FAILURE_CLASSES = {
    "cg-contract-failed": "a trust-cg-side consumer-contract target failed, skipped or fell below its minimum",
    "host-proof-promotion-residual": ("a listed trust-cg host residual failed exactly as recorded (strict proof "
                                      "promotion this host cannot discharge): named and kept red, never a pass"),
    "abi-selftest-failed": "abi-xback's result-contract self-test failed",
    "bridge-build-failed": "the release bridge backend did not build from this checkout",
    "bridge-backend-stale": "the bridge backend is older than one of its build inputs",
    "abi-mismatch": "a cross-backend call returned a different exit code than the LLVM x LLVM oracle",
    "abi-backend-decline": "the trust-cg backend declined a generated half",
    "abi-skip": ("a generator, oracle or link step failed, so a combination was not executed (a link "
                 "failure keeps the linker's diagnostic)"),
    "abi-incomplete": "the abi-xback run did not report its full requested domain",
    "consumer-pin-unavailable": "the pinned consumer commit is in neither the sibling checkout nor the lane's object cache",
    "consumer-export-failed": "the pinned consumer commit could not be exported",
    "consumer-cohort-substitution": "the consumer manifest could not be re-pointed at this checkout's cohort",
    "consumer-resolution-failed": "Cargo could not resolve the consumer against this checkout's cohort",
    "consumer-lock-drift": "resolution changed a package outside the substituted cohort families",
    "consumer-cohort-split": "the resolved lock carries a cohort family at a source other than this checkout's",
    "consumer-build-failed": "the consumer does not build against this checkout",
    "consumer-inventory-drift": "the consumer's test targets, ignored tests or pass counts differ from the pinned inventory",
    "consumer-test-regression": "a consumer test failed that is not a recorded consumer-owned failure",
    "consumer-known-failure-changed": "a recorded consumer-owned failure passed or failed differently (the list only shrinks)",
    "consumer-canary-failed": "the consumer's native canary did not complete with its success line",
    "consumer-replay-failed": ("the consumer's replay-corpus test did not compile every dumped module identically, "
                               "or the workloads dumped none"),
    "workload-failed": "a workload run exited abnormally, timed out or wrote no result document",
    "workload-mismatch": "the trust-cg and interpreter backends disagree, or differ from the pinned verdict and counts",
    "workload-not-native": "the trust-cg workload run did not execute on the consumer's trust-cg native tier",
    "timeout": "a bounded step exceeded its time limit",
    "temporary-leftovers": "a step left entries in its own TMPDIR",
    "runner-error": "the lane runner could not complete a step",
}

# ---------------------------------------------------------------------------
# Inventory: CG-side consumer contracts.
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class KnownFailure:
    klass: str
    reason: str
    # Substrings the failing test's captured output must contain; a value is
    # formatted with the run's cohort ({trust_ir_rev}, {clean_rev}).
    output: tuple[str, ...]
    # A trust-cg-owned host residual rather than a consumer-owned failure: it
    # must still fail exactly as recorded, and it fails its target under
    # `klass` (never `pass`), so the lane cannot go green on a defect the
    # Darwin floor counts as red.
    residual: bool = False


@dataclass(frozen=True)
class ContractTarget:
    package: str
    target: str
    # Executed passes the target must report on aarch64-apple-darwin.
    minimum: int
    # Exact test names passed to libtest's --skip, each with the reason it
    # cannot execute in this lane; the rollup must filter exactly these.
    filtered: tuple[tuple[str, str], ...] = ()
    # Exact test names that fail on this host for a named, non-consumer reason.
    known_failures: tuple[tuple[str, KnownFailure], ...] = ()


REPLAY_BUNDLE_REASON = (
    "reads a real TY crash replay bundle named by TRUST_CG_TY_REPLAY_BUNDLE; TY writes the crash and callout "
    "records of such a bundle only when a native callout faults, so a passing TY run produces none"
)
PROOF_PROMOTION_RESIDUAL = KnownFailure(
    klass="host-proof-promotion-residual",
    reason=("the compile-only BCP observation is refused by strict proof promotion on this host (frame opcodes "
            "StpPreIndex/AddRI/Movz/LdpPostIndex lack an independently replayed proof), the same host residual as "
            "the known jit_fail_closed_proof_policy failures; measured identically at origin/main 2dde71362"),
    # The whole refusal, opcode set included: a fifth uncovered opcode or
    # another proof entry is a changed failure, not this residual.
    output=("compile-only SAT BCP observation diagnostics",
            "proof promotion rejected for target Aarch64: non_verified proof entry opcode_inventory_instruction_0 "
            "in ay_sat_watch_bcp_status_probe: emitted opcode inventory found 4 uncovered non-pseudo opcode(s) "
            "across 4 distinct opcode(s) [AArch64::StpPreIndex, AArch64::AddRI, AArch64::Movz, "
            "AArch64::LdpPostIndex]"),
    residual=True,
)

# trust-cg-codegen's TY and AY consumer-contract targets: the full matrix's
# integration-ty shard plus the TY-materialized return regression from
# integration-e2e-misc (`ty_bfs_minimal` is a Darwin floor target and runs
# there), and its integration-ay-contracts shard plus the AY JIT regressions
# of integration-jit-runtime and integration-jit-artifacts. `x86_64_sysv_ay_abi`
# checks the x86-64 SysV ABI only and belongs to no AArch64 lane.
CG_CONTRACT_TARGETS = (
    ContractTarget("trust-cg-codegen", "jit_ty_canary_allowlist", 9),
    ContractTarget("trust-cg-codegen", "ty_bfs_minimal_o1_o3_summary", 2),
    ContractTarget("trust-cg-codegen", "ty_callback_abi_call_clobber", 3),
    ContractTarget("trust-cg-codegen", "ty_edge_copy_loop_call", 1),
    ContractTarget("trust-cg-codegen", "ty_mcl_fused_parent_loop", 10),
    ContractTarget("trust-cg-codegen", "ty_native_bfs_no_action_parent_loop", 1),
    ContractTarget("trust-cg-codegen", "ty_reducer_evidence_packet", 3),
    ContractTarget("trust-cg-codegen", "ty_request_1_1_replay_bundle_reducer", 5, filtered=(
        ("env_ty_request_replay_bundle_jit_invokes_in_child_when_present", REPLAY_BUNDLE_REASON),
        ("env_ty_request_replay_bundle_low_level_compile_raw_alloc_size_matches_proof_when_present",
         REPLAY_BUNDLE_REASON),
        ("env_ty_request_replay_bundle_parses_and_compiles_when_present", REPLAY_BUNDLE_REASON),
    )),
    ContractTarget("trust-cg-codegen", "ty_runtime_value_replay_contract", 3),
    ContractTarget("trust-cg-codegen", "o3_ty_materialized_return", 1),
    ContractTarget("trust-cg-codegen", "jit_ay_canary_allowlist", 13),
    ContractTarget("trust-cg-codegen", "ay_lra_manifest_contract", 46),
    ContractTarget("trust-cg-codegen", "ay_lra_runtime_value_replay", 2),
    ContractTarget("trust-cg-codegen", "ay_pb_pbo_checked_arithmetic_manifest_contract", 3),
    ContractTarget("trust-cg-codegen", "ay_sat_bcp_differential", 12),
    ContractTarget("trust-cg-codegen", "ay_sat_bcp_install_gate", 0, known_failures=(
        ("sat_bcp_executable_artifact_installs_only_after_manifest_gate_and_runs_via_bound_contract",
         PROOF_PROMOTION_RESIDUAL),
        ("sat_bcp_gate_fails_closed_for_missing_wrong_and_unrunnable_artifact_routes", PROOF_PROMOTION_RESIDUAL),
    )),
    ContractTarget("trust-cg-codegen", "ay_sat_bcp_manifest_contract", 4),
    ContractTarget("trust-cg-codegen", "ay_sat_helper_replacement_differential", 9),
    ContractTarget("trust-cg-codegen", "ay_sat_helper_replacement_install_gate", 6),
    ContractTarget("trust-cg-codegen", "ay_sat_helper_replacement_manifest_contract", 9),
    ContractTarget("trust-cg-codegen", "jit_ay_lra_status_abi", 8),
    ContractTarget("trust-cg-codegen", "jit_ay_pb_pbo_checked_arithmetic", 3),
    ContractTarget("trust-cg-codegen", "jit_ay_simplex_pivot", 4),
    ContractTarget("trust-cg-codegen", "jit_ay_widened_overflow_regression", 3),
)
# The floor's broad skip spelling ("Skipping ...", "[skip]"), applied to every
# target's transcript except libtest's own result and test-name lines (a test
# or module may be named `skip`). TY's tests print it when an environment
# guard returns early; such a test is filtered by name instead (TY_FILTERED).
BROAD_SKIP = re.compile(r"(?:^|\.\.\.\s*|\[)\s*(?:skip|skipped|skipping)\b", re.MULTILINE | re.IGNORECASE)

# ---------------------------------------------------------------------------
# Inventory: the TY consumer.
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class ConsumerPin:
    name: str
    url: str
    commit: str
    sibling: Path
    # Top-level paths of the commit that no consumer step reads (TY's
    # `reports/` is 3.8 GB of retained evidence).
    export_exclude: tuple[str, ...]


# TY `main` of 2026-10-14. Its own manifest pins trust-cg 7d845816, trust-ir
# 56a11da6 and Clean 023d17b6; the lane replaces those three with this
# checkout's cohort. The sibling checkout on the qualifying host was at
# 53e241c3 (2026-06-28), which predates TY's exact-revision pins and does not
# compile against trust-ir 0.14, so the pin comes from the lane cache.
TY = ConsumerPin(
    name="ty",
    url="https://github.com/alabsystems/ty.git",
    commit="9ce24d4de537d4c55d00b6bb16433dd8ad20e4dc",
    sibling=Path.home() / "ty",
    export_exclude=("reports",),
)
TY_PACKAGE = "tla-trust-cg"
TY_FEATURES = ("native",)
TY_BINARY_PACKAGE = "tla-cli"
TY_BINARY = "ty"
TY_CANARY = "native_bfs_mcl_canary"
TY_CANARY_LINE = "native BFS MCL canary passed: state_len=89, actions=27, parents=4"
# Every tla-trust-cg test target at the pin, with the minimum executed passes
# on this host; "lib" is the library's unit-test suite. A target the pin adds
# or removes is inventory drift.
TY_TARGETS = {
    "lib": 1339,
    "borrowed_parent_membership_no_alloc": 1,
    "coffeecan_record_set_native": 2,
    "compact_mixed_domain_func_apply_native": 11,
    "compact_model_value_func_apply_native": 2,
    "compact_model_value_func_except_native": 1,
    "ewd998_inv_native_initial_state": 3,
    "ewd_pending_sum_native": 1,
    "exact_callback_identity": 2,
    "extern_symbols_present": 6,
    "filtered_function_set_next_state_loop_native": 9,
    "mc_glue_hosted_units": 3,
    "mckvs_set_merge_native": 3,
    "nested_next_state_loop_native": 17,
    "parameterized_entry_compile_only": 1,
    "parameterized_family_entry_compile_only": 1,
    "pinned_purity_authority": 2,
    "pow_int_typed_native": 0,
    "producer_head_api_visibility": 1,
    "record_set_subset_eq_native": 3,
    "scalar_string_store_var_native": 2,
    "select_seq_lifted_native": 4,
    "semantic_predicate_native": 152,
    "seq_concat_capacity_native": 2,
    "seq_subset_compact_header_native": 1,
    "seq_subset_proc_native": 3,
    "set_canonicalization_native": 3,
    "string_concat_name_id_native": 2,
    "tla_ops_const_builtin_smoke": 6,
    "tla_ops_ffi_abort_subprocess": 1,
    "tla_ops_quantifier_smoke": 6,
    "tla_ops_record_func_smoke": 11,
    "tla_ops_seq_smoke": 10,
    "tla_ops_set_smoke": 9,
    "tla_ops_tuple_smoke": 6,
    "typed_predicate_source_native": 1,
    "value_ref_native": 2,
    "valueref_bag_ops_source_compile_only": 4,
    "valueref_family_entry_source_compile_only": 1,
    "valueref_iteration_source_compile_only": 2,
    "valueref_set_diff_source_compile_only": 2,
    "valueref_set_intersect_source_compile_only": 2,
    "valueref_set_union_source_compile_only": 20,
    "valueref_subseteq_source_compile_only": 2,
    "valueref_successor_yield_source_compile_only": 2,
}
# Targets that compile no test on aarch64-apple-darwin: recorded, never counted.
TY_COMPILED_OUT = {
    "host_target_compat": "every test is cfg-gated to another host",
}
# Tests whose body returns before doing anything unless an environment variable
# is set, passed to libtest as `--exact --skip`, by target, each with the
# reason the lane cannot run it. The rollup must filter exactly these, so none
# is counted as an executed pass.
TY_FILTERED: dict[str, tuple[tuple[str, str], ...]] = {
    "lib": (("compile::tests::test_linked_trust_ir_probe_publication_allocation_from_env",
             "a manual allocation probe: it prints 'skipping linked trust-ir native allocation probe' and returns "
             "unless TY_TRUST_CG_LINKED_TRUST_IR_PROBE_JSON names a captured linked trust-ir module, which no TY run "
             "writes"),),
    "tla_ops_ffi_abort_subprocess": (("child_tla_ops_malformed_handle_abort_entry",
                                      "the subprocess half of tla_ops_malformed_handle_aborts_child_process: it "
                                      "returns silently unless TY_TRUST_CG_RUN_FFI_ABORT_CHILD is set, and the "
                                      "parent test (which runs) re-executes it with that variable"),),
}
# Lane-owned test targets copied into the exported TY tree (never into a TY
# checkout) before resolution, with their minimum executed passes. Each is
# recorded by SHA-256 and counted apart from TY's own targets.
# `trust_cg_lane_pow_int_semantics` is TY's `pow_int_typed_native` test with
# its `0^0` expectation changed to the TypeMismatch error TY's lowering emits
# on purpose, so the boundary, exponent-domain and overflow assertions that
# TY's own test never reaches (it panics at `0^0`) execute natively.
TY_PACKAGE_DIR = Path("crates") / "tla-trust-cg"
TY_LANE_TARGETS: dict[str, tuple[Path, int]] = {
    "trust_cg_lane_pow_int_semantics": (SCRIPTS / "consumer_lane_ty_pow_int_semantics.rs", 1),
}
# TY crates at the pin that depend on tla-trust-cg (so on trust-cg) and whose
# own tests this lane does not run, with the description each crate's manifest
# gives: named in the report, never counted. tla-check carries TY's native
# dispatch and its committed cross-backend parity tests (for example
# tests/trust_cg_state_graph_parity.rs); tla-cli is built for the workloads.
TY_CRATES_NOT_IN_LANE = {
    "tla-check": "TY model checker - evaluation engine and state exploration (tla-trust-cg features native, "
                 "machine-code-cache)",
    "tla-cli": "TY command line interface (built here as the `ty` binary for the workloads; its tests are not run)",
    "tla-model-native": "generator lowering of Model IR v0 to Core TrustIR (optional tla-trust-cg, feature jit)",
    "tla-model-normalizer": "W1 route-N normalizer: a TLA+ model to Model IR v0 units",
    "tla-petri": "Petri net model checking frontend and MCC engine (default feature trust-cg-petri-native)",
    "tla-shape-ops": "W4 value-op entry for route N, legalized to Core TrustIR",
}
# The replay-corpus target: TY's own ignored test that compiles every
# `compile_module_native.pre_jit` TrustIR module of a replay-artifact dump
# through trust-cg four ways and requires the sealed link to leave every
# published image unchanged. The lane runs it on the dump its own trust-cg
# workload runs write (TY_TRUST_CG_REPLAY_ARTIFACT_DIR).
TY_REPLAY_TEST = "compile::tests::upstream_adoption_identity_tests::upstream_adoption_identity_over_replay_dump"
TY_REPLAY_STAGE = "compile_module_native.pre_jit"
# Temporary entries a consumer target may leave in its own TMPDIR, by target:
# (entry-name pattern, pattern every file inside must match, at most this many).
# TY's library suite sometimes leaves one tempfile directory holding a single
# artifact-cache metadata record (four of five runs on 2026-10-14, one of them
# at TY's own pins, so a race in TY's tests rather than a trust-cg effect); any
# other leftover fails. Whether it occurred is recorded with the target.
TY_TEMPORARY_LEAKS: dict[str, tuple[str, str, int]] = {
    "lib": (r"\.tmp[A-Za-z0-9]{6}", r"[0-9a-f]{64}\.meta\.json", 1),
}
# Tests the pin itself marks #[ignore], by target; the replay-corpus test runs
# in its own step.
TY_IGNORED: dict[str, frozenset[str]] = {
    "lib": frozenset({TY_REPLAY_TEST}),
}


# Consumer-owned failures at the pin, by (target, exact test name). The last
# two fail identically at TY's own cohort (trust-cg 7d845816, trust-ir
# 56a11da6, Clean 023d17b6; the baseline in the dated record), and the first
# is TY's self-audit of the very pins this lane substitutes.
TY_KNOWN_FAILURES: dict[tuple[str, str], KnownFailure] = {
    ("lib", "artifact_cache::tests::test_cache_version_tracks_exact_workspace_and_lock_pins"): KnownFailure(
        klass="consumer-own-pin-audit",
        reason=("TY audits that its cache version names its own committed trust-ir pin; the lane "
                "substitutes this checkout's trust-ir revision by design (passes at TY's own pins)"),
        output=('left: "{trust_ir_rev}"',),
    ),
    ("pow_int_typed_native", "typed_native_pow_matches_tla_integer_domain_and_overflow_semantics"): KnownFailure(
        klass="consumer-test-contradiction",
        reason=("TY's PowInt lowering at the pin routes 0^0 to its TypeMismatch error on purpose ('TLC: 0^0 is "
                "undefined', crates/tla-ir/src/lower/arithmetic.rs), while this test still expects 1; the lane's "
                "trust_cg_lane_pow_int_semantics target runs the same predicate with TY's 0^0 semantics and every "
                "assertion this test never reaches (the i64::MIN boundary, the u32 exponent domain, overflow)"),
        output=("zero to the zero power", "err_kind: TypeMismatch"),
    ),
    ("valueref_bag_ops_source_compile_only",
     "source_function_bag_update_chain_lowers_and_executes_without_legacy_helpers"): KnownFailure(
        klass="consumer-frontend-refusal",
        reason=("TY's own TIR-to-bytecode lowering refuses a lazy LET before any trust-cg compile; "
                "trust-cg is never reached"),
        output=("TIR to bytecode: Unsupported(\"lazy LET 'reduced'",),
    ),
}

# TLC-style workloads: `ty check <spec> --config <cfg>` on the trust-cg backend
# and on the interpreter, sequential BFS without reductions (the flags TY
# documents as giving TLC-identical counts; TLC itself is not run).
# (spec, cfg, status, error_code or None, states_found, transitions).
TY_WORKLOADS = (
    ("AddTwoTest", "AddTwoTest", "ok", None, 5, 5),
    ("TrustCgRecordSequenceParity", "TrustCgRecordSequenceParity", "ok", None, 16, 24),
    ("SpanTreeMinimal", "SpanTreeMinimal", "ok", None, 1236, 10277),
    ("MCBakery", "MCBakery", "ok", None, 2303, 10658),
    ("FlatSymScale", "FlatSymScale", "ok", None, 9610, 83390),
    ("TokenRing", "TokenRing", "ok", None, 46656, 202176),
    ("test19", "test19", "ok", None, 400000, 400000),
    ("PowInvariantViolated", "PowInvariantViolated", "error", "TLC_INVARIANT_VIOLATED", 5, 4),
    ("RangeInvariantViolated", "RangeInvariantViolated", "error", "TLC_INVARIANT_VIOLATED", 2, 2),
)
TY_WORKLOAD_FLAGS = ("--workers", "1", "--bfs-only", "--no-reduction", "--output", "json")
WORKLOAD_STATISTICS = ("states_found", "states_distinct", "states_initial", "transitions")
WORKLOAD_RESULT_FIELDS = ("status", "error_type", "error_code", "violated_property")
NATIVE_TIER_PREFIX = "trust-cg native"
NATIVE_ROUTES = ("compiled_bfs_fused",)

# Consumers with no trust-cg workload on this host: named, never counted.
ABSENT_CONSUMERS = {
    "aterm": {
        "status": "absent",
        "reason": ("aterm builds no trust-cg or trust-ir crate: no Cargo manifest under the aterm checkout "
                   "names one, and its PROOF_CARRYING_PERFORMANCE.md lists trust-cg as research "
                   "('aterm is not on trust-ir'); atpkg only packages the toolchain"),
        "sibling": Path.home() / "aterm",
    },
    "ay": {
        "status": "not-in-lane",
        "reason": ("the AY repository's trust-cg-backend suites (ay-jit, ay-sat's trust-cg-jit-matrix BCP "
                   "kernel) are not executed here; the lane runs trust-cg's AY contract targets only, and "
                   "the '40/40 consumer regressions' remain AY-repository results"),
        "sibling": Path.home() / "ay",
    },
}

# abi-xback's required domain.
ABI_SEEDS = (1, 40)
ABI_OPT_LEVELS = ("0", "1", "2", "3")
ABI_SELFTEST_LINE = "abi-xback result-contract selftest: positive arm + 4 rejection arms"
ABI_SUMMARY = re.compile(
    r"^abi-xback: (\d+) MATCH, (\d+) MISMATCH, (\d+) declined, (\d+) skipped$", re.MULTILINE)
ABI_DIRECTIONS = re.compile(
    r"^abi-xback: directions: llvm-caller x tcg-callee (\d+) MATCH; tcg-caller x llvm-callee (\d+) MATCH;",
    re.MULTILINE)
ABI_LINKER = re.compile(r"^abi-xback: host aarch64-apple-darwin; linker (\S.*) \(ld64 ", re.MULTILINE)
# run.sh's proof that rustc's link line invokes that linker.
ABI_LINK_PROBE = re.compile(r"^abi-xback: link probe: rustc links with (\S.*)$", re.MULTILINE)

TEST_RESULT = re.compile(r"^test (.+) \.\.\. (ok|FAILED|ignored)(?:, .*| <.*>)?$")
STDOUT_HEADER = re.compile(r"^---- (.+) stdout ----$")
ROLLUP = re.compile(r"^test result: \S+\. (\d+) passed; (\d+) failed; (\d+) ignored; (\d+) measured; (\d+) filtered out;")
# An explicit runtime skip spelling (matrix_results.SKIP's producer form).
SKIP = re.compile(r"^\s*SKIP(?=[:\s])")
GIT_SOURCE = re.compile(r"^git\+(?P<url>[^?#]+)\?rev=(?P<rev>[0-9a-f]{40})#(?P<precise>[0-9a-f]{40})$")
TRUST_IR_URL = "https://github.com/alabsystems/trust-ir.git"
CLEAN_URL = "https://github.com/alabsystems/clean.git"
TRUST_CG_URL = "https://github.com/alabsystems/trust-cg.git"


def _load(name: str, path: Path):
    spec = importlib.util.spec_from_file_location(name, path)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"required helper is missing: {path}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


def floor():
    """The Darwin floor runner, loaded on first use (it probes nothing at import)."""
    if "_darwin_consumers_floor" not in sys.modules:
        _load("_darwin_consumers_floor", FLOOR_SCRIPT)
    return sys.modules["_darwin_consumers_floor"]


def utc_now() -> str:
    return datetime.now(timezone.utc).isoformat()


def sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for block in iter(lambda: handle.read(1 << 20), b""):
            digest.update(block)
    return digest.hexdigest()


def write_report(path: Path, report: dict) -> None:
    temporary = path.with_suffix(".json.tmp")
    temporary.write_text(json.dumps(report, indent=2, default=str) + "\n", encoding="utf-8")
    temporary.replace(path)


# ---------------------------------------------------------------------------
# Cargo manifests and locks (text forms, so no TOML library is needed).
# ---------------------------------------------------------------------------

def lock_packages(text: str) -> set[tuple[str, str, str | None]]:
    """Every [[package]] of a Cargo.lock as (name, version, source or None for a path package)."""
    packages = set()
    for block in re.split(r"^\[\[package\]\]\s*$", text, flags=re.MULTILINE)[1:]:
        fields = dict(re.findall(r'^(name|version|source) = "([^"]*)"\s*$', block, flags=re.MULTILINE))
        if "name" not in fields or "version" not in fields:
            raise ValueError("Cargo.lock package without a name and version")
        packages.add((fields["name"], fields["version"], fields.get("source")))
    return packages


def git_source_revision(source: str | None, url: str) -> str | None:
    if source is None:
        return None
    match = GIT_SOURCE.match(source)
    if match is None or match["url"] != url:
        return None
    return match["rev"]


def cohort(root: Path = ROOT) -> dict:
    """This checkout's trust-ir pin (root manifest) and Clean revision (root lock)."""
    manifest = (root / "Cargo.toml").read_text(encoding="utf-8")
    trust_ir = set(re.findall(
        r'^trust-ir[a-z-]* = \{[^}\n]*git = "' + re.escape(TRUST_IR_URL) + r'", rev = "([0-9a-f]{40})"',
        manifest, flags=re.MULTILINE))
    if len(trust_ir) != 1:
        raise ValueError(f"expected one trust-ir revision in {root / 'Cargo.toml'}, found {sorted(trust_ir)}")
    packages = lock_packages((root / "Cargo.lock").read_text(encoding="utf-8"))
    clean = {git_source_revision(source, CLEAN_URL) for name, _, source in packages if name.startswith("clean-")}
    clean.discard(None)
    if len(clean) != 1:
        raise ValueError(f"expected one Clean revision in {root / 'Cargo.lock'}, found {sorted(clean)}")
    return {"trust_ir_rev": trust_ir.pop(), "clean_rev": clean.pop()}


def rewrite_manifest(text: str, target: dict) -> tuple[str, list[dict]]:
    """Re-point a consumer's trust-ir and Clean Git revisions at `target`'s cohort.

    Only `rev = "<40 hex>"` of a dependency on exactly those two URLs changes;
    every other byte is kept. Returns the new text and one record per changed line.
    """
    changes = []
    lines = text.splitlines(keepends=True)
    for index, line in enumerate(lines):
        for url, key in ((TRUST_IR_URL, "trust_ir_rev"), (CLEAN_URL, "clean_rev")):
            match = re.search(r'git = "' + re.escape(url) + r'", rev = "([0-9a-f]{40})"', line)
            if match is None:
                continue
            if match[1] != target[key]:
                lines[index] = line[:match.start(1)] + target[key] + line[match.end(1):]
                changes.append({"line": index + 1, "url": url, "from": match[1], "to": target[key]})
    return "".join(lines), changes


def trust_cg_dependencies(manifest: str) -> list[str]:
    """The trust-cg crates a consumer's root manifest takes from the trust-cg Git URL."""
    return sorted(set(re.findall(
        r'^(trust-cg-[a-z0-9-]+) = \{[^}\n]*git = "' + re.escape(TRUST_CG_URL) + r'"', manifest,
        flags=re.MULTILINE)))


def patch_configuration(crates: Sequence[str], root: Path = ROOT) -> list[str]:
    """Cargo `--config` arguments patching each trust-cg crate to this checkout."""
    arguments = []
    for name in crates:
        path = root / "crates" / name
        if not (path / "Cargo.toml").is_file():
            raise ValueError(f"consumer depends on {name}, which this checkout does not contain")
        arguments += ["--config", f'patch."{TRUST_CG_URL}".{name}.path="{path}"']
    return arguments


def family(name: str) -> str | None:
    if name.startswith("trust-cg-"):
        return "trust-cg"
    if name == "trust-ir" or name.startswith("trust-ir-"):
        return "trust-ir"
    if name.startswith("clean-"):
        return "clean"
    return None


def lock_problems(before: set, after: set, root_lock: set, target: dict, root: Path = ROOT) -> list[str]:
    """Named problems with a consumer lock re-resolved against this checkout's cohort."""
    problems = []
    for name, version, source in sorted(after - before, key=lambda row: (row[0], row[1], row[2] or "")):
        kind = family(name)
        if kind is None:
            if (name, version, source) not in root_lock:
                problems.append(f"consumer-lock-drift: added {name} {version} {source or 'path'}, "
                                "which this checkout's Cargo.lock does not pin")
    for name, version, source in sorted(after, key=lambda row: (row[0], row[1], row[2] or "")):
        kind = family(name)
        if kind == "trust-cg" and source is not None:
            problems.append(f"consumer-cohort-split: {name} {version} still resolves from {source}")
        elif kind == "trust-ir" and git_source_revision(source, TRUST_IR_URL) != target["trust_ir_rev"]:
            problems.append(f"consumer-cohort-split: {name} {version} resolves from {source or 'a path'}, "
                            f"not trust-ir {target['trust_ir_rev']}")
        elif kind == "clean" and git_source_revision(source, CLEAN_URL) != target["clean_rev"]:
            problems.append(f"consumer-cohort-split: {name} {version} resolves from {source or 'a path'}, "
                            f"not Clean {target['clean_rev']}")
    return problems


# ---------------------------------------------------------------------------
# Libtest transcripts.
# ---------------------------------------------------------------------------

def test_events(transcript: str) -> tuple[dict[str, str], dict[str, list[str]], list[tuple[int, ...]]]:
    """Named outcomes, each test's captured output, and the suite rollups of one transcript."""
    outcomes: dict[str, str] = {}
    outputs: dict[str, list[str]] = {}
    rollups: list[tuple[int, ...]] = []
    owner = None
    for raw in transcript.splitlines():
        line = raw.strip()
        header = STDOUT_HEADER.fullmatch(line)
        if header:
            owner = header[1]
            outputs.setdefault(owner, [])
            continue
        if owner is not None and raw.startswith(("successes:", "failures:", "---- ")):
            owner = None
        if owner is not None:
            outputs[owner].append(raw)
            continue
        result = TEST_RESULT.fullmatch(line)
        if result:
            outcomes[result[1]] = {"ok": "passed", "FAILED": "failed", "ignored": "ignored"}[result[2]]
            continue
        rollup = ROLLUP.match(line)
        if rollup:
            rollups.append(tuple(int(value) for value in rollup.groups()))
    return outcomes, outputs, rollups


def classify_consumer_target(
    target: str, returncode: int, transcript: str, *, minimum: int,
    known: dict[str, KnownFailure], ignored: frozenset[str], substitutions: dict,
    filtered: frozenset[str] = frozenset(), broad_skips: bool = False,
    regression_class: str = "consumer-test-regression",
) -> dict:
    """Judge one test target: exact failures, ignores and filters, minimum passes, no skips."""
    outcomes, outputs, rollups = test_events(transcript)
    errors: list[str] = []
    classes: set[str] = set()
    failed = sorted(name for name, outcome in outcomes.items() if outcome == "failed")
    observed_ignored = frozenset(name for name, outcome in outcomes.items() if outcome == "ignored")
    passed = sum(outcome == "passed" for outcome in outcomes.values())
    if returncode == 124:
        errors.append("timed out")
        classes.add("timeout")
    if len(rollups) != 1:
        errors.append(f"expected one completed test suite, observed {len(rollups)} rollups")
        classes.add("consumer-inventory-drift")
    elif rollups[0][:3] != (passed, len(failed), len(observed_ignored)) or rollups[0][4] != len(filtered):
        errors.append(f"rollup {rollups[0]} disagrees with the named results or the {len(filtered)} filtered tests")
        classes.add("consumer-inventory-drift")
    ran_filtered = sorted(filtered & set(outcomes))
    if ran_filtered:
        errors.append(f"filtered tests ran: {ran_filtered}")
        classes.add("consumer-inventory-drift")
    for name in failed:
        if name not in known:
            errors.append(f"unrecorded failure: {name}")
            classes.add(regression_class)
    known_failures = []
    for name, record in sorted(known.items()):
        text = "\n".join(outputs.get(name, []))
        missing = [marker.format(**substitutions) for marker in record.output
                   if marker.format(**substitutions) not in text]
        status = outcomes.get(name, "absent")
        if status != "failed":
            errors.append(f"recorded failure {name} is {status}; remove it from the list")
            classes.add("consumer-known-failure-changed")
        elif missing:
            errors.append(f"recorded failure {name} failed without its identifying output {missing}")
            classes.add("consumer-known-failure-changed")
        elif record.residual:
            # Matched exactly, and still red: a trust-cg host residual is
            # named by its own class and never counted as a pass.
            errors.append(f"listed host residual {name} failed as recorded ({record.klass})")
            classes.add(record.klass)
        known_failures.append({"test": name, "class": record.klass, "status": status, "reason": record.reason,
                               "residual": record.residual, "as_recorded": status == "failed" and not missing})
    if observed_ignored != ignored:
        errors.append(f"ignored tests {sorted(observed_ignored)} differ from the pinned {sorted(ignored)}")
        classes.add("consumer-inventory-drift")
    if passed < minimum:
        errors.append(f"executed passes {passed} are below the pinned minimum {minimum}")
        classes.add("consumer-inventory-drift")
    # libtest's own lines (a result line or a bare test name in its
    # successes/failures lists) are never skip notices, whatever the name.
    skips = [line.strip() for line in transcript.splitlines()
             if SKIP.match(line) or (broad_skips and BROAD_SKIP.search(line) and line.strip() not in outcomes
                                     and not TEST_RESULT.fullmatch(line.strip()))]
    if skips:
        errors.append(f"runtime SKIP lines: {skips[:3]}")
        classes.add("consumer-inventory-drift")
    # libtest exits 101 when a test failed; Cargo also exits 101 when a build
    # failed, which leaves no failed test in the transcript.
    if returncode == 101 and not failed:
        errors.append("cargo exited 101 without a failed test (a build or harness failure)")
        classes.add("consumer-build-failed")
    elif returncode not in (0, 101, 124):
        errors.append(f"cargo exited {returncode}")
        classes.add("consumer-build-failed")
    return {
        "target": target, "status": "fail" if errors else "pass", "errors": errors,
        "classes": sorted(classes), "passed": passed, "minimum": minimum, "failed": failed,
        "ignored": sorted(observed_ignored), "filtered": sorted(filtered), "known_failures": known_failures,
    }


# ---------------------------------------------------------------------------
# abi-xback and workload verdicts.
# ---------------------------------------------------------------------------

def classify_abi_run(returncode: int, transcript: str, expected_per_direction: int) -> dict:
    errors, classes = [], set()
    summary = ABI_SUMMARY.findall(transcript)
    directions = ABI_DIRECTIONS.findall(transcript)
    counts = None
    if len(summary) != 1 or len(directions) != 1:
        errors.append("the run printed no single summary and direction line")
        classes.add("abi-incomplete")
    else:
        match, mismatch, declined, skipped = (int(value) for value in summary[0])
        callee, caller = (int(value) for value in directions[0])
        counts = {"match": match, "mismatch": mismatch, "declined": declined, "skipped": skipped,
                  "llvm_caller_x_tcg_callee": callee, "tcg_caller_x_llvm_callee": caller}
        if mismatch:
            classes.add("abi-mismatch")
        if declined:
            classes.add("abi-backend-decline")
        if skipped:
            classes.add("abi-skip")
        if (callee, caller) != (expected_per_direction, expected_per_direction) \
                or match != 2 * expected_per_direction:
            errors.append(f"expected {expected_per_direction} MATCH in each direction, observed {callee} and {caller}")
            if not (mismatch or declined or skipped):
                classes.add("abi-incomplete")
        if mismatch or declined or skipped:
            errors.append(f"{mismatch} MISMATCH, {declined} declined, {skipped} skipped")
    named = [line for line in transcript.splitlines() if line.startswith(("MISMATCH ", "DECLINED ", "SKIPPED "))]
    if returncode != 0:
        errors.append(f"run.sh exited {returncode}")
        # run.sh exits 1 on any mismatch, decline or skip; only an exit the
        # named outcomes do not explain is an incomplete run.
        if returncode == 124:
            classes.add("timeout")
        elif not classes & {"abi-mismatch", "abi-backend-decline", "abi-skip"}:
            classes.add("abi-incomplete")
    linker = ABI_LINKER.findall(transcript)
    probe = ABI_LINK_PROBE.findall(transcript)
    if len(linker) != 1:
        errors.append("the run did not name its host-resolved ld64 linker")
        classes.add("abi-incomplete")
    elif probe != linker:
        errors.append(f"the link probe did not show rustc linking with {linker[0]} (observed {probe})")
        classes.add("abi-incomplete")
    return {"status": "fail" if errors else "pass", "errors": errors, "classes": sorted(classes),
            "counts": counts, "named_failures": named[:50], "linker": linker[0] if linker else None}


def workload_document(path: Path) -> dict | None:
    try:
        document = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, ValueError):
        return None
    return document if isinstance(document, dict) else None


def workload_summary(document: dict) -> dict:
    result = document.get("result") or {}
    statistics = document.get("statistics") or {}
    provenance = document.get("engine_provenance") or {}
    authority = provenance.get("successor_authority") or {}
    return {
        "result": {key: result.get(key) for key in WORKLOAD_RESULT_FIELDS},
        "statistics": {key: statistics.get(key) for key in WORKLOAD_STATISTICS},
        "tier": provenance.get("tier"),
        "primary_route": authority.get("primary"),
        "routes": authority.get("routes"),
    }


def classify_workload(row: tuple, native: dict | None, oracle: dict | None) -> dict:
    spec, _cfg, status, error_code, states, transitions = row
    errors, classes = [], set()
    if native is None or oracle is None:
        errors.append("a backend wrote no result document")
        return {"status": "fail", "errors": errors, "classes": ["workload-failed"]}
    native_summary, oracle_summary = workload_summary(native), workload_summary(oracle)
    if native_summary["result"] != oracle_summary["result"] \
            or native_summary["statistics"] != oracle_summary["statistics"]:
        errors.append("trust-cg and interpreter disagree")
        classes.add("workload-mismatch")
    observed = native_summary["result"]["status"], native_summary["result"]["error_code"], \
        native_summary["statistics"]["states_found"], native_summary["statistics"]["transitions"]
    if observed != (status, error_code, states, transitions):
        errors.append(f"pinned {(status, error_code, states, transitions)}, observed {observed}")
        classes.add("workload-mismatch")
    routes = native_summary["routes"] or {}
    accepted = sum((routes.get(route) or {}).get("accepted_results", 0) for route in NATIVE_ROUTES)
    if not str(native_summary["tier"] or "").startswith(NATIVE_TIER_PREFIX) \
            or native_summary["primary_route"] not in NATIVE_ROUTES or accepted <= 0:
        errors.append(f"trust-cg run executed on {native_summary['tier']!r} via {native_summary['primary_route']!r}")
        classes.add("workload-not-native")
    if oracle_summary["tier"] != "interpreter":
        errors.append(f"the oracle run executed on {oracle_summary['tier']!r}, not the interpreter")
        classes.add("workload-mismatch")
    return {"spec": spec, "status": "fail" if errors else "pass", "errors": errors, "classes": sorted(classes),
            "native": native_summary, "oracle": oracle_summary, "native_accepted_results": accepted}


# ---------------------------------------------------------------------------
# Consumer sources.
# ---------------------------------------------------------------------------

def git(arguments: Sequence[str], *, cwd: Path | None = None, check: bool = True,
        timeout: float = 120) -> subprocess.CompletedProcess:
    return subprocess.run(["git", *arguments], cwd=cwd, capture_output=True, text=True, timeout=timeout,
                          check=check)


def has_commit(repository: Path, commit: str) -> bool:
    if not repository.exists():
        return False
    result = git(["-C", str(repository), "cat-file", "-e", f"{commit}^{{commit}}"], check=False)
    return result.returncode == 0


def sibling_record(path: Path, commit: str | None = None) -> dict:
    """A sibling checkout's HEAD and cleanliness, read-only."""
    record: dict = {"path": str(path)}
    if not (path / ".git").exists():
        record["present"] = False
        return record
    head = git(["-C", str(path), "rev-parse", "HEAD"], check=False)
    status = git(["-C", str(path), "status", "--porcelain", "--untracked-files=no"], check=False)
    record.update(present=True, head=head.stdout.strip() or None,
                  dirty_tracked=bool(status.stdout.strip()) if status.returncode == 0 else None)
    if commit is not None:
        record["holds_pin"] = has_commit(path, commit)
    return record


def pin_source(pin: ConsumerPin, cache: Path, *, fetch: bool) -> tuple[Path, str]:
    """The repository that holds the pinned commit: sibling, cache, or a fetch into the cache."""
    if has_commit(pin.sibling, pin.commit):
        return pin.sibling, "sibling"
    if has_commit(cache, pin.commit):
        return cache, "lane-cache"
    if not fetch:
        raise LaneError("consumer-pin-unavailable",
                        f"{pin.name} {pin.commit} is in neither {pin.sibling} nor {cache}; "
                        "rerun with --fetch-consumers to fetch exactly that commit into the lane cache")
    cache.mkdir(parents=True, exist_ok=True)
    if not (cache / "HEAD").exists():
        git(["init", "--quiet", "--bare", str(cache)])
    fetched = git(["-C", str(cache), "fetch", "--quiet", "--depth", "1", pin.url, pin.commit], check=False,
                  timeout=1800)
    if fetched.returncode != 0 or not has_commit(cache, pin.commit):
        raise LaneError("consumer-pin-unavailable",
                        f"fetching {pin.url} {pin.commit} failed: {fetched.stderr.strip()[-400:]}")
    return cache, "fetched"


def default_consumer_cache(home: Path | None = None, environment: dict | None = None,
                           platform: str | None = None) -> Path:
    """The per-user cache directory consumer exports live in (never inside this checkout)."""
    home = Path.home() if home is None else home
    environment = os.environ if environment is None else environment
    platform = sys.platform if platform is None else platform
    if platform == "darwin":
        base = home / "Library" / "Caches"
    else:
        base = Path(environment.get("XDG_CACHE_HOME") or home / ".cache")
    key = hashlib.sha256(str(ROOT).encode()).hexdigest()[:12]
    return base / "trust-cg-consumer-lane" / key


def enclosing_cargo_configs(directory: Path, cargo_home: Path) -> list[Path]:
    """Cargo configuration files above `directory` that Cargo would merge, other than CARGO_HOME's."""
    found = []
    home_configs = {cargo_home / "config.toml", cargo_home / "config"}
    for ancestor in [directory, *directory.parents]:
        for name in ("config.toml", "config"):
            candidate = ancestor / ".cargo" / name
            if candidate.is_file() and candidate not in home_configs:
                found.append(candidate)
    return found


def export_commit(repository: Path, pin: ConsumerPin, destination: Path) -> dict:
    """Extract the pinned commit's tree (minus `export_exclude`) into a fresh `destination`."""
    if destination.exists():
        shutil.rmtree(destination)
    destination.mkdir(parents=True)
    pathspec = ["."] + [f":(exclude){path}" for path in pin.export_exclude]
    archive = subprocess.Popen(["git", "-C", str(repository), "archive", "--format=tar", pin.commit, "--", *pathspec],
                               stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    extract = subprocess.run(["tar", "-x", "-C", str(destination)], stdin=archive.stdout, capture_output=True)
    archive.stdout.close()
    archive_error = archive.stderr.read().decode(errors="replace")
    archive.stderr.close()
    archive.wait()
    if archive.returncode != 0 or extract.returncode != 0:
        raise LaneError("consumer-export-failed",
                        f"git archive {pin.commit} failed: {archive_error.strip()} {extract.stderr.decode(errors='replace').strip()}")
    tree = git(["-C", str(repository), "rev-parse", f"{pin.commit}^{{tree}}"]).stdout.strip()
    return {"repository": str(repository), "commit": pin.commit, "tree": tree, "excluded": list(pin.export_exclude),
            "destination": str(destination)}


class LaneError(RuntimeError):
    def __init__(self, klass: str, message: str):
        super().__init__(message)
        self.klass = klass


# ---------------------------------------------------------------------------
# Bounded processes.
# ---------------------------------------------------------------------------

class Runner:
    """Every child runs in its own bounded process group with a fresh TMPDIR."""

    def __init__(self, output: Path, environment: dict):
        self.output = output
        self.environment = environment
        self.cancelled: int | None = None
        self.process: subprocess.Popen | None = None

    def cancel(self, signum: int, _frame: object = None) -> None:
        if self.cancelled is None:
            self.cancelled = signum
        if self.process is not None:
            try:
                self.process.send_signal(signum)
            except ProcessLookupError:
                pass

    def run(self, command: Sequence[str], log_name: str, timeout: float, *, cwd: Path = ROOT,
            extra_environment: dict | None = None, stdout_path: Path | None = None,
            strip_controls: bool = False) -> dict:
        if self.cancelled is not None:
            raise LaneError("runner-error", f"interrupted by signal {self.cancelled}")
        temporary = Path(tempfile.mkdtemp(prefix="tcg-consumer-"))
        environment = {**self.environment, **(extra_environment or {}), "TMPDIR": f"{temporary}/"}
        for name in ("RUST_TEST_NOCAPTURE", "TRUST_CG_KEEP_TEST_OBJECTS", "TRUST_CG_KEEP_LINKRUN"):
            environment.pop(name, None)
        if strip_controls:
            # trustc refuses to run under any TRUST_CG_*/TCG_* control, and a
            # direct targo or trustc call has no trust_cargo.sh to remove them.
            environment = {key: value for key, value in environment.items()
                           if not key.startswith(("TRUST_CG_", "TCG_"))}
        bounded = [sys.executable, str(TIMEOUT_RUNNER), "--grace-seconds", "5", str(timeout), *command]
        log_path = self.output / log_name
        started = time.monotonic()
        with log_path.open("x", encoding="utf-8") as log:
            stdout = stdout_path.open("x", encoding="utf-8") if stdout_path is not None else log
            try:
                self.process = subprocess.Popen(bounded, cwd=cwd, stdout=stdout, stderr=log,
                                                start_new_session=True, env=environment)
                returncode = self.process.wait()
            except OSError as error:
                log.write(f"consumer lane launch error: {error}\n")
                returncode = 125
            finally:
                self.process = None
                if stdout is not log:
                    stdout.close()
        record = {
            "command": list(command), "cwd": str(cwd), "timeout_seconds": timeout,
            "elapsed_seconds": round(time.monotonic() - started, 3), "returncode": returncode,
            "log": log_name, "log_sha256": sha256_file(log_path),
            "environment": {key: value for key, value in (extra_environment or {}).items()},
        }
        leftovers = sorted(entry.name for entry in temporary.iterdir()
                           if not floor().is_tool_cache(entry)) if temporary.exists() else []
        record["temporary_leftovers"] = leftovers
        record["temporary_leftover_files"] = {
            name: sorted(path.relative_to(temporary / name).as_posix()
                         for path in (temporary / name).rglob("*") if path.is_file())[:20]
            if (temporary / name).is_dir() else [] for name in leftovers[:20]}
        shutil.rmtree(temporary, ignore_errors=True)
        return record


def leftover_errors(record: dict, allowance: tuple[str, str, int] | None = None) -> tuple[list[str], set[str]]:
    """A step's TMPDIR leftovers as errors, unless they are within the listed consumer leak."""
    leftovers = record.get("temporary_leftovers") or []
    if allowance is not None:
        name_pattern, file_pattern, count = allowance
        files = record.get("temporary_leftover_files") or {}
        listed = len(leftovers) <= count and all(
            re.fullmatch(name_pattern, name) and files.get(name)
            and all(re.fullmatch(file_pattern, Path(path).name) for path in files[name])
            for name in leftovers)
        if listed:
            record["listed_consumer_leaks"] = leftovers
            return [], set()
    if leftovers:
        return [f"left {len(leftovers)} entries in its TMPDIR: {', '.join(leftovers[:10])}"], {"temporary-leftovers"}
    return [], set()


# ---------------------------------------------------------------------------
# Steps.
# ---------------------------------------------------------------------------

def step_cg_contracts(runner: Runner, args) -> dict:
    rows = []
    for row in CG_CONTRACT_TARGETS:
        print(f"Running {row.package}/{row.target}", flush=True)
        libtest = ["--show-output", "--test-threads=1"]
        if row.filtered:
            libtest += ["--exact", *[argument for name, _ in row.filtered for argument in ("--skip", name)]]
        command = [str(TRUST_CARGO), "test", "--locked", *(["--offline"] if args.offline else []),
                   "--color", "never", "-j", str(args.jobs), "-p", row.package, "--test", row.target,
                   "--", *libtest]
        record = runner.run(command, f"cg-contracts--{row.target}.log", args.timeout_seconds)
        transcript = (runner.output / record["log"]).read_text(encoding="utf-8", errors="replace")
        verdict = classify_consumer_target(
            row.target, record["returncode"], transcript, minimum=row.minimum, known=dict(row.known_failures),
            ignored=frozenset(), substitutions={}, filtered=frozenset(name for name, _ in row.filtered),
            broad_skips=True, regression_class="cg-contract-failed")
        errors, classes = leftover_errors(record)
        record.update(verdict, package=row.package)
        record["errors"] += errors
        # A listed host residual keeps its own class; anything else is a
        # failed contract target.
        residual = {failure.klass for _, failure in row.known_failures if failure.residual}
        observed = set(record["classes"]) | classes
        record["classes"] = sorted(observed | ({"cg-contract-failed"} if observed - residual else set()))
        record["filtered_reasons"] = dict(row.filtered)
        record["status"] = "fail" if record["errors"] else "pass"
        rows.append(record)
        print(f"{record['status'].upper()}: {row.package}/{row.target}", flush=True)
    return {"status": "pass" if all(row["status"] == "pass" for row in rows) else "fail", "targets": rows,
            "executed_passes": sum(row["passed"] for row in rows),
            "host_residuals": [failure["test"] for row in rows for failure in row["known_failures"]
                               if failure["residual"] and failure["as_recorded"]],
            "errors": [f"{row['target']}: {'; '.join(row['errors'])}" for row in rows if row["errors"]],
            "classes": sorted({klass for row in rows for klass in row["classes"]})}


def step_abi_xback(runner: Runner, args, package: dict) -> dict:
    result: dict = {"status": "fail", "classes": [], "errors": []}
    # TMPDIR leftovers of the self-test and the bridge build fail the step
    # at the end; they do not stop the run.
    carried_errors: list[str] = []
    carried_classes: set[str] = set()
    selftest = runner.run(["bash", str(ABI_XBACK), "--selftest"], "abi-xback--selftest.log", 120)
    text = (runner.output / selftest["log"]).read_text(errors="replace")
    passed = selftest["returncode"] == 0 and ABI_SELFTEST_LINE in text
    leftovers, leftover_classes = leftover_errors(selftest)
    selftest["errors"] = ([] if passed else ["abi-xback self-test failed"]) + leftovers
    selftest["classes"] = sorted(({"abi-selftest-failed"} if not passed else set()) | leftover_classes)
    selftest["status"] = "fail" if selftest["errors"] else "pass"
    result["selftest"] = selftest
    if not passed:
        result.update(classes=selftest["classes"], errors=selftest["errors"])
        return result
    carried_errors += [f"self-test {error}" for error in leftovers]
    carried_classes |= leftover_classes
    print("Building the release bridge backend", flush=True)
    bridge = _load("_darwin_consumers_bridge_backend", BRIDGE_BACKEND)
    backend = BRIDGE_TARGET / "release" / bridge.file_name()
    build = runner.run(
        [package["targo"], "--unverified", "build", "--manifest-path", str(BRIDGE_DIR / "Cargo.toml"),
         "--target-dir", str(BRIDGE_TARGET), "--release", "--locked", *(["--offline"] if args.offline else []),
         "--color", "never", "-j", str(args.jobs)],
        "abi-xback--bridge-build.log", args.build_timeout_seconds,
        extra_environment={"RUSTC": package["compiler"], "RUSTUP_AUTO_INSTALL": "0"}, strip_controls=True,
    )
    result["bridge_build"] = build
    leftovers, leftover_classes = leftover_errors(build)
    build["errors"], build["classes"] = leftovers, sorted(leftover_classes)
    build["status"] = "pass" if build["returncode"] == 0 and not leftovers else "fail"
    if build["returncode"] != 0 or not backend.is_file():
        result.update(classes=sorted({"bridge-build-failed"} | leftover_classes),
                      errors=[f"bridge build exited {build['returncode']}", *leftovers])
        return result
    carried_errors += [f"bridge build {error}" for error in leftovers]
    carried_classes |= leftover_classes
    stale = bridge.stale_source(ROOT, backend)
    result["backend"] = {"path": str(backend), "sha256": sha256_file(backend), "stale_input": str(stale) if stale else None}
    if stale is not None:
        result.update(classes=sorted({"bridge-backend-stale"} | carried_classes),
                      errors=[f"{backend} is older than {stale}", *carried_errors])
        return result
    first, count = ABI_SEEDS
    work = runner.output / "abi-xback"
    print(f"Running abi-xback seeds {first}-{first + count - 1} at O{','.join(ABI_OPT_LEVELS)}", flush=True)
    run = runner.run(
        ["bash", str(ABI_XBACK), "--driver", package["compiler"], str(first), str(count), *ABI_OPT_LEVELS],
        "abi-xback--run.log", args.abi_timeout_seconds,
        extra_environment={"ABI_XBACK_OUT": str(work), "ABI_XBACK_DYLIB": str(backend)},
    )
    text = (runner.output / run["log"]).read_text(errors="replace")
    verdict = classify_abi_run(run["returncode"], text, count * len(ABI_OPT_LEVELS))
    errors, classes = leftover_errors(run)
    run.update(verdict)
    run["errors"] += errors
    run["classes"] = sorted(set(run["classes"]) | classes)
    run["status"] = "fail" if run["errors"] else "pass"
    # The generated sources stay with the record; per-combination build
    # directories are removed by run.sh itself.
    run["generated_sources"] = sorted(path.name for path in work.glob("*.rs")) if work.exists() else []
    result["run"] = run
    result["domain"] = {"seeds": [first, first + count - 1], "opt_levels": list(ABI_OPT_LEVELS),
                        "directions": ["llvm-caller x tcg-callee", "tcg-caller x llvm-callee"]}
    result["classes"] = sorted(set(run["classes"]) | carried_classes)
    result["errors"] = run["errors"] + carried_errors
    result["status"] = "fail" if result["errors"] else "pass"
    return result


def ty_cargo(runner: Runner, args, verb: str, cargo_arguments: Sequence[str], log: str, timeout: float,
             context: dict, *, libtest: Sequence[str] = (), stdout_path: Path | None = None,
             extra_environment: dict | None = None) -> dict:
    command = [str(TRUST_CARGO), verb, "--locked", "--offline", "--color", "never", "-j", str(args.jobs),
               "--target-dir", str(context["target_dir"]), *context["patches"], *cargo_arguments]
    if libtest:
        command += ["--", *libtest]
    environment = {"TY_CACHE_DIR": str(context["cache_dir"]), "TY_NO_CACHE": "1", **(extra_environment or {})}
    return runner.run(command, log, timeout, cwd=context["source"], extra_environment=environment,
                      stdout_path=stdout_path)


def step_ty(runner: Runner, args, target_cohort: dict) -> dict:
    result: dict = {"status": "fail", "classes": [], "errors": [], "pin": {
        "name": TY.name, "url": TY.url, "commit": TY.commit, "sibling": str(TY.sibling)}}
    try:
        repository, origin = pin_source(TY, LANE_CACHE / "git" / "ty.git", fetch=args.fetch_consumers)
        result["source"] = {"origin": origin}
        source = args.consumer_cache / "src" / f"ty-{TY.commit[:12]}"
        if source.resolve().is_relative_to(ROOT):
            raise LaneError("consumer-export-failed", f"{source} is inside this checkout, whose Cargo "
                                                      "configuration would apply to the consumer")
        cargo_home = Path(os.environ.get("CARGO_HOME") or Path.home() / ".cargo")
        foreign = enclosing_cargo_configs(source.parent, cargo_home)
        if foreign:
            raise LaneError("consumer-export-failed", f"Cargo would merge {', '.join(map(str, foreign))} into the "
                                                      f"consumer's configuration; choose another --consumer-cache")
        print(f"Exporting TY {TY.commit} from {origin}", flush=True)
        result["source"].update(export_commit(repository, TY, source))
        result["lane_targets"] = inject_lane_targets(source)
        manifest_path = source / "Cargo.toml"
        original = manifest_path.read_text(encoding="utf-8")
        crates = trust_cg_dependencies(original)
        if not crates:
            raise LaneError("consumer-cohort-substitution", "TY's manifest names no trust-cg crate")
        rewritten, changes = rewrite_manifest(original, target_cohort)
        manifest_path.write_text(rewritten, encoding="utf-8")
        (runner.output / "ty--Cargo.toml.patch.json").write_text(json.dumps(changes, indent=2) + "\n")
        result["substitution"] = {"trust_cg_crates": crates, "patched_to": str(ROOT / "crates"),
                                  "rewritten_lines": changes, **target_cohort}
        context = {
            "source": source, "target_dir": LANE_CACHE / "ty-target",
            "patches": patch_configuration(crates), "cache_dir": None,
        }
        before = lock_packages((source / "Cargo.lock").read_text(encoding="utf-8"))
        result["lock_before_sha256"] = sha256_file(source / "Cargo.lock")
        print("Resolving TY against this checkout's cohort", flush=True)
        # `metadata` is not a compilation verb, so targo runs it without a
        # lane flag (trust_cargo.sh would add --unverified, which it refuses).
        resolve = runner.run(
            [runner.environment["TRUST_TARGO"], "metadata", "--format-version", "1", "--color", "never",
             *(["--offline"] if args.offline else []), *context["patches"]],
            "ty--resolve.log", args.timeout_seconds, cwd=source, strip_controls=True,
            stdout_path=runner.output / "ty--metadata.json")
        result["resolve"] = resolve
        if resolve["returncode"] != 0:
            raise LaneError("consumer-resolution-failed", f"resolution exited {resolve['returncode']}")
        leftovers, leftover_classes = leftover_errors(resolve)
        result["errors"] += [f"resolution {error}" for error in leftovers]
        result["classes"] = sorted(set(result["classes"]) | leftover_classes)
        after_text = (source / "Cargo.lock").read_text(encoding="utf-8")
        shutil.copyfile(source / "Cargo.lock", runner.output / "ty--Cargo.lock")
        after = lock_packages(after_text)
        root_lock = lock_packages((ROOT / "Cargo.lock").read_text(encoding="utf-8"))
        result["lock_after_sha256"] = sha256_bytes(after_text.encode())
        result["lock_delta"] = {
            "added": sorted(f"{n} {v} {s or 'path'}" for n, v, s in after - before),
            "removed": sorted(f"{n} {v} {s or 'path'}" for n, v, s in before - after),
        }
        problems = lock_problems(before, after, root_lock, target_cohort)
        if problems:
            result["errors"] += problems
            result["classes"] = sorted({problem.split(":", 1)[0] for problem in problems})
            return result
        metadata = json.loads((runner.output / "ty--metadata.json").read_text(encoding="utf-8"))
        targets = inventory_targets(metadata)
        expected = set(TY_TARGETS) | set(TY_COMPILED_OUT) | set(TY_LANE_TARGETS)
        result["inventory"] = {"observed": sorted(targets), "expected": sorted(expected)}
        if targets != expected:
            result["errors"].append(f"tla-trust-cg targets differ from the pinned inventory: added "
                                    f"{sorted(targets - expected)}, removed {sorted(expected - targets)}")
            result["classes"] = ["consumer-inventory-drift"]
            return result
        cache_dir = Path(tempfile.mkdtemp(prefix="tcg-consumer-ty-cache-"))
        context["cache_dir"] = cache_dir
        # The trust-cg workload runs dump their TrustIR modules here for the
        # replay-corpus step; the dump stays with the run's logs.
        context["replay_dir"] = runner.output / "ty-replay-dump"
        try:
            run_ty_targets(runner, args, context, result, target_cohort)
        finally:
            shutil.rmtree(cache_dir, ignore_errors=True)
    except LaneError as error:
        result["errors"].append(str(error))
        result["classes"] = sorted(set(result["classes"]) | {error.klass})
        return result
    return summarize_ty(result)


def summarize_ty(result: dict) -> dict:
    """The TY step's verdict from its rows: classes, errors, and passes counted by owner."""
    classes = set(result["classes"])
    for key in ("build", "canary", "replay"):
        classes |= set((result.get(key) or {}).get("classes", []))
    for row in result.get("targets", []) + result.get("workloads", []):
        classes |= set(row.get("classes", []))
    result["classes"] = sorted(classes)
    failing = [row for row in result.get("targets", []) + result.get("workloads", []) if row["status"] != "pass"]
    result["errors"] += [f"{row.get('target') or row.get('spec')}: {'; '.join(row['errors'])}" for row in failing]
    for key in ("build", "canary", "replay"):
        if (result.get(key) or {}).get("status") != "pass":
            result["errors"] += (result.get(key) or {}).get("errors") or [f"{key} did not run"]
    # TY's own executed passes; the lane-owned targets are counted apart.
    result["executed_passes"] = sum(row.get("passed", 0) for row in result.get("targets", [])
                                    if row.get("owner") == "consumer")
    result["lane_target_passes"] = sum(row.get("passed", 0) for row in result.get("targets", [])
                                       if row.get("owner") == "lane")
    result["not_in_lane"] = dict(TY_CRATES_NOT_IN_LANE)
    result["status"] = "fail" if result["errors"] else "pass"
    return result


def inject_lane_targets(source: Path) -> list[dict]:
    """Copy each TY_LANE_TARGETS source into the exported tree's tla-trust-cg tests."""
    tests = source / TY_PACKAGE_DIR / "tests"
    if not tests.is_dir():
        raise LaneError("consumer-inventory-drift", f"the pin has no {TY_PACKAGE_DIR / 'tests'} directory")
    injected = []
    for target, (path, _minimum) in TY_LANE_TARGETS.items():
        destination = tests / f"{target}.rs"
        if destination.exists():
            raise LaneError("consumer-inventory-drift", f"the pin already has {destination.relative_to(source)}")
        shutil.copyfile(path, destination)
        injected.append({"target": target, "source": path.relative_to(ROOT).as_posix(),
                         "path": destination.relative_to(source).as_posix(), "sha256": sha256_file(path)})
    return injected


def replay_modules(root: Path) -> list[Path]:
    """Every metadata record of a pre-JIT module under a replay-artifact dump."""
    modules = []
    for path in sorted(root.rglob("*.metadata.json")) if root.exists() else []:
        try:
            stage = json.loads(path.read_text(encoding="utf-8")).get("stage")
        except (OSError, ValueError):
            continue
        if stage == TY_REPLAY_STAGE:
            modules.append(path)
    return modules


def classify_replay(returncode: int, transcript: str, summary_lines: Sequence[str], modules: int) -> dict:
    errors, classes = [], set()
    outcomes, _, rollups = test_events(transcript)
    if outcomes.get(TY_REPLAY_TEST) != "passed" or len(outcomes) != 1 or returncode != 0:
        errors.append(f"replay-corpus test outcome {outcomes.get(TY_REPLAY_TEST, 'absent')}, cargo exited {returncode}")
    summaries = []
    for line in summary_lines:
        try:
            record = json.loads(line)
        except ValueError:
            continue
        if isinstance(record, dict) and record.get("summary") is True:
            summaries.append(record)
    summary = summaries[-1] if len(summaries) == 1 else None
    if summary is None:
        errors.append("the replay-corpus run wrote no single summary record")
    elif (summary.get("compared"), summary.get("refused"), summary.get("sealed_mismatch")) != (modules, 0, 0):
        errors.append(f"compared {summary.get('compared')} of {modules} dumped modules, refused "
                      f"{summary.get('refused')}, sealed mismatches {summary.get('sealed_mismatch')}")
    if modules == 0:
        errors.append("the trust-cg workload runs dumped no pre-JIT module")
    if errors:
        classes.add("consumer-replay-failed")
    return {"status": "fail" if errors else "pass", "errors": errors, "classes": sorted(classes),
            "summary": summary, "dumped_modules": modules, "rollups": rollups}


def run_ty_replay(runner: Runner, args, context: dict, features: Sequence[str]) -> dict:
    modules = replay_modules(context["replay_dir"])
    out = runner.output / "ty--replay-identity.jsonl"
    print(f"Running TY's replay-corpus test over {len(modules)} dumped modules", flush=True)
    record = ty_cargo(runner, args, "test", ["-p", TY_PACKAGE, *features, "--lib"], "ty--replay.log",
                      args.timeout_seconds, context,
                      libtest=["--ignored", "--exact", TY_REPLAY_TEST, "--show-output", "--test-threads=1"],
                      extra_environment={"TY_ADOPTION_IDENTITY_DIR": str(context["replay_dir"]),
                                         "TY_ADOPTION_IDENTITY_OUT": str(out)})
    transcript = (runner.output / record["log"]).read_text(encoding="utf-8", errors="replace")
    lines = out.read_text(encoding="utf-8").splitlines() if out.exists() else []
    verdict = classify_replay(record["returncode"], transcript, lines, len(modules))
    errors, classes = leftover_errors(record)
    record.update(verdict)
    record["errors"] += errors
    record["classes"] = sorted(set(record["classes"]) | classes)
    record["status"] = "fail" if record["errors"] else "pass"
    record["modules_by_spec"] = {}
    for path in modules:
        spec = path.relative_to(context["replay_dir"]).parts[0]
        record["modules_by_spec"][spec] = record["modules_by_spec"].get(spec, 0) + 1
    print(f"{record['status'].upper()}: ty replay corpus", flush=True)
    return record


def inventory_targets(metadata: dict) -> set[str]:
    for package in metadata.get("packages", []):
        if package.get("name") == TY_PACKAGE:
            names = set()
            for target in package.get("targets", []):
                kinds = set(target.get("kind", []))
                if "test" in kinds:
                    names.add(target["name"])
                elif "lib" in kinds or "rlib" in kinds:
                    names.add("lib")
            return names
    raise LaneError("consumer-inventory-drift", f"resolved metadata has no package {TY_PACKAGE}")


def run_ty_targets(runner: Runner, args, context: dict, result: dict, target_cohort: dict) -> None:
    features = ["--features", ",".join(TY_FEATURES)]
    print("Building TY's trust-cg consumer and the ty binary", flush=True)
    build = ty_cargo(runner, args, "test", ["-p", TY_PACKAGE, *features, "--no-run"], "ty--build-tests.log",
                     args.build_timeout_seconds, context)
    binary = ty_cargo(runner, args, "build", ["-p", TY_BINARY_PACKAGE, "--bin", TY_BINARY], "ty--build-binary.log",
                      args.build_timeout_seconds, context)
    build_errors = [f"{name} build exited {row['returncode']}" for name, row in (("test", build), ("ty", binary))
                    if row["returncode"] != 0]
    leftover_messages: list[str] = []
    leftover_classes: set[str] = set()
    for name, row in (("test", build), ("ty", binary)):
        errors, classes = leftover_errors(row)
        leftover_messages += [f"{name} build {error}" for error in errors]
        leftover_classes |= classes
    result["build"] = {"tests": build, "binary": binary, "errors": build_errors + leftover_messages,
                       "status": "fail" if build_errors or leftover_messages else "pass",
                       "classes": sorted(({"consumer-build-failed"} if build_errors else set()) | leftover_classes)}
    if build_errors:
        return
    result["targets"] = []
    rows = [(target, minimum, "consumer") for target, minimum in TY_TARGETS.items()]
    rows += [(target, minimum, "lane") for target, (_, minimum) in TY_LANE_TARGETS.items()]
    for target, minimum, owner in rows:
        selector = ["--lib"] if target == "lib" else ["--test", target]
        filtered = TY_FILTERED.get(target, ())
        libtest = ["--show-output"]
        if filtered:
            libtest += ["--exact", *[argument for name, _ in filtered for argument in ("--skip", name)]]
        print(f"Running ty/{TY_PACKAGE}/{target}", flush=True)
        record = ty_cargo(runner, args, "test", ["-p", TY_PACKAGE, *features, *selector, "--no-fail-fast"],
                          f"ty--{target}.log", args.timeout_seconds, context, libtest=libtest)
        transcript = (runner.output / record["log"]).read_text(encoding="utf-8", errors="replace")
        known = {name: failure for (key, name), failure in TY_KNOWN_FAILURES.items() if key == target}
        verdict = classify_consumer_target(target, record["returncode"], transcript, minimum=minimum, known=known,
                                           ignored=TY_IGNORED.get(target, frozenset()), substitutions=target_cohort,
                                           filtered=frozenset(name for name, _ in filtered), broad_skips=True)
        errors, classes = leftover_errors(record, TY_TEMPORARY_LEAKS.get(target))
        record.update(verdict, owner=owner)
        record["errors"] += errors
        record["classes"] = sorted(set(record["classes"]) | classes)
        record["filtered_reasons"] = dict(filtered)
        record["status"] = "fail" if record["errors"] else "pass"
        result["targets"].append(record)
        print(f"{record['status'].upper()}: ty/{TY_PACKAGE}/{target}", flush=True)
    result["compiled_out"] = dict(TY_COMPILED_OUT)
    print(f"Running the TY canary {TY_CANARY}", flush=True)
    canary = ty_cargo(runner, args, "run", ["-p", TY_PACKAGE, *features, "--example", TY_CANARY], "ty--canary.log",
                      args.timeout_seconds, context)
    canary_text = (runner.output / canary["log"]).read_text(errors="replace")
    canary["errors"] = [] if canary["returncode"] == 0 and TY_CANARY_LINE in canary_text else [
        f"canary exited {canary['returncode']} without {TY_CANARY_LINE!r}"]
    leftovers, classes = leftover_errors(canary)
    canary["errors"] += leftovers
    canary["classes"] = sorted(classes | ({"consumer-canary-failed"} if canary["errors"] else set()))
    canary["status"] = "fail" if canary["errors"] else "pass"
    result["canary"] = canary
    ty_binary = context["target_dir"] / "debug" / TY_BINARY
    result["binary"] = {"path": str(ty_binary), "sha256": sha256_file(ty_binary)}
    result["workloads"] = []
    for row in TY_WORKLOADS:
        spec, cfg = row[0], row[1]
        documents = {}
        runs = {}
        for backend in ("trust-cg", "interpreter"):
            print(f"Running ty check {spec} --backend {backend}", flush=True)
            cache = Path(tempfile.mkdtemp(prefix="tcg-consumer-ty-wl-"))
            document_path = runner.output / f"ty--workload--{spec}--{backend}.json"
            extra = {"TY_CACHE_DIR": str(cache), "TY_NO_CACHE": "1"}
            if backend == "trust-cg":
                extra["TY_TRUST_CG_REPLAY_ARTIFACT_DIR"] = str(context["replay_dir"] / spec)
            try:
                run = runner.run(
                    [str(ty_binary), "check", f"test_specs/{spec}.tla", "--config", f"test_specs/{cfg}.cfg",
                     "--backend", backend, *TY_WORKLOAD_FLAGS],
                    f"ty--workload--{spec}--{backend}.log", args.workload_timeout_seconds, cwd=context["source"],
                    extra_environment=extra, stdout_path=document_path)
            finally:
                shutil.rmtree(cache, ignore_errors=True)
            runs[backend] = run
            document = workload_document(document_path)
            expected_rc = 0 if row[2] == "ok" else 1
            documents[backend] = document if run["returncode"] == expected_rc else None
        verdict = classify_workload(row, documents["trust-cg"], documents["interpreter"])
        for run in runs.values():
            errors, classes = leftover_errors(run)
            verdict["errors"] += errors
            verdict["classes"] = sorted(set(verdict["classes"]) | classes)
        verdict["status"] = "fail" if verdict["errors"] else "pass"
        verdict["runs"] = runs
        verdict["spec"] = spec
        result["workloads"].append(verdict)
        print(f"{verdict['status'].upper()}: ty check {spec}", flush=True)
    result["replay"] = run_ty_replay(runner, args, context, features)


# ---------------------------------------------------------------------------
# Main.
# ---------------------------------------------------------------------------

# Logs and documents an archive always keeps, besides report.json and the log
# of every row that did not pass: the inputs of the consumer substitution, the
# abi-xback transcript, the workload result documents and the replay summary.
ARCHIVE_ALWAYS = (
    "ty--Cargo.toml.patch.json", "ty--Cargo.lock", "ty--resolve.log", "ty--canary.log",
    "ty--replay.log", "ty--replay-identity.jsonl", "abi-xback--selftest.log", "abi-xback--run.log",
)
# Each declined or mismatched abi-xback combination's diagnostic and sources
# (run.sh copies them into fail/) are kept as well.
ARCHIVE_PATTERNS = ("ty--workload--*.json", "abi-xback/fail/*")


def archive(run: Path, destination: Path) -> int:
    """Copy a finished lane run's report and its cited logs into an evidence archive.

    The destination holds only the README.md its author wrote beforehand.
    report.json is copied as is; every other kept file is stored
    gzip-compressed (deterministic, mtime 0); a passing row's log is cited by
    the SHA-256 the report records. inventory.json lists every stored file in
    the form scripts/check_evidence_archive.py verifies.
    """
    import gzip
    report_path = run / "report.json"
    report = json.loads(report_path.read_text(encoding="utf-8"))
    if report.get("schema") != SCHEMA or report.get("status") == "incomplete":
        raise ValueError(f"{report_path} is not a finished {SCHEMA} report")
    if not (destination / "README.md").is_file():
        raise ValueError(f"{destination} needs its README.md before the payload is archived")
    if any(path.name != "README.md" for path in destination.iterdir()):
        raise ValueError(f"{destination} already holds files other than README.md")
    names = {name for name in ARCHIVE_ALWAYS if (run / name).is_file()}
    for pattern in ARCHIVE_PATTERNS:
        names |= {path.relative_to(run).as_posix() for path in run.glob(pattern) if path.is_file()}

    def rows(value):
        if isinstance(value, dict):
            if value.get("log") and value.get("status") not in (None, "pass"):
                yield value["log"]
            for child in value.values():
                yield from rows(child)
        elif isinstance(value, list):
            for child in value:
                yield from rows(child)

    names |= {name for name in rows(report.get("steps", {})) if (run / name).is_file()}
    data = report_path.read_bytes()
    (destination / "report.json").write_bytes(data)
    artifacts = [{"path": "report.json", "sha256": sha256_bytes(data), "bytes": len(data)}]
    for name in sorted(names):
        raw = (run / name).read_bytes()
        stored = gzip.compress(raw, compresslevel=9, mtime=0)
        relative = f"logs/{name}.gz"
        (destination / relative).parent.mkdir(parents=True, exist_ok=True)
        (destination / relative).write_bytes(stored)
        artifacts.append({"path": relative, "sha256": sha256_bytes(raw), "bytes": len(raw),
                          "stored_sha256": sha256_bytes(stored), "stored_bytes": len(stored)})
    inventory = {"source": (report.get("provenance") or {}).get("source_sha"), "artifacts": artifacts}
    (destination / "inventory.json").write_text(json.dumps(inventory, indent=2) + "\n", encoding="utf-8")
    print(f"archived {len(artifacts)} files into {destination}")
    return 0


def positive_seconds(value: str) -> float:
    try:
        seconds = float(value)
    except ValueError as error:
        raise argparse.ArgumentTypeError(f"not a number: {value}") from error
    if not seconds > 0:
        raise argparse.ArgumentTypeError(f"must be positive: {value}")
    return seconds


def positive_jobs(value: str) -> int:
    try:
        jobs = int(value)
    except ValueError as error:
        raise argparse.ArgumentTypeError(f"not an integer: {value}") from error
    if jobs <= 0:
        raise argparse.ArgumentTypeError(f"must be positive: {value}")
    return jobs


def plan() -> list[str]:
    lines = [f"cg-contracts {row.package}/{row.target} minimum={row.minimum}"
             + "".join(f" filtered={name}" for name, _ in row.filtered)
             + "".join(f" {'host-residual' if failure.residual else 'known-failure'}={name}"
                       for name, failure in row.known_failures)
             for row in CG_CONTRACT_TARGETS]
    first, count = ABI_SEEDS
    lines.append(f"abi-xback seeds={first}-{first + count - 1} opt={','.join(ABI_OPT_LEVELS)} directions=2 "
                 f"required_match={2 * count * len(ABI_OPT_LEVELS)}")
    lines.append(f"ty pin={TY.commit} url={TY.url}")
    lines += [f"ty {TY_PACKAGE}/{target} minimum={minimum}"
              + "".join(f" filtered={name}" for name, _ in TY_FILTERED.get(target, ()))
              for target, minimum in TY_TARGETS.items()]
    lines += [f"ty {TY_PACKAGE}/{target} minimum={minimum} lane-owned={path.relative_to(ROOT).as_posix()}"
              for target, (path, minimum) in TY_LANE_TARGETS.items()]
    lines += [f"ty {TY_PACKAGE}/{target} compiled-out: {reason}" for target, reason in TY_COMPILED_OUT.items()]
    lines += [f"ty known-failure {target}/{name} class={failure.klass}"
              for (target, name), failure in TY_KNOWN_FAILURES.items()]
    lines.append(f"ty canary {TY_CANARY}")
    lines.append(f"ty replay-corpus {TY_PACKAGE}/lib {TY_REPLAY_TEST} over the trust-cg workload dumps")
    lines += [f"ty workload {row[0]} status={row[2]} states_found={row[4]} transitions={row[5]}" for row in TY_WORKLOADS]
    lines += [f"absent {name}: {record['status']}" for name, record in ABSENT_CONSUMERS.items()]
    lines += [f"ty not-in-lane {name}: {reason}" for name, reason in TY_CRATES_NOT_IN_LANE.items()]
    return lines


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter,
                                     allow_abbrev=False)
    parser.add_argument("--list", action="store_true", help="print the lane's plan without probing or executing")
    parser.add_argument("--out", type=Path, help="new output directory outside the source tree")
    parser.add_argument("--only", action="append", choices=STEPS,
                        help="run only this step; repeatable; never a lane pass")
    parser.add_argument("--jobs", type=positive_jobs, default=3, help="Cargo build jobs (default: 3)")
    parser.add_argument("--timeout-seconds", type=positive_seconds, default=1800.0,
                        help="bound for each test target, resolution or canary (default: 1800)")
    parser.add_argument("--build-timeout-seconds", type=positive_seconds, default=10800.0,
                        help="bound for each consumer or bridge build (default: 10800)")
    parser.add_argument("--abi-timeout-seconds", type=positive_seconds, default=5400.0,
                        help="bound for the generated abi-xback run (default: 5400)")
    parser.add_argument("--workload-timeout-seconds", type=positive_seconds, default=600.0,
                        help="bound for each ty check workload run (default: 600)")
    parser.add_argument("--require-clean", action="store_true", help="refuse to run on a dirty source tree")
    parser.add_argument("--offline", action="store_true",
                        help="resolve and build with Cargo --offline (the consumer build always uses --offline)")
    parser.add_argument("--fetch-consumers", action="store_true",
                        help="fetch a pinned consumer commit absent from its sibling checkout into the lane cache")
    parser.add_argument("--archive", nargs=2, type=Path, metavar=("RUN", "DESTINATION"),
                        help="archive a finished run's report and kept logs into DESTINATION (which holds only its "
                             "README.md); nothing is executed")
    parser.add_argument("--consumer-cache", type=Path, default=None,
                        help="directory for exported consumer sources, outside this checkout (default: "
                             "~/Library/Caches/trust-cg-consumer-lane/<checkout key> on macOS)")
    args = parser.parse_args(argv)
    if args.list:
        print("\n".join(plan()))
        return 0
    if args.archive:
        try:
            return archive(*args.archive)
        except (OSError, ValueError) as error:
            print(f"Darwin consumer lane: archive error: {error}", file=sys.stderr)
            return 1
    try:
        if args.out is None:
            output = Path(tempfile.mkdtemp(prefix=OUTPUT_PREFIX))
        else:
            output = args.out.absolute()
            if output.resolve().is_relative_to(ROOT):
                raise OSError("output must be outside the source tree so logs cannot change source provenance")
            output.mkdir(mode=0o700)
    except OSError as error:
        print(f"Darwin consumer lane: output directory error: {error}", file=sys.stderr)
        return 1
    args.consumer_cache = (args.consumer_cache or default_consumer_cache()).absolute()
    selected = tuple(step for step in STEPS if not args.only or step in args.only)
    report: dict = {
        "schema": SCHEMA,
        "scope": ("required Darwin downstream-consumer lane (L13-P8): testing evidence for the consumers' current "
                  "domains; not proof, not a Trust-verified build, not performance, not Linux"),
        "host": "aarch64-apple-darwin", "status": "incomplete", "started_utc": utc_now(),
        "mode": "only" if args.only else "required", "selected_steps": list(selected),
        "options": {key: (str(value) if isinstance(value, Path) else value) for key, value in vars(args).items()},
        "failure_classes": FAILURE_CLASSES, "steps": {}, "errors": [],
        "absent_consumers": {name: {key: (str(value) if isinstance(value, Path) else value)
                                    for key, value in record.items()} for name, record in ABSENT_CONSUMERS.items()},
    }
    report_path = output / "report.json"
    write_report(report_path, report)
    print(f"Darwin consumer lane logs: {output}", flush=True)
    environment = floor().child_environment()
    runner = Runner(output, environment)
    previous = {signum: signal.signal(signum, runner.cancel) for signum in (signal.SIGHUP, signal.SIGINT, signal.SIGTERM)}
    try:
        report["provenance"] = floor().preflight(environment)
        environment["TRUST_TARGO"] = report["provenance"]["tools"]["targo"]
        if args.require_clean and report["provenance"]["dirty"]:
            raise RuntimeError("source tree is dirty; --require-clean refuses to run")
        report["cohort"] = cohort()
        report["siblings"] = {"ty": sibling_record(TY.sibling, TY.commit),
                              **{name: sibling_record(record["sibling"]) for name, record in ABSENT_CONSUMERS.items()}}
        write_report(report_path, report)
        package = floor().trust_package(environment)
        for step in selected:
            if runner.cancelled is not None:
                break
            print(f"=== consumer lane step: {step} ===", flush=True)
            try:
                if step == "cg-contracts":
                    report["steps"][step] = step_cg_contracts(runner, args)
                elif step == "abi-xback":
                    report["steps"][step] = step_abi_xback(runner, args, package)
                else:
                    report["steps"][step] = step_ty(runner, args, report["cohort"])
            except LaneError as error:
                report["steps"][step] = {"status": "fail", "classes": [error.klass], "errors": [str(error)]}
            except (OSError, ValueError, subprocess.SubprocessError) as error:
                report["steps"][step] = {"status": "fail", "classes": ["runner-error"], "errors": [repr(error)]}
            write_report(report_path, report)
            print(f"{report['steps'][step]['status'].upper()}: step {step}", flush=True)
        if runner.cancelled is not None:
            report["errors"].append(f"interrupted by signal {runner.cancelled}; the lane is incomplete")
        report["final_source"] = floor().source_provenance(report["provenance"]["tools"]["git"])
        if report["final_source"]["source_fingerprint"] != report["provenance"]["source_fingerprint"]:
            report["errors"].append("source changed while the lane was running")
        report["final_siblings"] = {"ty": sibling_record(TY.sibling, TY.commit)}
    except (OSError, RuntimeError, ValueError, subprocess.SubprocessError) as error:
        report["errors"].append(str(error))
    finally:
        for signum, handler in previous.items():
            signal.signal(signum, handler)
    steps = report["steps"]
    complete = set(steps) == set(selected)
    green = complete and not report["errors"] and all(row["status"] == "pass" for row in steps.values())
    report["status"] = ("pass" if not args.only else "partial-pass") if green else "fail"
    report["observed_classes"] = sorted({klass for row in steps.values() for klass in row.get("classes", [])})
    report["finished_utc"] = utc_now()
    write_report(report_path, report)
    if report["status"] == "pass":
        print(f"{SUCCESS_LINE} ({report_path})")
    else:
        label = report["status"].upper()
        if report["status"] == "partial-pass":
            label += " (selected steps only; not the required lane)"
        print(f"Darwin consumer lane: {label} ({report_path})")
        for name, row in steps.items():
            for error in row.get("errors", [])[:20]:
                print(f"  {name}: {error}", file=sys.stderr)
        for error in report["errors"]:
            print(f"  {error}", file=sys.stderr)
    return 0 if report["status"] in ("pass", "partial-pass") else 1


if __name__ == "__main__":
    raise SystemExit(main())
