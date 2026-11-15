#!/usr/bin/env python3
"""Partition the root-workspace test matrix into per-host required sets.

`scripts/run_full_test_matrix.sh` runs every Cargo test suite of the root
workspace on one host, so it cannot be green on any single host: on Darwin the
Linux-only suites compile to empty suites, and on Linux the macOS-only suites
print skip lines (ledger L13-P6). This module partitions the same denominator,
Cargo's own target list (`targo metadata`), into two required sets: one for
aarch64-apple-darwin and one for aarch64-unknown-linux-gnu.

A suite is one libtest binary that `cargo test -p <package>` runs: the library
unit tests, each binary's, integration test's, example's or bench's unit tests
(when Cargo builds it as a test), and the library doc-tests. Each suite is
classified exactly once:

  both     required on both AArch64 hosts
  darwin   required on Darwin only (reason)
  linux    required on Linux only (reason)
  neither  required on neither AArch64 host (reason: an x86-64 or Windows
           execution host, or an opt-in campaign)
  empty    contains no test on any host (reason)

The class comes from, in order: an explicit SUITE_CLASS entry with its reason;
the file-level `#![cfg(...)]` of the suite's root source evaluated for each
host with the features the suite is built with (a suite compiled out on a host
is never required there); a static census that finds no test function (or no
runnable doc-test block) in the suite's module tree; and otherwise `both`.

Inside a suite that is required on a host, a single test that does not run
in the suite's default invocation there is listed in TEST_CLASS with one lane
and a reason:

  darwin, linux   host-specific: required only on that host; a runner on the
                  other host passes it to libtest as an exact `--skip`
  formal          runs only in the strict proof campaign, a separate exact
                  invocation with TRUST_CG_RUN_FORMAL_PROOF_TESTS=1
  external-cert   runs only in the external-certificate campaign, a separate
                  exact invocation with TRUST_CG_RUN_EXTERNAL_CERT_TESTS=1 and
                  the resolved AY and Clean named explicitly
  other-lane      needs an execution host or tool neither AArch64 matrix has
                  (x86-64 execution, wasm-ld and node, RISC-V cross tools);
                  skipped by both AArch64 matrices
  opt-in          required by neither host's matrix (a measurement campaign
                  that needs a release build, a debugging aid); always skipped

No runner in this repository executes an `other-lane` or `opt-in` test:
`required_by_neither_host()` lists them, each report carries that list, and
they are a named residual of every matrix record, never a pass.

The filtered count a suite's default invocation reports must equal the number
of names it skips. An `#[ignore]`d unit or integration test is listed in
IGNORED_TESTS with its reason; a run that ignores a test missing from that
table, or runs one listed there, fails the suite. Ignored doc-test blocks are
documentation, counted but not listed.

A required suite must report a positive number of executed passes: at least
one, or the Darwin floor's pinned minimum for a Darwin floor target. A runtime
skip line never counts as a pass. The classification is static source
evidence. The Darwin set is executed by
`scripts/run_darwin_full_test_matrix.py`; nothing in this repository executes
the Linux set yet, so its classification is unmeasured.

Usage:
  full_test_matrix_hosts.py            print every suite with its class
  full_test_matrix_hosts.py --check    print nothing; fail on any inconsistency
  full_test_matrix_hosts.py --json     print the classification as JSON
"""

from __future__ import annotations

import argparse
from dataclasses import dataclass, field
import functools
import importlib.util
import json
import os
from pathlib import Path
import re
import subprocess
import sys
from typing import Iterable, Sequence


ROOT = Path(__file__).resolve().parents[1]
SCRIPTS = ROOT / "scripts"
HOSTS = ("darwin", "linux")
HOST_TRIPLES = {"darwin": "aarch64-apple-darwin", "linux": "aarch64-unknown-linux-gnu"}
CLASSES = ("both", "darwin", "linux", "neither", "empty")
REQUIRED_HOSTS = {
    "both": ("darwin", "linux"), "darwin": ("darwin",), "linux": ("linux",),
    "neither": (), "empty": (),
}
# The suites `cargo test -p <package>` runs, by Cargo target kind; a target
# runs as a test only when Cargo metadata says `test: true`.
TEST_KINDS = ("lib", "proc-macro", "bin", "test", "example", "bench")
SELECTORS = {"lib": "--lib", "bin": "--bin", "test": "--test", "example": "--example", "bench": "--bench"}

# Host cfg facts for the two AArch64 hosts. `feature` is filled in per suite
# with the features it is built with.
HOST_FACTS = {
    "darwin": {
        "target_arch": {"aarch64"}, "target_os": {"macos"}, "target_env": {""},
        "target_family": {"unix"}, "target_vendor": {"apple"},
        "target_endian": {"little"}, "target_pointer_width": {"64"}, "target_abi": {""},
        "target_has_atomic": {"8", "16", "32", "64", "128", "ptr"}, "panic": {"unwind"},
        "unix": True, "windows": False, "test": True, "debug_assertions": True,
        "miri": False, "doc": False, "doctest": False,
    },
    "linux": {
        "target_arch": {"aarch64"}, "target_os": {"linux"}, "target_env": {"gnu"},
        "target_family": {"unix"}, "target_vendor": {"unknown"},
        "target_endian": {"little"}, "target_pointer_width": {"64"}, "target_abi": {""},
        "target_has_atomic": {"8", "16", "32", "64", "128", "ptr"}, "panic": {"unwind"},
        "unix": True, "windows": False, "test": True, "debug_assertions": True,
        "miri": False, "doc": False, "doctest": False,
    },
}

# ---------------------------------------------------------------------------
# Classification tables. Each key is a suite id `<package>/<kind>[/<name>]`
# (`trust-cg-codegen/lib`, `trust-cg-codegen/doc`,
# `trust-cg-codegen/test/e2e_macho_link`, `trust-cg-cli/bin/trust-cg`).
# ---------------------------------------------------------------------------

# Suites whose host requirement is decided by what they execute at run time
# rather than by a file-level cfg: (class, reason). An entry the static
# derivation already produces is stale and fails the check.
_X86_EXECUTION = (
    "x86-64 code generation whose link-and-run legs need an x86-64 execution host (native, "
    "Rosetta 2 opted in with TRUST_CG_RUN_ROSETTA_LINKRUN=1, or qemu-user): the x86-64 lanes' "
    "target (scripts/check_linux_x86_64.py), not an AArch64 control; on an AArch64 host its "
    "execution legs print skips (measured on Darwin, L13-P6 census)"
)
SUITE_CLASS: dict[str, tuple[str, str]] = {
    f"trust-cg-codegen/test/{name}": ("neither", _X86_EXECUTION)
    for name in (
        "e2e_x86_64_aggregate_abi", "e2e_x86_64_aggregate_byval_arg", "e2e_x86_64_atomics",
        "e2e_x86_64_bool_to_byte", "e2e_x86_64_callee_saved", "e2e_x86_64_calling_conv", "e2e_x86_64_checked_arith",
        "e2e_x86_64_correctness", "e2e_x86_64_data_reloc", "e2e_x86_64_differential",
        "e2e_x86_64_dispatcher", "e2e_x86_64_fp", "e2e_x86_64_fp_across_call",
        "e2e_x86_64_heap_alloc", "e2e_x86_64_i128_checked_mul", "e2e_x86_64_i128_const_shift",
        "e2e_x86_64_i128_div",
        "e2e_x86_64_i128_stack_abi",
        "e2e_x86_64_indirect_calls", "e2e_x86_64_internal_multi_result",
        "e2e_x86_64_large_struct_byval", "e2e_x86_64_link", "e2e_x86_64_mixed_width_shift",
        "e2e_x86_64_module_batch_fnptr", "e2e_x86_64_module_batch_globals",
        "e2e_x86_64_opt_correctness", "e2e_x86_64_pair_bool_lane", "e2e_x86_64_recursion",
        "e2e_x86_64_scale_emergent", "e2e_x86_64_sext_bool", "e2e_x86_64_sib_rmw", "e2e_x86_64_swiftcc",
        "e2e_x86_64_symbol_address",
        "e2e_x86_64_triple_oracle", "e2e_x86_64_varargs", "e2e_x86_64_vector_fp",
        "e2e_x86_64_windows_host_objects", "guard_kernel_gate_x86_linkrun", "weak_linkage_x86",
        "x86_64_bool_load_abi", "x86_64_bool_not_abi", "x86_64_coff_link_smoke",
        "x86_64_sysv_ay_abi",
    )
} | {
    # L11-P11: a measurement, not a requirement. Every test prints SKIP unless
    # TCG_JIT_PROOF_CENSUS=1 is set; with the installed package's AY a full run
    # takes hours (reports/2026-10-12-jit-proof-coverage-census).
    "trust-cg-codegen/test/jit_proof_coverage_census": (
        "neither",
        "opt-in measurement campaign (TCG_JIT_PROOF_CENSUS=1): the proof-required JIT coverage census",
    ),
}

# Tests that do not run in their suite's default invocation on some host:
# (suite id, libtest test name) -> (lane, reason). See the module docstring.
TEST_LANES = ("darwin", "linux", "formal", "external-cert", "other-lane", "opt-in")
CAMPAIGN_LANES = ("formal", "external-cert")
_FORMAL = "solver-backed body runs only with TRUST_CG_RUN_FORMAL_PROOF_TESTS=1 (the strict proof campaign)"
_EXTERNAL_CERT = (
    "external-certificate campaign: runs only with TRUST_CG_RUN_EXTERNAL_CERT_TESTS=1 and explicit "
    "AY_SOLVER_PATH and TCG_EXTERNAL_CLEAN_CHECKER"
)
_MEASUREMENT = (
    "measurement campaign (TRUST_CG_RUN_MEASUREMENT_TESTS=1, release build): a timing observation, "
    "not a correctness requirement of either matrix"
)
_WASM_LINK = (
    "WebAssembly link/run leg: needs wasm-ld (WASM_LD) and node; no runner in this repository provides "
    "wasm-ld, so neither AArch64 matrix executes it (a named residual)"
)
_X86_LEG = "x86-64 execution leg: needs an x86-64 host or Rosetta 2 (TRUST_CG_RUN_ROSETTA_LINKRUN=1)"
TEST_CLASS: dict[tuple[str, str], tuple[str, str]] = {
    **{("trust-cg-verify/test/proof_gate_strict", name): ("formal", _FORMAL) for name in (
        "a_real_proof_check_records_the_tools_that_ran",
        "aarch64_eh_coverage_proofs_are_formally_verified",
        "aarch64_eh_lsda_proofs_are_formally_verified",
        "aarch64_elf_ldst_lo12_rows_are_formally_verified",
        "aarch64_elf_tls_reloc_proofs_are_formally_verified",
        "aarch64_fabs_full_bit_bindings_are_formally_verified",
        "aarch64_macho_call_reloc_proofs_are_formally_verified",
        "aarch64_macho_data_reloc_proofs_are_formally_verified",
        "aarch64_macho_tlvp_reloc_proofs_are_formally_verified",
        "aarch64_tlv_thunk_proof_is_formally_verified",
        "aggregate_placement_proofs_are_formally_verified",
        "coroutine_frame_proofs_are_formally_verified",
        "full_database_is_formally_verified",
        "pblendvb_canonical_mask_is_formally_verified",
        "representative_arithmetic_is_formally_verified",
        "wired_checked_overflow_bindings_are_formally_verified",
        "wired_packed_csel_fp_bindings_are_formally_verified",
    )},
    ("trust-cg-verify/test/aarch64_instruction_word_formal", "solver_lane_probe"): ("formal", _FORMAL),
    ("trust-cg-verify/test/aarch64_pure_jump_loop",
     "a_real_checked_proof_credits_only_the_exact_source_bound_loop"): ("formal", _FORMAL),
    ("trust-cg-verify/lib", "pass_validators::tests::popcnt_swar_64_emitted_width_genuinely_verifies"):
        ("formal", _FORMAL),
    ("trust-cg-verify/lib",
     "aarch64_memory_effect::tests::with_the_dev_ay_every_part_is_checked_by_each_capable_clean_and_the_row_stays_uncredited"):
        ("formal", _FORMAL),
    ("trust-cg-verify/lib", "obligation_cert_store::tests::end_to_end_mint_then_consume_real_binaries"):
        ("external-cert", _EXTERNAL_CERT),
    ("trust-cg-verify/lib",
     "function_verifier::tests::ror_immediate_live_checker_is_verified"):
        ("external-cert", "runs only against an explicitly named TCG_EXTERNAL_CLEAN_CHECKER, which the "
         "external-certificate campaign sets"),
    ("trust-cg-verify/lib", "verdict_db::tests::tier0_popcnt_canary_timing_probe"): ("opt-in", _MEASUREMENT),
    ("trust-cg-verify/lib", "verdict_db::tests::tier0_registry_discharge_timing_probe"): ("opt-in", _MEASUREMENT),
    ("trust-cg-verify/test/aarch64_stack_limit_lemma",
     "the_lemma_has_no_counterexample_and_reports_its_solver_verdict"): ("formal", _FORMAL),
    **{("trust-cg-codegen/lib", f"compiler::jit_source_campaign::{name}"): ("external-cert", _EXTERNAL_CERT)
       for name in ("high_level_source_bound_always_verify_native_campaign",
                    "high_level_source_bound_cached_verify_native_campaign")},
    ("trust-cg-codegen/lib", "compiler::tests::x86_parallel_multi_function_compile_time_delta"):
        ("opt-in", _MEASUREMENT),
    ("trust-cg-codegen/lib", "macho::reparse::tests::bench_reparse_overhead"): ("opt-in", _MEASUREMENT),
    ("trust-cg-codegen/lib", "pipeline::tests::sampled_verify_overhead_probe"): ("opt-in", _MEASUREMENT),
    ("trust-cg-jit-matrix/lib", "propagation_context_kernel::tests::perf_jit_cached_vs_bcpstate"):
        ("opt-in", _MEASUREMENT),
    ("trust-cg-regalloc/lib", "post_ra_coalesce::tests::test_huge_function_identity_and_speed_2000_blocks"):
        ("opt-in", _MEASUREMENT),
    ("trust-cg-regalloc/lib", "regalloc_validator::tests::bench_compute_pre_expected"): ("opt-in", _MEASUREMENT),
    **{("trust-cg-codegen/test/ty_request_1_1_replay_bundle_reducer", name): (
        "opt-in", "replays a real TY request bundle named by TRUST_CG_TY_REPLAY_BUNDLE, a downstream "
        "consumer artifact (L13-P8), not repository input") for name in (
        "env_ty_request_replay_bundle_jit_invokes_in_child_when_present",
        "env_ty_request_replay_bundle_low_level_compile_raw_alloc_size_matches_proof_when_present",
        "env_ty_request_replay_bundle_parses_and_compiles_when_present",
    )},
    ("trust-cg-codegen/test/guard_kernel_gate_riscv_compile_e2e", "riscv_compile_gate_off_child"): (
        "opt-in", "child-process entry point of riscv_compile_gate_off_keeps_bounds_check_with_real_trap, "
        "which runs it; alone it returns without a body"),
    ("trust-cg-codegen/test/proof_evidence_honesty",
     "a_certificates_required_compile_refuses_rather_than_downgrading"): (
        "opt-in", "exercises the refusal of a host without AY and Clean; a host with the proof route has "
        "nothing to refuse, and both matrices require that route"),
    **{("trust-cg-codegen/lib", f"compiler::x86_envelope_jit_tests::{name}"): (
        "other-lane", "x86-64 JIT execution: needs a System V x86-64 host") for name in (
        "x86_jit_envelope_cache_predicates_on_live_valid_reports",
        "x86_verifying_jit_recertifies_envelope_shapes_on_every_cached_call",
    )},
    **{("trust-cg-codegen/test/e2e_abi_dual_target_linkrun", name): ("other-lane", _X86_LEG) for name in (
        "test_abi_linkrun_const_sentinel_x86_64", "test_abi_linkrun_sum6i_3d_x86_64",
        "test_abi_linkrun_sum8_i64_x86_64",
    )},
    **{("trust-cg-codegen/test/e2e_elf_link", name): ("other-lane", "x86-64 ELF link-and-run leg: needs an "
       "x86-64 Linux host") for name in ("test_e2e_elf_add_link_and_run", "test_e2e_elf_const42_link_and_run")},
    ("trust-cg-codegen/test/e2e_riscv_elf", "test_riscv_e2e_external_tool_validation"): (
        "other-lane", "external RISC-V cross-tool validation: needs the RISC-V oracle lane's cross tools"),
    ("trust-cg-codegen/test/wasm_g1_lane_semantics", "linked_relocatable_object_agrees_with_the_interpreter"):
        ("other-lane", _WASM_LINK),
    **{("trust-cg-codegen/test/wasm_g2_lane_objects", name): ("other-lane", _WASM_LINK) for name in (
        "frem_binds_only_the_c_library_routine",
        "function_address_imports_the_table_without_an_indirect_call",
        "initializerless_weak_family_global_is_a_strong_undefined_data_symbol",
        "object_lane_admits_hidden_functions_and_available_externally_globals",
        "relocations_are_sorted_by_offset",
        "runtime_named_module_local_symbols_compile_when_not_referenced_by_name",
        "static_function_pointer_to_another_object_is_a_function_symbol",
    )},
    **{("trust-cg-codegen/test/wasm_g3_lane_frames", name): ("other-lane", _WASM_LINK) for name in (
        "a_parameter_live_along_the_untaken_edge_keeps_its_bytes",
        "a_repeated_alloca_is_fresh_while_earlier_pointers_are_observable",
        "a_repeated_alloca_no_earlier_pointer_can_reach_keeps_one_slot",
        "a_zero_byte_bulk_memory_op_through_an_out_of_memory_pointer_is_a_no_op",
        "coalesced_locals_keep_loop_carried_values",
        "entry_backedge_by_address_parameters_never_write_the_callers_storage",
        "homes_share_frame_bytes_by_liveness",
    )},
    **{("trust-cg-codegen/test/wasm_r3_lane_frames", name): ("other-lane", _WASM_LINK) for name in (
        "a_path_correlated_pointer_join_compiles_and_agrees",
        "indirect_repr_c_float_struct_stays_in_its_frames_from_the_first_call",
    )},
    **{("trust-cg-codegen/test/wasm_r6_lane", name): ("other-lane", _WASM_LINK) for name in (
        "a_link_replaceable_callee_never_writes_the_callers_argument",
        "an_alloca_with_a_runtime_count_is_carved_from_the_stack",
        "an_exposed_address_keeps_its_allocation",
        "an_irreducible_cfg_lowers_as_a_dispatch_loop",
    )},
    ("trust-cg-codegen/test/wasm_value_domain_differential",
     "linked_relocatable_object_agrees_with_the_interpreter"): ("other-lane", _WASM_LINK),
    **{("trust-cg-codegen/test/wasm_p2_lane_i128div", name): ("other-lane", _WASM_LINK) for name in (
        "linked_object_agrees_with_the_interpreter",
        "several_objects_link_with_one_helper_copy",
    )},
    **{("trust-cg-codegen/test/wasm_p3_emission", name): ("other-lane", _WASM_LINK) for name in (
        "control_cleanup_is_validated_and_removes_branches",
        "hand_written_programs_are_emitted_with_validated_rewrites",
        "premised_gep_folds_are_emitted_with_validated_rewrites",
        "pressure_limited_stackify_is_emitted_with_validated_rewrites",
        "random_irreducible_cfgs_with_memory_are_emitted_with_validated_rewrites",
        "random_reducible_cfgs_are_emitted_with_validated_rewrites",
        "stage_b_rewrites_are_emitted_with_validated_rewrites",
    )},
    **{("trust-cg-codegen/test/wasm_p4_irmid", name): ("other-lane", _WASM_LINK) for name in (
        "stage_b_forwards_stores_and_promotes_a_constant_table",
        "the_object_lane_runs_the_mid_end_and_links",
    )},
    ("trust-cg-codegen/test/wasm_p5_argpromo", "the_object_passes_promoted_slots_by_value_and_links"):
        ("other-lane", _WASM_LINK),
    ("trust-cg-codegen/test/wasm_p5_inline", "the_object_lane_honours_the_never_inline_side_table_and_links"):
        ("other-lane", _WASM_LINK),
    ("trust-cg-codegen/test/wasm_p5_range", "the_object_lane_folds_and_links"): ("other-lane", _WASM_LINK),
    ("trust-cg-codegen/test/wasm_p5_sroa", "the_object_lane_promotes_and_links"): ("other-lane", _WASM_LINK),
    **{("trust-cg-codegen/test/wasm_p6_multivalue", name): ("other-lane", _WASM_LINK) for name in (
        "a_caller_needs_its_callees_internal_entries",
        "a_session_without_multivalue_keeps_the_c_form",
        "internal_entries_link_across_objects_and_agree",
    )},
    ("trust-cg-codegen/test/wasm_p6_pair", "a_pair_carried_object_links_and_agrees"): ("other-lane", _WASM_LINK),
    ("trust-cg-codegen/test/wasm_p8_loops", "the_object_lane_closes_and_links"): ("other-lane", _WASM_LINK),
    **{("trust-cg-codegen/test/wasm_r7_lane", name): ("other-lane", _WASM_LINK) for name in (
        "the_c_librarys_bulk_memory_functions_do_not_pin_their_arguments",
        "two_by_address_entry_parameters_compile_without_a_frame",
    )},
    ("trust-cg-codegen/test/wasm_v57_templates", "instance_bodies_through_the_mid_end_at_o2_and_both_lanes"):
        ("other-lane", _WASM_LINK),
}

# `#[ignore]`d unit and integration tests, by suite and libtest name, with the
# reason. They are opt-in campaigns, timing observations or fixture dumpers:
# never a pass and never run by the matrix.
_SAVED_PAIR = "requires authenticated AY plus an independent proof checker (its #[ignore] reason)"
IGNORED_TESTS: dict[tuple[str, str], str] = {
    ("trust-cg-codegen/lib", "jit_cert::jit_request_cache_tests::raw_machir_request_cache_real_exhaustive_campaign"):
        "the explicit real-tool raw-MachIR request-cache campaign (its #[ignore] reason)",
    ("trust-cg-opt/lib", "scheduler::tests::test_pressure_forced_original_dense_microbenchmark"):
        "diagnostic dense-DAG microbenchmark, run with --release --ignored",
    ("trust-cg-opt/lib", "scheduler::tests::test_pressure_forced_original_microbenchmark"):
        "diagnostic microbenchmark, run with --release --ignored",
    ("trust-cg-regalloc/lib", "physical_liveness::tests::physical_liveness_timing_observation"):
        "optimized-build timing observation, run with --release --ignored",
    ("trust-cg-codegen/test/aarch64_multi_def_induction_start", "reduction::reduction_split_start_from_search_stop"):
        "needs TRUST_CG_DISABLE_PASSES=looplatch, which loop-latch-layout's rotation otherwise preempts "
        "(its #[ignore] reason)",
    ("trust-cg-verify/test/wasm_encoding_gate", "sleb128_full_i32_range_is_exhaustive"):
        "4.29e9-iteration exhaustive sweep, run with --release --ignored",
    # L13-P14: the SSE lane family's SDM-vs-silicon differential compiles only
    # for x86_64; on both AArch64 matrix hosts these are named stubs, so the
    # absence is a listed residual, never a silent pass. The soundness gate runs
    # the real tests on a native x86-64 host (SOUNDNESS_X86_HOST); Rosetta 2 is
    # translation, not silicon (OD-34).
    **{("trust-cg-verify/test/x86_sse_lane_gate", f"silicon::{name}"):
       "x86-64 silicon differential NOT RUN on an AArch64 host: compiled only for x86_64 "
       "(its #[ignore] reason; OD-34, L13-P14)" for name in (
        "ptest_zf_and_cf_agree_with_this_cpu",
        "the_sdm_denotation_agrees_with_this_cpu",
    )},
    ("trust-cg-verify/lib", "aarch64_pair_memory_forms::tests::dump_pair_memory_smt2"):
        "fixture dumper that writes the SMT-LIB queries; not a check",
    ("trust-cg-verify/lib", "aarch64_scalar_memory_proofs::tests::dump_scalar_memory_smt2"):
        "fixture dumper that writes the SMT-LIB queries; not a check",
    **{("trust-cg-verify/lib", f"x86_source_bound_body::tests::{name}"):
       "fixture printer that regenerates the pinned x86 body-theorem fixtures; not a check" for name in (
        "memory::print_memory_fixtures",
        "slice5_qualification::print_slice_five_fixtures",
        "slice6_qualification::print_slice_six_fixtures",
        "slice7_qualification::print_slice_seven_fixtures",
        "slice8_qualification::print_slice_eight_fixtures",
        "slice9_qualification::print_slice_nine_fixtures",
        "slice10_qualification::print_slice_ten_fixtures",
        "slice11_qualification::print_slice_eleven_fixtures",
        "slice12_qualification::print_slice_twelve_fixtures",
        "slice13_qualification::print_slice_thirteen_fixtures",
        "slice14_qualification::print_slice_fourteen_fixtures",
        "slice15_qualification::print_slice_fifteen_fixtures",
        "slice17_qualification::print_slice_seventeen_fixtures",
        "slice20_qualification::print_slice_twenty_fixtures",
        "slice21_qualification::print_slice_twenty_one_fixtures",
        "slice22_qualification::print_slice_twenty_two_fixtures",
        "slice23_qualification::print_slice_twenty_three_fixtures",
        "slice23_qualification::print_slice_twenty_three_qualification_fixtures",
        "slice24::print_slice_twenty_four_fixtures",
        "slice24_qualification::print_slice_twenty_four_qualification_fixtures",
        "slice25::print_slice_twenty_five_fixtures",
        "slice25::print_lea_sib_control_refusals",
        "slice25_qualification::print_slice_twenty_five_qualification_fixtures",
        "slice24c::print_slice_twenty_four_c_fixtures",
        "slice24c_qualification::print_slice_twenty_four_c_qualification_fixtures",
        "od233::print_od233_fixtures",
        "od233::print_od233_with_and_without_the_rule",
        "i128_const_shift_qualification::print_i128_const_shift_fixtures",
        "i128_mulo::print_i128_mulo_fixtures",
        "arraygep::print_arraygep_fixtures",
    )},
    ("trust-cg-codegen/test/e2e_x86_64_i128_const_shift", "census_proxy_lists_functions_with_a_folded_i128_shift"):
        "census proxy of the OD-215 report over TCG_I128_CONST_SHIFT_CENSUS_DIR (a core dump); "
        "prints, not a check",
    ("trust-cg-codegen/test/e2e_x86_64_i128_checked_mul", "write_x86_64_i128_checked_mul_objects"):
        "measurement aid of the OD-224 report: writes the x86-64 objects to MULO_OBJ_DIR for an "
        "instruction count; not a check",
    ("trust-cg-lower/lib",
     "adapter::i128_mulo_tests::the_division_free_expansions_are_exact_on_every_pair_at_sixteen_bits"):
        "the OD-224 exhaustive 2^32-pair sweep per sign of the 16-bit analog (minutes on two threads; "
        "its #[ignore] reason), run once per change of the expansion with --ignored --exact",
    ("trust-cg-verify/lib",
     "x86_source_bound_body::tests::od233_qualification::host_qualification_times_the_largest_recut_statement"):
        "measurement of the OD-233 report: replays every part of slice 20's ManySlots at every clean "
        "point on the host's AY, without the rule and with it, and prints each part's verdict and time "
        "(X86_BODY_OD233_RECUT_TIME); not a check (its #[ignore] reason)",
    ("trust-cg-verify/lib", "x86_source_bound_body::tests::slice9_qualification::dump_the_two_encodings_of_every_fixture"):
        "fixture dumper that writes both x86 body-theorem encodings as SMT-LIB to TCG_X86_BODY_QUALIFY_DUMP "
        "for an offline replay; not a check",
    ("trust-cg-verify/lib",
     "x86_source_bound_body::tests::host_qualification_replays_each_deadline_bound_label_with_the_recorded_budget"):
        "explicit lane of a host qualification on its qualified replayer pair, which the host's "
        "commands/qualify.sh runs after --lib _qualification: replays each deadline-bound label with a "
        "300 s budget, minutes per label (its #[ignore] reason; DR-PER-HOST-QUALIFIED-PAIR-20261015)",
    **{("trust-cg-verify/lib", f"aarch64_saved_pair::tests::{name}"): _SAVED_PAIR for name in (
        "saved_pair_raw_negative_missing_second_slot_preservation",
        "saved_pair_raw_negative_reversed_restore_order",
        "saved_pair_raw_negative_wrong_restore_writeback",
        "saved_pair_raw_positive_captured_ty_outer_pair_80",
        "saved_pair_raw_positive_fp_lr_16",
        "saved_pair_raw_positive_ordinary_callee_save_32",
    )},
}


# Tests whose own checked output contains a skip spelling while the test runs
# to completion: (suite id, test) -> (line prefix, reason). Only lines with
# that exact prefix in that test's output are exempt.
SKIP_OUTPUT_EXEMPTIONS: dict[tuple[str, str], tuple[str, str]] = {
    ("trust-cg-verify/lib", "formal_gap::tests::a_rejected_cegis_proof_fails_and_only_a_named_gap_skips"): (
        "SKIP t: ",
        "the test calls check_cegis_equivalent for the synthetic name `t` without proof authority and "
        "checks that it skips by name; the line is the checked behavior, not an early return",
    ),
}


@dataclass
class Suite:
    package: str
    kind: str  # lib, bin, test, example, bench or doc
    name: str
    src_path: Path
    features: tuple[str, ...]
    enabled_features: frozenset[str]
    compiled: dict[str, bool] = field(default_factory=dict)
    file_cfg: list[str] = field(default_factory=list)
    census: int = 0
    klass: str = "both"
    reason: str = ""
    basis: str = "default"

    @property
    def id(self) -> str:
        if self.kind in ("lib", "doc"):
            return f"{self.package}/{self.kind}"
        return f"{self.package}/{self.kind}/{self.name}"

    @property
    def required(self) -> tuple[str, ...]:
        return REQUIRED_HOSTS[self.klass]

    def cargo_arguments(self) -> list[str]:
        """Arguments after `test` that select exactly this suite."""
        arguments = ["-p", self.package]
        if self.features:
            arguments += ["--features", ",".join(self.features)]
        if self.kind == "doc":
            return arguments + ["--doc"]
        if self.kind == "lib":
            return arguments + ["--lib"]
        return arguments + [SELECTORS[self.kind], self.name]


# ---------------------------------------------------------------------------
# Static source evidence.
# ---------------------------------------------------------------------------

def _load(name: str, path: Path):
    spec = importlib.util.spec_from_file_location(name, path)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"required helper is missing: {path}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


@functools.cache
def _native_matrix():
    return _load("_full_matrix_native_host_matrix", SCRIPTS / "native_test_host_matrix.py")


@functools.cache
def darwin_floor():
    return _load("_full_matrix_darwin_floor", SCRIPTS / "check_darwin_aarch64.py")


@functools.cache
def linux_floor():
    return _load("_full_matrix_linux_floor", SCRIPTS / "check_linux_aarch64.py")


TEST_ATTRIBUTE = re.compile(r"#\[(?:tokio::)?test\]|#\[cfg_attr\([^\[\]]*?,\s*test\s*\)\]")
MOD_DECLARATION = re.compile(
    r"(?P<attributes>(?:#\[[^\]]*\]\s*)*)(?:pub(?:\([^)]*\))?\s+)?mod\s+(?P<name>[A-Za-z_][A-Za-z0-9_]*)\s*;"
)
PATH_ATTRIBUTE = re.compile(r'#\[path\s*=\s*"([^"]+)"\]')
INCLUDE = re.compile(r'\binclude!\(\s*"([^"]+)"\s*\)')
DOC_LINE = re.compile(r"^\s*(?:///|//!)(.*)$")
FENCE = re.compile(r"^\s*(```+|~~~+)\s*([^`]*)$")
# Code-block languages rustdoc runs as doc-tests (an empty info string is Rust).
DOCTEST_ATTRIBUTES = {
    "rust", "should_panic", "no_run", "compile_fail", "edition2015", "edition2018",
    "edition2021", "edition2024", "test_harness", "standalone_crate",
}


BLOCK_COMMENT = re.compile(r"/\*.*?\*/", re.DOTALL)
LINE_TOKEN = re.compile(r'\\.|"|//')


def strip_comments(text: str) -> str:
    """Drop block comments, then `//` line comments outside string literals.

    The same rule as scripts/native_test_host_matrix.py's strip_comments,
    scanning only the escape, quote and `//` tokens of each line.
    """
    out = []
    for line in BLOCK_COMMENT.sub("", text).splitlines():
        if "//" in line:
            in_string = False
            for token in LINE_TOKEN.finditer(line):
                if token.group() == '"':
                    in_string = not in_string
                elif token.group() == "//" and not in_string:
                    line = line[:token.start()]
                    break
        out.append(line)
    return "\n".join(out)


def inner_cfg_predicates(text: str) -> list[str]:
    """Every `#![cfg(...)]` predicate in comment-stripped source."""
    return _native_matrix().predicates(strip_comments(text), "#![cfg(")


def evaluate(predicate: str, facts: dict) -> bool:
    return _native_matrix().evaluate(predicate, facts)


@functools.cache
def stripped_source(path: Path) -> str:
    """A source file without comments (read once per process)."""
    return strip_comments(path.read_text(encoding="utf-8", errors="replace"))


def module_tree(root: Path) -> list[Path]:
    """The root file and every file it reaches by `mod name;`, `#[path]` or `include!`."""
    return list(_module_tree(root.resolve()))


@functools.cache
def _module_tree(root: Path) -> tuple[Path, ...]:
    seen: list[Path] = []
    pending = [(root, True)]
    while pending:
        path, is_root = pending.pop()
        if path in seen or not path.is_file():
            continue
        seen.append(path)
        text = stripped_source(path)
        directory = path.parent
        # A non-root, non-mod.rs file owns the directory named after itself.
        owned = directory if is_root or path.name == "mod.rs" else directory / path.stem
        for match in MOD_DECLARATION.finditer(text):
            path_attribute = PATH_ATTRIBUTE.search(match.group("attributes"))
            if path_attribute:
                pending.append(((directory / path_attribute.group(1)).resolve(), False))
                continue
            name = match.group("name")
            for candidate in (owned / f"{name}.rs", owned / name / "mod.rs"):
                if candidate.is_file():
                    pending.append((candidate.resolve(), False))
                    break
        for relative in INCLUDE.findall(text):
            pending.append(((directory / relative).resolve(), False))
    return tuple(seen)


def test_census(root: Path) -> int:
    """`#[test]` attributes in the module tree (a static count, not a host count)."""
    return sum(len(TEST_ATTRIBUTE.findall(stripped_source(path))) for path in module_tree(root))


def doctest_census(root: Path) -> int:
    """Doc-comment code blocks rustdoc would run (not `ignore`, not another language)."""
    count = 0
    for path in module_tree(root):
        fence = None
        for line in path.read_text(encoding="utf-8", errors="replace").splitlines():
            doc = DOC_LINE.match(line)
            if doc is None:
                continue
            opened = FENCE.match(doc.group(1))
            if opened is None:
                continue
            if fence is None:
                fence = opened.group(1)
                attributes = {part.strip() for part in re.split(r"[,\s]+", opened.group(2)) if part.strip()}
                if "ignore" not in attributes and attributes <= DOCTEST_ATTRIBUTES:
                    count += 1
            elif opened.group(1).startswith(fence[0]) and not opened.group(2).strip():
                fence = None
    return count


def enabled_features(declared: dict[str, list[str]], requested: Iterable[str]) -> frozenset[str]:
    """Package features enabled by `default` plus `requested`, transitively."""
    enabled: set[str] = set()
    pending = ["default", *requested]
    while pending:
        feature = pending.pop()
        if feature in enabled or feature not in declared:
            continue
        enabled.add(feature)
        pending.extend(entry for entry in declared[feature] if "/" not in entry and not entry.startswith("dep:"))
    return frozenset(enabled)


FEATURE_LITERAL = re.compile(r'feature\s*=\s*"([^"]+)"')


def suite_features(package: dict, target: dict, predicates: Sequence[str]) -> tuple[str, ...]:
    """Required features, plus every declared non-default feature a file-level cfg names positively."""
    declared = package.get("features", {})
    defaults = enabled_features(declared, ())
    wanted = list(target.get("required-features") or [])
    for predicate in predicates:
        if "not(" in predicate:
            continue
        wanted.extend(name for name in FEATURE_LITERAL.findall(predicate) if name in declared and name not in defaults)
    return tuple(sorted(set(wanted)))


# ---------------------------------------------------------------------------
# Inventory.
# ---------------------------------------------------------------------------

@functools.cache
def _trust_toolchain():
    return _load("_full_matrix_trust_toolchain", SCRIPTS / "trust_toolchain.py")


def suite_targo(environment: dict) -> str:
    """The targo the suites build with, and so the one `load_metadata` runs.

    scripts/trust_cargo.sh builds with $TRUST_TARGO when set (an absolute
    path), else with the package scripts/trust_toolchain.py resolves from PATH
    for the `workspace` purpose. That package's own file runs, never the PATH
    `targo`: it may be an atpkg launcher shim whose shell prelude the resolver
    reads but never runs (DR-ATPKG-PRELUDE-SHIM-20261015), and the denominator
    must not rest on what such a prelude prints.
    """
    explicit = environment.get("TRUST_TARGO", "")
    if explicit:
        if not (os.path.isabs(explicit) and os.path.isfile(explicit) and os.access(explicit, os.X_OK)):
            raise RuntimeError(f"TRUST_TARGO must name an executable file by absolute path, got {explicit!r}")
        return explicit
    return _trust_toolchain().resolve(path=environment.get("PATH", ""), purpose="workspace")["targo"]


def load_metadata(root: Path = ROOT, environment: dict | None = None) -> dict:
    """Cargo's own target list for the root workspace, from the package targo (`suite_targo`)."""
    environ = dict(os.environ if environment is None else environment)
    targo = suite_targo(environ)
    # trustc refuses every TRUST_CG_*/TCG_* control, even for metadata probes.
    environ = {key: value for key, value in environ.items() if not key.startswith(("TRUST_CG_", "TCG_"))}
    result = subprocess.run(
        [targo, "metadata", "--locked", "--no-deps", "--format-version", "1"],
        cwd=root, env=environ, capture_output=True, text=True, check=False, timeout=300,
    )
    if result.returncode != 0:
        raise RuntimeError(f"{targo} metadata failed ({result.returncode}): {result.stderr.strip()}")
    return json.loads(result.stdout)


def suites(metadata: dict) -> list[Suite]:
    """Every test suite of every workspace member, classified."""
    members = set(metadata.get("workspace_members", []))
    found: list[Suite] = []
    for package in sorted(metadata.get("packages", []), key=lambda item: item["name"]):
        if package.get("id") not in members:
            continue
        declared = package.get("features", {})
        for target in sorted(package.get("targets", []), key=lambda item: (item["kind"], item["name"])):
            kinds = [kind for kind in target.get("kind", []) if kind in TEST_KINDS]
            if not kinds:
                continue
            kind = "lib" if kinds[0] in ("lib", "proc-macro") else kinds[0]
            source = Path(target["src_path"])
            text = source.read_text(encoding="utf-8", errors="replace") if source.is_file() else ""
            predicates = inner_cfg_predicates(text) if kind != "lib" else []
            entries = []
            if target.get("test"):
                entries.append(kind)
            if kind == "lib" and target.get("doctest"):
                entries.append("doc")
            for entry in entries:
                features = suite_features(package, target, predicates) if entry != "doc" else ()
                found.append(Suite(
                    package=package["name"], kind=entry, name=target["name"], src_path=source,
                    features=features, enabled_features=enabled_features(declared, features),
                    file_cfg=list(predicates) if entry != "doc" else [],
                ))
    for suite in found:
        classify(suite)
    return found


def classify(suite: Suite) -> None:
    """Fill in compiled hosts, census and the single class of `suite`."""
    for host in HOSTS:
        facts = dict(HOST_FACTS[host], feature=set(suite.enabled_features))
        suite.compiled[host] = all(evaluate(predicate, facts) for predicate in suite.file_cfg)
    suite.census = doctest_census(suite.src_path) if suite.kind == "doc" else test_census(suite.src_path)
    if suite.id in SUITE_CLASS:
        suite.klass, suite.reason = SUITE_CLASS[suite.id]
        suite.basis = "classified"
        return
    suite.klass, suite.reason, suite.basis = derived_class(suite)


def derived_class(suite: Suite) -> tuple[str, str, str]:
    """The class static evidence alone gives `suite`."""
    if suite.census == 0:
        what = "runnable doc-test block" if suite.kind == "doc" else "#[test] function"
        return "empty", f"no {what} in its module tree", "static census"
    compiled = tuple(host for host in HOSTS if suite.compiled[host])
    if compiled == HOSTS:
        if macos_guarded_unmeasured_on_linux(suite):
            return "darwin", (
                'its own source guards legs on target_os = "macos" and none on Linux, and it is not a '
                "Linux-floor target: not required on Linux until a Linux run measures it"
            ), "macOS guard"
        return "both", "", "default"
    predicate = " && ".join(suite.file_cfg)
    if not compiled:
        return "neither", f"file-level cfg({predicate}) compiles it out on both AArch64 hosts", "file-level cfg"
    other = next(host for host in HOSTS if host not in compiled)
    return compiled[0], f"file-level cfg({predicate}) compiles it out on {other}", "file-level cfg"


MACOS_GUARD = re.compile(r'target_os\s*=\s*"macos"')
LINUX_GUARD = re.compile(r'target_os\s*=\s*"linux"')


def macos_guarded_unmeasured_on_linux(suite: Suite) -> bool:
    """An integration target whose own file guards legs on macOS only and that no Linux floor measures."""
    if suite.kind != "test":
        return False
    text = stripped_source(suite.src_path.resolve())
    if not MACOS_GUARD.search(text) or LINUX_GUARD.search(text):
        return False
    return (suite.package, suite.name) not in set(linux_floor().TARGETS)


def host_skipped_tests(suite_id: str, host: str) -> list[str]:
    """Tests the suite's runs on `host` never execute: another host's, and opt-in ones."""
    return sorted(test for (identifier, test), (lane, _) in TEST_CLASS.items()
                  if identifier == suite_id and lane in (*HOSTS, "other-lane", "opt-in") and lane != host)


# Lanes neither AArch64 matrix executes; see required_by_neither_host().
NO_HOST_LANES = ("other-lane", "opt-in")


def required_by_neither_host() -> dict[str, list[str]]:
    """`suite id::test` of every test no AArch64 matrix runs, by lane: a named residual, never a pass."""
    lanes: dict[str, list[str]] = {lane: [] for lane in NO_HOST_LANES}
    for (identifier, test), (lane, _) in sorted(TEST_CLASS.items()):
        if lane in NO_HOST_LANES:
            lanes[lane].append(f"{identifier}::{test}")
    return lanes


def campaign_tests(suite_id: str) -> dict[str, list[str]]:
    """The suite's proof-campaign tests by lane; they leave its default invocation."""
    lanes: dict[str, list[str]] = {}
    for (identifier, test), (lane, _) in sorted(TEST_CLASS.items()):
        if identifier == suite_id and lane in CAMPAIGN_LANES:
            lanes.setdefault(lane, []).append(test)
    return lanes


def ignored_tests(suite_id: str) -> list[str]:
    return sorted(test for (identifier, test) in IGNORED_TESTS if identifier == suite_id)


def minimum_passes(suite: Suite, host: str) -> int:
    """Executed passes a required suite must report on `host` (always positive)."""
    if host not in suite.required:
        return 0
    minimum = 1
    if host == "darwin" and suite.kind == "test":
        for package, target, floor_minimum in darwin_floor().TARGETS:
            if (package, target) == (suite.package, suite.name):
                minimum = max(minimum, floor_minimum)
    if host == "linux" and suite.kind == "test":
        minimum = max(minimum, linux_floor().TARGET_MINIMUM_PASSES.get((suite.package, suite.name), 1))
    return minimum


def problems(found: Sequence[Suite]) -> list[str]:
    """Every inconsistency between the tables, the source tree and the floors."""
    issues: list[str] = []
    by_id: dict[str, Suite] = {}
    for suite in found:
        if suite.id in by_id:
            issues.append(f"{suite.id}: classified more than once")
        by_id[suite.id] = suite
    for suite_id, entry in sorted(SUITE_CLASS.items()):
        suite = by_id.get(suite_id)
        if suite is None:
            issues.append(f"SUITE_CLASS names no suite: {suite_id}")
            continue
        if not isinstance(entry, tuple) or len(entry) != 2 or entry[0] not in CLASSES or not str(entry[1]).strip():
            issues.append(f"{suite_id}: SUITE_CLASS entry needs a class in {CLASSES} and a reason")
            continue
        derived = derived_class(suite)
        if entry[0] == derived[0]:
            issues.append(f"{suite_id}: SUITE_CLASS entry is stale; static evidence already gives {derived[0]}")
        for host in REQUIRED_HOSTS[entry[0]]:
            if not suite.compiled[host]:
                issues.append(f"{suite_id}: classified {entry[0]} but its file-level cfg compiles it out on {host}")
        if REQUIRED_HOSTS[entry[0]] and suite.census == 0:
            issues.append(f"{suite_id}: classified {entry[0]} but its module tree has no test")
    for (suite_id, test), entry in sorted(TEST_CLASS.items()):
        suite = by_id.get(suite_id)
        if suite is None:
            issues.append(f"TEST_CLASS names no suite: {suite_id} ({test})")
            continue
        lane, reason = entry if isinstance(entry, tuple) and len(entry) == 2 else ("", "")
        if lane not in TEST_LANES or not str(reason).strip():
            issues.append(f"{suite_id}::{test}: TEST_CLASS entry needs a lane in {TEST_LANES} and a reason")
            continue
        if not suite.required:
            issues.append(f"{suite_id}::{test}: TEST_CLASS names a test of a suite no host requires")
        if lane in HOSTS and suite.required == (lane,):
            issues.append(f"{suite_id}::{test}: TEST_CLASS lane {lane} is already its suite's only host")
        if lane in HOSTS and lane not in suite.required:
            issues.append(f"{suite_id}::{test}: TEST_CLASS requires it on {lane}, which does not require its suite")
        if (suite_id, test) in IGNORED_TESTS:
            issues.append(f"{suite_id}::{test}: both in TEST_CLASS and IGNORED_TESTS")
        if not defines_test(suite, test):
            issues.append(f"{suite_id}::{test}: TEST_CLASS names a test its module tree does not define")
    for (suite_id, test), entry in sorted(SKIP_OUTPUT_EXEMPTIONS.items()):
        suite = by_id.get(suite_id)
        if suite is None:
            issues.append(f"SKIP_OUTPUT_EXEMPTIONS names no suite: {suite_id} ({test})")
        elif (not isinstance(entry, tuple) or len(entry) != 2 or not str(entry[0]).strip()
              or not str(entry[1]).strip()):
            issues.append(f"{suite_id}::{test}: SKIP_OUTPUT_EXEMPTIONS entry needs a line prefix and a reason")
        elif not defines_test(suite, test):
            issues.append(f"{suite_id}::{test}: SKIP_OUTPUT_EXEMPTIONS names a test its module tree does not define")
    for suite in found:
        if not suite.required or suite.kind == "doc":
            continue
        listed = {test.rsplit("::", 1)[-1] for (identifier, test) in IGNORED_TESTS if identifier == suite.id}
        unlisted = sorted(ignored_functions(suite) - listed)
        if unlisted:
            issues.append(f"{suite.id}: #[ignore]d test(s) missing from IGNORED_TESTS: {', '.join(unlisted)}")
    for (suite_id, test), reason in sorted(IGNORED_TESTS.items()):
        suite = by_id.get(suite_id)
        if suite is None:
            issues.append(f"IGNORED_TESTS names no suite: {suite_id} ({test})")
            continue
        if not str(reason).strip():
            issues.append(f"{suite_id}::{test}: IGNORED_TESTS entry needs a reason")
        if not defines_test(suite, test, ignored=True):
            issues.append(f"{suite_id}::{test}: IGNORED_TESTS names a test its module tree does not #[ignore]")
    issues.extend(floor_problems(by_id))
    return issues


IGNORED_FUNCTION = re.compile(r"#\[ignore\b[^\]]*\]\s*(?:#\[[^\]]*\]\s*)*(?:pub(?:\([^)]*\))?\s+)?(?:async\s+)?fn\s+(\w+)")


def ignored_functions(suite: Suite) -> set[str]:
    """Names of the `#[ignore]`d functions in the suite's module tree (a static census)."""
    return {name for path in module_tree(suite.src_path) for name in IGNORED_FUNCTION.findall(stripped_source(path))}


def skip_output_exemptions(suite_id: str) -> dict[str, str]:
    """Test name -> exempt output-line prefix for one suite."""
    return {test: entry[0] for (identifier, test), entry in SKIP_OUTPUT_EXEMPTIONS.items() if identifier == suite_id}


def defines_test(suite: Suite, test: str, *, ignored: bool = False) -> bool:
    """Whether the suite's module tree defines `fn <last path segment>` (with `#[ignore]`)."""
    leaf = re.escape(test.rsplit("::", 1)[-1])
    pattern = re.compile(
        (r"#\[ignore\b[^\]]*\][^{;]*?" if ignored else "") + rf"\bfn\s+{leaf}\s*[<(]", re.DOTALL,
    )
    return any(pattern.search(stripped_source(path)) for path in module_tree(suite.src_path))


def floor_problems(by_id: dict[str, Suite]) -> list[str]:
    """The required floors are subsets of the matching host's required set."""
    issues: list[str] = []
    packages = {suite.package for suite in by_id.values()}
    floors = (
        ("darwin", [(package, target) for package, target, _ in darwin_floor().TARGETS]),
        ("linux", list(linux_floor().TARGETS)),
    )
    for host, rows in floors:
        for package, target in rows:
            if package not in packages:
                continue  # the separate rustc bridge workspace
            suite = by_id.get(f"{package}/test/{target}")
            if suite is None:
                issues.append(f"{host} floor target {package}/{target} is not a suite of the root workspace")
            elif host not in suite.required:
                issues.append(f"{host} floor target {package}/{target} is not in the {host} required set ({suite.klass})")
    for (package, target), _reason in darwin_floor().DARWIN_COMPILED_OUT.items():
        suite = by_id.get(f"{package}/test/{target}")
        if suite is not None and "darwin" in suite.required:
            issues.append(f"{package}/{target}: the Darwin floor reports it compiled out, but it is Darwin-required")
    return issues


def required_set(found: Sequence[Suite], host: str) -> list[Suite]:
    return [suite for suite in found if host in suite.required]


def record(suite: Suite) -> dict:
    """The JSON form of one classified suite."""
    return {
        "id": suite.id, "package": suite.package, "kind": suite.kind, "name": suite.name,
        "class": suite.klass, "reason": suite.reason, "basis": suite.basis,
        "features": list(suite.features), "census": suite.census,
        "compiled": dict(suite.compiled), "required": list(suite.required),
        "minimum": {host: minimum_passes(suite, host) for host in HOSTS},
        "host_skipped_tests": {host: host_skipped_tests(suite.id, host) for host in HOSTS},
        "campaign_tests": campaign_tests(suite.id),
        "ignored_tests": ignored_tests(suite.id),
    }


def summary(found: Sequence[Suite]) -> dict:
    counts = {klass: sum(suite.klass == klass for suite in found) for klass in CLASSES}
    return {
        "suites": len(found), "classes": counts,
        "required": {host: len(required_set(found, host)) for host in HOSTS},
        "test_lanes": {lane: sum(entry[0] == lane for entry in TEST_CLASS.values()) for lane in TEST_LANES},
        "ignored_tests": len(IGNORED_TESTS), "skip_output_exemptions": len(SKIP_OUTPUT_EXEMPTIONS),
    }


def render(found: Sequence[Suite]) -> str:
    lines = []
    for suite in found:
        detail = f" [{suite.basis}] {suite.reason}" if suite.reason else ""
        features = f" features={','.join(suite.features)}" if suite.features else ""
        lines.append(f"{suite.klass:8} {suite.id}{features}{detail}")
    totals = summary(found)
    lines.append(
        f"{totals['suites']} suites: "
        + ", ".join(f"{klass} {count}" for klass, count in totals["classes"].items())
        + f"; Darwin required {totals['required']['darwin']}, Linux required {totals['required']['linux']}"
    )
    return "\n".join(lines) + "\n"


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter,
                                     allow_abbrev=False)
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument("--check", action="store_true", help="print nothing; fail on any inconsistency")
    mode.add_argument("--json", action="store_true", help="print the classification as JSON")
    args = parser.parse_args(argv)
    try:
        found = suites(load_metadata())
    except (OSError, RuntimeError, ValueError, subprocess.TimeoutExpired) as error:
        print(f"full test matrix hosts: {error}", file=sys.stderr)
        return 1
    issues = problems(found)
    if args.json:
        print(json.dumps({"summary": summary(found), "suites": [record(suite) for suite in found]}, indent=2))
    elif not args.check:
        sys.stdout.write(render(found))
    for issue in issues:
        print(f"full test matrix hosts: {issue}", file=sys.stderr)
    return 1 if issues else 0


if __name__ == "__main__":
    raise SystemExit(main())
