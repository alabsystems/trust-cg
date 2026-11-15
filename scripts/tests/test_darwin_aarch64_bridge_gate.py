"""The Darwin AArch64 bridge runner refuses bad hosts, packages and backends.

Fake Trust packages, rustup links, targo builds and libtest executables drive
the real runner. Nothing here builds the bridge or runs a Rust test suite, and
every control runs on Python 3.9 (no tomllib) as well as on newer versions.
"""

from __future__ import annotations

import contextlib
import hashlib
import importlib.util
import io
import json
import os
from pathlib import Path
import re
import stat
import sys
import tempfile
import time
import unittest
from unittest import mock


ROOT = Path(__file__).resolve().parents[2]
SCRIPT = ROOT / "scripts" / "check_darwin_aarch64_bridge.py"
SPEC = importlib.util.spec_from_file_location("darwin_aarch64_bridge_gate", SCRIPT)
assert SPEC is not None and SPEC.loader is not None
GATE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(GATE)
HOST = "aarch64-apple-darwin"
COMMIT = "5" * 40
SHA = hashlib.sha256(b"built backend").hexdigest()

FAKE_TRUST = f"#!{sys.executable}\n" + r'''import os
from pathlib import Path
import sys

mode = os.environ.get("FAKE_TRUST_MODE", "")
name = Path(sys.argv[0]).name
arguments = sys.argv[1:]
package = Path(sys.argv[0]).resolve().parent.parent
calls = os.environ.get("FAKE_TRUST_CALLS")
if calls:
    with open(calls, "a") as out:
        out.write(name + " " + " ".join(arguments) + "\n")
if name == "targo":
    if arguments == ["--version"]:
        print("targo 1.99.0-dev (555555555 2026-09-17) (targo 0.1.0)")
        sys.exit(0)
    sys.exit(64)
if arguments == ["-vV"]:
    print("rustc 1.99.0-dev (555555555 2026-09-17) (trustc 0.1.0)")
    print("binary: " + ("rustc" if mode == "unbranded" else "trustc"))
    print("commit-hash: " + ("unknown" if mode == "unknown-commit" else "5" * 40))
    print("host: " + ("aarch64-unknown-linux-gnu" if mode == "linux-host" else "aarch64-apple-darwin"))
    print("release: 1.99.0-dev")
    sys.exit(0)
if arguments == ["--print", "sysroot"]:
    if mode == "sysroot-fails" and name == "rustc":
        sys.exit(1)
    print(package)
    sys.exit(0)
if arguments == ["-Zhelp"]:
    if mode != "no-knobs":
        print("    -Z    trust-ir-cg-args=val -- backend knobs")
    print("    -Z    other-option=val -- unrelated")
    sys.exit(0)
sys.exit(64)
'''
FAKE_HOST_TOOL = f"#!{sys.executable}\nimport sys\nprint('fixture host tool ' + sys.argv[0])\n"
FAKE_RUSTUP = f"#!{sys.executable}\n" + r'''import os
import sys

if sys.argv[1:] == ["which", "--toolchain", "trust", "rustc"]:
    linked = os.environ.get("FAKE_RUSTUP_TRUST", "")
    if not linked:
        print("error: toolchain 'trust' is not installed", file=sys.stderr)
        sys.exit(1)
    print(linked)
    sys.exit(0)
sys.exit(64)
'''


def executable(path: Path, text: str) -> Path:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text)
    path.chmod(0o755)
    return path


def make_package(root: Path, *, crates=None, std=True, hosts=(HOST,), targo=True) -> Path:
    executable(root / "bin" / "trustc", FAKE_TRUST)
    if targo:
        executable(root / "bin" / "targo", FAKE_TRUST)
    for host in hosts:
        library = root / "lib" / "rustlib" / host / "lib"
        library.mkdir(parents=True)
        for name in GATE.required_private_crates() if crates is None else crates:
            (library / f"lib{name}-0123456789abcdef.rmeta").write_text("fixture metadata")
        if std:
            (library / "libstd-0123456789abcdef.rlib").write_text("fixture std")
    return root


def make_tools(root: Path, names=GATE.HOST_TOOLS) -> Path:
    for name in names:
        executable(root / name, FAKE_HOST_TOOL)
    return root


def libtest(tests, outputs=None, *, ignored=(), filtered=0) -> str:
    """A stable-libtest --show-output transcript for passing tests."""
    outputs = outputs or {}
    lines = [f"running {len(tests) + len(ignored)} test{'s' if len(tests) + len(ignored) != 1 else ''}"]
    lines += [f"test {name} ... ok" for name in tests]
    lines += [f"test {name} ... ignored" for name in ignored]
    lines += ["", "successes:", ""]
    for name in tests:
        if name in outputs:
            lines += [f"---- {name} stdout ----", *outputs[name].splitlines(), ""]
    lines += ["", "successes:", *(f"    {name}" for name in tests), ""]
    lines.append(
        f"test result: ok. {len(tests)} passed; 0 failed; {len(ignored)} ignored; "
        f"0 measured; {filtered} filtered out; finished in 0.01s"
    )
    return "\n".join(lines) + "\n"


CORPUS_GUESTS = [f"p{index:02d}_guest" for index in range(1, 14)]


def corpus_output(compiled=19, *, hard=0, printed=None, drop_rows=0, ratchet=False) -> str:
    rows = [f"{guest}@O{opt}" for guest in CORPUS_GUESTS for opt in (0, 3)]
    total = len(rows)
    lines = []
    for index, row in enumerate(rows[:total - drop_rows]):
        if index < compiled:
            lines.append(f"  [a64] {row}: COMPILED")
        elif index < total - hard:
            codes = '["TCG-PROOF-465"]' if ratchet else '["TCG-MIR-UNSUPPORTED"]'
            lines += [f"  [a64] {row}: INCOMPLETE ({codes})", "error: failing closed on unsupported MIR"]
        else:
            lines += [f"  [a64] {row}: HARD ERROR", "error: internal compiler error"]
    incomplete = total - compiled - hard
    coverage = printed if printed is not None else f"{100.0 * compiled / total:.1f}"
    lines += ["", f"[a64 corpus row] {compiled}/{total} rows COMPILED ({coverage}%), "
              f"{incomplete} incomplete, {hard} hard errors",
              "[a64 corpus row] ranked gap tags: {\"TCG-MIR-UNSUPPORTED\": 7}"]
    if ratchet:
        lines.append(f"[a64 corpus row] coverage floor SKIPPED: {incomplete}/{total} rows refused by the "
                     "aarch64 Mach-O object-relocation promotion ratchet (TCG-PROOF-465 reappeared)")
    return "\n".join(lines) + "\n"


TEST_FUNCTION = re.compile(r"#\[test\]\s*(?:(?://[^\n]*|#\[[^\n]*\])\s*)*fn\s+([A-Za-z0-9_]+)")


def copy_test_sources(destination: Path) -> None:
    """Copy every Rust source under the bridge tests/ tree, keeping its layout.

    The inventory follows each required fixture's modules (support/, and the
    corpus guests it includes), so a copy of the top-level files alone is not
    the fixture set the runner checks.
    """
    for path in GATE.TESTS_DIR.rglob("*.rs"):
        copy = destination / path.relative_to(GATE.TESTS_DIR)
        copy.parent.mkdir(parents=True, exist_ok=True)
        copy.write_bytes(path.read_bytes())


def source_tests(name):
    """The #[test] function names a fixture source defines, in source order."""
    return TEST_FUNCTION.findall((GATE.TESTS_DIR / f"{name}.rs").read_text())


def marker(kind, certs, test):
    return f"{GATE.POSITIVE_MARKER} kind={kind} certs={certs} test={test}"


def knobs(*items):
    """The trace tests/support/toolchain.rs backend_knobs_arg prints."""
    return f"{GATE.KNOB_TRACE} knobs={' '.join(items)}"


# The knob arguments a certificates-on test builds (a certs=off test builds
# no-proof-certs, and a certs=none test none).
CERTS_ON_KNOBS = {
    "m1_hello_loop_compiles_and_runs_until_killed": ("bridge-notes",),
    "a_trivial_compile_stays_within_its_fixed_cost_budget": ("time",),
}


def evidenced(test, kind, certs):
    """A test's knob trace (if it builds one) followed by its marker."""
    if certs == "off":
        trace = [knobs("no-proof-certs")]
    elif test in CERTS_ON_KNOBS:
        trace = [knobs(*CERTS_ON_KNOBS[test])]
    else:
        trace = []
    return "\n".join([*trace, marker(kind, certs, test)])


def evidence_markers(row, tests):
    """One positive-evidence marker per test, matching the target's exact profile."""
    kinds = [kind for kind, count in row.evidence for _ in range(count)]
    assert len(kinds) == len(tests), (row.name, kinds, tests)
    lines, off = {}, row.certs_off
    for test, kind in zip(tests, kinds):
        if kind == GATE.UNIT_CHECK:
            certs = "none"
        elif off:
            certs, off = "off", off - 1
        else:
            certs = "on"
        lines[test] = evidenced(test, kind, certs)
    assert off == 0, row.name
    return lines


# Real test names from the fixture sources, with the lines each prints on its
# asserted success path (the positive-evidence markers are added by
# success_transcript from each target's evidence profile).
SUCCESS = {
    "coroutine_generator_aarch64": (["coroutine_generator_yields_in_order_and_links_runs_aarch64"], {}),
    "drop_heap_aarch64": ([
        "box_drop_frees_heap_value_and_links_runs_aarch64",
        "address_taken_box_new_links_runs_without_reachable_trap_aarch64",
        "box_drop_staticlib_archive_matches_llvm_aarch64",
    ], {}),
    "hello_loop": (["m1_hello_loop_compiles_and_runs_until_killed"], {
        "m1_hello_loop_compiles_and_runs_until_killed":
            "rustc stderr:\nrustc_codegen_trust_cg: #574 entry wrapper uses lang_start\n\nrustc exit: exit status: 0",
    }),
    "static_data_aarch64": ([
        "immutable_statics_emit_correct_bytes_and_link_runs_aarch64",
        "mutable_static_is_shared_writable_and_link_runs_aarch64",
        "over_aligned_statics_land_aligned_and_survive_a_16_byte_atomic_aarch64",
        "statics_pointing_at_extern_statics_link_and_run_aarch64",
    ], {"statics_pointing_at_extern_statics_link_and_run_aarch64":
            "EXTERN_STATIC_LINK rows=2 matched=2 opts=0,2"}),
    "tls_thread_local_aarch64": (["thread_local_static_reads_writes_per_thread_isolated_aarch64"], {}),
    "unwind_cleanup_aarch64": ([
        "bridge_lowers_unwind_cleanup_to_eh_object_aarch64",
        "bridge_unwind_cleanup_real_panic_caught_aarch64",
    ], {
        "bridge_lowers_unwind_cleanup_to_eh_object_aarch64":
            "bridge unwind-cleanup EH lowering VERIFIED (object level): Invoke + cleanup LandingPad",
        "bridge_unwind_cleanup_real_panic_caught_aarch64":
            "REAL Rust panic CAUGHT through the bridge: AY_CAUGHT=1 CLEANUP_RAN=1 (cleanup landing pad "
            "freed the live Box mid-unwind, catch_unwind caught the re-raise, clean exit 0).",
    }),
    "real_program_corpus_a64": (["real_program_corpus_a64_compile_gate"], {
        "real_program_corpus_a64_compile_gate": corpus_output(),
    }),
    "fixed_cost_budget_aarch64": ([
        "a_trivial_compile_stays_within_its_fixed_cost_budget",
        "the_process_cost_line_parses_every_bounded_field",
    ], {
        "a_trivial_compile_stays_within_its_fixed_cost_budget":
            "fixed-cost cold: Cost { checker_probes: 2, executable_digests: 4, solver_starts: 1, assessment_spawns: 1 }\n"
            "fixed-cost warm: Cost { checker_probes: 2, executable_digests: 4, solver_starts: 0, assessment_spawns: 0 }\n"
            "fixed-cost budget held: cold Cost { checker_probes: 2, executable_digests: 4, solver_starts: 1, assessment_spawns: 1 }, "
            "warm Cost { checker_probes: 2, executable_digests: 4, solver_starts: 0, assessment_spawns: 0 }",
    }),
}
# Targets whose success path prints nothing but the marker: their test names
# come from the fixture sources.
for _name in ("m142_bridge_bookkeeping_aarch64", "signature_placement_families_xback",
              "rust_call_boundary_aarch64",
              "m140_x86_scalar_pair_return_xback", "m141_x86_scalar_pair_arg_xback",
              "m144_x86_pair_arg_exhaustion_xback", "m145_x86_indirect_arg_xback",
              "m146_x86_bool_load_xback", "opt_loop_state_run", "float_semantics",
              "overflow_asserts", "reference_union_semantics", "unsupported_program"):
    SUCCESS[_name] = (source_tests(_name), {})
SUCCESS["x86_split_copy_replay_run"] = (source_tests("x86_split_copy_replay_run"), {
    "x86_64_split_copies_survive_the_regalloc_replay_on_whole_programs":
        "X86_SPLIT_COPY_REPLAY rows=20 matched=20",
})
SUCCESS["panic_hook_differential"] = (source_tests("panic_hook_differential"), {
    "panic_abort_runs_the_hook_with_the_real_location_like_llvm": "panic-hook rows: 49/49 matched LLVM",
    "panic_hook_observes_preceding_stores_abort_and_unwind_like_llvm":
        "PRE_PANIC_EFFECTS matched=24 strategies=abort,unwind opts=0,2,3",
})
SUCCESS["assert_panic_differential_aarch64"] = (source_tests("assert_panic_differential_aarch64"), {
    "source_assert_panic_payload_location_cleanup_match_llvm_aarch64":
        "ASSERT_PANIC_KINDS entries=14 cells=16 cases=18 native_runs=304 controls=272 caught=120 aborts=168",
})
SUCCESS["panic_assert_kinds_differential"] = (source_tests("panic_assert_kinds_differential"), {
    "every_failed_assert_calls_rustcs_panic_entry_like_llvm":
        "ASSERT_PANIC_KIND_ROWS fixtures=4 configs=16 rows=1344 matched=1344 refused=0",
})
SUCCESS["std_panic_payload_differential"] = (source_tests("std_panic_payload_differential"), {
    "std_panics_reach_the_hook_with_stds_payload_and_location_like_llvm":
        "STD_PANIC_PAYLOAD_ROWS fixtures=3 configs=8 rows=1680 matched=1680 refused=0",
})
SUCCESS["terminate_panic_differential_aarch64"] = (source_tests("terminate_panic_differential_aarch64"), {
    "source_termination_reasons_payload_location_and_drops_match_llvm_aarch64":
        "TERMINATE_PANIC_KINDS reasons=2 cells=16 cases=2 native_runs=48 controls=32 aborts=32 hooks=56 cleanup_drops=8\n"
        "TERMINATE_PANIC_ROUTES llvm_runs=24 cg_runs=24 opts=0,1,2,3 strategies=abort,unwind\n"
        "TERMINATE_FOREIGN_ABORT_KINDS cells=8 cases=3 native_runs=32 controls=16 aborts=24 hooks=48 throw_drops=24 throw_callbacks=40\n"
        "TERMINATE_FOREIGN_ABORT_OUTCOMES reached_abi=16 fatal_search=8 nested_reason_hooks=0\n"
        "TERMINATE_FOREIGN_ABORT_OBJECTS cells=8 complete_sets=8 stable=1 max_per_cell=16\n"
        "TERMINATE_FOREIGN_ABORT_ROUTES llvm_runs=16 cg_runs=16 opts=0,1,2,3 callee_strategy=abort driver_strategy=unwind\n"
        "TERMINATE_FOREIGN_ABORT_BOUNDARY_CONTROLS expected_refusals=12 compiled_nounwind_roots=8 llvm_source_roots=16 native_runs=0 opts=0,1,2,3",
    "nounwind_frame_call_site_regions_match_llvm_aarch64":
        "TERMINATE_NOUNWIND_REGIONS rows=68 cells=8 native_runs=544 llvm_runs=272 cg_runs=272 opts=0,1,2,3 callee_strategy=abort driver_strategy=unwind\n"
        "TERMINATE_NOUNWIND_REGION_OUTCOMES returns=40 fatal_search=135 reached_abi=48 caught=49",
    "extern_c_callee_panics_run_mir_cleanups_aarch64":
        "TERMINATE_UNWIND_CALLEE_REGIONS rows=38 cells=8 native_runs=304 llvm_runs=152 cg_runs=152 opts=0,1,2,3 callee_strategy=unwind driver_strategy=unwind\n"
        "TERMINATE_UNWIND_CALLEE_OUTCOMES returns=8 caught=56 reached_abi=63 mir_cleanup_where_llvm_fails_search=25",
})
SUCCESS["unsized_arguments_aarch64"] = (source_tests("unsized_arguments_aarch64"), {
    "unsized_arguments_corpus_matches_llvm_aarch64":
        "TCG_UNSIZED_ARGUMENT_DARWIN_CORPUS executions=8 checks=912384 opts=0,1,2,3 panic=abort",
    "unsized_str_slice_arguments_match_llvm_aarch64":
        "TCG_UNSIZED_ARGUMENT_DARWIN_STR_SLICES executions=16 checks=359424 opts=0,1,2,3 panic=abort,unwind",
    "unsized_arguments_admission_controls_aarch64":
        "TCG_UNSIZED_ARGUMENT_DARWIN_ADMISSION fixtures=3 compilations=24 refusals=8 opts=0,1,2,3",
})
SUCCESS["atomic_load_store_aarch64"] = (source_tests("atomic_load_store_aarch64"), {
    "atomic_nonvolatile_accesses_match_llvm_aarch64":
        "TCG_ATOMIC_NONVOLATILE fixtures=20 cells=160 executions=320 opts=0,1,2,3 panic=abort,unwind",
    "volatile_atomics_are_explicitly_refused_aarch64":
        "TCG_ATOMIC_VOLATILE fixtures=2 cells=16 refused=16 llvm_runs=16 opts=0,1,2,3 panic=abort,unwind",
    "atomic_type_and_ordering_contracts_fail_closed_aarch64":
        "TCG_ATOMIC_POLICY order_fixtures=4 type_fixtures=5 cells=72 refused=72 llvm_type_refusals=40 opts=0,1,2,3 panic=abort,unwind layout_abi_fixtures=2 layout_abi_refusals=16 llvm_abi_runs=16",
})
SUCCESS["abort_immediate_aarch64"] = (source_tests("abort_immediate_aarch64"), {
    "immediate_abort_signals_match_llvm_aarch64":
        "TCG_ABORT_IMMEDIATE_DARWIN fixtures=3 executions=48 opts=0,1,2,3 panic=abort,unwind trap=5 libc_abort=6",
})
SUCCESS["intrinsic_validity_aarch64"] = (source_tests("intrinsic_validity_aarch64"), {
    "intrinsic_validity_matches_llvm_aarch64":
        "TCG_INTRINSIC_VALIDITY_DARWIN fixtures=linux,generic executions=64 opts=0,1,2,3 panic=abort,unwind strict=no,yes",
})
SUCCESS["deref_field_wide_image_store_aarch64"] = (source_tests("deref_field_wide_image_store_aarch64"), {
    "deref_field_wide_image_stores_match_llvm_aarch64":
        "DEREF_FIELD_WIDE_IMAGE_STORES subjects=subject,strings,bombs opts=0,1,2,3 matched=12 refused=0",
    "deref_field_wide_image_store_kinds_aarch64":
        "DEREF_FIELD_WIDE_IMAGE_KINDS kinds=7 opts=0,1,2,3 matched=4 refused=0",
    "deref_field_wide_image_store_refusals_aarch64":
        "DEREF_FIELD_WIDE_IMAGE_REFUSALS subjects=packed opts=0,1,2,3 matched=0 refused=4",
})
SUCCESS["box_pointer_entry_aarch64"] = (source_tests("box_pointer_entry_aarch64"), {
    "ordinary_box_entry_and_retargeted_cell_match_llvm":
        "BOX_POINTER_ENTRY_DIFFERENTIAL cells=8 cases=2 native_runs=16 llvm_runs=8 cg_runs=8 mir_routes=16 box_drop_frees=24 reads=16 retargets=8 bad_layout=0 provider=LLVM oracle=LLVM certs=off\n"
        "BOX_POINTER_ENTRY_MIR_TRACE_CONTROLS cases=14 accepted=3 refused=11",
})
SUCCESS["executable_trap_stub_routes_aarch64"] = (source_tests("executable_trap_stub_routes_aarch64"), {
    "range_inclusive_rev_reductions_never_trap_aarch64":
        "EXECUTABLE_TRAP_STUB_RANGE refusals=0 llvm_native=6 cg_native=6",
    "dead_std_iterator_body_fails_closed_aarch64":
        "EXECUTABLE_TRAP_STUB_DEAD_ITER rows=4 llvm_native=4 cg_native=0 cg_refused=4",
    "generator_source_take_reductions_never_trap_aarch64":
        "EXECUTABLE_TRAP_STUB_GENERATOR_TAKE rows=4 llvm_native=4 cg_native=4 cg_refused=0",
    "dyn_heap_glue_drop_fails_closed_aarch64":
        "EXECUTABLE_TRAP_STUB_DYN rows=4 llvm_native=4 cg_native=4 cg_refused=0",
    "library_trap_stub_reached_by_local_code_fails_closed_aarch64":
        "LIBRARY_TRAP_STUB_REACHED refused=4 compiled=5",
})
SUCCESS["cross_crate_copies_native_aarch64"] = (source_tests("cross_crate_copies_native_aarch64"), {
    "cross_crate_inline_copies_and_static_identity_agree_with_llvm_aarch64":
        "CROSS_CRATE_COPIES cells=6 llvm_runs=6 cg_runs=18 opts=0,1,2 cgus=1,16",
})
SUCCESS["statics_linkage_native_aarch64"] = (source_tests("statics_linkage_native_aarch64"), {
    "statics_constants_and_multi_cgu_linkage_agree_with_llvm_aarch64":
        "STATICS_LINKAGE cells=4 llvm_runs=4 cg_runs=4 combined_object_sets=2 opts=0,2 cgus=1,16",
})
SUCCESS["assert_constant_condition_aarch64"] = (source_tests("assert_constant_condition_aarch64"), {
    "constant_condition_assert_emits_no_panic_path_aarch64":
        "ASSERT_CONSTANT_CONDITION const_index=folded dynamic_index=raises",
})
SUCCESS["vec_from_elem_capacity_aarch64"] = (source_tests("vec_from_elem_capacity_aarch64"), {
    "vec_from_elem_reports_rustc_capacity_including_zero_aarch64":
        "VEC_FROM_ELEM_CAPACITY cases=2 cells=16 opts=0,3",
})
SUCCESS["slice_sort_order_aarch64"] = (source_tests("slice_sort_order_aarch64"), {
    "slice_sorts_order_like_std_or_refuse_by_name":
        "SLICE_SORT_ORDER cases=4 cells=16 matched=10 refused=6 opts=0,1,2,3",
})
SUCCESS["slice_sort_cached_key_effects_aarch64"] = (
    source_tests("slice_sort_cached_key_effects_aarch64"), {
        "cached_key_counter_calls_once_per_element_or_refuses_by_name":
            "CACHED_KEY_COUNTER cells=4 matched=4 refused=0 certs=off artifacts=/fixture/cached-key",
    })
SUCCESS["aarch64_closure_body_pair_xback"] = (source_tests("aarch64_closure_body_pair_xback"), {
    "closure_body_pairs_match_llvm_across_native_backend_boundaries":
        "CLOSURE_BODY_PAIR_XBACK rows=7 cells=16 opts=0,1,2,3 certs=off artifacts=/fixture/closure-pair",
})
SUCCESS["subslice_loop_compile_bound_aarch64"] = (source_tests("subslice_loop_compile_bound_aarch64"), {
    "subslice_reborrow_loops_compile_in_bounded_time_and_match_llvm":
        "SUBSLICE_LOOP_COMPILE_BOUND cases=4 cells=16 matched=16 opts=0,1,2,3",
})
SUCCESS["runtime_parity_rewrites_aarch64"] = (source_tests("runtime_parity_rewrites_aarch64"), {
    "runtime_parity_rewrites_match_llvm_aarch64":
        "RUNTIME_PARITY_REWRITES rows=666 matched=666 opts=2,3 "
        "fused_xorshift_instances=30 paired_gathers=1",
})
SUCCESS["slice_constant_index_aarch64"] = (source_tests("slice_constant_index_aarch64"), {
    "slice_constant_index_element_guests_match_llvm":
        "SLICE_CONSTANT_INDEX test=elements cells=64 matched=60 refused_by_name=4 opts=0,1,2,3",
    "slice_from_end_element_kinds_match_llvm":
        "SLICE_CONSTANT_INDEX test=from_end_kinds cells=12 matched=12 refused_by_name=0 opts=0,1,2,3",
    "std_stable_sort_and_select_match_llvm_or_refuse_by_name":
        "SLICE_CONSTANT_INDEX test=stable_select cells=32 matched=4 refused_by_name=28 opts=0,1,2,3",
})
SUCCESS["stride_iter_family_differential_aarch64"] = (
    source_tests("stride_iter_family_differential_aarch64"), {
        "slice_chunk_and_window_iterators_match_llvm_or_refuse_by_name":
            "STRIDE_ITER_FAMILY fixtures=4 cells=32 matched=28 refused=4 runs=92 rows=164072 "
            "synthesized_messages=0 opts=0,1,2,3 strategies=abort,unwind",
    })
SUCCESS["format_length_black_box_aarch64"] = (source_tests("format_length_black_box_aarch64"), {
    "length_placeholders_render_like_llvm_aarch64":
        "FORMAT_LENGTH programs=9 cells=72 matched=72 opts=0,1,2,3 strategies=abort,unwind",
    "std_black_box_of_a_collection_matches_llvm_aarch64":
        "STD_BLACK_BOX programs=6 cells=48 must_match=32 opts=0,1,2,3 strategies=abort,unwind\n"
        "STD_BLACK_BOX_OTHERS matched=0 refused_by_name=16",
})
SUCCESS["core_values_user_trait_differential_aarch64"] = (
    source_tests("core_values_user_trait_differential_aarch64"), {
        "call_results_into_memory_backed_fields_reach_the_slot":
            "CORE_VALUES_FIELD_RESULTS cases=16 cells=96 matched=92 refused=4",
        "vec_float_partial_cmp_writes_the_layout_none_byte":
            "CORE_VALUES_PARTIAL_CMP cases=7 cells=28 matched=28 refused=0",
        "vec_eq_intercepts_only_a_vec_operand":
            "CORE_VALUES_VEC_EQ cases=9 cells=36 matched=34 refused=2",
    })
SUCCESS["map_model_user_trait_differential_aarch64"] = (
    source_tests("map_model_user_trait_differential_aarch64"), {
        "map_model_refuses_user_traits_drops_and_hashers_aarch64":
            "MAP_MODEL_USER_TRAIT_REFUSALS guests=34 cells=136 refused=136 llvm_runs=136 opts=0,1,2,3",
        "map_model_still_serves_primitive_and_derived_types_aarch64":
            "MAP_MODEL_LANE_CONTROLS guests=16 cells=64 matched=64 opts=0,1,2,3",
    })
SUCCESS["switch_case_signed_aarch64"] = (source_tests("switch_case_signed_aarch64"), {
    "signed_switch_cases_take_llvms_arm":
        "SWITCH_CASE_SIGNED cases=2 cells=8 matched=8 opts=0,1,2,3",
})
SUCCESS["format_capacity_aarch64"] = (source_tests("format_capacity_aarch64"), {
    "format_write_and_to_string_strings_have_stds_capacity_aarch64":
        "FORMAT_CAPACITY programs=5 cells=40 matched=40 opts=0,1,2,3 strategies=abort,unwind",
})
SUCCESS["vec_extend_capacity_aarch64"] = (source_tests("vec_extend_capacity_aarch64"), {
    "vec_extend_from_a_chain_leaves_stds_capacity_aarch64":
        "VEC_EXTEND_CAPACITY programs=6 cells=48 must_match=24 opts=0,1,2,3 strategies=abort,unwind\n"
        "VEC_EXTEND_CAPACITY_O2_O3 matched=0 refused_by_name=24",
})
SUCCESS["switch_join_constant_aarch64"] = (source_tests("switch_join_constant_aarch64"), {
    "a_switch_case_constant_is_not_reused_where_it_was_skipped_aarch64":
        "SWITCH_JOIN_CONSTANT programs=5 cells=40 matched=40 opts=0,1,2,3 strategies=abort,unwind",
})
SUCCESS["vec_compact_user_trait_differential_aarch64"] = (
    source_tests("vec_compact_user_trait_differential_aarch64"), {
        "vec_models_destroy_removed_elements_and_call_key_eq_like_llvm_aarch64":
            "VEC_COMPACT_DESTRUCTION cases=18 cells=144 matched=144 refused=0 opts=0,1,2,3 "
            "strategies=abort,unwind",
        "vec_models_repair_the_vec_when_a_closure_or_drop_unwinds_aarch64":
            "VEC_COMPACT_UNWIND cases=15 cells=60 matched=60 opts=0,1,2,3 strategies=unwind",
        "vec_models_still_compile_primitive_and_derived_elements_aarch64":
            "VEC_COMPACT_CONTROLS cases=6 cells=48 matched=48 opts=0,1,2,3 strategies=abort,unwind",
        "vec_models_refuse_unlowered_drops_by_name_aarch64":
            "VEC_COMPACT_REFUSALS cases=3 cells=24 refused=24 opts=0,1,2,3 strategies=abort,unwind",
        "vec_into_iter_terminals_free_the_buffer_when_a_payload_unwinds_aarch64":
            "VEC_INTO_ITER_UNWIND cases=35 cells=188 matched=120 refused=68 opts=0,1,2,3 "
            "strategies=abort,unwind",
    })
SUCCESS["clone_sort_user_trait_differential_aarch64"] = (
    source_tests("clone_sort_user_trait_differential_aarch64"), {
        "vec_from_elem_runs_the_user_clone_or_refuses_aarch64":
            "CLONE_SORT_FROM_ELEM rows=11 cells=56 matched=20 refused=36 opts=0,1,2,3 strategies=abort,unwind",
        "cell_clones_are_bitwise_copies_aarch64":
            "CLONE_SORT_CELL_CLONES rows=30 cells=240 matched=156 refused=84 opts=0,1,2,3 strategies=abort,unwind",
        "slice_sorts_keep_std_order_and_key_calls_aarch64":
            "CLONE_SORT_SLICE_SORTS rows=34 cells=164 matched=96 refused=68 opts=0,1,2,3 strategies=abort,unwind",
        "tuple_items_keep_their_scalar_bits_aarch64":
            "CLONE_SORT_TUPLE_SCALARS rows=7 cells=56 matched=56 refused=0 opts=0,1,2,3 strategies=abort,unwind",
    })
SUCCESS["iter_chain_unwind_item_differential_aarch64"] = (
    source_tests("iter_chain_unwind_item_differential_aarch64"), {
        "by_reference_payloads_drop_the_item_they_hold_when_they_unwind_aarch64":
            "ITER_CHAIN_UNWIND_HELD cases=26 cells=208 matched=190 refused=18 opts=0,1,2,3 "
            "strategies=abort,unwind",
        "by_reference_payloads_keep_the_item_they_write_aarch64":
            "ITER_CHAIN_INTERIOR_MUT_ITEMS cases=9 cells=72 matched=52 refused=20 opts=0,1,2,3 "
            "strategies=abort,unwind",
        "drives_holding_nothing_across_an_unwind_still_match_aarch64":
            "ITER_CHAIN_UNWIND_CONTROLS cases=10 cells=80 matched=70 refused=10 opts=0,1,2,3 "
            "strategies=abort,unwind",
        "collect_frees_the_vec_it_builds_when_a_payload_unwinds_aarch64":
            "ITER_CHAIN_UNWIND_COLLECT cases=9 cells=72 matched=72 refused=0 no_eh_levels=4 "
            "opts=0,1,2,3 strategies=abort,unwind",
        "held_items_the_drive_cannot_drop_refuse_by_name_aarch64":
            "ITER_CHAIN_UNWIND_REFUSALS cases=8 cells=56 matched=30 refused=26 no_eh_sites=16 "
            "opts=0,1,2,3 strategies=abort,unwind",
    })
SUCCESS["multi_cgu_link_aarch64"] = (source_tests("multi_cgu_link_aarch64"), {
    "multi_cgu_executables_link_and_match_llvm_aarch64": "MULTI_CGU_EXECUTABLES rows=24 matched=24",
    "multi_cgu_rlib_and_downstream_bin_link_and_match_llvm_aarch64":
        "MULTI_CGU_RLIB_PAIR rows=12 matched=12",
    "multi_cgu_staticlib_links_into_a_c_driver_and_matches_llvm_aarch64":
        "MULTI_CGU_STATICLIB rows=12 matched=12",
    "multi_cgu_private_copies_are_cgu_qualified_private_externs_aarch64":
        "MULTI_CGU_PRIVATE_EXTERNS cgus>=2 duplicated=0 exported=0",
})
SUCCESS["dyn_heap_glue_differential_aarch64"] = (source_tests("dyn_heap_glue_differential_aarch64"), {
    "dyn_heap_glue_matches_llvm_aarch64": "DYN_HEAP_GLUE cells=48 must_match=31 matched=36 refused=12",
    "dyn_heap_glue_borrowed_vec_string_vtable_matches_llvm_aarch64":
        "DYN_HEAP_GLUE_BORROWED_VEC_STRING cells=20 must_match=16 matched=18 refused=2",
    "dyn_heap_glue_borrowed_map_vtable_fails_closed_aarch64":
        "DYN_HEAP_GLUE_BORROWED_MAP refused=8 heap_image_vtable=4",
    "dyn_heap_glue_real_owned_map_origin_fails_closed_aarch64":
        "DYN_HEAP_GLUE_REAL_OWNED_MAP refused=4",
    "staticlib_dyn_box_chain_glue_aarch64":
        "DYN_HEAP_GLUE_STATICLIB deep_chain: r=8 allocs=7 deallocs=7 live=0 box_chain: r=42 allocs=3 deallocs=3 live=0",
})
for _name in ("debuginfo_dwarf_aarch64", "linkage_macho_aarch64"):
    SUCCESS[_name] = (source_tests(_name), {})
# The AArch64 differential lanes (L06-P3) print their summary markers only
# once their census holds; each test's line is its target's own marker.
def _row_markers(name):
    return next(row.markers for row in GATE.TARGETS if row.name == name)


SUCCESS["bridge_differential_aarch64"] = (source_tests("bridge_differential_aarch64"), dict(zip(
    ["bridge_corpus_proofs_off_matches_llvm_natively",
     "bridge_corpus_certs_on_matches_llvm_or_refuses_by_name"],
    _row_markers("bridge_differential_aarch64"))))
SUCCESS["bridge_feature_suites_aarch64"] = (source_tests("bridge_feature_suites_aarch64"), dict(zip(
    source_tests("bridge_feature_suites_aarch64"), _row_markers("bridge_feature_suites_aarch64"))))
SUCCESS["bridge_regressions_aarch64"] = (source_tests("bridge_regressions_aarch64"), dict(zip(
    source_tests("bridge_regressions_aarch64"), _row_markers("bridge_regressions_aarch64"))))
SUCCESS["mir_families_aarch64"] = (source_tests("mir_families_aarch64"), {
    "set_discriminant_writes_every_enum_layout_as_llvm_does":
        "SET_DISCRIMINANT_LAYOUTS slots=18 writes=19 opts=0,1,2,3 matched=4",
    "discriminant_reads_every_enum_layout_as_llvm_does":
        "DISCRIMINANT_READS values=43 opts=0,1,2,3 matched=4",
    "user_drop_glue_and_cleanup_edges_match_llvm_through_real_panics":
        "USER_DROP_CLEANUP scenarios=16 opts=0,1,2,3 matched=4 caught_panics=28",
    "link_section_statics_land_in_their_mach_o_sections":
        "LINK_SECTION_STATICS sections=3 ctor=ran opts=0,2 matched=2",
    "bounded_fp_asm_matches_the_hardware_like_llvm":
        "BOUNDED_FP_ASM checks=2359296 opts=0,1,2,3 llvm=4 bridge=4",
    "unmodeled_families_are_refused_by_name": "UNMODELED_MIR_FAMILIES refused=7",
})
# Synthetic classifier inputs, never native execution evidence.
SUCCESS["current_private_api"] = (source_tests("current_private_api"), {})

# The marker kinds of the targets whose tests do not all share one kind, by test.
MIXED_EVIDENCE = {
    "current_private_api": {
        "actual_box_deref_mir_refuses_before_object_emission": (GATE.EXPECTED_REFUSAL, "on"),
        "scalar_widths_and_allocation_provenance_execute_against_c_driver": (GATE.NATIVE_RUN, "off"),
    },
    "debuginfo_dwarf_aarch64": {
        "line_tables_drive_dsymutil_dwarfdump_and_lldb_by_file_line": (GATE.NATIVE_RUN, "off"),
        "unpacked_split_debuginfo_keeps_objects_lldb_resolves_by_file_line": (GATE.NATIVE_RUN, "off"),
        "unhonoured_codegen_options_are_refused_by_name_before_lowering": (GATE.EXPECTED_REFUSAL, "on"),
        "honoured_options_note_or_warn_and_another_dwarf_version_is_refused": (GATE.COMPILED, "off"),
    },
    "linkage_macho_aarch64": {
        "cgu_local_copies_and_hidden_definitions_bind_as_llvm_binds_them": (GATE.NATIVE_RUN, "off"),
        "weak_definitions_coalesce_across_crates_and_yield_to_a_strong_one": (GATE.NATIVE_RUN, "off"),
        "a_cdylib_exports_only_its_no_mangle_interface": (GATE.NATIVE_RUN, "off"),
        "linkages_without_a_faithful_mach_o_spelling_are_refused_by_name": (GATE.EXPECTED_REFUSAL, "on"),
    },
    "mir_families_aarch64": {
        "set_discriminant_writes_every_enum_layout_as_llvm_does": (GATE.NATIVE_RUN, "off"),
        "discriminant_reads_every_enum_layout_as_llvm_does": (GATE.NATIVE_RUN, "off"),
        "user_drop_glue_and_cleanup_edges_match_llvm_through_real_panics": (GATE.NATIVE_RUN, "off"),
        "link_section_statics_land_in_their_mach_o_sections": (GATE.NATIVE_RUN, "off"),
        "bounded_fp_asm_matches_the_hardware_like_llvm": (GATE.NATIVE_RUN, "off"),
        "unmodeled_families_are_refused_by_name": (GATE.EXPECTED_REFUSAL, "on"),
    },
    "static_data_aarch64": {
        "immutable_statics_emit_correct_bytes_and_link_runs_aarch64": (GATE.NATIVE_RUN, "on"),
        "mutable_static_is_shared_writable_and_link_runs_aarch64": (GATE.NATIVE_RUN, "off"),
        "over_aligned_statics_land_aligned_and_survive_a_16_byte_atomic_aarch64": (GATE.NATIVE_RUN, "off"),
        "statics_pointing_at_extern_statics_link_and_run_aarch64": (GATE.NATIVE_RUN, "off"),
    },
    "executable_trap_stub_routes_aarch64": {
        "range_inclusive_rev_reductions_never_trap_aarch64": (GATE.NATIVE_RUN, "off"),
        "dead_std_iterator_body_fails_closed_aarch64": (GATE.EXPECTED_REFUSAL, "off"),
        "generator_source_take_reductions_never_trap_aarch64": (GATE.NATIVE_RUN, "off"),
        "dyn_heap_glue_drop_fails_closed_aarch64": (GATE.NATIVE_RUN, "off"),
        "library_trap_stub_reached_by_local_code_fails_closed_aarch64": (GATE.EXPECTED_REFUSAL, "off"),
    },
    "unsupported_program": {
        "branch_variant_mutable_scalar_reference_tuple_escape_now_compiles_after_backend_load": (GATE.COMPILED, "on"),
        "promoted_scalar_reference_return_tuple_escape_fails_closed_after_backend_load": (GATE.EXPECTED_REFUSAL, "on"),
        "mutable_scalar_reference_return_compiles_via_general_lowering": (GATE.COMPILED, "on"),
        "intercepted_collection_reference_return_still_fails_closed": (GATE.EXPECTED_REFUSAL, "on"),
        "wrapped_mut_scalar_ref_return_still_fails_closed": (GATE.EXPECTED_REFUSAL, "on"),
        "celled_return_local_loads_from_its_cell": (GATE.COMPILED, "off"),
        "nonzst_pointer_loop_carrier_compiles_and_threads_its_update": (GATE.NATIVE_RUN, "off"),
        "joined_reference_and_direct_borrow_without_home_fail_closed": (GATE.EXPECTED_REFUSAL, "on"),
        "overlapping_joined_references_without_home_fail_closed": (GATE.EXPECTED_REFUSAL, "on"),
        "nested_array_reference_unit_leaf_whole_store_fails_after_backend_load": (GATE.EXPECTED_REFUSAL, "on"),
        "multi_variant_enum_reference_parameter_abi_fails_after_backend_load": (GATE.COMPILED, "on"),
        "no_mangle_roots_are_never_dropped_when_their_object_compile_fails": (GATE.COMPILED, "on"),
        "unsupported_int_to_float_u128_source_fails_after_backend_load": (GATE.EXPECTED_REFUSAL, "on"),
        "float_remainder_is_now_supported_after_backend_load": (GATE.COMPILED, "on"),
        "loop_carried_aggregate_field_mutation_now_compiles_after_backend_load": (GATE.COMPILED, "on"),
        "zst_before_sized_field_whole_store_from_scalarized_source_compiles": (GATE.COMPILED, "off"),
        "non_promoted_zst_constant_trait_object_data_pointer_fails_closed": (GATE.EXPECTED_REFUSAL, "on"),
        "retained_pointer_locals_compile": (GATE.COMPILED, "off"),
    },
    "dyn_heap_glue_differential_aarch64": {
        "dyn_heap_glue_matches_llvm_aarch64": (GATE.NATIVE_RUN, "off"),
        "dyn_heap_glue_borrowed_vec_string_vtable_matches_llvm_aarch64": (GATE.NATIVE_RUN, "off"),
        "dyn_heap_glue_borrowed_map_vtable_fails_closed_aarch64": (GATE.EXPECTED_REFUSAL, "off"),
        "dyn_heap_glue_real_owned_map_origin_fails_closed_aarch64": (GATE.EXPECTED_REFUSAL, "off"),
        "staticlib_dyn_box_chain_glue_aarch64": (GATE.NATIVE_RUN, "off"),
    },
    "unsized_arguments_aarch64": {
        "unsized_arguments_corpus_matches_llvm_aarch64": (GATE.NATIVE_RUN, "off"),
        "unsized_str_slice_arguments_match_llvm_aarch64": (GATE.NATIVE_RUN, "off"),
        "unsized_arguments_admission_controls_aarch64": (GATE.EXPECTED_REFUSAL, "off"),
    },
    "deref_field_wide_image_store_aarch64": {
        "deref_field_wide_image_stores_match_llvm_aarch64": (GATE.NATIVE_RUN, "off"),
        "deref_field_wide_image_store_kinds_aarch64": (GATE.NATIVE_RUN, "off"),
        "deref_field_wide_image_store_refusals_aarch64": (GATE.EXPECTED_REFUSAL, "off"),
    },
    "map_model_user_trait_differential_aarch64": {
        "map_model_refuses_user_traits_drops_and_hashers_aarch64": (GATE.EXPECTED_REFUSAL, "off"),
        "map_model_still_serves_primitive_and_derived_types_aarch64": (GATE.NATIVE_RUN, "off"),
    },
    "unwind_cleanup_aarch64": {
        "bridge_lowers_unwind_cleanup_to_eh_object_aarch64": (GATE.COMPILED, "off"),
        "bridge_unwind_cleanup_real_panic_caught_aarch64": (GATE.NATIVE_RUN, "off"),
    },
    "fixed_cost_budget_aarch64": {
        "a_trivial_compile_stays_within_its_fixed_cost_budget": (GATE.FIXED_COST_EVIDENCE, "on"),
        "the_process_cost_line_parses_every_bounded_field": (GATE.UNIT_CHECK, "none"),
    },
    "bridge_differential_aarch64": {
        "bridge_corpus_proofs_off_matches_llvm_natively": (GATE.NATIVE_RUN, "off"),
        "bridge_corpus_certs_on_matches_llvm_or_refuses_by_name": (GATE.EXPECTED_REFUSAL, "on"),
    },
    "bridge_regressions_aarch64": {
        "consumed_closures_with_observable_drop_glue_match_llvm_or_refuse_by_name": (GATE.EXPECTED_REFUSAL, "off"),
        "uncleaned_allocation_owners_match_or_refuse_by_name": (GATE.EXPECTED_REFUSAL, "off"),
        "borrowing_and_cleaned_fold_closures_match_llvm": (GATE.NATIVE_RUN, "off"),
        "float_vec_partial_cmp_none_matches_llvm": (GATE.NATIVE_RUN, "off"),
        "u128_saturating_add_sub_match_llvm": (GATE.NATIVE_RUN, "off"),
        "chain_with_a_cleared_half_matches_llvm": (GATE.NATIVE_RUN, "off"),
        "captured_pair_closures_keep_the_vec_models_matching_llvm": (GATE.NATIVE_RUN, "off"),
    },
}


def target(name):
    return next(row for row in GATE.TARGETS if row.name == name)


def success_outputs(name):
    """Each test's success-path output plus its positive-evidence marker."""
    tests, outputs = SUCCESS[name]
    if name in MIXED_EVIDENCE:
        markers = {test: evidenced(test, kind, certs) for test, (kind, certs) in MIXED_EVIDENCE[name].items()}
    else:
        markers = evidence_markers(target(name), tests)
    return {test: "\n".join(filter(None, [outputs.get(test, ""), markers[test]])) for test in tests}


def quiet_main(argv):
    """Run the gate's main() with its progress output captured."""
    with contextlib.redirect_stdout(io.StringIO()), contextlib.redirect_stderr(io.StringIO()):
        return GATE.main(argv)


def success_transcript(name, **overrides):
    tests, _ = SUCCESS[name]
    return libtest(tests, {**success_outputs(name), **overrides})


def darwin_host():
    return (mock.patch.object(GATE.sys, "platform", "darwin"),
            mock.patch.object(GATE.platform, "machine", return_value="arm64"))


class PackageFixture:
    """A fake installed Trust package plus host tools and an isolated HOME."""

    def __init__(self, directory: Path, **package):
        self.directory = directory
        self.package = make_package(directory / "pack", **package)
        self.tools = make_tools(directory / "tools")
        self.home = directory / "home"
        self.home.mkdir()
        self.calls = directory / "trust-calls"
        self.environment = {
            "PATH": os.pathsep.join([str(self.package / "bin"), str(self.tools)]),
            "HOME": str(self.home), "FAKE_TRUST_CALLS": str(self.calls),
        }

    def preflight(self, driver=None, target_dir=None, **extra):
        environment = {**self.environment, **extra}
        target_dir = self.directory / "cache" if target_dir is None else target_dir
        with mock.patch.dict(os.environ, environment, clear=True):
            return GATE.preflight(target_dir, driver, environment)

    def codes(self, **kwargs):
        try:
            self.preflight(**kwargs)
        except GATE.GateError as error:
            return [code for code, _ in error.findings], error
        return [], None


class TestExecutableArtifactTests(unittest.TestCase):
    """Bind genuine Cargo layouts to source, profile and immutable file identity."""

    def classify(self, directory, *, layout="trust", change=None):
        directory = directory.resolve()
        target = directory / "target"
        name, unit = "hello_loop", "0123456789abcdef"
        parent = (target / "release" / "build" / GATE.PACKAGE_TARGET / unit / "out"
                  if layout == "trust" else target / "release" / "deps")
        path = executable(parent / (name + "-" + unit), "#!/bin/sh\nexit 0\n")
        artifact = {
            "reason": "compiler-artifact", "manifest_path": str(GATE.MANIFEST),
            "package_id": "path+" + GATE.BRIDGE_DIR.as_uri() + "#" + GATE.PACKAGE_TARGET + "@0.1.0",
            "target": {"name": name, "kind": ["test"], "src_path": str(GATE.TESTS_DIR / (name + ".rs"))},
            "profile": {"test": True, "opt_level": "3", "debuginfo": 0,
                        "debug_assertions": False, "overflow_checks": False},
            "filenames": [str(path)], "executable": str(path),
        }
        records = [artifact, {"reason": "build-finished", "success": True}]
        if change:
            change(artifact, path, records)
        result = GATE.classify_test_build(0, "\n".join(json.dumps(row) for row in records), target, [name])
        return result, path

    def test_both_cargo_layouts_bind_the_actual_executable_bytes(self):
        for layout in ("trust", "standard"):
            with self.subTest(layout=layout), tempfile.TemporaryDirectory() as tmp:
                result, path = self.classify(Path(tmp), layout=layout)
                self.assertEqual(result["status"], "pass", result)
                self.assertEqual(result["executables"]["hello_loop"], GATE.backend_identity(path))

    def test_wrong_provenance_profile_and_ambiguous_records_are_refused(self):
        changes = {
            "package": lambda a, p, r: a.update(package_id="registry+other#rustc_codegen_trust_cg@0.1.0"),
            "source": lambda a, p, r: a["target"].update(src_path=str(GATE.TESTS_DIR / "other.rs")),
            "manifest": lambda a, p, r: a.update(manifest_path="/other/Cargo.toml"),
            "debug": lambda a, p, r: a["profile"].update(opt_level="0"),
            "debuginfo": lambda a, p, r: a["profile"].update(debuginfo=2),
            "assertions": lambda a, p, r: a["profile"].update(debug_assertions=True),
            "overflow": lambda a, p, r: a["profile"].update(overflow_checks=True),
            "not-test": lambda a, p, r: a["profile"].update(test=False),
            "filenames": lambda a, p, r: a.update(filenames=[str(p), str(p) + ".d"]),
            "duplicate": lambda a, p, r: r.insert(0, dict(a)),
            "non-executable": lambda a, p, r: p.chmod(0o600),
            "empty": lambda a, p, r: p.write_bytes(b""),
            "missing": lambda a, p, r: p.unlink(),
            "failed-finish": lambda a, p, r: r[-1].update(success=False),
        }
        for label, change in changes.items():
            for layout in ("trust", "standard"):
                with self.subTest(label=label, layout=layout), tempfile.TemporaryDirectory() as tmp:
                    result, _ = self.classify(Path(tmp), layout=layout, change=change)
                    self.assertEqual(result["status"], "fail", result)
                    if label != "failed-finish":
                        self.assertEqual(result["executables"], {})

    def test_wrong_unit_layout_and_symlink_escapes_are_refused(self):
        def relocate(a, path, destination):
            destination.parent.mkdir(parents=True, exist_ok=True)
            path.rename(destination)
            a.update(executable=str(destination), filenames=[str(destination)])

        def symlink(a, path, records):
            original = path.with_suffix(".real")
            path.rename(original)
            path.symlink_to(original)

        def parent_symlink(a, path, records):
            original = path.parent.with_name("real-out")
            path.parent.rename(original)
            path.parent.symlink_to(original, target_is_directory=True)

        changes = {
            "unit": lambda a, p, r: relocate(a, p, p.with_name("hello_loop-fedcba9876543210")),
            "bad-unit": lambda a, p, r: relocate(a, p, p.with_name("hello_loop-not-a-unit")),
            "debug-dir": lambda a, p, r: relocate(a, p, p.parents[5] / "debug" / "deps" / p.name),
            "outside": lambda a, p, r: relocate(a, p, p.parents[6] / "outside" / p.name),
            "wrong-package-dir": lambda a, p, r: relocate(a, p, p.parents[3] / "other" / p.parent.parent.name / "out" / p.name),
            "file-symlink": symlink,
            "parent-symlink": parent_symlink,
            "dot-dot": lambda a, p, r: a.update(executable=str(p.parent / ".." / "out" / p.name),
                                                filenames=[str(p.parent / ".." / "out" / p.name)]),
        }
        for label, change in changes.items():
            with self.subTest(label=label), tempfile.TemporaryDirectory() as tmp:
                result, _ = self.classify(Path(tmp), change=change)
                self.assertEqual(result["status"], "fail", result)
                self.assertEqual(result["executables"], {})


class DarwinBridgeGateTests(unittest.TestCase):
    def setUp(self):
        patches = [*darwin_host(), mock.patch.object(GATE, "current_source", return_value={
            "source_fingerprint": "fixture", "dirty": False})]
        for patch in patches:
            patch.start()
            self.addCleanup(patch.stop)

    # Host, package and identity refusals -------------------------------------------

    def test_non_darwin_hosts_are_refused_before_any_probe(self):
        for platform_name, machine in (("linux", "aarch64"), ("darwin", "x86_64"), ("win32", "ARM64")):
            with self.subTest(platform=platform_name, machine=machine), \
                    mock.patch.object(GATE.sys, "platform", platform_name), \
                    mock.patch.object(GATE.platform, "machine", return_value=machine), \
                    mock.patch.object(GATE.TOOLCHAIN, "resolve", side_effect=AssertionError("probed")):
                with self.assertRaises(GATE.GateError) as caught:
                    GATE.preflight(Path("/fixture/cache"))
                self.assertEqual([code for code, _ in caught.exception.findings], [GATE.HOST_REFUSED])

    def test_host_refusal_is_retained_by_a_real_run_without_building(self):
        with tempfile.TemporaryDirectory() as temp, \
                mock.patch.object(GATE.sys, "platform", "linux"), \
                mock.patch.object(GATE.platform, "machine", return_value="aarch64"):
            output = Path(temp) / "report"
            self.assertEqual(quiet_main(["--out", str(output), "--target-dir", str(Path(temp) / "cache")]), 1)
            report = json.loads((output / "report.json").read_text())
            self.assertEqual(report["status"], "fail")
            self.assertEqual(report["finding_codes"], [GATE.HOST_REFUSED])
            self.assertEqual(sorted(path.name for path in output.iterdir()), ["report.json"])

    def test_one_coherent_package_is_bound_by_commit_sysroot_and_private_crates(self):
        with tempfile.TemporaryDirectory() as temp:
            fixture = PackageFixture(Path(temp).resolve())
            provenance = fixture.preflight()
            toolchain = provenance["toolchain"]
            self.assertEqual(toolchain["commit"], COMMIT)
            self.assertEqual(toolchain["compiler"], str(fixture.package / "bin" / "trustc"))
            self.assertEqual(toolchain["targo"], str(fixture.package / "bin" / "targo"))
            self.assertEqual(toolchain["sysroot"], str(fixture.package))
            self.assertEqual(toolchain["build_command"], [str(fixture.package / "bin" / "targo"), "--unverified"])
            self.assertIsNone(provenance["rustup_trust"])
            self.assertEqual(provenance["private_crates"], list(GATE.required_private_crates()))
            self.assertIn("unverified", provenance["lane"])
            self.assertEqual(provenance["backend_knobs_option"], "-Ztrust-ir-cg-args")
            self.assertEqual(set(provenance["tools"]), set(GATE.HOST_TOOLS))
            # An explicit package driver resolves the same identity.
            explicit = fixture.preflight(driver=str(fixture.package / "bin" / "trustc"))
            self.assertEqual(explicit["toolchain"]["commit"], COMMIT)
            self.assertEqual(explicit["toolchain"]["selection"], "explicit-driver")

    def test_required_private_crates_come_from_the_backend_source(self):
        crates = GATE.required_private_crates()
        for name in ("rustc_middle", "rustc_codegen_ssa", "rustc_driver", "rustc_interface"):
            self.assertIn(name, crates)
        self.assertTrue(all(name.startswith("rustc_") for name in crates))

    def test_pin_refuses_the_retired_nightly_and_every_non_trust_channel(self):
        with tempfile.TemporaryDirectory() as temp:
            fixture = PackageFixture(Path(temp).resolve())
            pin = Path(temp) / "rust-toolchain.toml"
            for channel in ("nightly-2026-04-20", "stable", "1.97.1", "nightly"):
                pin.write_text(f'[toolchain]\nchannel = "{channel}"\n')
                with self.subTest(channel=channel), mock.patch.object(GATE, "PIN", pin), \
                        mock.patch.object(GATE.TOOLCHAIN, "resolve", side_effect=AssertionError("resolved")):
                    codes, error = fixture.codes()
                    self.assertIn(GATE.PIN_NOT_TRUST, codes)
                    if channel == "nightly-2026-04-20":
                        self.assertIn("retired", str(error))

    def test_package_identity_refusals_are_named(self):
        with tempfile.TemporaryDirectory() as temp:
            fixture = PackageFixture(Path(temp).resolve(), hosts=(HOST, "aarch64-unknown-linux-gnu"))
            for mode, code in (("unbranded", GATE.TOOLCHAIN_UNRESOLVED),
                               ("unknown-commit", GATE.TOOLCHAIN_UNRESOLVED),
                               ("linux-host", GATE.HOST_REFUSED)):
                with self.subTest(mode=mode):
                    codes, _ = fixture.codes(FAKE_TRUST_MODE=mode)
                    self.assertIn(code, codes)
            split = executable(fixture.directory / "other" / "targo", FAKE_TRUST)
            (fixture.package / "bin" / "targo").unlink()
            codes, error = fixture.codes(PATH=os.pathsep.join([
                str(fixture.package / "bin"), str(split.parent), str(fixture.tools)]))
            self.assertEqual(codes, [GATE.TOOLCHAIN_UNRESOLVED])
            self.assertIn("same installed package", str(error))
            codes, error = fixture.codes()
            self.assertEqual(codes, [GATE.TOOLCHAIN_UNRESOLVED])
            self.assertIn("targo", str(error))

    def test_missing_rustc_dev_is_named_and_prevents_the_doomed_build(self):
        with tempfile.TemporaryDirectory() as temp:
            required = GATE.required_private_crates()
            # trust_toolchain's own two-crate probe and this runner's complete
            # extern-crate inventory must both name the same diagnostic.
            for crates, missing in (([], "rustc_middle"),
                                    ([name for name in required if name != "rustc_hir"], "rustc_hir")):
                with self.subTest(missing=missing):
                    directory = Path(temp).resolve() / missing
                    directory.mkdir()
                    fixture = PackageFixture(directory, crates=crates)
                    codes, error = fixture.codes()
                    self.assertEqual(codes, [GATE.RUSTC_DEV_ABSENT])
                    self.assertIn(missing, str(error))
                    output = directory / "report"
                    environment = {**fixture.environment}
                    with mock.patch.dict(os.environ, environment, clear=True):
                        code = quiet_main(["--out", str(output), "--target-dir", str(directory / "cache")])
                    self.assertEqual(code, 1)
                    report = json.loads((output / "report.json").read_text())
                    self.assertEqual(report["finding_codes"], [GATE.RUSTC_DEV_ABSENT])
                    self.assertNotIn("build", report)
                    self.assertFalse((output / "build.log").exists())
                    calls = fixture.calls.read_text() if fixture.calls.exists() else ""
                    self.assertNotIn("targo --unverified", calls)
                    self.assertFalse((directory / "cache").exists())

    def test_missing_darwin_rust_std_and_backend_knobs_are_named(self):
        with tempfile.TemporaryDirectory() as temp:
            for name in ("nostd", "knobs"):
                (Path(temp) / name).mkdir()
            fixture = PackageFixture(Path(temp).resolve() / "nostd", std=False)
            codes, _ = fixture.codes()
            self.assertEqual(codes, [GATE.RUST_STD_ABSENT])
            fixture = PackageFixture(Path(temp).resolve() / "knobs")
            codes, error = fixture.codes(FAKE_TRUST_MODE="no-knobs")
            self.assertEqual(codes, [GATE.KNOBS_ABSENT])
            self.assertIn("trust-ir-cg-args", str(error))

    def test_rustup_trust_link_divergence_is_refused(self):
        with tempfile.TemporaryDirectory() as temp:
            directory = Path(temp).resolve()
            fixture = PackageFixture(directory)
            executable(fixture.tools / "rustup", FAKE_RUSTUP)
            other = make_package(directory / "recon")
            executable(other / "bin" / "rustc", FAKE_TRUST)
            codes, error = fixture.codes(FAKE_RUSTUP_TRUST=str(other / "bin" / "rustc"))
            self.assertEqual(codes, [GATE.DIVERGENT])
            self.assertIn(str(other), str(error))
            executable(fixture.package / "bin" / "rustc", FAKE_TRUST)
            provenance = fixture.preflight(FAKE_RUSTUP_TRUST=str(fixture.package / "bin" / "rustc"))
            self.assertEqual(provenance["rustup_trust"]["sysroot"], str(fixture.package))
            codes, _ = fixture.codes(FAKE_RUSTUP_TRUST=str(other / "bin" / "rustc"), FAKE_TRUST_MODE="sysroot-fails")
            self.assertEqual(codes, [GATE.IDENTITY_UNKNOWN])
            # A rustup that cannot answer does not hide the RUSTUP_HOME link.
            link = fixture.home / ".rustup" / "toolchains" / "trust" / "bin" / "rustc"
            executable(link, FAKE_TRUST)
            codes, _ = fixture.codes()
            self.assertEqual(codes, [GATE.DIVERGENT])
            (fixture.tools / "rustup").unlink()
            codes, _ = fixture.codes()
            self.assertEqual(codes, [GATE.DIVERGENT])
            link.unlink()
            self.assertEqual(fixture.codes(), ([], None))

    def test_ambient_compiler_backend_and_codegen_overrides_are_refused(self):
        with tempfile.TemporaryDirectory() as temp:
            fixture = PackageFixture(Path(temp).resolve())
            for name, value in (("TCG_NO_PROOF_CERTS", "1"), ("TCG_TEST_BACKEND_PATH", "/x"),
                                ("TRUST_CG_TOOLCHAIN_LANE", "path"), ("RUSTC", "/x/rustc"),
                                ("RUSTC_WRAPPER", "sccache"), ("RUSTFLAGS", "-Copt-level=0"),
                                ("CARGO_BUILD_TARGET", "x86_64-apple-darwin"),
                                ("CARGO_TARGET_AARCH64_APPLE_DARWIN_RUNNER", "qemu"),
                                ("RUSTUP_TOOLCHAIN", "nightly-2026-04-20")):
                with self.subTest(name=name):
                    codes, error = fixture.codes(**{name: value})
                    self.assertEqual(codes, [GATE.AMBIENT_OVERRIDE])
                    self.assertIn(name if name != "RUSTUP_TOOLCHAIN" else "RUSTUP_TOOLCHAIN", str(error))
            self.assertEqual(fixture.codes(RUSTUP_TOOLCHAIN="trust"), ([], None))

    def test_signature_family_filters_and_backend_overrides_are_always_refused(self):
        with tempfile.TemporaryDirectory() as temp:
            fixture = PackageFixture(Path(temp).resolve())
            for name, values in {
                "SIGFAM_ROWS": ("p7", "unknown-row", ""),
                "SIGFAM_LEVELS": ("0", "0,2", "99", "invalid", ""),
                "SIGFAM_DYLIB": ("/fixture/old-backend.dylib", ""),
                "SIGFAM_FUTURE_FILTER": ("1", ""),
            }.items():
                for value in values:
                    with self.subTest(name=name, value=value):
                        codes, error = fixture.codes(**{name: value})
                        self.assertEqual(codes, [GATE.AMBIENT_OVERRIDE])
                        self.assertIn(name, str(error))
                        self.assertNotIn(name, GATE.RECORDED_CONFIGURATION)
                        self.assertNotIn(name, GATE.probe_environment({name: value}))
            self.assertEqual(fixture.codes(), ([], None))

    def test_signature_family_zero_work_refuses_before_backend_or_native_credit(self):
        source = (GATE.TESTS_DIR / "signature_placement_families_xback.rs").read_text()
        run_lane = source[source.index("fn run_lane("):source.index("#[test]", source.index("fn run_lane("))]
        rows_guard = run_lane.index("!rows.is_empty()")
        work_guard = run_lane.index("!work.is_empty()")
        self.assertLess(rows_guard, work_guard)
        self.assertLess(work_guard, run_lane.index("x86_rosetta_support::x86_execution("))
        self.assertLess(work_guard, run_lane.index("backend_under_test()"))
        self.assertLess(work_guard, run_lane.index("std::thread::scope("))
        self.assertIn("[SIGFAM-EMPTY-ROWS]", run_lane)
        self.assertIn("[SIGFAM-EMPTY-WORK]", run_lane)
        self.assertEqual(source_tests("signature_placement_families_xback"), [
            "signature_placement_families_agree_aarch64",
            "signature_placement_families_agree_x86_64",
            "x86_rosetta_core_is_built_from_the_compiler_commit",
        ])
        row = target("signature_placement_families_xback")
        self.assertEqual((row.minimum, row.evidence, row.certs_off),
                         (3, ((GATE.NATIVE_RUN, 3),), 2))
        tests, _ = SUCCESS[row.name]
        for filtered in (1, 2, 3):
            with self.subTest(filtered=filtered):
                verdict = GATE.classify_target(row, 0,
                                              libtest(tests, success_outputs(row.name), filtered=filtered))
                self.assertEqual(verdict["status"], "fail")

    def test_required_disassembly_and_debug_tools_are_checked_before_build(self):
        for name in ("objdump", "dwarfdump", "dsymutil", "lldb", "shasum"):
            with self.subTest(tool=name), tempfile.TemporaryDirectory() as temp:
                self.assertIn(name, GATE.HOST_TOOLS)
                fixture = PackageFixture(Path(temp).resolve())
                (fixture.tools / name).unlink()
                codes, error = fixture.codes()
                self.assertEqual(codes, [GATE.HOST_TOOL_MISSING])
                self.assertIn(f"required host tool is missing: {name}", str(error))

    def test_required_disassembly_and_debug_tools_must_answer_the_identity_probe(self):
        for name in ("objdump", "dwarfdump", "dsymutil", "lldb", "shasum"):
            with self.subTest(tool=name), tempfile.TemporaryDirectory() as temp:
                self.assertEqual(GATE.HOST_TOOL_PROBES.get(name), ("--version",))
                fixture = PackageFixture(Path(temp).resolve())
                executable(fixture.tools / name, f"#!{sys.executable}\nraise SystemExit(1)\n")
                codes, error = fixture.codes()
                self.assertEqual(codes, [GATE.HOST_TOOL_MISSING])
                self.assertIn(f"host tool {name} at ", str(error))
                self.assertIn("cannot be identified", str(error))

    def test_root_fixture_prerequisites_are_declared_before_build(self):
        module = re.compile(
            r'#\[path\s*=\s*"support/darwin_native_prerequisites\.rs"\]'
            r'\s*(?:#\[[^\]]*\]\s*)*(?:pub(?:\([^)]*\))?\s+)?mod\s+(\w+)\s*;'
        )
        calls = 0
        for target in GATE.TARGETS:
            path = GATE.BRIDGE_DIR / "tests" / f"{target.name}.rs"
            code, skeleton = GATE.rust_views(path.read_text())
            for alias in module.findall(code):
                for call in re.finditer(r"\b" + re.escape(alias) + r"::require\s*\(", skeleton):
                    end, depth = call.end(), 1
                    while depth and end < len(skeleton):
                        depth += (skeleton[end] == "(") - (skeleton[end] == ")")
                        end += 1
                    self.assertEqual(depth, 0, f"{target.name}: unclosed prerequisite call")
                    arguments = skeleton[call.end():end - 1]
                    array = re.search(r"&\s*\[", arguments)
                    self.assertIsNotNone(array, f"{target.name}: tools must be a literal list")
                    start = call.end() + array.end()
                    close = skeleton.index("]", start, end)
                    values = code[start:close]
                    names = re.findall(r'"([A-Za-z0-9_.+-]+)"', values)
                    remainder = re.sub(r'"[A-Za-z0-9_.+-]+"', "", values)
                    self.assertIsNotNone(re.fullmatch(r"[\s,]*", remainder),
                                         f"{target.name}: tools must be literal names")
                    for name in names:
                        self.assertIn(name, GATE.HOST_TOOLS,
                                      f"{target.name}: prerequisite {name} missing from preflight")
                    calls += 1
        self.assertGreater(calls, 0, "no native prerequisite declarations were inspected")

    def test_missing_host_tools_cargo_reroutes_and_root_target_dir_are_refused(self):
        with tempfile.TemporaryDirectory() as temp:
            fixture = PackageFixture(Path(temp).resolve())
            (fixture.tools / "nm").unlink()
            codes, error = fixture.codes()
            self.assertEqual(codes, [GATE.HOST_TOOL_MISSING])
            self.assertIn("required host tool is missing: nm", str(error))
            executable(fixture.tools / "nm", FAKE_HOST_TOOL)
            config = fixture.home / ".cargo" / "config.toml"
            config.parent.mkdir(parents=True)
            config.write_text('[build]\nrustc-wrapper = "/usr/bin/env"\n')
            codes, _ = fixture.codes()
            self.assertEqual(codes, [GATE.CARGO_CONFIG_REROUTE])
            config.write_text("[net]\ngit-fetch-with-cli = true\n")
            provenance = fixture.preflight()
            self.assertIn(str(config), provenance["cargo_configs"])
            for target_dir in (GATE.ROOT, GATE.ROOT.parent):
                codes, _ = fixture.codes(target_dir=target_dir)
                self.assertEqual(codes, [GATE.TARGET_DIR_REFUSED])

    def test_independent_findings_are_all_reported(self):
        with tempfile.TemporaryDirectory() as temp:
            fixture = PackageFixture(Path(temp).resolve(), std=False)
            (fixture.tools / "otool").unlink()
            codes, _ = fixture.codes(TCG_NO_PROOF_CERTS="1", FAKE_TRUST_MODE="no-knobs")
            self.assertEqual(sorted(codes), sorted([
                GATE.AMBIENT_OVERRIDE, GATE.RUST_STD_ABSENT, GATE.KNOBS_ABSENT, GATE.HOST_TOOL_MISSING]))

    # Backend staleness --------------------------------------------------------------

    def staleness_fixture(self, directory: Path):
        backend = directory / "cache" / "release" / GATE.BACKEND_NAME
        backend.parent.mkdir(parents=True)
        source = directory / "src dir" / "extra source.rs"
        source.parent.mkdir()
        source.write_text("// fixture source\n")
        old = time.time() - 3600
        os.utime(source, (old, old))
        backend.write_bytes(b"built backend")
        dep_info = backend.with_name(GATE.DEP_INFO_NAME)
        lib_rs = GATE.BRIDGE_DIR / "src" / "lib.rs"
        escape = lambda path: str(path).replace(" ", "\\ ")
        dep_info.write_text(f"{escape(backend)}: {escape(lib_rs)} {escape(source)}\n")
        return backend, dep_info, source

    def test_dep_info_parsing_keeps_escaped_spaces_and_requires_the_backend_rule(self):
        text = "/t/release/lib x.dylib /t/release/other: /a/b\\ c.rs /d.rs\n\n/t/unrelated: /e.rs\n"
        self.assertEqual(GATE.split_make_words("a\\ b c:"), ["a b", "c:"])
        self.assertEqual(GATE.dep_info_sources("/t/release/other: /a/b\\ c.rs /d.rs\n", Path("/t/release/other")),
                         [Path("/a/b c.rs"), Path("/d.rs")])
        self.assertEqual(GATE.dep_info_sources(text.replace("lib x", "libx"), Path("/t/release/other")),
                         [Path("/a/b c.rs"), Path("/d.rs")])
        with self.assertRaises(ValueError):
            GATE.dep_info_sources(text, Path("/t/release/missing.dylib"))

    def test_backend_newer_than_every_dep_info_source_is_current(self):
        with tempfile.TemporaryDirectory() as temp:
            backend, dep_info, _ = self.staleness_fixture(Path(temp).resolve())
            record = GATE.backend_staleness(backend, dep_info)
            self.assertFalse(record["stale"], record)
            self.assertEqual(record["sources"], 2)
            self.assertEqual(record["newer_source_count"], 0)

    def test_stale_or_undecidable_backends_are_refused(self):
        with tempfile.TemporaryDirectory() as temp:
            directory = Path(temp).resolve()
            backend, dep_info, source = self.staleness_fixture(directory)
            future = time.time() + 3600
            os.utime(source, (future, future))
            record = GATE.backend_staleness(backend, dep_info)
            self.assertTrue(record["stale"])
            self.assertEqual(record["code"], GATE.STALE_BACKEND)
            self.assertEqual(record["newer_sources"], [str(source)])
            source.unlink()
            record = GATE.backend_staleness(backend, dep_info)
            self.assertEqual((record["stale"], record["code"]), (True, GATE.STALE_BACKEND))
            self.assertEqual(record["missing_sources"], [str(source)])
            dep_info.write_text(f"{backend}: {directory / 'only.rs'}\n")
            (directory / "only.rs").write_text("")
            record = GATE.backend_staleness(backend, dep_info)
            self.assertEqual((record["stale"], record["code"]), (True, GATE.STALENESS_UNDECIDABLE))
            dep_info.write_text(f"{directory / 'other.dylib'}: {GATE.BRIDGE_DIR / 'src' / 'lib.rs'}\n")
            record = GATE.backend_staleness(backend, dep_info)
            self.assertEqual((record["stale"], record["code"]), (True, GATE.STALENESS_UNDECIDABLE))
            dep_info.unlink()
            record = GATE.backend_staleness(backend, dep_info)
            self.assertEqual((record["stale"], record["code"]), (True, GATE.STALENESS_UNDECIDABLE))

    # Transcript classification ------------------------------------------------------

    def test_every_required_target_passes_its_positive_success_transcript(self):
        for row in GATE.TARGETS:
            with self.subTest(target=row.name):
                verdict = GATE.classify_target(row, 0, success_transcript(row.name))
                self.assertEqual(verdict["status"], "pass", verdict)
                self.assertEqual(verdict["counts"]["executed"], row.minimum)
                self.assertEqual(verdict["refusal_lines"], [])
        corpus = GATE.classify_target(target("real_program_corpus_a64"), 0, success_transcript("real_program_corpus_a64"))
        self.assertEqual(corpus["compile_verdict"]["label"], GATE.COMPILE_VERDICT_LABEL)
        self.assertEqual(corpus["compile_verdict"]["compiled"], 19)
        self.assertEqual(corpus["compile_verdict"]["total"], 26)
        self.assertEqual(corpus["kind"], GATE.COMPILE_VERDICT)

    def test_skip_guard_and_tcg_proof_465_early_returns_fail(self):
        test = SUCCESS["coroutine_generator_aarch64"][0][0]
        coroutine = target("coroutine_generator_aarch64")
        for line in ("skipping: cc not available",
                     "skipping: rust-std for aarch64-apple-darwin not installed for pinned toolchain",
                     "skipping: requires an aarch64-apple-darwin host",
                     "coroutine_generator_aarch64: SKIPPED — this build compiler has no `-Ztrust-ir-cg-args`",
                     "SKIP: native execution unavailable",
                     "error: proof promotion rejected (TCG-PROOF-465): no object relocation proof is registered"):
            with self.subTest(line=line):
                verdict = GATE.classify_target(coroutine, 0, libtest([test], {test: line}))
                self.assertEqual(verdict["status"], "fail", verdict)
                self.assertEqual(verdict["refusal_lines"], [line])
                self.assertEqual(verdict["refused_tests"], [test])
                self.assertEqual(verdict["counts"]["executed"], 0)
        hello = SUCCESS["hello_loop"][0][0]
        for line in ("hello_loop: SKIPPED — this M0 smoke test targets aarch64-apple-darwin hosts",
                     "skipping hello-loop end-to-end run: std `fn main` is fail-closed on lowering"):
            verdict = GATE.classify_target(target("hello_loop"), 0, libtest([hello], {hello: line}))
            self.assertEqual(verdict["status"], "fail")
        corpus = SUCCESS["real_program_corpus_a64"][0][0]
        verdict = GATE.classify_target(target("real_program_corpus_a64"), 0,
                                       libtest([corpus], {corpus: corpus_output(ratchet=True)}))
        self.assertEqual(verdict["status"], "fail")
        self.assertTrue(any("coverage floor SKIPPED" in line for line in verdict["refusal_lines"]))
        self.assertTrue(any("TCG-PROOF-465" in line for line in verdict["refusal_lines"]))
        # A refusal line outside any test's captured output still fails.
        text = "skipping: unattributed guard\n" + success_transcript("coroutine_generator_aarch64")
        self.assertEqual(GATE.classify_target(coroutine, 0, text)["status"], "fail")

    def test_one_early_return_cannot_hide_behind_its_sibling_test(self):
        tests, _ = SUCCESS["drop_heap_aarch64"]
        outputs = success_outputs("drop_heap_aarch64")
        verdict = GATE.classify_target(target("drop_heap_aarch64"), 0,
                                       libtest(tests, {**outputs, tests[1]: "skipping: cc not available"}))
        self.assertEqual(verdict["status"], "fail")
        self.assertEqual(verdict["counts"]["executed"], 2)
        self.assertEqual(verdict["refused_tests"], [tests[1]])
        self.assertTrue(any("below the required minimum 3" in error for error in verdict["errors"]))
        # A silent early return prints nothing at all; only the missing marker shows it.
        verdict = GATE.classify_target(target("drop_heap_aarch64"), 0,
                                       libtest(tests, {tests[0]: outputs[tests[0]]}))
        self.assertEqual(verdict["status"], "fail")
        self.assertEqual(verdict["counts"]["executed"], 1)
        self.assertEqual(verdict["unevidenced_passes"], [tests[1], tests[2]])
        self.assertEqual(verdict["refusal_lines"], [])

    def test_a_pass_is_credited_only_with_its_own_well_formed_marker(self):
        row = target("coroutine_generator_aarch64")
        test = SUCCESS[row.name][0][0]
        good = evidenced(test, GATE.NATIVE_RUN, "off")
        cases = {
            "no marker": "linked and ran",
            "marker names a sibling": marker(GATE.NATIVE_RUN, "off", "some_other_test"),
            "malformed marker": f"{GATE.POSITIVE_MARKER} kind=native-run test={test}",
            "unknown kind": marker("vibes", "off", test),
            "unknown certificate state": marker(GATE.NATIVE_RUN, "maybe", test),
            "conflicting markers": good + "\n" + marker(GATE.COMPILED, "off", test),
            "kind not credited for the target kind": marker(GATE.VERDICT, "off", test),
        }
        for name, output in cases.items():
            with self.subTest(case=name):
                verdict = GATE.classify_target(row, 0, libtest([test], {test: output}))
                self.assertEqual(verdict["status"], "fail", verdict)
                self.assertEqual(verdict["counts"]["executed"], 0)
        # A marker outside any test's captured output credits nothing.
        verdict = GATE.classify_target(row, 0, good + "\n" + libtest([test]))
        self.assertEqual(verdict["status"], "fail")
        self.assertTrue(any("outside any test's captured output" in error for error in verdict["errors"]))
        # The same marker twice is one credited test.
        verdict = GATE.classify_target(row, 0, libtest([test], {test: good + "\n" + good}))
        self.assertEqual(verdict["status"], "pass", verdict)
        self.assertEqual(verdict["positive_evidence"], {test: {"kind": GATE.NATIVE_RUN, "certs": "off"}})

    def test_evidence_profile_and_proofs_off_count_are_exact(self):
        unwind = target("unwind_cleanup_aarch64")
        tests, outputs = SUCCESS[unwind.name]
        weakened = {**success_outputs(unwind.name)}
        weakened[tests[1]] = outputs[tests[1]] + "\n" + evidenced(tests[1], GATE.COMPILED, "off")
        verdict = GATE.classify_target(unwind, 0, libtest(tests, weakened))
        self.assertEqual(verdict["status"], "fail")
        self.assertTrue(any("evidence profile" in error for error in verdict["errors"]), verdict["errors"])
        coroutine = target("coroutine_generator_aarch64")
        test = SUCCESS[coroutine.name][0][0]
        verdict = GATE.classify_target(coroutine, 0, libtest([test], {test: marker(GATE.NATIVE_RUN, "on", test)}))
        self.assertEqual(verdict["status"], "fail")
        self.assertTrue(any("proofs-off" in error for error in verdict["errors"]), verdict["errors"])
        static = target("static_data_aarch64")
        tests = SUCCESS[static.name][0]
        all_off = {name: "\n".join(filter(None, [SUCCESS[static.name][1].get(name, ""),
                                                evidenced(name, GATE.NATIVE_RUN, "off")]))
                   for name in tests}
        verdict = GATE.classify_target(static, 0, libtest(tests, all_off))
        self.assertEqual(verdict["status"], "fail", "a fourth proofs-off test is a weakening")
        self.assertTrue(any("proofs-off" in error for error in verdict["errors"]), verdict)
        verdict = GATE.classify_target(static, 0, success_transcript(static.name))
        self.assertEqual(verdict["status"], "pass", verdict)
        self.assertEqual(verdict["certs_counts"], {"off": 3, "on": 1})
        self.assertEqual(len(verdict["certs_off_tests"]), 3)

    def test_a_certs_label_is_checked_against_the_knobs_the_test_built(self):
        # The review's mutation: hello_loop gains `no-proof-certs` but keeps its
        # certs=on marker. Its own knob trace contradicts the label.
        hello = target("hello_loop")
        test = SUCCESS[hello.name][0][0]
        output = SUCCESS[hello.name][1][test]
        mutated = "\n".join([output, knobs("bridge-notes", "no-proof-certs"),
                             marker(GATE.NATIVE_RUN, "on", test)])
        verdict = GATE.classify_target(hello, 0, libtest([test], {test: mutated}))
        self.assertEqual(verdict["status"], "fail")
        self.assertEqual(verdict["counts"]["executed"], 0)
        self.assertEqual(verdict["certs_counts"], {})
        self.assertTrue(any("says certs=on but it built a no-proof-certs" in error
                            for error in verdict["errors"]), verdict["errors"])
        # The rejected marker is named as such, not as a missing one.
        self.assertEqual(verdict["unevidenced_passes"], [])
        self.assertEqual(verdict["backend_knob_traces"], {test: ["bridge-notes no-proof-certs"]})
        # The same weakening in a target that already passes the knob elsewhere
        # (unsupported_program's shared compile helper): still caught per test.
        row = target("unsupported_program")
        tests, _ = SUCCESS[row.name]
        outputs = success_outputs(row.name)
        on_tests = [name for name in tests if "certs=on" in outputs[name]]
        weakened = {**outputs, on_tests[0]: knobs("no-proof-certs") + "\n" + outputs[on_tests[0]]}
        verdict = GATE.classify_target(row, 0, libtest(tests, weakened))
        self.assertEqual(verdict["status"], "fail")
        self.assertNotIn(on_tests[0], verdict["positive_evidence"])
        coroutine = target("coroutine_generator_aarch64")
        test = SUCCESS[coroutine.name][0][0]
        for name, output, text in (
                ("off without any knob trace", marker(GATE.NATIVE_RUN, "off", test), "says certs=off"),
                ("off with an unrelated knob", knobs("bridge-notes") + "\n" + marker(GATE.NATIVE_RUN, "off", test),
                 "says certs=off"),
                ("off with the knob spelled off", knobs("no-proof-certs=0") + "\n"
                 + marker(GATE.NATIVE_RUN, "off", test), "says certs=off"),
                ("on with a malformed knob value", knobs("no-proof-certs=nope") + "\n"
                 + marker(GATE.NATIVE_RUN, "on", test), "says certs=on"),
                ("none with a knob trace", knobs("time") + "\n" + marker(GATE.NATIVE_RUN, "none", test),
                 "says certs=none"),
                ("malformed knob trace", f"{GATE.KNOB_TRACE}: no-proof-certs\n"
                 + evidenced(test, GATE.NATIVE_RUN, "off"), "malformed")):
            with self.subTest(case=name):
                verdict = GATE.classify_target(coroutine, 0, libtest([test], {test: output}))
                self.assertEqual(verdict["status"], "fail", verdict)
                self.assertTrue(any(text in error for error in verdict["errors"]), verdict["errors"])
        # A knob trace outside any test's captured output fails the target.
        verdict = GATE.classify_target(coroutine, 0,
                                       knobs("no-proof-certs") + "\n" + success_transcript(coroutine.name))
        self.assertEqual(verdict["status"], "fail")
        self.assertTrue(any("knob trace outside" in error for error in verdict["errors"]))
        # Every accepted spelling that turns certificates off counts as off; an
        # explicit off spelling keeps them on.
        for items, expected in ((["no-proof-certs"], True), (["no-proof-certs=1"], True),
                                (["time", "no-proof-certs=yes"], True), (["no-proof-certs=nope"], True),
                                (["no-proof-certs=0"], False), (["no-proof-certs=off"], False),
                                (["no-proof-cache"], False), (["time"], False)):
            with self.subTest(items=items):
                self.assertEqual(GATE.disables_proof_certificates(items), expected)
        self.assertEqual(GATE.traced_certificates([]), "none")
        self.assertEqual(GATE.traced_certificates([["time"]]), "on")
        self.assertEqual(GATE.traced_certificates([["time"], ["no-proof-certs"]]), "off")

    def test_knob_use_is_tied_to_the_proofs_off_row_in_the_fixture_sources(self):
        with tempfile.TemporaryDirectory() as temp:
            tests = Path(temp)
            copy_test_sources(tests)
            self.assertEqual(GATE.inventory_problems(tests), [])
            hello = tests / "hello_loop.rs"
            original = hello.read_text()
            self.assertEqual(original.count('backend_knobs_arg(&["bridge-notes"])'), 1)
            # A certs_off == 0 target that gains the knob is an inventory problem.
            hello.write_text(original.replace('backend_knobs_arg(&["bridge-notes"])',
                                              'backend_knobs_arg(&["bridge-notes", "no-proof-certs"])'))
            self.assertTrue(any("hello_loop: passes" in problem and "no proofs-off" in problem
                                for problem in GATE.inventory_problems(tests)))
            # Spelling the option itself bypasses the trace.
            for spelling in ('.arg("-Ztrust-ir-cg-args=bridge-notes")',
                             '.arg(format!("{}=bridge-notes", toolchain_support::BACKEND_KNOBS_OPTION))'):
                with self.subTest(spelling=spelling):
                    hello.write_text(original.replace(
                        '.arg(toolchain_support::backend_knobs_arg(&["bridge-notes"]))', spelling))
                    self.assertTrue(any("spells the backend knob option itself" in problem
                                        for problem in GATE.inventory_problems(tests)))
            # A comment may name the option.
            hello.write_text(original + "\n// -Ztrust-ir-cg-args=no-proof-certs is not used here\n")
            self.assertEqual(GATE.inventory_problems(tests), [])
            hello.write_text(original)
            # A certs_off > 0 target whose code no longer names the knob.
            tls = tests / "tls_thread_local_aarch64.rs"
            tls.write_text(tls.read_text().replace('&["no-proof-certs"]', '&["bridge-notes"]'))
            self.assertTrue(any("tls_thread_local_aarch64: its row counts 1 proofs-off" in problem
                                for problem in GATE.inventory_problems(tests)))

    def test_every_module_a_required_fixture_compiles_in_is_held_to_the_knob_rule(self):
        with tempfile.TemporaryDirectory() as temp:
            tests = Path(temp)
            copy_test_sources(tests)
            self.assertEqual(GATE.inventory_problems(tests), [])
            toolchain = tests / "support" / "toolchain.rs"
            original = toolchain.read_text()
            anchor = '    cmd.arg("-Ztrust-verify=off");\n'
            self.assertEqual(original.count(anchor), 1)
            # The review's mutation: the shared constructor every certificates-on
            # oracle starts from gains the knob, which prints no trace. It must
            # be refused for the module, named by its enclosing fn.
            for added in ('    cmd.arg("-Ztrust-ir-cg-args=no-proof-certs");\n',
                          '    cmd.arg(format!("{BACKEND_KNOBS_OPTION}=time"));\n',
                          '    cmd.arg(backend_knobs_arg(&["no-proof-certs"]));\n'):
                with self.subTest(added=added):
                    toolchain.write_text(original.replace(anchor, anchor + added))
                    problems = GATE.inventory_problems(tests)
                    self.assertTrue(problems)
                    self.assertTrue(all(problem.startswith("support/toolchain.rs (compiled into ")
                                        for problem in problems), problems)
                    # Every required target includes the constructor.
                    self.assertTrue(all(row.name in problems[0] for row in GATE.TARGETS), problems[0])
                    if "backend_knobs_arg" not in added:
                        self.assertTrue(any("in fn/item rustc_command_with_edition" in problem
                                            for problem in problems), problems)
            # A module comment may name both; the owner items stay exempt.
            toolchain.write_text(original + "\n// -Ztrust-ir-cg-args=no-proof-certs is not used here\n"
                                 "/* nor BACKEND_KNOBS_OPTION /* nested */ here */\n")
            self.assertEqual(GATE.inventory_problems(tests), [])
            # An owner item defined twice no longer names one item.
            toolchain.write_text(original + '\npub const BACKEND_KNOBS_OPTION: &str = "-Zother";\n')
            self.assertTrue(any("owner item BACKEND_KNOBS_OPTION is defined 2 times" in problem
                                for problem in GATE.inventory_problems(tests)))
            toolchain.write_text(original)
            # An owner of one module exempts nothing in another.
            prerequisites = tests / "support" / "darwin_native_prerequisites.rs"
            text = prerequisites.read_text()
            prerequisites.write_text(text + '\nfn backend_knobs_arg() -> String { format!("{}=time", '
                                     'crate::toolchain_support::BACKEND_KNOBS_OPTION) }\n')
            self.assertTrue(any("support/darwin_native_prerequisites.rs" in problem
                                and "in fn/item backend_knobs_arg" in problem
                                for problem in GATE.inventory_problems(tests)))
            prerequisites.write_text(text)
            # A new module, by #[path], by a bare `mod`, or by a literal include!,
            # is followed; so is a module a module compiles in.
            hello = tests / "hello_loop.rs"
            original_hello = hello.read_text()
            (tests / "support" / "extra.rs").write_text(
                'pub fn knobs() -> &\'static str { "-Ztrust-ir-cg-args=no-proof-certs" }\n')
            for declaration in ('#[path = "support/extra.rs"]\nmod extra;\n',
                                'include!("support/extra.rs");\n'):
                with self.subTest(declaration=declaration):
                    hello.write_text(declaration + original_hello)
                    problems = GATE.inventory_problems(tests)
                    self.assertTrue(any(problem.startswith("support/extra.rs (compiled into hello_loop)")
                                        for problem in problems), problems)
            (tests / "sneaky.rs").write_text('#[path = "support/extra.rs"]\nmod extra;\n')
            hello.write_text("mod sneaky;\n" + original_hello)
            self.assertTrue(any(problem.startswith("support/extra.rs (compiled into hello_loop)")
                                for problem in GATE.inventory_problems(tests)))
            # An unresolvable or unscannable declaration fails closed.
            for declaration, text in (("mod ghost;\n", "`mod ghost;` resolves to no file"),
                                      ('#[path = "support/missing.rs"]\nmod missing;\n', "which is not a file"),
                                      ('include!(concat!("support/", "extra.rs"));\n', "not a literal"),
                                      ('#[path = "support/extra.rs"]\nmod inline { }\n', "#[path] attribute"),
                                      ('#[cfg_attr(unix, path = "support/extra.rs")]\nmod extra;\n',
                                       "#[path] attribute")):
                with self.subTest(declaration=declaration):
                    hello.write_text(declaration + original_hello)
                    self.assertTrue(any(text in problem for problem in GATE.inventory_problems(tests)),
                                    GATE.inventory_problems(tests))
            # A guest program in a string is data, not a declaration.
            hello.write_text(original_hello + '\nconst GUEST: &str = "mod ghost; include!(\\"x\\");";\n')
            self.assertEqual(GATE.inventory_problems(tests), [])

    def test_rust_views_blank_comments_and_literals_at_their_offsets(self):
        source = ('let a = "// not a comment { ";  // a comment {\n'
                  "let b = r#\"raw \" { \"#; /* block /* nested */ { */ let c = '{';\n"
                  "fn f<'a>(x: &'a str) -> &'static str { x }\n")
        code, skeleton = GATE.rust_views(source)
        self.assertEqual(len(code), len(source))
        self.assertEqual(len(skeleton), len(source))
        self.assertEqual(code.count("\n"), source.count("\n"))
        self.assertIn('"// not a comment { "', code)
        self.assertNotIn("// a comment", code)
        self.assertNotIn("nested", code)
        self.assertIn("r#\"raw \" { \"#", code)
        # Only the fn body's braces survive in the skeleton.
        self.assertEqual(skeleton.count("{"), 1)
        self.assertEqual(skeleton.count("}"), 1)
        self.assertEqual([name for name, _, _ in GATE.item_spans(skeleton)], ["f"])
        spans = GATE.item_spans(GATE.rust_views(
            "pub const fn k() -> u8 { const N: u8 = 1; N }\nstatic mut S: u8 = 0;\n"
            "fn g<const M: usize>() { }\n")[1])
        self.assertEqual([name for name, _, _ in spans], ["k", "N", "S", "g", "M"])

    def test_only_the_named_backend_diagnostics_are_exempt_from_the_skip_rule(self):
        row = target("reference_union_semantics")
        tests, _ = SUCCESS[row.name]
        # The exact lines a recorded run echoed (2026-10-04, pack 9192), with
        # this host's paths.
        checker = (
            "[trust-cg] proof checker $HOME/Library/Application Support/aterm/pkg/store/trust/9192/bin/"
            "clean skipped (it was built WITHOUT the `carcara-verify` cargo feature, so it rejects every "
            "Alethe proof regardless of validity); using $HOME/Library/Application Support/aterm/pkg/"
            "store/clean/8606/bin/clean")
        certificates = (
            "trust-cg-verify::canary_cert: WARNING: portable certificate set is DISABLED; CERT-SKIP "
            "declined for every query and live discharge retained: the vendored drat-trim checker "
            "$HOME/trust-cg/crates/rustc-codegen-trust-cg/target/gate/release/build/"
            "trust-cg-drat-trim-8619b34440237ff9/out/drat-trim hashes to " + "f0" * 32
            + " but manifest.v1 authorizes " + "69" * 32 + "; the checker's bytes follow the host C "
            "toolchain (compiler, SDK, and the deployment target pinned in "
            "crates/trust-cg-drat-trim/build.rs). Options: restore the toolchain the manifest was minted "
            "against, or review the toolchain change and re-authorize the complete set with `scripts/trust_cargo.sh "
            "run --release -p trust-cg-verify --bin regen_canary_certs`")
        outputs = {test: f"rustc stderr:\n{checker}\n{certificates}\n{line}"
                   for test, line in success_outputs(row.name).items()}
        verdict = GATE.classify_target(row, 0, libtest(tests, outputs))
        self.assertEqual(verdict["status"], "pass", verdict["errors"][:3])
        self.assertEqual(verdict["exempted_diagnostics"], {
            "checker-candidate-passed-over": len(tests), "portable-certificates-declined": len(tests)})
        # The exemptions are anchored on the whole line: another feature, a
        # truncated line, a prefix or ANY appended text is a refusal again.
        for variant in (checker.replace("carcara-verify", "other-feature"),
                        "[trust-cg] proof checker /pkg/bin/clean skipped",
                        checker.replace("validity); using", "validity; more text); using"),
                        checker + "; test SKIPPED",
                        # Appended text that itself ends in a checker path
                        # (review of edf620177): never absorbed into the path.
                        checker + " -- hello_loop SKIPPED, see /x/bin/clean",
                        checker + " -- hello_loop SKIPPED see /x/bin/clean",
                        checker.replace("/8606/bin/clean", "/8606/bin/clean, then /x/bin/clean"),
                        # A checker that is not a `bin/clean`.
                        checker.replace("store/clean/8606/bin/clean", "store/clean/8606/clean"),
                        certificates + " -- test skipped",
                        certificates.replace("f0" * 32, "not-a-digest"),
                        "note: " + certificates):
            with self.subTest(variant=variant):
                changed = {**outputs, tests[0]: f"{variant}\n{success_outputs(row.name)[tests[0]]}"}
                self.assertEqual(GATE.classify_target(row, 0, libtest(tests, changed))["status"], "fail")

    def test_checker_exemption_matches_the_line_trust_cg_verify_prints(self):
        # The exemption's fixed text must be what note_checker_skipped prints
        # for CheckerDefect::CarcaraFeatureMissing TODAY. 4ff6cd0fe shortened
        # that reason, the hand-copied line above kept the old wording, and
        # every certificates-on row that printed the real line was refused for
        # it. Rebuild the line from the Rust source instead of copying it.
        source = (ROOT / "crates" / "trust-cg-verify" / "src" / "obligation_cert_store.rs").read_text(
            encoding="utf-8")
        literal = r'"((?:[^"\\]|\\.)*)"'

        def rust_string(pattern: str) -> str:
            found = re.search(pattern + literal, source, re.DOTALL)
            self.assertIsNotNone(found, pattern)
            # A backslash-newline continuation drops the newline and the next
            # line's leading whitespace; no other escape occurs in these two.
            text = re.sub(r"\\\n\s*", "", found.group(1))
            self.assertNotIn("\\", text)
            return text

        reason = rust_string(r"Self::CarcaraFeatureMissing => String::from\(\s*")
        template = rust_string(r"fn note_checker_skipped\([^{]*\{.*?eprintln!\(\s*")
        self.assertEqual(template.count("{}"), 3, template)
        line = template.replace("{}", "$HOME/Library/Application Support/aterm/pkg/store/trust/9192/bin/clean", 1)
        line = line.replace("{}", reason, 1)
        line = line.replace("{}", "$HOME/Library/Application Support/aterm/pkg/store/clean/8606/bin/clean", 1)
        self.assertEqual(GATE.exempt_diagnostic(line), "checker-candidate-passed-over", line)
        # Still the whole line only: another reason for the same skip is not exempt.
        self.assertIsNone(GATE.exempt_diagnostic(line.replace(reason, reason + " and more")))

    def test_tcg_proof_465_is_data_only_in_a_test_whose_claim_is_a_refusal(self):
        row = target("unsupported_program")
        tests, _ = SUCCESS[row.name]
        outputs = success_outputs(row.name)
        refusal = "- main: [TCG-PROOF-465] proof promotion rejected for target Aarch64"
        refused = [test for test in tests if f"kind={GATE.EXPECTED_REFUSAL}" in outputs[test]]
        native = [test for test in tests if f"kind={GATE.NATIVE_RUN}" in outputs[test]]
        self.assertTrue(refused and native)
        with_context = {**outputs, refused[0]: refusal + "\n" + outputs[refused[0]]}
        verdict = GATE.classify_target(row, 0, libtest(tests, with_context))
        self.assertEqual(verdict["status"], "pass", verdict["errors"][:3])
        for test, line in ((native[0], refusal), (refused[0], "skipping: the refusal was expected")):
            with self.subTest(test=test, line=line):
                changed = {**outputs, test: line + "\n" + outputs[test]}
                verdict = GATE.classify_target(row, 0, libtest(tests, changed))
                self.assertEqual(verdict["status"], "fail")
                self.assertEqual(verdict["refused_tests"], [test])
                # A passed test with a refusal line is never credited, even
                # though it printed its marker: the per-target and report
                # totals count only the other tests.
                self.assertEqual(verdict["counts"]["executed"], row.minimum - 1)
                self.assertNotIn(test, verdict["positive_evidence"])
                self.assertEqual(sum(verdict["evidence_counts"].values()), row.minimum - 1)
                self.assertEqual(sum(verdict["certs_counts"].values()), row.minimum - 1)
        corpus = target("real_program_corpus_a64")
        verdict = GATE.classify_target(corpus, 0, success_transcript(corpus.name))
        self.assertEqual(verdict["status"], "pass", verdict["errors"])

    def test_failed_tests_are_reported_with_their_tcg_codes(self):
        row = target("overflow_asserts")
        tests, _ = SUCCESS[row.name]
        failing = tests[0]
        passing = success_outputs(row.name)
        lines = [f"running {len(tests)} tests", f"test {failing} ... FAILED",
                 *(f"test {test} ... ok" for test in tests[1:]), "", "successes:", ""]
        for test in tests[1:]:
            lines += [f"---- {test} stdout ----", passing[test], ""]
        lines += ["", "successes:", *(f"    {test}" for test in tests[1:]), "", "failures:", "",
                  f"---- {failing} stdout ----",
                  f"thread '{failing}' panicked at tests/overflow_asserts.rs:1:1:",
                  "rustc failed: [TCG-MIR-UNSUPPORTED] ... [TCG-PROOF-465] proof promotion rejected", "",
                  "failures:", f"    {failing}", "",
                  f"test result: FAILED. {len(tests) - 1} passed; 1 failed; 0 ignored; 0 measured; "
                  "0 filtered out; finished in 0.01s"]
        verdict = GATE.classify_target(row, 101, "\n".join(lines) + "\n")
        self.assertEqual(verdict["status"], "fail")
        self.assertEqual(verdict["counts"]["executed"], len(tests) - 1)
        self.assertEqual(verdict["failed_tests"], {failing: ["TCG-MIR-UNSUPPORTED", "TCG-PROOF-465"]})

    def test_ignored_filtered_incomplete_failed_or_missing_suites_fail(self):
        tests, _ = SUCCESS["drop_heap_aarch64"]
        row = target("drop_heap_aarch64")
        cases = {
            "ignored": libtest(tests, ignored=["extra_ignored_test"]),
            "filtered": libtest(tests, filtered=1),
            "one test only": libtest(tests[:1]),
            "no suite": "",
            "two suites": libtest(tests) + libtest(tests),
            "incomplete": libtest(tests).rsplit("test result:", 1)[0],
        }
        for name, text in cases.items():
            with self.subTest(case=name):
                self.assertEqual(GATE.classify_target(row, 0, text)["status"], "fail")
        self.assertEqual(GATE.classify_target(row, 101, libtest(tests))["status"], "fail")
        self.assertEqual(GATE.classify_target(row, 124, libtest(tests))["status"], "fail")

    def test_tuple_scalar_credit_requires_every_cell_and_both_panic_strategies(self):
        row = target("clone_sort_user_trait_differential_aarch64")
        text = success_transcript(row.name)
        marker = "CLONE_SORT_TUPLE_SCALARS rows=7 cells=56 matched=56 refused=0 opts=0,1,2,3 strategies=abort,unwind"
        self.assertEqual(text.count(marker), 1)
        self.assertEqual(GATE.classify_target(row, 0, text)["status"], "pass")
        for changed in ("omitted", marker.replace("cells=56", "cells=55"),
                        marker.replace("matched=56", "matched=55"),
                        marker.replace("refused=0", "refused=1"),
                        marker.replace("opts=0,1,2,3", "opts=0,1,2"),
                        marker.replace("abort,unwind", "abort")):
            with self.subTest(marker=changed):
                verdict = GATE.classify_target(row, 0, text.replace(marker, changed))
                self.assertEqual(verdict["status"], "fail")

    def test_required_execution_markers_cannot_be_omitted(self):
        tests, outputs = SUCCESS["unwind_cleanup_aarch64"]
        row = target("unwind_cleanup_aarch64")
        for test in tests:
            with self.subTest(dropped=test):
                verdict = GATE.classify_target(row, 0, libtest(tests, {**outputs, test: "done"}))
                self.assertEqual(verdict["status"], "fail")
                self.assertTrue(any("marker missing" in error for error in verdict["errors"]))
        caught = tests[1]
        verdict = GATE.classify_target(row, 0, libtest(tests, {
            **outputs, caught: "REAL Rust panic CAUGHT through the bridge: AY_CAUGHT=1 CLEANUP_RAN=0"}))
        self.assertEqual(verdict["status"], "fail")
        hello = SUCCESS["hello_loop"][0]
        self.assertEqual(GATE.classify_target(target("hello_loop"), 0, libtest(hello))["status"], "fail")

    def test_termination_credit_requires_original_mixed_and_boundary_controls(self):
        row = target("terminate_panic_differential_aarch64")
        tests, _ = SUCCESS[row.name]
        outputs = success_outputs(row.name)
        self.assertEqual(GATE.classify_target(row, 0, libtest(tests, outputs))["status"], "pass")
        # A positive native marker cannot hide an omitted original cell,
        # foreign-unwind route, object set, source-boundary control, call-site
        # region row or unwind-callee region row. All eleven aggregate markers
        # come after their mandatory checks in the fixture's three tests.
        for required in row.markers:
            with self.subTest(omitted=required):
                self.assertEqual(sum(required in output for output in outputs.values()), 1)
                changed = {test: output.replace(required, "omitted required control")
                           for test, output in outputs.items()}
                verdict = GATE.classify_target(row, 0, libtest(tests, changed))
                self.assertEqual(verdict["status"], "fail")
                self.assertTrue(any("marker missing" in error for error in verdict["errors"]))

    def test_subslice_loop_credit_requires_every_cell_and_native_evidence(self):
        row = target("subslice_loop_compile_bound_aarch64")
        text = success_transcript(row.name)
        self.assertEqual(GATE.classify_target(row, 0, text)["status"], "pass")
        mutations = {
            "missing cell ledger": text.replace(row.markers[0], "loops checked"),
            "a cell that did not match": text.replace("matched=16", "matched=15"),
            "incomplete cells": text.replace("cells=16", "cells=12"),
            "missing native evidence": text.replace(GATE.NATIVE_RUN, GATE.COMPILED),
            "wrong certificate mode": text.replace("certs=off", "certs=on"),
            "zero tests": libtest([]),
        }
        for label, mutated in mutations.items():
            with self.subTest(label=label):
                self.assertEqual(GATE.classify_target(row, 0, mutated)["status"], "fail")

    def test_slice_sort_order_credit_requires_every_cell_and_native_evidence(self):
        row = target("slice_sort_order_aarch64")
        text = success_transcript(row.name)
        self.assertEqual(GATE.classify_target(row, 0, text)["status"], "pass")
        mutations = {
            "missing cell ledger": text.replace(row.markers[0], "sorts checked"),
            "a wrong order counted as refused": text.replace("matched=10", "matched=9"),
            "incomplete cells": text.replace("cells=16", "cells=15"),
            "missing native evidence": text.replace(GATE.NATIVE_RUN, GATE.COMPILED),
            "wrong certificate mode": text.replace("certs=off", "certs=on"),
            "zero tests": libtest([]),
        }
        for label, mutated in mutations.items():
            with self.subTest(label=label):
                self.assertEqual(GATE.classify_target(row, 0, mutated)["status"], "fail")

    def test_closure_pair_credit_requires_exact_mixed_cells_and_owned_native_marker(self):
        row = target("aarch64_closure_body_pair_xback")
        tests, _ = SUCCESS[row.name]
        outputs = success_outputs(row.name)
        test = tests[0]
        good = outputs[test]
        summary = good.splitlines()[0]
        self.assertEqual(GATE.classify_target(row, 0, libtest(tests, outputs))["status"], "pass")
        mutations = {
            "missing summary": good.replace(summary, ""),
            "missing producer": good.replace("rows=7", "rows=6"),
            "incomplete backend cells": good.replace("cells=16", "cells=15"),
            "wrong cell denominator": good.replace("cells=16", "cells=160"),
            "missing optimization level": good.replace("opts=0,1,2,3", "opts=0,1,2"),
            "missing artifact owner": good.replace(" artifacts=/fixture/closure-pair", ""),
            "summary hidden in prose": good.replace(summary, "untrusted prefix " + summary),
            "duplicate complete summary": good + "\n" + summary,
            "contradictory later summary": good + "\n" + summary.replace("cells=16", "cells=15"),
            "compile instead of execution": good.replace(GATE.NATIVE_RUN, GATE.COMPILED),
            "refusal masquerading as execution": good.replace(GATE.NATIVE_RUN, GATE.EXPECTED_REFUSAL),
            "missing positive marker": "\n".join(line for line in good.splitlines()
                                                  if GATE.POSITIVE_MARKER not in line),
            "wrong certificate mode": good.replace("certs=off", "certs=on"),
        }
        for label, output in mutations.items():
            with self.subTest(mutation=label):
                self.assertEqual(GATE.classify_target(row, 0, libtest(tests, {test: output}))["status"], "fail")
        evidence_only = good.replace(summary, "")
        self.assertEqual(GATE.classify_target(row, 0, summary + "\n" +
                         libtest(tests, {test: evidence_only}))["status"], "fail")
        self.assertEqual(GATE.classify_target(row, 0, libtest([]))["status"], "fail")

    def test_cached_key_credit_requires_four_native_matches_not_refusal_success(self):
        row = target("slice_sort_cached_key_effects_aarch64")
        tests, _ = SUCCESS[row.name]
        test = tests[0]
        good = success_outputs(row.name)[test]
        summary = good.splitlines()[0]
        self.assertEqual(GATE.classify_target(row, 0, libtest(tests, {test: good}))["status"], "pass")
        for outcomes, kind in [
            ("matched=0 refused=4", GATE.EXPECTED_REFUSAL),
            ("matched=0 refused=4", GATE.NATIVE_RUN),
            ("matched=3 refused=1", GATE.NATIVE_RUN),
            ("matched=4 refused=1", GATE.NATIVE_RUN),
        ]:
            with self.subTest(outcomes=outcomes, evidence=kind):
                changed = good.replace("matched=4 refused=0", outcomes).replace(GATE.NATIVE_RUN, kind)
                self.assertEqual(GATE.classify_target(row, 0, libtest(tests, {test: changed}))["status"], "fail")
        mutations = {
            "incomplete cells": good.replace("cells=4", "cells=3"),
            "inflated cells": good.replace("cells=4", "cells=40"),
            "missing summary": good.replace(summary, ""),
            "duplicate complete summary": good + "\n" + summary,
            "contradictory later summary": good + "\n" + summary.replace("matched=4 refused=0", "matched=0 refused=4"),
            "refusal beside forged success": good + "\nCACHED_KEY_COUNTER O0 refused=[TCG-MIR-UNSUPPORTED]",
            "wrong certificate state": good.replace("certs=off", "certs=on"),
            "missing positive marker": "\n".join(line for line in good.splitlines()
                                                  if GATE.POSITIVE_MARKER not in line),
        }
        for label, output in mutations.items():
            with self.subTest(mutation=label):
                self.assertEqual(GATE.classify_target(row, 0, libtest(tests, {test: output}))["status"], "fail")
        self.assertEqual(GATE.classify_target(row, 0, libtest([]))["status"], "fail")

    def test_closure_pair_and_cached_key_are_additive_required_native_rows(self):
        for name, test in (
            ("aarch64_closure_body_pair_xback", "closure_body_pairs_match_llvm_across_native_backend_boundaries"),
            ("slice_sort_cached_key_effects_aarch64", "cached_key_counter_calls_once_per_element_or_refuses_by_name"),
        ):
            with self.subTest(target=name):
                row = target(name)
                self.assertEqual((row.minimum, row.kind, row.evidence, row.certs_off),
                                 (1, GATE.NATIVE, ((GATE.NATIVE_RUN, 1),), 1))
                self.assertEqual(source_tests(name), [test])
                self.assertNotIn(name, GATE.NOT_COVERED)
                self.assertNotIn(name, GATE.OUT_OF_SCOPE)
                self.assertNotIn(name, GATE.NAMED_REFUSALS)
        source = (GATE.TESTS_DIR / "aarch64_closure_body_pair_xback.rs").read_text()
        self.assertLess(source.index("assert_eq!(cells, 12)"), source.index("positive_evidence::record("))

    def test_switch_case_signed_credit_requires_every_cell_and_native_evidence(self):
        row = target("switch_case_signed_aarch64")
        text = success_transcript(row.name)
        self.assertEqual(GATE.classify_target(row, 0, text)["status"], "pass")
        mutations = {
            "missing cell ledger": text.replace(row.markers[0], "switches checked"),
            "a cell that did not match": text.replace("matched=8", "matched=7"),
            "incomplete cells": text.replace("cells=8", "cells=4"),
            "missing native evidence": text.replace(GATE.NATIVE_RUN, GATE.COMPILED),
            "wrong certificate mode": text.replace("certs=off", "certs=on"),
            "zero tests": libtest([]),
        }
        for label, mutated in mutations.items():
            with self.subTest(label=label):
                self.assertEqual(GATE.classify_target(row, 0, mutated)["status"], "fail")

    def test_format_capacity_credit_requires_every_cell_and_native_evidence(self):
        row = target("format_capacity_aarch64")
        text = success_transcript(row.name)
        self.assertEqual(GATE.classify_target(row, 0, text)["status"], "pass")
        mutations = {
            "missing cell ledger": text.replace(row.markers[0], "capacities checked"),
            "a cell that did not match": text.replace("matched=40", "matched=39"),
            "incomplete cells": text.replace("cells=40", "cells=32"),
            "missing native evidence": text.replace(GATE.NATIVE_RUN, GATE.COMPILED),
            "wrong certificate mode": text.replace("certs=off", "certs=on"),
            "zero tests": libtest([]),
        }
        for label, mutated in mutations.items():
            with self.subTest(label=label):
                self.assertEqual(GATE.classify_target(row, 0, mutated)["status"], "fail")

    def test_vec_extend_capacity_credit_requires_every_cell_and_native_evidence(self):
        row = target("vec_extend_capacity_aarch64")
        text = success_transcript(row.name)
        self.assertEqual(GATE.classify_target(row, 0, text)["status"], "pass")
        mutations = {
            "missing cell ledger": text.replace(row.markers[0], "extends checked"),
            "fewer must-match cells": text.replace("must_match=24", "must_match=16"),
            "incomplete cells": text.replace("cells=48", "cells=32"),
            "missing native evidence": text.replace(GATE.NATIVE_RUN, GATE.COMPILED),
            "wrong certificate mode": text.replace("certs=off", "certs=on"),
            "zero tests": libtest([]),
        }
        for label, mutated in mutations.items():
            with self.subTest(label=label):
                self.assertEqual(GATE.classify_target(row, 0, mutated)["status"], "fail")

    def test_switch_join_constant_credit_requires_every_cell_and_native_evidence(self):
        row = target("switch_join_constant_aarch64")
        text = success_transcript(row.name)
        self.assertEqual(GATE.classify_target(row, 0, text)["status"], "pass")
        mutations = {
            "missing cell ledger": text.replace(row.markers[0], "switches checked"),
            "a cell that did not match": text.replace("matched=40", "matched=39"),
            "incomplete cells": text.replace("cells=40", "cells=32"),
            "missing native evidence": text.replace(GATE.NATIVE_RUN, GATE.COMPILED),
            "wrong certificate mode": text.replace("certs=off", "certs=on"),
            "zero tests": libtest([]),
        }
        for label, mutated in mutations.items():
            with self.subTest(label=label):
                self.assertEqual(GATE.classify_target(row, 0, mutated)["status"], "fail")

    def test_vec_capacity_credit_requires_all_cells_and_native_evidence(self):
        row = target("vec_from_elem_capacity_aarch64")
        text = success_transcript(row.name)
        self.assertEqual(GATE.classify_target(row, 0, text)["status"], "pass")
        mutations = {
            "missing cell ledger": text.replace(row.markers[0], "capacity checked"),
            "missing zero/struct case": text.replace("cases=2", "cases=1"),
            "incomplete backend cells": text.replace("cells=16", "cells=15"),
            "missing native evidence": text.replace(GATE.NATIVE_RUN, GATE.COMPILED),
            "wrong certificate mode": text.replace("certs=off", "certs=on"),
            "zero tests": libtest([]),
        }
        for name, changed in mutations.items():
            with self.subTest(case=name):
                self.assertEqual(GATE.classify_target(row, 0, changed)["status"], "fail")

    def test_stride_family_credit_requires_every_cell_and_the_pinned_split(self):
        row = target("stride_iter_family_differential_aarch64")
        text = success_transcript(row.name)
        self.assertEqual(GATE.classify_target(row, 0, text)["status"], "pass")
        mutations = {
            "missing cell ledger": text.replace(row.markers[0], "stride family checked"),
            "a matched cell turned refused": text.replace("matched=28 refused=4",
                                                          "matched=27 refused=5"),
            "a dropped fixture": text.replace("fixtures=4 cells=32", "fixtures=3 cells=24"),
            "fewer rows compared": text.replace("rows=164072", "rows=164071"),
            "an unpinned synthesized message": text.replace("synthesized_messages=0",
                                                            "synthesized_messages=1"),
            "missing native evidence": text.replace(GATE.NATIVE_RUN, GATE.COMPILED),
            "wrong certificate mode": text.replace("certs=off", "certs=on"),
            "zero tests": libtest([]),
        }
        for name, changed in mutations.items():
            with self.subTest(case=name):
                self.assertEqual(GATE.classify_target(row, 0, changed)["status"], "fail")

    def test_box_entry_credit_requires_complete_native_and_reader_markers(self):
        row = target("box_pointer_entry_aarch64")
        text = success_transcript(row.name)
        self.assertEqual(GATE.classify_target(row, 0, text)["status"], "pass")
        native, reader = row.markers
        mutations = {
            "missing native aggregate": text.replace(native, ""),
            "missing reader controls": text.replace(reader, ""),
            "truncated native aggregate": text.replace(native, native.rsplit(" certs=", 1)[0]),
            "truncated reader controls": text.replace(reader, reader.rsplit(" refused=", 1)[0]),
        }
        for field, correct, wrong in (
            ("cells", 8, 7), ("native_runs", 16, 15), ("llvm_runs", 8, 7),
            ("cg_runs", 8, 7), ("mir_routes", 16, 15), ("box_drop_frees", 24, 23),
            ("reads", 16, 15), ("retargets", 8, 7),
        ):
            mutations[f"wrong native {field}"] = text.replace(
                native, native.replace(f"{field}={correct}", f"{field}={wrong}"))
        for field, correct, wrong in (("cases", 14, 13), ("accepted", 3, 2), ("refused", 11, 10)):
            mutations[f"wrong reader {field}"] = text.replace(
                reader, reader.replace(f"{field}={correct}", f"{field}={wrong}"))
        for label, changed in mutations.items():
            with self.subTest(mutation=label):
                verdict = GATE.classify_target(row, 0, changed)
                self.assertEqual(verdict["status"], "fail")
                self.assertTrue(any("marker missing" in error for error in verdict["errors"]))

    def test_slice_constant_index_credit_requires_every_cell_ledger_and_native_evidence(self):
        row = target("slice_constant_index_aarch64")
        text = success_transcript(row.name)
        self.assertEqual(GATE.classify_target(row, 0, text)["status"], "pass")
        elements, from_end, stable = row.markers
        ledgers = {
            "missing element ledger": text.replace(elements, ""),
            "missing from-end ledger": text.replace(from_end, ""),
            "missing stable/select ledger": text.replace(stable, ""),
            "an element cell refused": text.replace(elements, elements.replace(
                "matched=60 refused_by_name=4", "matched=59 refused_by_name=5")),
            "a from-end cell refused": text.replace(from_end, from_end.replace(
                "matched=12 refused_by_name=0", "matched=11 refused_by_name=1")),
            "a stable/select cell dropped": text.replace(stable, stable.replace("cells=32", "cells=31")),
            "an opt level dropped": text.replace(elements, elements.replace("opts=0,1,2,3", "opts=0,1,2")),
        }
        for label, changed in ledgers.items():
            with self.subTest(mutation=label):
                verdict = GATE.classify_target(row, 0, changed)
                self.assertEqual(verdict["status"], "fail")
                self.assertTrue(any("marker missing" in error for error in verdict["errors"]))
        for label, changed in {
            "compiled, not run": text.replace(GATE.NATIVE_RUN, GATE.COMPILED),
            "certificates on": text.replace("certs=off", "certs=on"),
            "zero tests": libtest([]),
        }.items():
            with self.subTest(mutation=label):
                self.assertEqual(GATE.classify_target(row, 0, changed)["status"], "fail")

    def test_box_entry_source_inventory_is_required_native_and_certs_off(self):
        row = target("box_pointer_entry_aarch64")
        self.assertEqual((row.minimum, row.kind, row.evidence, row.certs_off),
                         (1, GATE.NATIVE, ((GATE.NATIVE_RUN, 1),), 1))
        self.assertEqual(source_tests(row.name), ["ordinary_box_entry_and_retargeted_cell_match_llvm"])
        self.assertEqual(GATE.inventory_problems(), [])
        self.assertNotIn(row.name, GATE.NOT_COVERED)
        self.assertNotIn(row.name, GATE.OUT_OF_SCOPE)
        self.assertNotIn(row.name, GATE.NAMED_REFUSALS)
        with tempfile.TemporaryDirectory() as temporary:
            tests = Path(temporary)
            copy_test_sources(tests)
            path = tests / f"{row.name}.rs"
            original = path.read_text()
            for label, changed, expected in (
                ("vanished test", original.replace("#[test]", "", 1), "differs from its 0"),
                ("missing positive module", original.replace(GATE.POSITIVE_EVIDENCE_MODULE, ""),
                 "required fixture does not include"),
                ("missing certificates-off knob", original.replace("no-proof-certs", "bridge-notes"),
                 "never passes"),
            ):
                with self.subTest(mutation=label):
                    path.write_text(changed)
                    self.assertTrue(any(row.name in problem and expected in problem
                                        for problem in GATE.inventory_problems(tests)))
                    path.write_text(original)

    def test_corpus_compile_verdict_must_be_complete_consistent_and_above_its_floor(self):
        row = target("real_program_corpus_a64")
        test = SUCCESS["real_program_corpus_a64"][0][0]
        for name, output in (("missing summary", "[a64] p01_guest@O0: COMPILED\n"),
                             ("hard error", corpus_output(hard=1)),
                             ("wrong percentage", corpus_output(printed="99.9")),
                             ("missing rows", corpus_output(drop_rows=2)),
                             ("below floor", corpus_output(compiled=17))):
            with self.subTest(case=name):
                verdict = GATE.classify_target(row, 0, libtest([test], {test: output}))
                self.assertEqual(verdict["status"], "fail", verdict)
        with tempfile.TemporaryDirectory() as temp:
            floor = Path(temp) / "floor.txt"
            floor.write_text("a64_compile_floor_percent = 80.0\n")
            verdict = GATE.classify_target(row, 0, success_transcript(row.name), floor_path=floor)
            self.assertEqual(verdict["status"], "fail")
            floor.write_text("no floor here\n")
            self.assertEqual(GATE.classify_target(row, 0, success_transcript(row.name), floor_path=floor)["status"], "fail")
        self.assertEqual(GATE.corpus_floor(), 69.2)

    def test_only_an_allowlisted_exact_refusal_becomes_an_open_named_refusal(self):
        test = SUCCESS["coroutine_generator_aarch64"][0][0]
        row = target("coroutine_generator_aarch64")
        line = "skipping: cc not available"
        allowlist = {row.name: {"gap": "X-DARWIN-P5", "reason": "fixture decision", "markers": [re.escape(line)]}}
        verdict = GATE.classify_target(row, 0, libtest([test], {test: line}), named_refusals=allowlist)
        self.assertEqual(verdict["status"], "named-refusal")
        self.assertEqual(verdict["counts"]["executed"], 0)
        self.assertEqual(verdict["named_refusal"]["gap"], "X-DARWIN-P5")
        self.assertEqual(verdict["named_refusal"]["lines"], [line])
        for text in (libtest([test], {test: line + " (other)"}),
                     libtest([test], {test: line + "\nskipping: rust-std missing"}),
                     libtest([test], {test: line}, ignored=["ignored_test"]),
                     libtest([test], {test: line}, filtered=1)):
            with self.subTest(text=text):
                self.assertEqual(GATE.classify_target(row, 0, text, named_refusals=allowlist)["status"], "fail")
        self.assertEqual(GATE.classify_target(row, 1, libtest([test], {test: line}),
                                              named_refusals=allowlist)["status"], "fail")
        other = {"drop_heap_aarch64": allowlist[row.name]}
        self.assertEqual(GATE.classify_target(row, 0, libtest([test], {test: line}),
                                              named_refusals=other)["status"], "fail")
        self.assertEqual(GATE.NAMED_REFUSALS, {}, "adding a named refusal is an owner decision")

    def test_new_panic_rows_require_both_complete_native_markers(self):
        row = target("panic_hook_differential")
        self.assertEqual(GATE.classify_target(row, 0, success_transcript(row.name))["status"], "pass")
        for test in SUCCESS[row.name][0]:
            with self.subTest(test=test):
                text = success_transcript(row.name, **{test: evidenced(test, GATE.NATIVE_RUN, "off")})
                self.assertEqual(GATE.classify_target(row, 0, text)["status"], "fail")

    def test_incoming_bridge_rows_require_full_success_markers(self):
        for name in ("static_data_aarch64", "executable_trap_stub_routes_aarch64",
                     "cross_crate_copies_native_aarch64", "statics_linkage_native_aarch64"):
            row = target(name)
            text = success_transcript(name)
            self.assertEqual(GATE.classify_target(row, 0, text)["status"], "pass", name)
            for required in row.markers:
                with self.subTest(target=name, missing=required):
                    self.assertEqual(GATE.classify_target(row, 0, text.replace(required, ""))["status"],
                                     "fail")

    def test_unsupported_program_profile_preserves_compile_refusal_and_certificate_lanes(self):
        row = target("unsupported_program")
        self.assertEqual((row.minimum, row.evidence, row.certs_off),
                         (18, ((GATE.NATIVE_RUN, 1), (GATE.COMPILED, 9),
                               (GATE.EXPECTED_REFUSAL, 8)), 4))
        self.assertEqual(set(MIXED_EVIDENCE[row.name]), set(source_tests(row.name)))
        verdict = GATE.classify_target(row, 0, success_transcript(row.name))
        self.assertEqual(verdict["status"], "pass", verdict)
        self.assertEqual(MIXED_EVIDENCE[row.name]["zst_before_sized_field_whole_store_from_scalarized_source_compiles"],
                         (GATE.COMPILED, "off"))
        self.assertEqual(MIXED_EVIDENCE[row.name]["retained_pointer_locals_compile"],
                         (GATE.COMPILED, "off"))

    def test_dyn_heap_credit_follows_actual_native_and_refusal_partition(self):
        row = target("executable_trap_stub_routes_aarch64")
        test = "dyn_heap_glue_drop_fails_closed_aarch64"
        # Both -O0 rows must run natively (heap_image_glue); the -O2 rows may
        # refuse or match.
        for native in range(5):
            kind = GATE.NATIVE_RUN if native else GATE.EXPECTED_REFUSAL
            text = success_transcript(row.name, **{test:
                f"EXECUTABLE_TRAP_STUB_DYN rows=4 llvm_native=4 cg_native={native} cg_refused={4-native}\n"
                + evidenced(test, kind, "off")})
            verdict = GATE.classify_target(row, 0, text)
            self.assertEqual(verdict["status"], "pass" if native >= 2 else "fail", verdict)
            self.assertEqual(verdict["guarded_execution"]["cg_native"], native)
        for counts, kind in (("3 cg_refused=0", GATE.NATIVE_RUN),
                             ("0 cg_refused=4", GATE.NATIVE_RUN),
                             ("1 cg_refused=3", GATE.EXPECTED_REFUSAL)):
            text = success_transcript(row.name, **{test:
                "EXECUTABLE_TRAP_STUB_DYN rows=4 llvm_native=4 cg_native=" + counts + "\n"
                + evidenced(test, kind, "off")})
            self.assertEqual(GATE.classify_target(row, 0, text)["status"], "fail")
        text = success_transcript(row.name, **{test: evidenced(test, GATE.EXPECTED_REFUSAL, "off")})
        self.assertEqual(GATE.classify_target(row, 0, text)["status"], "fail")

    def test_trap_route_range_and_dead_iterator_rows_are_pinned(self):
        row = target("executable_trap_stub_routes_aarch64")
        self.assertEqual(GATE.classify_target(row, 0, success_transcript(row.name))["status"], "pass")
        # A reversed-inclusive cell that refuses again is a lost capability.
        test = "range_inclusive_rev_reductions_never_trap_aarch64"
        text = success_transcript(row.name, **{test:
            "EXECUTABLE_TRAP_STUB_RANGE refusals=1 llvm_native=6 cg_native=5\n"
            + evidenced(test, GATE.NATIVE_RUN, "off")})
        self.assertEqual(GATE.classify_target(row, 0, text)["status"], "fail")
        # The dead-iterator rows are the gate's live witnesses: one that builds
        # (natively or not) leaves the gate unwitnessed and needs a table edit.
        test = "dead_std_iterator_body_fails_closed_aarch64"
        for counts, kind in (("1 cg_refused=3", GATE.NATIVE_RUN),
                             ("1 cg_refused=3", GATE.EXPECTED_REFUSAL),
                             ("0 cg_refused=4", GATE.NATIVE_RUN),
                             ("4 cg_refused=0", GATE.NATIVE_RUN)):
            with self.subTest(counts=counts, kind=kind):
                text = success_transcript(row.name, **{test:
                    "EXECUTABLE_TRAP_STUB_DEAD_ITER rows=4 llvm_native=4 cg_native=" + counts + "\n"
                    + evidenced(test, kind, "off")})
                self.assertEqual(GATE.classify_target(row, 0, text)["status"], "fail")
        text = success_transcript(row.name, **{test: evidenced(test, GATE.EXPECTED_REFUSAL, "off")})
        self.assertEqual(GATE.classify_target(row, 0, text)["status"], "fail")
        # The former dead-iterator rows (Repeat/Successors) lower since
        # f09e5fa9c: every cell must build and match, so a refusal is a lost
        # capability and none of them may be credited as a refusal.
        test = "generator_source_take_reductions_never_trap_aarch64"
        for counts, kind in (("3 cg_refused=1", GATE.NATIVE_RUN),
                             ("0 cg_refused=4", GATE.EXPECTED_REFUSAL),
                             ("4 cg_refused=0", GATE.EXPECTED_REFUSAL)):
            with self.subTest(counts=counts, kind=kind):
                text = success_transcript(row.name, **{test:
                    "EXECUTABLE_TRAP_STUB_GENERATOR_TAKE rows=4 llvm_native=4 cg_native=" + counts + "\n"
                    + evidenced(test, kind, "off")})
                self.assertEqual(GATE.classify_target(row, 0, text)["status"], "fail")

    def test_current_private_api_requires_native_execution_beside_the_refusal(self):
        row = target("current_private_api")
        native = "scalar_widths_and_allocation_provenance_execute_against_c_driver"
        self.assertEqual(GATE.classify_target(row, 0, success_transcript(row.name))["status"], "pass")
        for label, output in {
            "missing-native-marker": "",
            "refusal-instead-of-native": evidenced(native, GATE.EXPECTED_REFUSAL, "off"),
            "wrong-certificate-scope": evidenced(native, GATE.NATIVE_RUN, "on"),
        }.items():
            with self.subTest(label=label):
                transcript = success_transcript(row.name, **{native: output})
                self.assertEqual(GATE.classify_target(row, 0, transcript)["status"], "fail")

    def test_abort_immediate_requires_all_executions_and_distinct_signals(self):
        row = target("abort_immediate_aarch64")
        text = success_transcript(row.name)
        self.assertEqual(GATE.classify_target(row, 0, text)["status"], "pass")
        mutations = {
            "missing ledger": text.replace(row.markers[0], "abort checked"),
            "missing execution": text.replace("executions=48", "executions=47"),
            "trap became libc abort": text.replace("trap=5", "trap=6"),
            "libc abort became trap": text.replace("libc_abort=6", "libc_abort=5"),
            "incomplete opts": text.replace("opts=0,1,2,3", "opts=0,3"),
            "missing unwind": text.replace("panic=abort,unwind", "panic=abort"),
            "not executed": text.replace(GATE.NATIVE_RUN, GATE.COMPILED),
            "wrong certificate mode": text.replace("certs=off", "certs=on"),
        }
        for label, mutated in mutations.items():
            with self.subTest(label=label):
                self.assertEqual(GATE.classify_target(row, 0, mutated)["status"], "fail")

    def test_atomic_access_requires_complete_execution_and_refusal_ledgers(self):
        row = target("atomic_load_store_aarch64")
        text = success_transcript(row.name)
        self.assertEqual(GATE.classify_target(row, 0, text)["status"], "pass")
        mutations = {"not executed": text.replace(GATE.NATIVE_RUN, GATE.COMPILED),
                     "refusal not established": text.replace(GATE.EXPECTED_REFUSAL, GATE.COMPILED),
                     "wrong cert mode": text.replace("certs=off", "certs=on"),
                     "missing opt": text.replace("opts=0,1,2,3", "opts=0,3"),
                     "missing unwind": text.replace("panic=abort,unwind", "panic=abort")}
        for index, marker in enumerate(row.markers):
            mutations[f"missing ledger {index}"] = text.replace(marker, "atomic checked")
        for old, new in [("executions=320", "executions=319"), ("cells=160", "cells=159"),
                         ("refused=16", "refused=15"), ("refused=72", "refused=71"),
                         ("llvm_type_refusals=40", "llvm_type_refusals=39"),
                         ("layout_abi_refusals=16", "layout_abi_refusals=15"),
                         ("llvm_abi_runs=16", "llvm_abi_runs=15")]:
            mutations[old] = text.replace(old, new)
        for label, mutated in mutations.items():
            with self.subTest(label=label):
                self.assertEqual(GATE.classify_target(row, 0, mutated)["status"], "fail")

    # Inventory ----------------------------------------------------------------------

    def test_required_inventory_matches_the_fixture_sources(self):
        self.assertEqual(GATE.inventory_problems(), [])
        self.assertEqual([row.name for row in GATE.TARGETS], [
            "coroutine_generator_aarch64", "drop_heap_aarch64", "hello_loop", "static_data_aarch64",
            "tls_thread_local_aarch64", "unwind_cleanup_aarch64", "m142_bridge_bookkeeping_aarch64",
            "signature_placement_families_xback", "rust_call_boundary_aarch64",
            "m140_x86_scalar_pair_return_xback",
            "m141_x86_scalar_pair_arg_xback", "m144_x86_pair_arg_exhaustion_xback",
            "m145_x86_indirect_arg_xback", "m146_x86_bool_load_xback",
            "opt_loop_state_run", "x86_split_copy_replay_run", "debuginfo_dwarf_aarch64",
            "linkage_macho_aarch64",
            "mir_families_aarch64",
            "panic_hook_differential", "assert_panic_differential_aarch64",
            "panic_assert_kinds_differential", "std_panic_payload_differential",
            "terminate_panic_differential_aarch64",
            "unsized_arguments_aarch64",
            "atomic_load_store_aarch64",
            "abort_immediate_aarch64",
            "intrinsic_validity_aarch64",
            "deref_field_wide_image_store_aarch64",
            "box_pointer_entry_aarch64",
            "executable_trap_stub_routes_aarch64",
            "dyn_heap_glue_differential_aarch64", "multi_cgu_link_aarch64",
            "cross_crate_copies_native_aarch64", "statics_linkage_native_aarch64",
            "assert_constant_condition_aarch64", "vec_from_elem_capacity_aarch64",
            "runtime_parity_rewrites_aarch64",
            "slice_constant_index_aarch64",
            "stride_iter_family_differential_aarch64",
            "slice_sort_order_aarch64",
            "slice_sort_cached_key_effects_aarch64", "aarch64_closure_body_pair_xback",
            "subslice_loop_compile_bound_aarch64",
            "format_length_black_box_aarch64",
            "core_values_user_trait_differential_aarch64",
            "map_model_user_trait_differential_aarch64",
            "vec_compact_user_trait_differential_aarch64",
            "clone_sort_user_trait_differential_aarch64",
            "switch_case_signed_aarch64",
            "format_capacity_aarch64",
            "vec_extend_capacity_aarch64",
            "switch_join_constant_aarch64",
            "iter_chain_unwind_item_differential_aarch64",
            "float_semantics", "overflow_asserts", "reference_union_semantics", "unsupported_program",
            "bridge_differential_aarch64", "bridge_feature_suites_aarch64", "bridge_regressions_aarch64",
            "fixed_cost_budget_aarch64", "real_program_corpus_a64", "current_private_api"])
        self.assertEqual(sum(row.minimum for row in GATE.TARGETS), 214)
        # Every Darwin bridge target is required (L06-P10); none is reported only.
        self.assertEqual(GATE.NOT_COVERED, {})
        self.assertEqual(sum(row.certs_off for row in GATE.TARGETS), 141)
        self.assertEqual({row.name for row in GATE.TARGETS if row.kind == GATE.HOST_ORACLE},
                         {"m140_x86_scalar_pair_return_xback", "m141_x86_scalar_pair_arg_xback",
                          "m144_x86_pair_arg_exhaustion_xback", "m145_x86_indirect_arg_xback",
                          "m146_x86_bool_load_xback", "float_semantics", "overflow_asserts",
                          "reference_union_semantics", "unsupported_program",
                          "panic_hook_differential", "panic_assert_kinds_differential",
                          "std_panic_payload_differential",
                          "executable_trap_stub_routes_aarch64", "dyn_heap_glue_differential_aarch64",
                          "multi_cgu_link_aarch64", "bridge_differential_aarch64",
                          "bridge_feature_suites_aarch64", "bridge_regressions_aarch64",
                          "core_values_user_trait_differential_aarch64",
                          "clone_sort_user_trait_differential_aarch64"})
        self.assertEqual([row.name for row in GATE.TARGETS if row.kind == GATE.COMPILE_VERDICT],
                         ["real_program_corpus_a64"])
        # A bound on counted start-up work links and runs nothing, so it is
        # never counted as native execution.
        self.assertEqual([row.name for row in GATE.TARGETS if row.kind == GATE.FIXED_COST],
                         ["fixed_cost_budget_aarch64"])
        for row in GATE.TARGETS:
            source = (GATE.TESTS_DIR / f"{row.name}.rs").read_text()
            with self.subTest(target=row.name):
                self.assertEqual(len(re.findall(r"#\[test\]", source)), row.minimum)
                self.assertEqual(len(source_tests(row.name)), row.minimum)
                self.assertEqual(GATE.evidence_profile_problems(row), [])
                self.assertIn(GATE.POSITIVE_EVIDENCE_MODULE, source)
                # No guard return is left on this host: a Darwin-only fixture
                # is compiled only on its host, and a missing prerequisite there
                # fails. A host-target oracle may keep the shared knob skip for
                # OTHER hosts only, in a branch this host does not compile.
                not_this_host = '#[cfg(not(all(target_os = "macos", target_arch = "aarch64")))]'
                for match in re.finditer(r"skip_without_backend_knobs\(", source):
                    preceding = source[:match.start()].splitlines()[-3:]
                    self.assertEqual(row.kind, GATE.HOST_ORACLE)
                    self.assertTrue(any(line.strip() == not_this_host for line in preceding),
                                    (row.name, preceding))
                self.assertNotIn("host_is_aarch64_macos", source)
                self.assertNotIn("aarch64_macho_promotion_ratchet", source)
                self.assertIsNone(re.search(r"[Cc]ompiled with `TCG_NO_PROOF_CERTS=1`", source))
                if row.kind != GATE.HOST_ORACLE:
                    host_cfg = ('#![cfg(all(target_os = "macos", target_arch = "aarch64", rustc_session_split))]'
                                if row.name == "current_private_api" else
                                '#![cfg(all(target_os = "macos", target_arch = "aarch64"))]')
                    self.assertIn(host_cfg, source)
                # The runner binds the snapshot by running a copy of each test
                # executable beside it; that holds only while every fixture
                # loads the library beside its own executable.
                self.assertIn("backend_artifact_support::current_test_backend()", source)
                self.assertNotIn("CARGO_TARGET_DIR", source)
                self.assertNotIn("TCG_TEST_BACKEND", source)
        selector = (GATE.TESTS_DIR / "support/backend_artifact.rs").read_text()
        self.assertIn("std::env::current_exe()", selector)
        self.assertIn('name == "deps"', selector)
        hello = (GATE.TESTS_DIR / "hello_loop.rs").read_text()
        self.assertIn('stderr.contains("rustc_codegen_trust_cg: #574 entry wrapper uses lang_start")', hello)
        unwind = (GATE.TESTS_DIR / "unwind_cleanup_aarch64.rs").read_text()
        self.assertIn("bridge unwind-cleanup EH lowering VERIFIED (object level)", unwind)
        self.assertIn("REAL Rust panic CAUGHT through the bridge: {}", unwind)
        self.assertIn('stdout.contains("AY_CAUGHT=1 CLEANUP_RAN=1")', unwind)
        corpus = (GATE.TESTS_DIR / "real_program_corpus_a64.rs").read_text()
        self.assertIn("[a64 corpus row] {compiled}/{total_rows} rows COMPILED ({coverage:.1}%)", corpus)
        self.assertIn('eprintln!("  [a64] {row}: COMPILED")', corpus)
        self.assertIn('"--emit=obj"', corpus)
        # No refusal suspends the corpus floor any more.
        self.assertNotIn("coverage floor SKIPPED", corpus)
        support = (GATE.TESTS_DIR / "support" / "positive_evidence.rs").read_text()
        self.assertIn(f'pub const MARKER: &str = "{GATE.POSITIVE_MARKER}";', support)
        self.assertIn('"{MARKER} kind={} certs={} test={test}"', support)
        for kind in GATE.EVIDENCE_KINDS:
            self.assertIn(f'=> "{kind}"', support)
        for certs in GATE.CERTS:
            self.assertIn(f'=> "{certs}"', support)
        prerequisites = (GATE.TESTS_DIR / "support" / "darwin_native_prerequisites.rs").read_text()
        self.assertIn("DARWIN_BRIDGE_PREREQUISITE_MISSING", prerequisites)
        self.assertNotIn("return;", prerequisites)
        self.assertNotIn("return false", prerequisites)
        # macOS ships no GNU `timeout` and HOST_TOOLS requires none, so a
        # required fixture or support module that spawns one is unbounded on
        # this host; native runs are bounded in process by run_with_deadline.
        gnu_timeout = re.compile(r'Command::new\(\s*"g?timeout"\s*\)')
        # The Linux-only runtime twin requires GNU timeout on Linux. Verify
        # its callers stay Linux-only before excluding that unreachable helper
        # from the Darwin tool census.
        linux_helper = GATE.TESTS_DIR / "support/linux_runtime_twin.rs"
        callers = [path for path in GATE.TESTS_DIR.glob("*.rs")
                   if 'support/linux_runtime_twin.rs' in path.read_text()]
        self.assertEqual({path.stem for path in callers},
                         {"static_data_linux", "drop_heap_linux", "coroutine_generator_linux"})
        for path in callers:
            self.assertIn('#![cfg(all(target_arch = "aarch64", target_os = "linux", target_env = "gnu"))]',
                          path.read_text())
        for path in [*(GATE.TESTS_DIR / f"{row.name}.rs" for row in GATE.TARGETS),
                     *sorted((GATE.TESTS_DIR / "support").rglob("*.rs"))]:
            if path != linux_helper:
                self.assertIsNone(gnu_timeout.search(path.read_text()), path)

    def test_evidence_profile_problems_are_inventory_problems(self):
        row = target("unwind_cleanup_aarch64")
        for change, text in (({"evidence": ()}, "nonempty"),
                             ({"evidence": ((GATE.NATIVE_RUN, 3),)}, "sum to the minimum"),
                             ({"evidence": ((GATE.NATIVE_RUN, 1), (GATE.NATIVE_RUN, 1))}, "kind twice"),
                             ({"evidence": ((GATE.NATIVE_RUN, 1), (GATE.VERDICT, 1))}, "not credited"),
                             ({"evidence": ((GATE.NATIVE_RUN, 2), (GATE.COMPILED, 0))}, "positive integer"),
                             ({"certs_off": 3}, "certs_off"), ({"certs_off": -1}, "certs_off")):
            with self.subTest(change=change):
                problems = GATE.evidence_profile_problems(row._replace(**change))
                self.assertTrue(any(text in problem for problem in problems), problems)
        with tempfile.TemporaryDirectory() as temp:
            tests = Path(temp)
            copy_test_sources(tests)
            source = tests / "overflow_asserts.rs"
            source.write_text(source.read_text().replace(GATE.POSITIVE_EVIDENCE_MODULE, "", 1))
            self.assertTrue(any("overflow_asserts: required fixture does not include" in problem
                                for problem in GATE.inventory_problems(tests)))

    def test_unclassified_darwin_fixtures_and_malformed_rows_are_inventory_problems(self):
        with tempfile.TemporaryDirectory() as temp:
            tests = Path(temp)
            copy_test_sources(tests)
            self.assertEqual(GATE.inventory_problems(tests), [])
            (tests / "new_fixture_aarch64.rs").write_text('const TARGET: &str = "aarch64-apple-darwin";\n')
            (tests / "gated_oracle.rs").write_text('fn f() -> bool { cfg!(all(target_os = "macos", target_arch = "aarch64")) }\n')
            problems = GATE.inventory_problems(tests)
            self.assertTrue(any("new_fixture_aarch64" in problem for problem in problems))
            self.assertTrue(any("gated_oracle" in problem for problem in problems))
            (tests / "new_fixture_aarch64.rs").unlink()
            (tests / "gated_oracle.rs").unlink()
            source = tests / "tls_thread_local_aarch64.rs"
            source.write_text(source.read_text().replace("#[test]", "#[test]\n#[ignore]", 1))
            self.assertTrue(any("#[ignore]" in problem for problem in GATE.inventory_problems(tests)))
            source.write_text(source.read_text().replace("#[test]\n#[ignore]", "", 1))
            self.assertTrue(any("differs from its 0" in problem for problem in GATE.inventory_problems(tests)))
            source.write_text(source.read_text() + "\n#[test]\nfn added_a() {}\n#[test]\nfn added_b() {}\n")
            self.assertTrue(any("differs from its 2" in problem for problem in GATE.inventory_problems(tests)))
            (tests / "hello_loop.rs").unlink()
            self.assertTrue(any("hello_loop: missing" in problem for problem in GATE.inventory_problems(tests)))
        for allowlist, text in (({"not_required": {"gap": "X", "reason": "r", "markers": ["x"]}}, "not a required"),
                                ({"hello_loop": {"gap": "", "reason": "r", "markers": ["x"]}}, "ledger gap"),
                                ({"hello_loop": {"gap": "X", "reason": "r", "markers": []}}, "ledger gap"),
                                ({"hello_loop": {"gap": "X", "reason": "r", "markers": ["("]}}, "regular expression")):
            with self.subTest(allowlist=allowlist):
                problems = GATE.inventory_problems(named_refusals=allowlist)
                self.assertTrue(any(text in problem for problem in problems), problems)

    def test_list_prints_the_inventory_without_probing_or_writing(self):
        with mock.patch.object(GATE, "preflight", side_effect=AssertionError("probed")), \
                mock.patch.object(GATE.tempfile, "mkdtemp", side_effect=AssertionError("wrote")), \
                mock.patch("sys.stdout") as stdout:
            self.assertEqual(GATE.main(["--list"]), 0)
        printed = "".join(call.args[0] for call in stdout.write.call_args_list)
        for row in GATE.TARGETS:
            profile = " ".join(f"{kind}={count}" for kind, count in row.evidence)
            self.assertIn(f"{row.name} {row.minimum} {row.kind} [{profile} certs-off={row.certs_off}]\n",
                          printed)
        for name in (*GATE.NOT_COVERED, *GATE.OUT_OF_SCOPE):
            self.assertIn(name, printed)

    # Complete runs through fake targo builds and libtest executables ----------------

    def fixture_run(self, mode="pass", *, fingerprints=None, timeout=20, args=(), named=None, dirty=False):
        with tempfile.TemporaryDirectory() as temp:
            directory = Path(temp).resolve()
            target_dir = directory / "cache"
            backend = target_dir / "release" / GATE.BACKEND_NAME
            backend.parent.mkdir(parents=True)
            backend.write_bytes(b"old preexisting backend")
            calls = directory / "calls"
            output = directory / "report"
            runtime_backend = output / "runtime-target" / "release" / "deps" / GATE.BACKEND_NAME
            source = directory / "src dir" / "extra source.rs"
            source.parent.mkdir()
            source.write_text("// fixture source\n")
            old = time.time() - 3600
            os.utime(source, (old, old))
            transcripts = {row.name: success_transcript(row.name) for row in GATE.TARGETS}
            coroutine = SUCCESS["coroutine_generator_aarch64"][0][0]
            if mode in ("skip_target", "named_refusal"):
                transcripts["coroutine_generator_aarch64"] = libtest(
                    [coroutine], {coroutine: "skipping: cc not available"})
            native = (
                f"#!{sys.executable}\n"
                "import os, sys\nfrom pathlib import Path\n"
                f"mode = {mode!r}\n"
                "name = Path(sys.argv[0]).name.rsplit('-', 1)[0]\n"
                f"with open({str(calls)!r}, 'a') as out: out.write('run:' + name + '\\n')\n"
                "assert sys.argv[1:] == ['--show-output', '--test-threads=1'], sys.argv\n"
                f"assert os.environ['CARGO_TARGET_DIR'] == {str(output / 'runtime-target')!r}\n"
                f"assert os.environ['CARGO_MANIFEST_DIR'] == {str(GATE.BRIDGE_DIR)!r}\n"
                "assert 'RUSTC' not in os.environ and 'RUST_TEST_NOCAPTURE' not in os.environ\n"
                f"snapshot = Path({str(runtime_backend)!r})\n"
                "assert snapshot.read_bytes() == b'built backend'\n"
                "assert snapshot.stat().st_mode & 0o777 == 0o444\n"
                # A fixture loads the library beside its own executable
                # (tests/support/backend_artifact.rs): it must run from the
                # snapshot's directory as an independent read-only copy.
                "me = Path(sys.argv[0])\n"
                "assert me.is_absolute() and me.parent == snapshot.parent, me\n"
                "assert me.stat().st_mode & 0o777 == 0o555 and me.stat().st_nlink == 1\n"
                "if mode == 'fallback_build' and name == 'drop_heap_aarch64':\n"
                "    fallback = snapshot.parent.parent.parent / 'debug' / snapshot.name\n"
                "    fallback.parent.mkdir()\n"
                "    fallback.write_bytes(b'fallback backend')\n"
                "if mode == 'tamper_executable' and name == 'hello_loop':\n"
                "    sibling = me.parent / 'static_data_aarch64-0123456789abcdef'\n"
                "    sibling.chmod(0o755)\n"
                "    sibling.write_text(sibling.read_text() + '# tampered\\n')\n"
                "    sibling.chmod(0o555)\n"
                "if mode == 'tamper_snapshot' and name == 'hello_loop':\n"
                "    snapshot.chmod(0o600)\n"
                "    snapshot.write_bytes(b'tampered during test')\n"
                "    snapshot.chmod(0o444)\n"
                f"transcripts = {transcripts!r}\n"
                "sys.stdout.write(transcripts[name])\n"
            )
            dep_rule = f"{str(backend).replace(' ', chr(92) + ' ')}: " + " ".join(
                str(path).replace(" ", "\\ ") for path in (GATE.BRIDGE_DIR / "src" / "lib.rs", source))
            targo = executable(directory / "targo-fixture", (
                f"#!{sys.executable}\n"
                "import json, os, sys, time\nfrom pathlib import Path\n"
                f"mode = {mode!r}\n"
                f"backend = Path({str(backend)!r})\n"
                f"target_dir = Path({str(target_dir)!r})\n"
                f"assert sys.argv[1] == '--unverified', sys.argv\n"
                "action = sys.argv[2]\n"
                f"with open({str(calls)!r}, 'a') as out: out.write({{'build': 'build', 'test': 'test-build'}}[action] + '\\n')\n"
                f"assert os.environ['RUSTC'] == {str(directory / 'trustc-fixture')!r}\n"
                "assert Path(os.environ['CARGO_TARGET_DIR']) == target_dir\n"
                "assert not any(key.startswith(('TCG_', 'TRUST_CG_', 'SIGFAM_')) for key in os.environ)\n"
                "for flag in ('--release', '--locked', '--message-format=json-render-diagnostics'):\n"
                "    assert flag in sys.argv, flag\n"
                "assert Path(sys.argv[sys.argv.index('--target-dir') + 1]) == target_dir\n"
                f"assert sys.argv[sys.argv.index('--manifest-path') + 1] == {str(GATE.MANIFEST)!r}\n"
                "if action == 'build':\n"
                "    if mode == 'timeout': time.sleep(60)\n"
                "    if mode == 'buildfail': raise SystemExit(9)\n"
                "    backend.write_bytes(b'built backend')\n"
                f"    rule = {dep_rule!r}\n"
                f"    if mode == 'stale': rule += ' ' + {str(directory / 'future.rs')!r}\n"
                "    backend.with_name('librustc_codegen_trust_cg.d').write_text(rule + '\\n')\n"
                "    if mode != 'missing_artifact':\n"
                "        print(json.dumps({'reason': 'compiler-artifact',\n"
                f"            'manifest_path': {str(GATE.MANIFEST)!r},\n"
                "            'target': {'name': 'rustc_codegen_trust_cg', 'kind': ['dylib']},\n"
                "            'filenames': [str(backend)], 'fresh': False}))\n"
                "    print(json.dumps({'reason': 'build-finished', 'success': True}))\n"
                "elif action == 'test':\n"
                "    assert '--no-run' in sys.argv\n"
                "    if mode == 'testbuildfail': raise SystemExit(8)\n"
                "    names = [sys.argv[index + 1] for index, value in enumerate(sys.argv) if value == '--test']\n"
                f"    assert names == {[row.name for row in GATE.TARGETS]!r}, names\n"
                "    for name in names:\n"
                "        if mode == 'missing_test_artifact' and name == 'hello_loop': continue\n"
                "        native = target_dir / 'release' / 'deps' / (name + '-0123456789abcdef')\n"
                "        native.parent.mkdir(parents=True, exist_ok=True)\n"
                f"        native.write_text({native!r})\n"
                "        native.chmod(0o755)\n"
                "        print(json.dumps({'reason': 'compiler-artifact',\n"
                f"            'manifest_path': {str(GATE.MANIFEST)!r},\n"
                f"            'package_id': {'path+' + GATE.BRIDGE_DIR.as_uri() + '#' + GATE.PACKAGE_TARGET + '@0.1.0'!r},\n"
                f"            'target': {{'name': name, 'kind': ['test'], 'src_path': str(Path({str(GATE.TESTS_DIR)!r}) / (name + '.rs'))}},\n"
                "            'profile': {'test': True, 'opt_level': '3', 'debuginfo': 0, 'debug_assertions': False, 'overflow_checks': False},\n"
                "            'filenames': [str(native)], 'executable': str(native), 'fresh': False}))\n"
                "    if mode == 'rebuilt_cache': backend.write_bytes(b'cache rebuilt by the test graph')\n"
                "    print(json.dumps({'reason': 'build-finished', 'success': True}))\n"
                "else: raise AssertionError(action)\n"
            ))
            if mode == "stale":
                future_source = directory / "future.rs"
                future_source.write_text("// edited after the build\n")
                future = time.time() + 3600
                os.utime(future_source, (future, future))
            provenance = {
                "source_fingerprint": "same", "dirty": dirty,
                "toolchain": {"compiler": str(directory / "trustc-fixture"), "targo": str(targo)},
                "tools": {"git": {"path": "fixture-git"}},
            }
            snapshots = [{"source_fingerprint": value} for value in (fingerprints or ["same"] * 3)]
            environment = {key: value for key, value in os.environ.items()
                           if not key.startswith(("TCG_", "TRUST_CG_", "SIGFAM_"))}
            environment["RUST_TEST_NOCAPTURE"] = "1"
            with mock.patch.dict(os.environ, environment, clear=True), \
                    mock.patch.object(GATE, "preflight", return_value=provenance), \
                    mock.patch.object(GATE, "current_source", side_effect=snapshots), \
                    mock.patch.object(GATE, "NAMED_REFUSALS", named or {}):
                code = quiet_main(["--out", str(output), "--target-dir", str(target_dir),
                                  "--timeout-seconds", str(timeout), *args])
            report = json.loads((output / "report.json").read_text())
            logs = sorted(path.name for path in output.glob("*.log"))
            observed = calls.read_text().splitlines() if calls.exists() else []
            runtime = GATE.runtime_entries(output / "runtime-target") if (output / "runtime-target").exists() else None
            return code, report, observed, logs, runtime

    def expected_calls(self):
        return ["build", "test-build", *(f"run:{row.name}" for row in GATE.TARGETS)]

    def test_complete_run_builds_once_binds_the_snapshot_and_runs_every_target(self):
        code, report, calls, logs, runtime = self.fixture_run()
        self.assertEqual(code, 0, report)
        self.assertEqual(report["status"], "pass")
        self.assertEqual(calls, self.expected_calls())
        self.assertEqual(report["schema"], GATE.SCHEMA)
        # This family-level counter counts both current-API tests; the
        # per-test totals below distinguish the refusal from native execution.
        self.assertEqual(report["native_executed_passes"], 97)
        self.assertEqual(report["compile_verdict_passes"], 1)
        totals = report["positive_evidence_totals"]
        self.assertEqual((totals["required_tests"], totals["credited_tests"]), (214, 214))
        self.assertEqual(totals["by_kind"], {
            GATE.COMPILED: 17, GATE.VERDICT: 1, GATE.EXPECTED_REFUSAL: 28, GATE.FIXED_COST_EVIDENCE: 1,
            GATE.NATIVE_RUN: 166, GATE.UNIT_CHECK: 1})
        self.assertEqual(totals["by_certs"]["off"], 141)
        self.assertEqual(len(totals["certs_off_tests"]), 141)
        self.assertEqual((totals["failed_tests"], totals["unevidenced_passes"]), ({}, {}))
        self.assertEqual(set(totals["target_status"].values()), {"pass"})
        self.assertIn(GATE.POSITIVE_MARKER, report["positive_evidence_marker"])
        self.assertEqual(report["named_refusals"], [])
        self.assertEqual(report["backend_after_build"]["sha256"], SHA)
        self.assertEqual(report["backend_snapshot"]["sha256"], SHA)
        self.assertEqual(report["backend_snapshot"]["stat"]["mode"], stat.S_IFREG | 0o444)
        self.assertNotEqual(report["backend_before_build"]["sha256"], SHA)
        self.assertFalse(report["staleness"]["stale"])
        self.assertEqual(report["staleness"]["sources"], 2)
        self.assertEqual(runtime, sorted([
            "release", "release/deps", f"release/deps/{GATE.BACKEND_NAME}",
            *(f"release/deps/{row.name}-0123456789abcdef" for row in GATE.TARGETS)]))
        for row in GATE.TARGETS:
            copy = report["runtime_executables"][row.name]
            self.assertEqual(Path(copy["path"]).parent, Path(report["backend_snapshot"]["path"]).parent)
            self.assertEqual(copy["stat"]["mode"], stat.S_IFREG | 0o555)
            self.assertEqual(copy["sha256"], report["test_build"]["executables"][row.name]["sha256"])
        self.assertEqual(logs, sorted(["build.log", "test-build.log", *(f"{row.name}.log" for row in GATE.TARGETS)]))
        self.assertEqual([row["target"] for row in report["targets"]], [row.name for row in GATE.TARGETS])
        corpus = next(row for row in report["targets"] if row["target"] == "real_program_corpus_a64")
        self.assertEqual(corpus["kind"], GATE.COMPILE_VERDICT)
        self.assertEqual(corpus["compile_verdict"]["label"], GATE.COMPILE_VERDICT_LABEL)
        for row in report["targets"]:
            self.assertEqual(len(row["log_sha256"]), 64)
            self.assertIn("RUST_TEST_NOCAPTURE", row["unset_environment"])
        self.assertIn("no Darwin C FnAbi aggregate regression exists (twin of aarch64_c_fnabi_aggregate_linux)",
                      report["not_established"])
        self.assertTrue(any("source-text scan" in entry and "KNOB_OPTION_OWNERS" in entry
                            for entry in report["not_established"]))
        # Fixtures that turn proof certificates off are named as testing-only evidence.
        disabled = report["proof_certificates_disabled"]
        self.assertEqual(disabled, GATE.proof_certificate_opt_outs())
        self.assertTrue(any(name in entry for name in disabled for entry in report["not_established"]))

    def test_proof_certificate_opt_outs_are_read_from_the_fixture_sources(self):
        self.assertEqual(GATE.proof_certificate_opt_outs(), [
            "coroutine_generator_aarch64", "drop_heap_aarch64", "static_data_aarch64",
            "tls_thread_local_aarch64", "unwind_cleanup_aarch64", "m142_bridge_bookkeeping_aarch64",
            "signature_placement_families_xback", "rust_call_boundary_aarch64",
            "m140_x86_scalar_pair_return_xback",
            "m141_x86_scalar_pair_arg_xback", "m144_x86_pair_arg_exhaustion_xback",
            "m145_x86_indirect_arg_xback", "m146_x86_bool_load_xback",
            "opt_loop_state_run", "x86_split_copy_replay_run", "debuginfo_dwarf_aarch64",
            "linkage_macho_aarch64",
            "mir_families_aarch64",
            "panic_hook_differential", "assert_panic_differential_aarch64",
            "panic_assert_kinds_differential", "std_panic_payload_differential",
            "terminate_panic_differential_aarch64",
            "unsized_arguments_aarch64",
            "atomic_load_store_aarch64",
            "abort_immediate_aarch64",
            "intrinsic_validity_aarch64",
            "deref_field_wide_image_store_aarch64",
            "box_pointer_entry_aarch64",
            "executable_trap_stub_routes_aarch64",
            "dyn_heap_glue_differential_aarch64", "multi_cgu_link_aarch64",
            "cross_crate_copies_native_aarch64", "statics_linkage_native_aarch64",
            "assert_constant_condition_aarch64", "vec_from_elem_capacity_aarch64",
            "runtime_parity_rewrites_aarch64",
            "slice_constant_index_aarch64",
            "stride_iter_family_differential_aarch64",
            "slice_sort_order_aarch64",
            "slice_sort_cached_key_effects_aarch64", "aarch64_closure_body_pair_xback",
            "subslice_loop_compile_bound_aarch64",
            "format_length_black_box_aarch64",
            "core_values_user_trait_differential_aarch64",
            "map_model_user_trait_differential_aarch64",
            "vec_compact_user_trait_differential_aarch64",
            "clone_sort_user_trait_differential_aarch64",
            "switch_case_signed_aarch64",
            "format_capacity_aarch64",
            "vec_extend_capacity_aarch64",
            "switch_join_constant_aarch64",
            "iter_chain_unwind_item_differential_aarch64",
            "unsupported_program",
            "bridge_differential_aarch64", "bridge_feature_suites_aarch64", "bridge_regressions_aarch64",
            "current_private_api",
        ])
        # Exactly the targets whose evidence profile admits proofs-off tests.
        self.assertEqual(GATE.proof_certificate_opt_outs(),
                         [row.name for row in GATE.TARGETS if row.certs_off])
        with tempfile.TemporaryDirectory() as temp:
            directory = Path(temp)
            (directory / "hello_loop.rs").write_text('backend_knobs_arg(&["no-proof-certs"])\n')
            (directory / "drop_heap_aarch64.rs").write_text('backend_knobs_arg(&["bridge-notes"])\n')
            self.assertEqual(GATE.proof_certificate_opt_outs(directory), ["hello_loop"])

    def test_cache_rebuild_by_the_test_graph_cannot_change_the_tested_backend(self):
        code, report, calls, _, _ = self.fixture_run("rebuilt_cache")
        self.assertEqual(code, 0, report)
        self.assertEqual(calls, self.expected_calls())
        self.assertNotEqual(report["cache_backend_after_tests"]["sha256"], SHA)
        self.assertEqual(report["backend_snapshot"]["sha256"], SHA)

    def test_failed_or_unidentified_build_never_reuses_a_preexisting_backend(self):
        for mode in ("buildfail", "missing_artifact"):
            with self.subTest(mode=mode):
                code, report, calls, _, runtime = self.fixture_run(mode)
                self.assertEqual(code, 1, report)
                self.assertEqual(calls, ["build"])
                self.assertEqual(report["finding_codes"], [GATE.BUILD_FAILED])
                self.assertIsNotNone(report["backend_before_build"])
                self.assertNotIn("backend_snapshot", report)
                self.assertIsNone(runtime)

    def test_stale_backend_is_refused_before_any_test_build_or_execution(self):
        code, report, calls, _, runtime = self.fixture_run("stale")
        self.assertEqual(code, 1, report)
        self.assertEqual(calls, ["build"])
        self.assertEqual(report["finding_codes"], [GATE.STALE_BACKEND])
        self.assertTrue(report["staleness"]["stale"])
        self.assertEqual(report["staleness"]["newer_source_count"], 1)
        self.assertIsNone(runtime)

    def test_failed_or_ambiguous_test_build_executes_nothing(self):
        for mode in ("testbuildfail", "missing_test_artifact"):
            with self.subTest(mode=mode):
                code, report, calls, _, _ = self.fixture_run(mode)
                self.assertEqual(code, 1, report)
                self.assertEqual(calls, ["build", "test-build"])
                self.assertEqual(report["finding_codes"], [GATE.TEST_BUILD_FAILED])
                self.assertEqual(report["targets"], [])

    def test_a_skipping_target_fails_the_run_while_every_target_still_executes(self):
        code, report, calls, _, _ = self.fixture_run("skip_target")
        self.assertEqual(code, 1, report)
        self.assertEqual(calls, self.expected_calls())
        self.assertEqual(report["status"], "fail")
        statuses = {row["target"]: row["status"] for row in report["targets"]}
        self.assertEqual(statuses["coroutine_generator_aarch64"], "fail")
        self.assertEqual(sum(status == "pass" for status in statuses.values()), 63)
        self.assertEqual(report["native_executed_passes"], 96)
        self.assertEqual(report["positive_evidence_totals"]["credited_tests"], 213)
        self.assertEqual(report["positive_evidence_totals"]["unevidenced_passes"],
                         {"coroutine_generator_aarch64": [SUCCESS["coroutine_generator_aarch64"][0][0]]})

    def test_an_allowlisted_named_refusal_is_open_not_a_pass(self):
        named = {"coroutine_generator_aarch64": {
            "gap": "X-DARWIN-P5", "reason": "fixture decision", "markers": [re.escape("skipping: cc not available")]}}
        code, report, calls, _, _ = self.fixture_run("named_refusal", named=named)
        self.assertEqual(code, GATE.EXIT_NAMED_REFUSAL, report)
        self.assertEqual(report["status"], "named-refusal")
        self.assertEqual(report["named_refusals"], ["coroutine_generator_aarch64"])
        self.assertEqual(report["native_executed_passes"], 96)
        totals = report["positive_evidence_totals"]
        self.assertEqual(totals["credited_tests"], 213)
        # A named refusal credits nothing, in the totals by kind and certificates too.
        self.assertEqual(sum(totals["by_kind"].values()), 213)
        self.assertEqual(totals["by_certs"]["off"], 140)
        self.assertNotIn("coroutine_generator_aarch64", " ".join(totals["certs_off_tests"]))
        self.assertEqual(calls, self.expected_calls())

    def test_fixture_fallback_build_or_snapshot_tampering_is_rejected(self):
        for mode, code_name, last in (("fallback_build", GATE.FALLBACK_BUILD, "run:drop_heap_aarch64"),
                                      ("tamper_snapshot", GATE.BACKEND_CHANGED, "run:hello_loop"),
                                      ("tamper_executable", GATE.BACKEND_CHANGED, "run:hello_loop")):
            with self.subTest(mode=mode):
                code, report, calls, _, _ = self.fixture_run(mode)
                self.assertEqual(code, 1, report)
                self.assertEqual(report["finding_codes"], [code_name])
                self.assertEqual(calls[-1], last)

    def test_source_change_during_qualification_is_refused(self):
        for fingerprints, expected in ((["changed"], ["build"]),
                                       (["same", "changed"], ["build", "test-build"]),
                                       (["same", "same", "changed"], self.expected_calls())):
            with self.subTest(fingerprints=fingerprints):
                code, report, calls, _, _ = self.fixture_run(fingerprints=fingerprints)
                self.assertEqual(code, 1, report)
                self.assertEqual(calls, expected)
                self.assertEqual(report["finding_codes"], [GATE.SOURCE_CHANGED])

    def test_require_clean_refuses_a_dirty_tree_and_accepts_a_clean_one(self):
        code, report, calls, _, _ = self.fixture_run(dirty=True, args=["--require-clean"])
        self.assertEqual(code, 1, report)
        self.assertEqual(report["finding_codes"], [GATE.DIRTY_TREE])
        self.assertEqual(calls, [])
        code, report, calls, _, _ = self.fixture_run(dirty=False, args=["--require-clean"])
        self.assertEqual(code, 0, report)
        self.assertTrue(report["options"]["require_clean"])
        # Without the option a dirty tree is recorded, not refused.
        code, report, _, _, _ = self.fixture_run(dirty=True)
        self.assertEqual(code, 0, report)
        self.assertTrue(report["provenance"]["dirty"])

    def test_build_timeout_is_bounded(self):
        # The fixture build sleeps 60 s; the gate must stop it at the bound and
        # report 124. The bound is 10 s, not 1 s: the fixture is a fresh Python
        # interpreter, and on a loaded host its start-up alone took over a second,
        # so a 1 s bound killed it before it could record the build call
        # (`[] != ['build']`, a load flake, not a gate defect).
        code, report, calls, _, _ = self.fixture_run("timeout", timeout=10)
        self.assertEqual(code, 1)
        self.assertEqual(calls, ["build"])
        self.assertEqual(report["build"]["returncode"], 124)
        self.assertEqual(report["finding_codes"], [GATE.BUILD_FAILED])

    # Output and artifact identity -------------------------------------------------

    def test_output_inside_the_tree_or_existing_evidence_is_refused(self):
        self.assertEqual(quiet_main(["--out", str(GATE.ROOT / "scripts" / "bridge-report")]), 1)
        self.assertFalse((GATE.ROOT / "scripts" / "bridge-report").exists())
        with tempfile.TemporaryDirectory() as temp:
            marker = Path(temp) / "report.json"
            marker.write_text("preserve")
            self.assertEqual(quiet_main(["--out", temp]), 1)
            self.assertEqual(marker.read_text(), "preserve")

    def test_backend_identity_and_snapshot_refuse_substitution(self):
        with tempfile.TemporaryDirectory() as temp:
            directory = Path(temp)
            backend = directory / "backend"
            backend.write_bytes(b"")
            with self.assertRaisesRegex(RuntimeError, "empty"):
                GATE.backend_identity(backend)
            backend.write_bytes(b"built backend")
            link = directory / "link"
            link.symlink_to(backend)
            with self.assertRaisesRegex(RuntimeError, "symlink"):
                GATE.backend_identity(link)
            expected = GATE.backend_identity(backend)
            snapshot = GATE.snapshot_backend(backend, directory / "snapshot", expected)
            self.assertEqual(snapshot["sha256"], SHA)
            self.assertEqual(stat.S_IMODE((directory / "snapshot").stat().st_mode), 0o444)
            existing = directory / "existing"
            existing.write_bytes(b"preserve")
            with self.assertRaises(FileExistsError):
                GATE.snapshot_backend(backend, existing, expected)
            self.assertEqual(existing.read_bytes(), b"preserve")
            backend.write_bytes(b"changed before copy")
            with self.assertRaises(GATE.GateError) as caught:
                GATE.snapshot_backend(backend, directory / "after-change", expected)
            self.assertEqual(caught.exception.findings[0][0], GATE.BACKEND_CHANGED)
            self.assertFalse((directory / "after-change").exists())


if __name__ == "__main__":
    unittest.main()
