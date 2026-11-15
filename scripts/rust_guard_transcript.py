# Copyright 2026 Andrew Yates
# Licensed under the Apache License, Version 2.0

"""Closed, named libtest receipts for the fixed compiler-cohort guards.

The roster is a reviewed source contract, not inferred from child output. This
checks observed harness results only, not proof or silent test-body coverage.
Each roster is keyed by (package, integration target), in the order the pin
transaction runs them: two packages have a `trust_ir_binary_container`
target, and one package's receipt is never credited for the other's.
"""

from __future__ import annotations

import re


GUARD_TEST_NAMES = {
    ("trust-cg-test", "dependency_authority"): (
        "committed_lockfiles_bind_cross_repo_sources_exactly",
        "committed_manifests_bind_cross_repo_sources_exactly",
        "compile_artifact_cache_defaults_bind_dependency_authorities",
        "local_source_redirect_is_explicit_and_uncommitted",
    ),
    ("trust-cg-verify", "fsym_layout"): (
        "sizes_and_alignments_are_the_interpreters",
        "a_typed_store_writes_the_bytes_fsym_says_and_no_others",
        "a_typed_load_needs_no_byte_fsym_says_it_does_not",
        "array_coverage_is_one_periodic_run_whatever_the_length",
        "storage_dimensions_never_grant_initialized_coverage_or_a_bounded_verdict",
        "single_inhabited_coverage_uses_selected_payload_and_refuses_impossible_writes",
        "inactive_storage_retains_geometry_but_never_initialized_coverage",
        "stored_closure_geometry_and_covered_bytes_match_actual_interpreter",
        "stored_closure_layout_refuses_missing_conflicting_and_malformed_bindings",
    ),
    ("trust-cg-verify", "fsym_ub_map"): (
        "admission_gate_follows_the_map",
        "classes_table_agrees_with_the_map",
        "dialect_gate_preserves_char_and_unresolved_result_refusals",
        "each_site_is_raised_by_exactly_the_mapped_instructions",
        "every_hand_stated_stance_is_confirmed_or_reviewed",
        "every_owed_kind_is_its_class_kind_or_a_pinned_exception",
        "every_raise_the_interpreter_shows_is_owed_by_its_stance",
        "every_raiser_is_an_inst_variant_or_a_pseudo_raiser",
        "every_restricted_owed_shape_accepts_an_admitted_instance",
        "interpreter_ub_sites_are_exactly_the_map",
        "leaf_interpreter_modules_reach_no_ub_site",
        "named_ub_message_is_resolved_before_an_unrelated_later_literal",
        "non_test_census_preserves_production_after_test_modules",
        "the_layout_port_matches_the_pinned_interpreter",
        "v47_v49_constructs_are_refused_before_any_verdict",
        "v53_call_unwind_boundaries_are_refused_before_any_verdict",
        "v54_panic_sites_are_refused_before_any_verdict",
        "v55_v56_unwinding_twins_are_refused_before_any_verdict",
        "v68_v70_tensor_constructs_are_refused_before_any_verdict",
    ),
    ("trust-cg-lower", "trust_ir_construct_inventory"): (
        "every_cast_op_variant_has_exactly_one_row",
        "every_constant_variant_has_exactly_one_row",
        "every_inst_variant_has_exactly_one_row",
        "every_module_table_has_exactly_one_row",
        "every_ty_variant_has_exactly_one_row",
        "negative_twins_are_refused_by_name",
        "positive_probes_lower_through_the_adapter",
        "refused_rows_are_refused_by_the_adapter_by_name",
        "row_count_is_every_variant_and_table",
        "rows_are_well_formed",
        "runtime_raw_niche_constructor_preserves_inventory_refusal",
        "sited_assert_is_refused_by_the_site_name",
        "variant_name_functions_agree_with_the_derived_lists",
    ),
    # The conformance data this backend keeps in step with the pin by hand: the
    # corpus census over the pinned corpus, then the vendored container
    # fixtures through the in-process readers and through the CLI.
    ("trust-cg-codegen", "trust_ir_corpus_roundtrip"): (
        "corpus_census_and_exception_tables_are_exact",
        "every_corpus_module_round_trips_through_trust_cg_or_is_refused_by_name",
        "json_twin_of_the_producer_omission_row_is_refused_unless_explicitly_permitted",
        "the_oracle_catches_a_self_consistent_misread",
    ),
    ("trust-cg-codegen", "trust_ir_binary_container"): (
        "bare_ambiguous_lineage_blob_is_refused_by_trust_ir",
        "bare_blob_outside_the_pinned_version_window_is_refused",
        "binary_refusal_names_what_trust_ir_sniffs",
        "bound_synthetic_kernel_recheck_roundtrips_through_tmbc_at_v61",
        "container_dispatch_is_trust_ir_sniff_format",
        "every_bare_trust_ir_fixture_decodes_and_equals_its_json_twin",
        "json_extension_still_dispatches_to_json",
        "near_miss_magic_is_refused_by_name",
        "review_every_truncation_of_a_bare_module_is_refused_without_panic",
        "review_nested_containers_are_refused",
        "review_single_bit_flips_never_panic_the_loader",
        "review_trailing_bytes_after_a_bare_module_are_refused",
        "the_newest_module_version_is_the_readers_and_above_the_template_floor",
        "the_vendored_conformance_fixtures_are_the_pinned_corpus_bytes",
        "tmbc_envelope_around_the_newest_payload_still_decodes",
        "tmbc_writer_and_trust_ir_sniff_agree",
        "trust_ir_binary_magic_matches_serializer",
        "unbound_synthetic_kernel_recheck_roundtrips_through_tmbc",
        "v49_crystal_lane_blob_decodes_and_the_adapter_floor_refuses_it_by_name",
        "whitespace_before_the_trust_ir_magic_is_refused_by_name",
    ),
    ("trust-cg-cli", "trust_ir_binary_container"): (
        "bare_blob_outside_the_reader_window_is_refused_by_trust_ir",
        "bare_trust_ir_binary_compiles_like_its_json_twin",
        "default_format_refusal_names_what_trust_ir_sniffs",
        "default_license_refuses_the_claim_less_corpus",
        "near_miss_magic_is_refused_by_name",
        "review_non_binary_inputs_are_refused_under_the_default_format",
    ),
    ("trust-cg-codegen", "must_refuse_corpus"): (
        "default_wasm_entries_refuse_the_claim_less_body_and_abi_subjects",
        "default_wasm_entries_refuse_the_native_operand_admission_subjects",
        "every_must_refuse_row_is_refused_by_every_trust_cg_admission_lane",
        "the_control_row_bounds_a_refuse_everything_lane",
        "wasm_entries_take_the_callers_license_and_default_to_the_production_policy",
    ),
}

START = re.compile(r"running ([0-9]+) tests?")
NAMED = re.compile(r"test ([A-Za-z_][A-Za-z_0-9:]*) \.\.\.(?: (.*))?")
SUMMARY = re.compile(
    r"test result: ok\. ([0-9]+) passed; ([0-9]+) failed; ([0-9]+) ignored; "
    r"([0-9]+) measured; ([0-9]+) filtered out; finished in [0-9]+(?:\.[0-9]+)?s"
)


def validate_rust_test_transcript(transcript: str, expected: tuple[str, ...]) -> int:
    """Require one complete, exact, nonempty all-green integration suite.

    Serial nocapture diagnostics may interrupt a named result; the pending
    name earns no credit until its own final ``ok``. Any overlapping harness
    record, duplicate name, missing terminator or inconsistent count refuses.
    """
    return _validate_rust_test_transcript(transcript, expected, filtered=0)


def validate_exact_rust_test_transcript(transcript: str, name: str, inventory_total: int) -> int:
    """Require the named case to execute once, filtering only its pinned peers.

    This is execution accounting for one isolated layout-fixture case, not a
    full-suite receipt. Existing compiler-cohort guards still require zero
    filtered cases through ``validate_rust_test_transcript``.
    """
    if (not isinstance(inventory_total, int) or isinstance(inventory_total, bool)
            or inventory_total <= 0):
        raise ValueError("exact Rust test needs a positive pinned inventory total")
    if not isinstance(name, str) or re.fullmatch(r"[A-Za-z_][A-Za-z_0-9:]*", name) is None:
        raise ValueError("exact Rust test needs a valid case name")
    return _validate_rust_test_transcript(transcript, (name,), filtered=inventory_total - 1)


def _validate_rust_test_transcript(
    transcript: str, expected: tuple[str, ...], *, filtered: int
) -> int:
    if not isinstance(transcript, str):
        raise ValueError("Rust test transcript is not text")
    if (not isinstance(expected, tuple) or not expected
            or any(not isinstance(name, str) or not name for name in expected)
            or len(set(expected)) != len(expected)):
        raise ValueError("Rust guard needs a distinct nonempty expected-name tuple")
    lines = [line for line in transcript.splitlines() if line.strip()]
    declared = None
    completed = False
    pending = None
    passed = set()
    for index, line in enumerate(lines):
        if completed:
            raise ValueError("output after the terminal Rust test result")
        if line.lstrip().startswith("running "):
            start = START.fullmatch(line)
            if declared is not None or pending is not None or start is None:
                raise ValueError("malformed or repeated Rust suite start")
            declared = int(start[1])
            if declared != len(expected):
                raise ValueError("Rust running count disagrees with the reviewed roster")
        elif line.lstrip().startswith("test result:"):
            summary = SUMMARY.fullmatch(line)
            if declared is None or pending is not None or summary is None:
                raise ValueError("missing, malformed or interrupted Rust terminal result")
            counts = tuple(int(value) for value in summary.groups())
            if counts != (len(expected), 0, 0, 0, filtered) or passed != set(expected):
                raise ValueError("Rust result is not exact, nonvacuous and all-green with zero ignored")
            if index != len(lines) - 1:
                raise ValueError("Rust terminal result is not the end of the transcript")
            completed = True
        elif line.lstrip().startswith("test "):
            named = NAMED.fullmatch(line)
            if declared is None or pending is not None or named is None:
                raise ValueError("malformed or overlapping named Rust result")
            name, status = named.groups()
            if name not in expected or name in passed:
                raise ValueError(f"unexpected or duplicate Rust test name: {name}")
            if status == "ok":
                passed.add(name)
            elif status is not None and status.startswith(("FAILED", "ignored")):
                raise ValueError(f"Rust test did not pass: {name}: {status}")
            else:
                pending = name
        elif line in {"ok", "FAILED", "ignored"} or line.startswith("ignored,"):
            if pending is None or line != "ok":
                raise ValueError("unmatched or non-green Rust test status")
            passed.add(pending)
            pending = None
        elif line.lstrip().startswith(("error:", "SKIP:", "SKIP ", "failures:")):
            raise ValueError("Rust transcript reports an error, skip or failure")
        # Other lines are diagnostics, never named execution credit.
    if not completed:
        raise ValueError("Rust guard has no complete terminal test result")
    return len(passed)


if __name__ == "__main__":
    import argparse
    from pathlib import Path

    parser = argparse.ArgumentParser(description="Validate one isolated named Rust test execution")
    parser.add_argument("--exact-name", required=True)
    parser.add_argument("--inventory-total", required=True, type=int)
    parser.add_argument("transcript", type=Path)
    args = parser.parse_args()
    try:
        validate_exact_rust_test_transcript(
            args.transcript.read_text(encoding="utf-8"), args.exact_name, args.inventory_total
        )
    except (OSError, UnicodeError, ValueError) as error:
        parser.exit(1, f"Rust exact execution refused: {error}\n")
    print(f"Rust exact execution: PASS {args.exact_name}")
