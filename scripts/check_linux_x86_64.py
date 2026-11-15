#!/usr/bin/env python3
"""Run the required Linux x86-64 regression floor, not full qualification.

The x86-64 twin of scripts/check_linux_aarch64.py: the same runner (bounded
per-target processes, skip-as-failure classification through
scripts/matrix_results.py, retained logs and JSON, source fingerprints,
dependency identity before and after, --require-clean, --require-offline-deps,
--max-rss-gib) over the complete x86-64 integration targets below, on an
`x86_64-unknown-linux-gnu` host. Native execution, ABI admission and encoding
controls are all required; a target that prints a runtime SKIP, executes zero
tests, times out or fails is a floor failure. Passing this floor establishes no
compiler completion, proof authority or release readiness; see
docs/linux-x86-64-completion.md for the remaining requirements.

Opened 2026-09-20 with every x86-64 integration target the tree then had,
including the ones still guarded on `target_os = "macos"`: those fail here
by design until they gain Linux arms, so the first records of this floor are
the census of that work, not a pass.

DECIDED_ABSENT lists the targets a recorded ruling (docs/decision-record.md)
has taken out of this floor's requirement; they are printed and recorded in
every report but never run, so the omission stays visible. TARGETS stays
all-required. No ruling takes a target out today.

One required target lives in the rustc bridge workspace and is run there by the
pinned Trust package (see BRIDGE_PACKAGE in the shared runner): name the package
with --trust-driver <package>/bin/trustc, or the floor fails closed on it.

Every target builds in the shared runner's Trust development lane (`targo
--unverified`; the stock cargo/rustc lane is retired, owner directive
2026-09-28). No atpkg Trust package exists for this host (XD-02 / X12), so the
runner needs a Trust `bin` directory holding trustc, trustdoc and targo
together first on PATH (the host's rustup-linked stage2 Trust, for instance),
and fails closed without one. This floor has not yet run in that lane.
"""

from __future__ import annotations

import importlib.util
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]

_spec = importlib.util.spec_from_file_location(
    "_linux_x86_64_floor_shared", ROOT / "scripts" / "check_linux_aarch64.py"
)
assert _spec is not None and _spec.loader is not None
SHARED = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(SHARED)

HOST = "x86_64-unknown-linux-gnu"
# Complete test targets, never substring filters. Object-format-only targets
# for other operating systems (Mach-O, COFF, Windows JIT) are not in this
# floor: they attest other targets' bytes and are covered by their own lanes.
TARGETS = (
    ("trust-cg-verify", "bdefs_differential_bridge_x86"),
    ("trust-cg-verify", "bdefs_differential_bridge_x86_fp"),
    ("trust-cg-verify", "bdefs_differential_bridge_x86_packed"),
    ("trust-cg-verify", "reconstruction_x86"),
    ("trust-cg-verify", "x86_addressing_gate"),
    ("trust-cg-verify", "x86_encoding_gate"),
    ("trust-cg-verify", "x86_movsxd_sib_gate"),
    ("trust-cg-verify", "x86_sse_lane_gate"),
    ("trust-cg-codegen", "decode_check_x86"),
    ("trust-cg-codegen", "e2e_elf_link"),
    ("trust-cg-codegen", "e2e_x86_64_aggregate_abi"),
    ("trust-cg-codegen", "e2e_x86_64_aggregate_byval_arg"),
    ("trust-cg-codegen", "e2e_x86_64_atomics"),
    ("trust-cg-codegen", "e2e_x86_64_callee_saved"),
    ("trust-cg-codegen", "e2e_x86_64_calling_conv"),
    ("trust-cg-codegen", "e2e_x86_64_checked_arith"),
    ("trust-cg-codegen", "e2e_x86_64_correctness"),
    ("trust-cg-codegen", "e2e_x86_64_data_reloc"),
    ("trust-cg-codegen", "e2e_x86_64_differential"),
    ("trust-cg-codegen", "e2e_x86_64_dispatcher"),
    ("trust-cg-codegen", "e2e_x86_64_eh_catch"),
    ("trust-cg-codegen", "e2e_x86_64_eh_invoke_trust_ir_run"),
    ("trust-cg-codegen", "e2e_x86_64_eh_resume_trust_ir"),
    ("trust-cg-codegen", "e2e_x86_64_fp"),
    ("trust-cg-codegen", "e2e_x86_64_fp_across_call"),
    ("trust-cg-codegen", "e2e_x86_64_heap_alloc"),
    ("trust-cg-codegen", "e2e_x86_64_i128_div"),
    ("trust-cg-codegen", "e2e_x86_64_i128_stack_abi"),
    ("trust-cg-codegen", "e2e_x86_64_indirect_calls"),
    ("trust-cg-codegen", "e2e_x86_64_internal_multi_result"),
    ("trust-cg-codegen", "e2e_x86_64_large_struct_byval"),
    ("trust-cg-codegen", "e2e_x86_64_link"),
    ("trust-cg-codegen", "e2e_x86_64_mixed_width_shift"),
    ("trust-cg-codegen", "e2e_x86_64_module_batch_fnptr"),
    ("trust-cg-codegen", "e2e_x86_64_module_batch_globals"),
    ("trust-cg-codegen", "e2e_x86_64_opt_correctness"),
    ("trust-cg-codegen", "e2e_x86_64_recursion"),
    ("trust-cg-codegen", "e2e_x86_64_scale_emergent"),
    ("trust-cg-codegen", "e2e_x86_64_sib_rmw"),
    ("trust-cg-codegen", "e2e_x86_64_split_copy_replay"),
    # Required since ruling XD-03 (docs/decision-record.md): swiftcc is a
    # required Linux x86-64 convention. The test needs a driver that honours
    # `__attribute__((swiftcall))`; on a GCC-only host it prints its XD-03 SKIP,
    # which this floor counts as a failure, so the row is red until that driver
    # is provisioned for this test.
    ("trust-cg-codegen", "e2e_x86_64_swiftcc"),
    ("trust-cg-codegen", "e2e_x86_64_symbol_address"),
    ("trust-cg-codegen", "e2e_x86_64_triple_oracle"),
    ("trust-cg-codegen", "e2e_x86_64_varargs"),
    ("trust-cg-codegen", "e2e_x86_64_vector_fp"),
    ("trust-cg-codegen", "encode_objdump_differential_x86"),
    ("trust-cg-codegen", "guard_bounds_probe_x86"),
    ("trust-cg-codegen", "guard_kernel_gate_x86_divzero_e2e"),
    ("trust-cg-codegen", "guard_kernel_gate_x86_e2e"),
    ("trust-cg-codegen", "guard_kernel_gate_x86_linkrun"),
    ("trust-cg-codegen", "guard_kernel_gate_x86_null_e2e"),
    ("trust-cg-codegen", "guard_kernel_gate_x86_shiftrange_e2e"),
    ("trust-cg-codegen", "jit_cert_cache_identity_x86_64"),
    ("trust-cg-codegen", "jit_integration_x86_64"),
    ("trust-cg-codegen", "jit_sysv_x86_64_spill_replay"),
    ("trust-cg-codegen", "jit_validation_modes_x86_64"),
    ("trust-cg-codegen", "jit_x86_64_aggregate_abi_fail_closed"),
    ("trust-cg-codegen", "jit_x86_64_profile_modes"),
    ("trust-cg-codegen", "panic_fuzz_compile_x86_64"),
    ("trust-cg-codegen", "panic_fuzz_encode_x86_64"),
    ("trust-cg-codegen", "static_indirect_devirtualization"),
    ("trust-cg-codegen", "weak_linkage_x86"),
    ("trust-cg-codegen", "x86_64_constant_pool"),
    ("trust-cg-codegen", "x86_64_external_call_relocations"),
    ("trust-cg-codegen", "x86_64_imm8_encoding"),
    ("trust-cg-codegen", "x86_64_ir_inline_seam"),
    ("trust-cg-codegen", "x86_64_sse2_dword_shifts"),
    ("trust-cg-codegen", "x86_64_sse2_lane_encoding"),
    ("trust-cg-codegen", "x86_64_sysv_ay_abi"),
    ("trust-cg-codegen", "x86_64_target_features"),
    # Bridge target: run in `crates/rustc-codegen-trust-cg` under the pinned
    # Trust package (BRIDGE_PACKAGE in the shared runner), not by the root
    # workspace's targo. The x86-64 SSE2 vectorizer's beat-llvm tiers must still
    # fire on the p4/h1/v2 program shapes through the bridge at -Copt-level=3 and
    # the vectorized binaries must exit with the manifest codes; a tier that
    # stops firing shows up here as a missing trace line rather than as a timing
    # regression noticed later.
    ("rustc-codegen-trust-cg", "m143_x86_vectorize_trace"),
    # --- Clean-kernel and TY programs on this host (clean-ty-x86) ---
    # ty_bfs_minimal: the TY BFS kernel through the x86-64 AOT path at O0-O3,
    # linked by the host cc and checked against its C driver.
    ("trust-cg-codegen", "ty_bfs_minimal"),
    #
    # clean_fixture_host_lowering: the x86-64 AOT lowering ratchet for the 38
    # frozen Clean-kernel fixtures, all 38 at O0 AND O1 with an EMPTY refusal
    # class map. This is now a row. It was held out until 2026-09-28 because its
    # wall clock was nondeterministic and unbounded — three runs at 986s, 606s
    # and 433s, then 1844s once the formal-arg prefix gap let previously-refused
    # fixtures compile every function, with seven of them reaching no decision
    # inside the target's own per-fixture deadline and their uncancelled workers
    # each holding a core for the rest of the run. The class even drifted between
    # runs (`clean_phase_completion.gate.trust.tir` at O0 refused in 0.6s on one
    # run and timed out at 120s on the next).
    #
    # That variance had ONE cause and it is fixed, so the reason for holding the
    # row out is gone rather than merely smaller: the greedy allocator re-enqueued
    # both halves of every split at Stage::New, so a split product was itself
    # splittable without bound and one function (`build_env`) performed 159 813
    # splits, spilled 157 852 of the pieces and cost 331s of a 343s compile. With
    # the split-generation bound (`trust-cg-regalloc`'s `split_depth_cap`, LLVM's
    # RS_Split2 rule) the whole target is 54.28s / 54.47s / 54.28s over three
    # consecutive debug runs on this host — a 0.4% spread, ~390 MiB peak RSS, and
    # 34x under this runner's default --timeout-seconds. Nothing reaches a
    # deadline any more, so there are no uncancelled workers and no drifting
    # class. Its slowest single fixture decision is 2.6s.
    #
    # TARGET_MINIMUM_PASSES pins 5: the two floor sweeps (O0, O1) plus the three
    # structural guards. Without that, the three cheap guards would satisfy the
    # row on a host where neither sweep ran.
    ("trust-cg-codegen", "clean_fixture_host_lowering"),
    #
    # The JIT-executing Clean and TY reducers are NOT floor rows either: on
    # this host they lower and encode but stop at the verifying JIT's
    # proof-promotion gate (the XD-01 class). The x86-64 guard-carrier canary
    # that ALSO refused them here was closed on 2026-09-27 by qualifying this
    # host's bundled DRAT checker
    # (docs/portable-checker-host-qualification.md); those rows were not
    # re-measured in that change, so what remains of their refusal here is
    # unmeasured rather than known to be XD-01 alone.
)

# Targets held out of this floor's requirement under a NAMED ruling id, as
# (package, target, ruling id, reason); see docs/decision-record.md. A row is
# added only by a ruling recorded there: a lane never takes a target out for
# itself. XD-03 (2026-10-02) made e2e_x86_64_swiftcc required again, so the
# table is empty.
DECIDED_ABSENT: tuple[tuple[str, str, str, str], ...] = ()

# None of these targets is gated on a non-default Cargo feature; the shared
# runner's feature table must name only this floor's rows.
TARGET_FEATURES: dict[tuple[str, str], tuple[str, ...]] = {}
# None of these targets runs the AArch64 floor's three-linker legs; the shared
# runner's environment table must name only this floor's rows.
TARGET_ENVIRONMENT: dict[tuple[str, str], dict[str, str]] = {}
# These native System V aggregate oracles each compile all of their test
# functions on Linux x86-64. A one-test libtest pass must not stand in for the
# whole ABI family. Other targets retain the shared runner's one-pass minimum.
TARGET_MINIMUM_PASSES = {
    ("trust-cg-codegen", "e2e_x86_64_aggregate_abi"): 18,
    ("trust-cg-codegen", "e2e_x86_64_aggregate_byval_arg"): 6,
    # All twelve: on this host the link-run lane and the JIT lane EXECUTE the
    # internal multi-result convention (they only skip where no x86-64
    # executor exists); the ten admission and machine-shape tests alone must
    # not satisfy the row.
    ("trust-cg-codegen", "e2e_x86_64_internal_multi_result"): 12,
    # All three: the run leg links and EXECUTES the two bridge-dumped kernels
    # whose split copies the x86 regalloc replay once dropped (one returned a
    # wrong value), and is the only evidence of that fix on this host; the
    # provenance and compile-only tests alone must not satisfy the row.
    ("trust-cg-codegen", "e2e_x86_64_split_copy_replay"): 3,
    # Both bridge vector-tier tests: the three-kernel tier sweep and the tracked
    # `no-x86-fill-memset` opt-out. They compile #[test] functions on this host
    # unconditionally, so one pass must not stand in for both — and each one
    # returns early with a `skipping:` line when the pinned toolchain has no
    # host rust-std, which the shared runner already classifies as a failure.
    ("rustc-codegen-trust-cg", "m143_x86_vectorize_trace"): 2,
    # All nine: five compile-only tests plus the four legs that LINK and EXECUTE
    # the TY BFS kernel against its C driver. Without this the row is satisfied
    # by the compile-only subset, which is how a TY lane could pass on a host
    # where nothing TY actually ran.
    ("trust-cg-codegen", "ty_bfs_minimal"): 9,
    # All five: the O0 and O1 lowering sweeps over the 38 frozen Clean fixtures,
    # plus `every_committed_clean_fixture_is_listed`,
    # `lowering_floor_names_are_swept_fixtures` and
    # `host_loading_rewrites_only_the_target_header_line`. The three guards are
    # cheap and always run; the two sweeps are the evidence. A minimum below 5
    # lets the guards alone satisfy the row.
    ("trust-cg-codegen", "clean_fixture_host_lowering"): 5,
}

SHARED.HOST = HOST
SHARED.TARGETS = TARGETS
SHARED.DECIDED_ABSENT = DECIDED_ABSENT
SHARED.TARGET_FEATURES = TARGET_FEATURES
SHARED.TARGET_ENVIRONMENT = TARGET_ENVIRONMENT
SHARED.TARGET_MINIMUM_PASSES = TARGET_MINIMUM_PASSES
SHARED.FLOOR_NAME = "Linux x86-64"
SHARED.SCHEMA = "trust-cg-linux-x86-64-regressions-v1"
SHARED.OUTPUT_PREFIX = "trust-cg-linux-x86-64-"


def main(argv: list[str] | None = None) -> int:
    return SHARED.main(argv)


if __name__ == "__main__":
    sys.exit(main())
