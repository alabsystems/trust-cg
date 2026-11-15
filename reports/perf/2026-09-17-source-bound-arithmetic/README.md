# Source-bound AArch64 arithmetic admission

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> The gzipped captures were removed earlier; their last commit is
> `ea8492fd9315ed8863af166657fed1b75bcf2c93`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

Clean source `899e4cd75e3f14e05d0a7789a91b34aee06941fc` passes the expanded **50/50** complete Linux targets:
**358 passed, 0 failed, 0 ignored,
0 measured, 0 filtered**. Source and tool
identities remain unchanged through the floor and additional regressions.
This is bounded leaf qualification; every whole-system L01–L14 requirement remains open.

The new required target compiles all **160/160** cases: four exact signed/unsigned
32/64-bit source types, ten arithmetic shapes, and O0–O3. All **23,040 native
calls** match independent wrapping arithmetic. Each published image's actual
hash and proof-required certificate are checked, and a separate source-to-byte
interpreter compares the original module/LIR with the final emitted bytes.
The optimized doubling cases reject **84 altered instruction words**. The
second method checks captured and warm authority, fresh no-cache proof without
reusable credit, altered source/machine input, corrupted source digests and
coordinates, and missing/disabled solver or checker authority. Previously
captured requests retain their own authority when ambient tools change.

A private arithmetic owner requires a complete independently checked original
LIR/machine body and an independently replayed frame theorem. Register operands,
widths and immediates come from the actual live instruction. Wrapping ADD/SUB
use widened arithmetic and truncation; LSL uses bit extraction/concatenation
against the machine shift model. Every exact obligation is independently
replayed by the captured AY/Clean authority. Raw target-only reconstruction
remains statistical. Optimized opcode-class changes can use the checked body;
source-coordinate and source-digest validation still run. No calling-frame,
callee contract, private-cell, general-memory or self-hosting authority is added.
The Rust source/body checker is still inside the trusted boundary.

The independent final-byte decoder now recognizes LSL's UBFM form, including
zero-shift identity, and rejects other bitfield forms, reserved width fields,
undefined inputs and reserved destinations. Six literal byte controls were
assembled independently with GNU AArch64 as. Erased I32 formal copies can retain
the incoming X-register ABI spelling without defining any value; existing
hidden-effect, invalid-register, live-use and Gpr64/W-width refusals remain.

The focused binding run passes **39 tests**, with 3,918 unrelated library tests
explicitly filtered. It exports **36 exact formulas** spanning both widths,
operand aliasing, zero registers, immediate bounds and shift bounds. The final
independent CLI campaign accepts **36/36 original certificates** and rejects
**108/108 corruptions**: a hole rule, removed empty conclusion and opposite
asserted premise for each certificate. Exact executable hashes are retained.

The original baseline refuses all **160/160** required positives. The first
candidate passes 112; the diagnostic repeat records the erased-copy and opcode
attribution causes. The next passes 154, retaining six 64-bit optimized-double
refusals. Direct replay of the original wider-multiply formulation accepts 34
certificates and rejects 102 mutations, then AY strictly returns `unknown` for
the next query because its proof contains an unsupported hole rule. That
campaign remains incomplete and is retained unchanged. The equivalent bit-wiring
formulation passes the complete final campaign; no solver/checker policy is
relaxed. Three earlier test builds also retain their compiler diagnostics for
fixture type inference, an edit delimiter and a moved type value.

The first complete 50-target floor passes 49 targets and 357 tests, with one
stale high-level assertion failing: explicit AlwaysVerify expected the now
source-bound ADD to refuse. Its raw sampled-ADD control already passes. The
repair requires the independently proved high-level function to execute with
optional report emission disabled and preserves every raw negative assertion.
The focused seven-method target and the complete second floor both pass.

The existing policy suite now requires checked ADD to execute even in object
compatibility mode; its raw sampled-ADD, vacuous-trap and unproved-calling-frame
negative controls remain. The new arithmetic target increases the required
floor from 49 to 50. Whole-workspace formatting, documentation and gate
orchestration tests pass.

The complete CLI proof-publication target also passes all 13
methods, preserving object binding, frame replay and refusal/publication ordering.
It does not claim new arithmetic AOT sidecar export support.

Additional boundary regressions:

- `request-and-provenance`: 23 passes; 3934 unrelated library tests filtered.
- `core-byte-and-certificate`: 16 passes; 3811 unrelated library tests filtered.
- `soundness_manifest`: 10 passes, zero failure/ignore/filter.
- `meta_theorems`: 8 passes, zero failure/ignore/filter.
- `mutation_catalog`: 9 passes, zero failure/ignore/filter.
- `coverage_gate_tests`: 40 passes, zero failure/ignore/filter.

The additional runner's first startup was refused by the exclusive host lease;
no test ran then. Its second invocation starts after the floor completes and
executes all six selections. All 40 opcode-inventory tests pass, but the Linux
wrapper mistakes their `[skip]` pseudo/trap classifications for runtime skips.
The third invocation reruns that complete target with `--show-output` and the
repository's soundness capture parser; the original failed classification is
preserved. Five other successful selections are explicitly carried forward with
unchanged source and tools. All
Cargo executions use two build jobs, a 16 GiB process-group RSS ceiling with
zero grace, a 1,200-second deadline, and retained supervision receipts. CLI
formula replay uses 16 GiB for AY and 8 GiB for Clean with 180-second deadlines.
The external floor harness imports the maintained target inventory and result
classifier; it adds RSS supervision and is not the unmodified timeout-only
entrypoint. These focused soundness inventories do not claim the full
cross-repository soundness gate, Lean proof closure, or complete compiler acceptance.

The installed compiler at the time of this source qualification remains the
previous development cohort.
Source qualification does not silently replace its binary. The
[previous 49-target floor](../2026-09-17-linux-jit-floor-repair/README.md) is retained separately.

| Target | Pass | Fail | Ignore | Filter |
| --- | ---: | ---: | ---: | ---: |
| `trust-cg-lower/aarch64_variadic_abi` | 3 | 0 | 0 | 0 |
| `trust-cg-lower/aarch64_aggregate_stack_abi` | 4 | 0 | 0 | 0 |
| `trust-cg-lower/aarch64_hva_abi` | 4 | 0 | 0 | 0 |
| `trust-cg-lower/vector_type_admission` | 5 | 0 | 0 | 0 |
| `trust-cg-lower/container_pointer_metadata` | 12 | 0 | 0 | 0 |
| `trust-cg-lower/aggregate_constants` | 13 | 0 | 0 | 0 |
| `trust-cg-lower/packed_aggregate_constants` | 8 | 0 | 0 | 0 |
| `trust-cg-codegen/aarch64_call_result_liveness` | 2 | 0 | 0 | 0 |
| `trust-cg-codegen/aggregate_call_results` | 1 | 0 | 0 | 0 |
| `trust-cg-codegen/multi_result_call_abi` | 1 | 0 | 0 | 0 |
| `trust-cg-codegen/e2e_aarch64_variadic_linux` | 1 | 0 | 0 | 0 |
| `trust-cg-codegen/e2e_aarch64_aggregate_stack_linux` | 1 | 0 | 0 | 0 |
| `trust-cg-codegen/e2e_aarch64_hva_linux` | 2 | 0 | 0 | 0 |
| `trust-cg-codegen/e2e_aarch64_vector_types_linux` | 2 | 0 | 0 | 0 |
| `trust-cg-codegen/e2e_aarch64_bool_atomics_linux` | 2 | 0 | 0 | 0 |
| `trust-cg-codegen/e2e_aarch64_bool_abi_linux` | 3 | 0 | 0 | 0 |
| `trust-cg-codegen/aarch64_exclusive_encoding` | 3 | 0 | 0 | 0 |
| `trust-cg-codegen/aarch64_cond_select` | 6 | 0 | 0 | 0 |
| `trust-cg-codegen/aarch64_fp_cond_select` | 9 | 0 | 0 | 0 |
| `trust-cg-codegen/aarch64_fp_memory_decode` | 19 | 0 | 0 | 0 |
| `trust-cg-codegen/aarch64_gpr_memory_decode` | 8 | 0 | 0 | 0 |
| `trust-cg-codegen/aarch64_scalar_writeback_decode` | 8 | 0 | 0 | 0 |
| `trust-cg-codegen/aarch64_register_offset_decode` | 7 | 0 | 0 | 0 |
| `trust-cg-codegen/aarch64_narrow_register_offset_decode` | 8 | 0 | 0 | 0 |
| `trust-cg-codegen/aarch64_pair_memory_decode` | 8 | 0 | 0 | 0 |
| `trust-cg-codegen/panic_fuzz_encode` | 11 | 0 | 0 | 0 |
| `trust-cg-codegen/a64_fp_integer_conversion` | 7 | 0 | 0 | 0 |
| `trust-cg-codegen/e2e_fp_to_int_saturation` | 5 | 0 | 0 | 0 |
| `trust-cg-codegen/e2e_aarch64_exclusive_status_linux` | 2 | 0 | 0 | 0 |
| `trust-cg-codegen/e2e_aarch64_elf_tlsie` | 8 | 0 | 0 | 0 |
| `trust-cg-codegen/e2e_aarch64_elf_link` | 11 | 0 | 0 | 0 |
| `trust-cg-codegen/e2e_aarch64_global_layout` | 3 | 0 | 0 | 0 |
| `trust-cg-codegen/e2e_aarch64_nested_bytes` | 7 | 0 | 0 | 0 |
| `trust-cg-codegen/e2e_aarch64_narrow_int_diff` | 1 | 0 | 0 | 0 |
| `trust-cg-codegen/e2e_aarch64_call_arg_signext` | 1 | 0 | 0 | 0 |
| `trust-cg-codegen/e2e_aarch64_stack_narrow_args` | 2 | 0 | 0 | 0 |
| `trust-cg-codegen/e2e_aarch64_callee_saved_fpr` | 2 | 0 | 0 | 0 |
| `trust-cg-codegen/e2e_aarch64_calling_conv` | 2 | 0 | 0 | 0 |
| `trust-cg-codegen/aarch64_affine_bytes` | 13 | 0 | 0 | 0 |
| `trust-cg-codegen/aarch64_pseudo_boundary` | 6 | 0 | 0 | 0 |
| `trust-cg-codegen/aarch64_raw_dataflow_boundary` | 5 | 0 | 0 | 0 |
| `trust-cg-codegen/core_jit_planning` | 11 | 0 | 0 | 0 |
| `trust-cg-codegen/jit_fail_closed_proof_policy` | 7 | 0 | 0 | 0 |
| `trust-cg-codegen/jit_source_bound_arithmetic` | 2 | 0 | 0 | 0 |
| `trust-cg-verify/aarch64_affine_lowering` | 39 | 0 | 0 | 0 |
| `trust-cg-verify/aarch64_trust_ir_affine_lowering` | 38 | 0 | 0 | 0 |
| `trust-cg-verify/aarch64_fcmp_binding` | 15 | 0 | 0 | 0 |
| `trust-cg-verify/fp_normal_classification` | 5 | 0 | 0 | 0 |
| `trust-cg-codegen/aarch64_cmp_admission` | 7 | 0 | 0 | 0 |
| `trust-cg-codegen/aarch64_integer_predicate_binding` | 8 | 0 | 0 | 0 |

Every stored and decoded artifact is checked against its inventory SHA256 and
length. Original failures, full transcripts, exact queries/certificates,
mutation packets, qualified source patch and test/harness sources are retained.
