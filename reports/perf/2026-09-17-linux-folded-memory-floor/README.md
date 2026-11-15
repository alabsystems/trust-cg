# Linux AArch64 regression floor with folded-memory proof tools

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> The gzipped captures were removed earlier; their last commit is
> `ea8492fd9315ed8863af166657fed1b75bcf2c93`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

Source `67d5c834114a2b2d54adf7d9b76f91f8a53f173c` executes all **49/49** complete
integration targets from the maintained Linux floor. **48/49 targets pass**.
Libtest totals: **352 passed, 3 failed,
0 ignored, 0 measured, 0 filtered**.
The source fingerprint is unchanged throughout the run. This is a bounded
regression floor, not the complete Linux acceptance contract.

The external harness imports the maintained target inventory, environment
selection and transcript classifier without editing their source. Each exact
Cargo invocation runs sequentially under the shared host lease, an enforced
16 GiB process-group RSS watchdog with zero grace, a 1,200-second deadline and
two build jobs. Guard receipts and complete stdout/stderr are retained. The
external supervisor differs from the maintained gate's timeout-only runner;
this report does not claim execution of that unmodified entrypoint.

The supported custom tool prefix selects the qualified AY folded-index binary
and independent Clean checker. No TCG/AY proof-policy overrides are injected.
Tool identities are retained in `records/tools.json.gz`; the installed compiler
checkpoint is documented separately under
the installed report.

- `jit_fail_closed_proof_policy`: command exited 101, test suite did not report positive passing execution, failed, ignored, measured or filtered tests are not permitted, started test count does not match passing test count.

| Target | Verdict | Pass | Fail | Ignore | Filter |
| --- | --- | ---: | ---: | ---: | ---: |
| `trust-cg-lower/aarch64_variadic_abi` | pass | 3 | 0 | 0 | 0 |
| `trust-cg-lower/aarch64_aggregate_stack_abi` | pass | 4 | 0 | 0 | 0 |
| `trust-cg-lower/aarch64_hva_abi` | pass | 4 | 0 | 0 | 0 |
| `trust-cg-lower/vector_type_admission` | pass | 5 | 0 | 0 | 0 |
| `trust-cg-lower/container_pointer_metadata` | pass | 12 | 0 | 0 | 0 |
| `trust-cg-lower/aggregate_constants` | pass | 13 | 0 | 0 | 0 |
| `trust-cg-lower/packed_aggregate_constants` | pass | 8 | 0 | 0 | 0 |
| `trust-cg-codegen/aarch64_call_result_liveness` | pass | 2 | 0 | 0 | 0 |
| `trust-cg-codegen/aggregate_call_results` | pass | 1 | 0 | 0 | 0 |
| `trust-cg-codegen/multi_result_call_abi` | pass | 1 | 0 | 0 | 0 |
| `trust-cg-codegen/e2e_aarch64_variadic_linux` | pass | 1 | 0 | 0 | 0 |
| `trust-cg-codegen/e2e_aarch64_aggregate_stack_linux` | pass | 1 | 0 | 0 | 0 |
| `trust-cg-codegen/e2e_aarch64_hva_linux` | pass | 2 | 0 | 0 | 0 |
| `trust-cg-codegen/e2e_aarch64_vector_types_linux` | pass | 2 | 0 | 0 | 0 |
| `trust-cg-codegen/e2e_aarch64_bool_atomics_linux` | pass | 2 | 0 | 0 | 0 |
| `trust-cg-codegen/e2e_aarch64_bool_abi_linux` | pass | 3 | 0 | 0 | 0 |
| `trust-cg-codegen/aarch64_exclusive_encoding` | pass | 3 | 0 | 0 | 0 |
| `trust-cg-codegen/aarch64_cond_select` | pass | 6 | 0 | 0 | 0 |
| `trust-cg-codegen/aarch64_fp_cond_select` | pass | 9 | 0 | 0 | 0 |
| `trust-cg-codegen/aarch64_fp_memory_decode` | pass | 19 | 0 | 0 | 0 |
| `trust-cg-codegen/aarch64_gpr_memory_decode` | pass | 8 | 0 | 0 | 0 |
| `trust-cg-codegen/aarch64_scalar_writeback_decode` | pass | 8 | 0 | 0 | 0 |
| `trust-cg-codegen/aarch64_register_offset_decode` | pass | 7 | 0 | 0 | 0 |
| `trust-cg-codegen/aarch64_narrow_register_offset_decode` | pass | 8 | 0 | 0 | 0 |
| `trust-cg-codegen/aarch64_pair_memory_decode` | pass | 8 | 0 | 0 | 0 |
| `trust-cg-codegen/panic_fuzz_encode` | pass | 11 | 0 | 0 | 0 |
| `trust-cg-codegen/a64_fp_integer_conversion` | pass | 7 | 0 | 0 | 0 |
| `trust-cg-codegen/e2e_fp_to_int_saturation` | pass | 5 | 0 | 0 | 0 |
| `trust-cg-codegen/e2e_aarch64_exclusive_status_linux` | pass | 2 | 0 | 0 | 0 |
| `trust-cg-codegen/e2e_aarch64_elf_tlsie` | pass | 8 | 0 | 0 | 0 |
| `trust-cg-codegen/e2e_aarch64_elf_link` | pass | 11 | 0 | 0 | 0 |
| `trust-cg-codegen/e2e_aarch64_global_layout` | pass | 3 | 0 | 0 | 0 |
| `trust-cg-codegen/e2e_aarch64_nested_bytes` | pass | 7 | 0 | 0 | 0 |
| `trust-cg-codegen/e2e_aarch64_narrow_int_diff` | pass | 1 | 0 | 0 | 0 |
| `trust-cg-codegen/e2e_aarch64_call_arg_signext` | pass | 1 | 0 | 0 | 0 |
| `trust-cg-codegen/e2e_aarch64_stack_narrow_args` | pass | 2 | 0 | 0 | 0 |
| `trust-cg-codegen/e2e_aarch64_callee_saved_fpr` | pass | 2 | 0 | 0 | 0 |
| `trust-cg-codegen/e2e_aarch64_calling_conv` | pass | 2 | 0 | 0 | 0 |
| `trust-cg-codegen/aarch64_affine_bytes` | pass | 13 | 0 | 0 | 0 |
| `trust-cg-codegen/aarch64_pseudo_boundary` | pass | 6 | 0 | 0 | 0 |
| `trust-cg-codegen/aarch64_raw_dataflow_boundary` | pass | 5 | 0 | 0 | 0 |
| `trust-cg-codegen/core_jit_planning` | pass | 11 | 0 | 0 | 0 |
| `trust-cg-codegen/jit_fail_closed_proof_policy` | fail | 3 | 3 | 0 | 0 |
| `trust-cg-verify/aarch64_affine_lowering` | pass | 39 | 0 | 0 | 0 |
| `trust-cg-verify/aarch64_trust_ir_affine_lowering` | pass | 38 | 0 | 0 | 0 |
| `trust-cg-verify/aarch64_fcmp_binding` | pass | 15 | 0 | 0 | 0 |
| `trust-cg-verify/fp_normal_classification` | pass | 5 | 0 | 0 | 0 |
| `trust-cg-codegen/aarch64_cmp_admission` | pass | 7 | 0 | 0 | 0 |
| `trust-cg-codegen/aarch64_integer_predicate_binding` | pass | 8 | 0 | 0 | 0 |

Every stored and decoded artifact is checked against its inventory hash and
length. Passing native or refusal controls receive only their reported scope.
Source-to-byte composition for calls, full ABI/frontend support, TrustCG
self-hosting, certified whole-system publication, performance qualification and
all L01–L14 requirements remain open.
