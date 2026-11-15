# XD-01 residual: statistically credited x86-64 instructions per function

Source: `TCG_TRACE_STATISTICAL=1 cargo test -p trust-cg-codegen --test <target> -- --nocapture --test-threads=1`
on x86_64-unknown-linux-gnu at wave1/cert-path (base 23e081da0), stock Rust 1.97.1, 2026-09-21.
Rows are deduplicated by (function, instruction index) across repeated certifications within a target.
Most rows are `RECONSTRUCTED x86_64 ...` obligations from the reconstructed route, which grants no Formal
credit by design; the rest (`MovsdRipRel`/`MovssRipRel` constant-pool loads, `UCOMISS+SETcc`, `CMP+SETE`,
`MOVQ xmm,r64`) are static-DB obligations whose registry discharge fell back to sampling on this host (no
tier-0 or portable certificate hit, no live Formal answer). Either way the function's aggregate
`statistical_validation` certificate is `verified: false` and `Compiler::gate_jit_proofs_promotable`
refuses to publish it in a verifying JIT mode.

## Grand total by opcode (all seven targets, 74 distinct functions)

| opcode | statistical rows |
| --- | --- |
| `x86_64::AddRR` | 147 |
| `x86_64::ImulRR` | 94 |
| `x86_64::MovRR32` | 84 |
| `x86_64::MovsdRipRel` | 83 |
| `x86_64::MovRM` | 79 |
| `x86_64::Addsd` | 73 |
| `x86_64::Lea` | 70 |
| `x86_64::MovRR` | 69 |
| `x86_64::MovMR` | 52 |
| `x86_64::Mulsd` | 39 |
| `x86_64::MovsdRM` | 35 |
| `x86_64::LeaSib` | 18 |
| `x86_64::MovMR32` | 16 |
| `x86_64::MovRM32` | 16 |
| `x86_64::MovsdMR` | 6 |
| `x86_64::Cvtsi2sd` | 4 |
| `x86_64::MovMRSib` | 4 |
| `x86_64::Movsx` | 4 |
| `x86_64::Jcc` | 2 |
| `x86_64::MovRMSib` | 2 |
| `x86_64::MovqToXmm` | 2 |
| `x86_64::MovssRipRel` | 2 |
| `x86_64::Movzx` | 2 |
| `x86_64::Setcc` | 2 |
| `x86_64::AndRI` | 1 |
| `x86_64::AndRR` | 1 |
| `x86_64::CmpRI` | 1 |
| `x86_64::CmpRR` | 1 |
| `x86_64::Punpcklqdq` | 1 |
| `x86_64::Ucomiss` | 1 |
| **total** | **911** |

Integer-class rows (GPR copies, ALU, bitwise, shifts, extends, LEA, integer loads/stores, integer compare/setcc/jcc): 665; FP/SSE/XMM rows (`Addsd`, `Mulsd`, `Movsd*`, `Movss*`, `Cvtsi2sd`, `Ucomiss`, `MovqToXmm`, `Punpcklqdq`): 246.

## jit_cert_cache_identity_x86_64

result: FAILED 1 passed / 4 failed; failing tests: call_placeholder_binds_raw_target_name_even_at_the_same_host_address, function_name_is_bound_even_when_published_machine_bytes_match, provenance_warn_and_enforce_have_distinct_cache_policy_keys, recovered_exact_and_ordinary_direct_calls_do_not_share_a_caller_verdict

| function | statistical rows | opcode -> count |
| --- | --- | --- |
| `cache_binding_caller` | 4 | MovRR32 4 |
| `cache_internal_target` | 2 | MovRR32 2 |
| `call_shared_host` | 4 | MovRR32 4 |
| `deep_override` | 2 | MovRR32 2 |
| `provenance_policy` | 2 | MovRR32 2 |
| `same_layout_a` | 2 | MovRR32 2 |

## jit_sysv_x86_64_spill_replay

result: FAILED 2 passed / 2 failed; failing tests: x86_64_sysv_jit_high_fpr_pressure_spill_replay_executes, x86_64_sysv_jit_high_gpr_pressure_spill_replay_executes

| function | statistical rows | opcode -> count |
| --- | --- | --- |
| `sysv_high_fpr_pressure_reduce` | 258 | MovsdRipRel 65, Addsd 64, AddRR 32, MovsdRM 32, Mulsd 32, ImulRR 29, LeaSib 3, MovRR 1 |
| `sysv_high_gpr_pressure_reduce` | 194 | AddRR 96, ImulRR 51, MovRM 32, LeaSib 13, MovRR 2 |

## jit_validation_modes_x86_64

result: FAILED 2 passed / 5 failed; failing tests: x86_always_verify_never_serves_from_cache, x86_cache_miss_reverifies_not_skips, x86_cached_verified_certifies_every_published_function, x86_cached_verified_warm_latency_overhead_reported, x86_warm_cache_hit_does_not_respawn_verifier

| function | statistical rows | opcode -> count |
| --- | --- | --- |
| `answer` | 1 | MovRR 1 |
| `kernel` | 1 | MovRR 1 |
| `miss_a` | 1 | MovRR 1 |
| `pack_uncertified` | 5 | MovRR 2, MovqToXmm 2, Punpcklqdq 1 |
| `paranoid` | 1 | MovRR 1 |
| `warm_answer` | 1 | MovRR 1 |

## jit_x86_64_aggregate_abi_fail_closed

result: FAILED 4 passed / 33 failed; failing tests: host_jit_calls_native_large_struct_sret_function, host_jit_executes_large_struct_sret_cross_call, host_jit_executes_single_i32_struct_return, host_jit_executes_single_i64_struct_return, host_jit_executes_sysv_i32_pair_return_in_rax, host_jit_executes_sysv_large_struct_formal, host_jit_executes_sysv_small_struct_call_result_in_rax_rdx, host_jit_executes_sysv_small_struct_return_in_rax_rdx, host_jit_extracts_single_i32_struct_call_result, host_jit_extracts_single_i32_struct_formal, host_jit_extracts_single_i64_struct_call_result, host_jit_extracts_single_i64_struct_formal, host_jit_extracts_sysv_i32_pair_call_result, host_jit_extracts_sysv_i32_pair_formal_in_one_gpr, host_jit_extracts_sysv_i64_array_formal_in_gprs, host_jit_extracts_sysv_small_struct_formal_in_gprs, host_jit_passes_single_i32_struct_by_value_to_native_callback, host_jit_passes_single_i32_struct_by_value_to_trust_ir_callee, host_jit_passes_single_i64_struct_by_value_to_native_callback, host_jit_passes_single_i64_struct_by_value_to_trust_ir_callee, host_jit_passes_spilled_single_i64_struct_by_value_to_native_callback, host_jit_passes_sysv_f64_array_in_xmms_to_native_callback, host_jit_passes_sysv_f64_i64_struct_in_xmm_gpr_to_native_callback, host_jit_passes_sysv_i32_pair_by_value_to_trust_ir_callee, host_jit_passes_sysv_i64_array_in_gprs_to_native_callback, host_jit_passes_sysv_i64_array_in_gprs_to_trust_ir_callee, host_jit_passes_sysv_i64_f64_struct_in_gpr_xmm_to_native_callback, host_jit_passes_sysv_small_struct_in_gprs_to_native_callback, host_jit_passes_sysv_small_struct_in_gprs_to_trust_ir_callee, host_jit_passes_sysv_two_f64_struct_in_xmms_to_native_callback, host_jit_reads_sysv_f64_i64_struct_result_from_xmm0_rax, host_jit_reads_sysv_i64_f64_struct_result_from_rax_xmm0, host_jit_reads_sysv_two_f64_struct_result_from_xmm0_xmm1

| function | statistical rows | opcode -> count |
| --- | --- | --- |
| `adds_i32_pair_by_value` | 8 | Lea 2, MovRM32 2, AddRR 1, MovMR 1, MovRR 1, MovRR32 1 |
| `calls_i32_pair_by_value` | 7 | Lea 2, MovMR32 2, MovRR32 2, MovRM 1 |
| `calls_i32_pair_result` | 5 | Lea 2, MovMR 1, MovRM32 1, MovRR32 1 |
| `calls_i64_array_by_value` | 7 | MovMRSib 2, MovRM 2, MovRR 2, Lea 1 |
| `calls_large_struct_result` | 10 | MovMR 3, MovRM 3, MovRR 3, Lea 1 |
| `calls_native_f64_array_by_value` | 7 | LeaSib 2, MovsdMR 2, MovsdRipRel 2, Lea 1 |
| `calls_native_f64_i64_struct_by_value` | 7 | Lea 2, MovMR 1, MovRM 1, MovRR 1, MovsdMR 1, MovsdRipRel 1 |
| `calls_native_i64_array_by_value` | 7 | MovMRSib 2, MovRM 2, MovRR 2, Lea 1 |
| `calls_native_i64_f64_struct_by_value` | 6 | Lea 2, MovMR 1, MovRM 1, MovsdMR 1, MovsdRipRel 1 |
| `calls_native_large_struct` | 10 | MovMR 3, MovRM 3, MovRR 3, Lea 1 |
| `calls_native_single_i32_struct_by_value` | 5 | MovRR32 2, Lea 1, MovMR32 1, MovRM32 1 |
| `calls_native_single_i64_struct_by_value` | 5 | MovRR 2, Lea 1, MovMR 1, MovRM 1 |
| `calls_native_small_struct_by_value` | 8 | Lea 2, MovMR 2, MovRM 2, MovRR 2 |
| `calls_native_spilled_single_i64_struct_by_value` | 12 | MovRR 8, MovMR 2, Lea 1, MovRM 1 |
| `calls_native_two_f64_struct_by_value` | 7 | Lea 2, MovsdMR 2, MovsdRipRel 2, MovRR 1 |
| `calls_single_i32_struct_and_extracts` | 4 | Lea 1, MovMR32 1, MovRM32 1, MovRR32 1 |
| `calls_single_i32_struct_and_returns` | 3 | Lea 1, MovMR32 1, MovRM32 1 |
| `calls_single_i32_struct_by_value` | 5 | MovRR32 2, Lea 1, MovMR32 1, MovRM32 1 |
| `calls_single_i64_struct_and_extracts` | 4 | Lea 1, MovMR 1, MovRM 1, MovRR 1 |
| `calls_single_i64_struct_and_returns` | 3 | Lea 1, MovMR 1, MovRM 1 |
| `calls_single_i64_struct_by_value` | 5 | MovRR 2, Lea 1, MovMR 1, MovRM 1 |
| `calls_small_struct_by_value` | 8 | Lea 2, MovMR 2, MovRM 2, MovRR 2 |
| `calls_small_struct_result_and_returns` | 5 | MovMR 2, MovRM 2, Lea 1 |
| `extracts_i32_pair_param` | 6 | Lea 2, MovMR 1, MovRM32 1, MovRR 1, MovRR32 1 |
| `extracts_i64_array_by_value` | 7 | MovRR 3, MovMR 2, Lea 1, MovRMSib 1 |
| `extracts_i64_array_param` | 7 | MovRR 3, MovMR 2, Lea 1, MovRMSib 1 |
| `extracts_single_i32_struct_by_value` | 5 | MovRR32 2, Lea 1, MovMR32 1, MovRM32 1 |
| `extracts_single_i32_struct_param` | 5 | MovRR32 2, Lea 1, MovMR32 1, MovRM32 1 |
| `extracts_single_i64_struct_by_value` | 5 | MovRR 2, Lea 1, MovMR 1, MovRM 1 |
| `extracts_single_i64_struct_param` | 5 | MovRR 2, Lea 1, MovMR 1, MovRM 1 |
| `extracts_small_struct_by_value` | 8 | MovRR 3, Lea 2, MovMR 2, MovRM 1 |
| `extracts_small_struct_param` | 8 | MovRR 3, Lea 2, MovMR 2, MovRM 1 |
| `reads_native_f64_i64_struct_f64_field` | 3 | Lea 1, MovMR 1, MovsdRM 1 |
| `reads_native_f64_i64_struct_i64_field` | 5 | Lea 2, MovMR 1, MovRM 1, MovRR 1 |
| `reads_native_i64_f64_struct_f64_field` | 4 | Lea 2, MovMR 1, MovsdRM 1 |
| `reads_native_i64_f64_struct_i64_field` | 4 | Lea 1, MovMR 1, MovRM 1, MovRR 1 |
| `reads_native_two_f64_struct_second_field` | 3 | Lea 2, MovsdRM 1 |
| `returns_i32_pair_for_call` | 5 | Lea 2, MovMR32 2, MovRM 1 |
| `returns_large_struct` | 14 | MovMR 6, Lea 3, MovRM 3, MovRR 2 |
| `returns_single_i32_struct` | 3 | Lea 1, MovMR32 1, MovRM32 1 |
| `returns_single_i32_struct_for_call` | 3 | Lea 1, MovMR32 1, MovRM32 1 |
| `returns_single_i64_struct` | 3 | Lea 1, MovMR 1, MovRM 1 |
| `returns_single_i64_struct_for_call` | 3 | Lea 1, MovMR 1, MovRM 1 |
| `returns_small_struct` | 6 | Lea 2, MovMR 2, MovRM 2 |
| `returns_small_struct_for_call` | 6 | Lea 2, MovMR 2, MovRM 2 |
| `returns_unsupported_i32_pair` | 5 | Lea 2, MovMR32 2, MovRM 1 |
| `takes_large_struct` | 16 | MovRM 6, Lea 4, MovMR 3, AddRR 2, MovRR 1 |

## jit_x86_64_profile_modes

result: FAILED 3 passed / 5 failed; failing tests: x86_64_host_jit_accepts_block_counts_profile_hooks, x86_64_host_jit_accepts_call_counts_profile_hooks, x86_64_host_jit_block_counts_preserve_late_call_fixup, x86_64_host_jit_block_counts_preserve_late_rip_const_pool_fixup, x86_64_host_jit_block_counts_profile_hooks_count_conditional_targets

| function | statistical rows | opcode -> count |
| --- | --- | --- |
| `callee` | 1 | MovRR 1 |
| `caller` | 2 | MovRR 2 |
| `late_const` | 1 | MovsdRipRel 1 |
| `linear` | 1 | MovRR 1 |
| `profiled_answer` | 1 | MovRR 1 |
| `selective` | 4 | MovRR 2, CmpRR 1, Jcc 1 |

## x86_64_constant_pool

result: FAILED 1 passed / 1 failed; failing tests: x86_host_jit_returns_f64_neg_zero_with_f32_pos_zero_in_same_pool

| function | statistical rows | opcode -> count |
| --- | --- | --- |
| `mixed_zero_runtime` | 13 | MovsdRipRel 2, MovssRipRel 2, Movzx 2, Setcc 2, AndRI 1, AndRR 1, CmpRI 1, Jcc 1, Ucomiss 1 |

## x86_64_sysv_ay_abi

result: FAILED 3 passed / 1 failed; failing tests: x86_64_sysv_host_jit_executes_ay_abi_canaries

| function | statistical rows | opcode -> count |
| --- | --- | --- |
| `ay_sysv_eight_i32_call` | 19 | MovRR32 14, MovMR32 2, MovRM32 2, AddRR 1 |
| `ay_sysv_eight_i32_direct` | 25 | AddRR 8, ImulRR 8, MovRR32 7, MovRM32 2 |
| `ay_sysv_mixed_i32_f64_call` | 10 | MovRR32 8, Addsd 1, MovsdRipRel 1 |
| `ay_sysv_mixed_i32_f64_direct` | 35 | Addsd 8, MovsdRipRel 8, Mulsd 7, Cvtsi2sd 4, MovRR32 4, Movsx 4 |
| `ay_sysv_six_i32_call` | 15 | MovRR32 14, AddRR 1 |
| `ay_sysv_six_i32_direct` | 19 | MovRR32 7, AddRR 6, ImulRR 6 |
