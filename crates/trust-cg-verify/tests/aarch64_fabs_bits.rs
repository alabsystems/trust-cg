// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use trust_cg_verify::lowering_proof::{proof_fabs_f32, proof_fabs_f64, verify_fp_by_evaluation};
use trust_cg_verify::smt::{EvalEnv, EvalResult, SmtExpr, SmtSort};
use trust_cg_verify::verify::VerificationResult;

fn samples(width: u32) -> Vec<u64> {
    let mask = u64::MAX >> (64 - width);
    let mut values = vec![0, mask, mask >> 1, 1u64 << (width - 1)];
    for bit in 0..width {
        values.extend([1u64 << bit, mask ^ (1u64 << bit)]);
    }
    if width == 32 {
        values.extend([0x7f80_0000, 0xff80_0000, 0x7f80_0001, 0xffc1_2345]);
    } else {
        values.extend([
            0x7ff0_0000_0000_0000,
            0xfff0_0000_0000_0000,
            0x7ff0_0000_0000_0001,
            0xfff8_1234_5678_9abc,
        ]);
    }
    let mut state = 0x1234_5678_9abc_def0u64;
    for _ in 0..4096 {
        state ^= state << 13;
        state ^= state >> 7;
        state ^= state << 17;
        values.push(state & mask);
    }
    values
}

fn env(value: u64) -> EvalEnv {
    let mut env = EvalEnv::default();
    env.insert("a".into(), value);
    env
}

#[test]
fn fabs_obligations_bind_complete_raw_inputs_and_are_not_identities() {
    for (width, proof) in [(32, proof_fabs_f32()), (64, proof_fabs_f64())] {
        assert_eq!(proof.inputs, vec![("a".into(), width)]);
        assert!(proof.fp_inputs.is_empty());
        assert!(proof.preconditions.is_empty());
        assert!(proof.is_genuinely_proven());
        for side in [&proof.trust_ir_expr, &proof.aarch64_expr] {
            assert_eq!(side.free_vars(), vec!["a".to_string()]);
            assert_eq!(side.sort(), SmtSort::BitVec(width));
        }
        for value in samples(width) {
            let expected = value & !(1u64 << (width - 1));
            assert_eq!(
                proof.trust_ir_expr.eval(&env(value)),
                EvalResult::Bv(expected)
            );
            assert_eq!(
                proof.aarch64_expr.eval(&env(value)),
                EvalResult::Bv(expected)
            );
        }
        let smt = proof.to_smt2();
        assert!(smt.contains(&format!("(declare-const a (_ BitVec {width}))")));
        assert!(smt.contains("(bvand a "));
        assert!(smt.contains("(concat "));
    }
}

#[test]
fn changed_sign_payload_or_source_operand_has_a_concrete_counterexample() {
    for (width, proof) in [(32, proof_fabs_f32()), (64, proof_fabs_f64())] {
        let source = &proof.trust_ir_expr;
        let wrong_sign = SmtExpr::var("a", width);
        assert_ne!(
            source.eval(&env(1 << (width - 1))),
            wrong_sign.eval(&env(1 << (width - 1)))
        );
        let dropped_payload =
            SmtExpr::bv_const(0, 2).concat(SmtExpr::var("a", width).extract(width - 3, 0));
        assert_ne!(
            source.eval(&env(1 << (width - 2))),
            dropped_payload.eval(&env(1 << (width - 2)))
        );
        let wrong_operand = SmtExpr::bv_const(0, width);
        assert_ne!(source.eval(&env(1)), wrong_operand.eval(&env(1)));
        for wrong in [wrong_sign, dropped_payload, wrong_operand] {
            let mut changed = proof.clone();
            changed.aarch64_expr = wrong;
            assert!(matches!(
                verify_fp_by_evaluation(&changed),
                VerificationResult::Invalid { .. }
            ));
        }
        assert!(matches!(
            verify_fp_by_evaluation(&proof),
            VerificationResult::Valid
        ));
    }
}

#[cfg(target_arch = "aarch64")]
#[test]
fn full_bit_models_match_executed_aarch64_fabs_including_nan_payloads() {
    let mut compared = 0;
    for width in [32, 64] {
        let proof = if width == 32 {
            proof_fabs_f32()
        } else {
            proof_fabs_f64()
        };
        for input in samples(width) {
            let actual = if width == 32 {
                let mut value = f32::from_bits(input as u32);
                // SAFETY: FABS reads and writes only the allocated SIMD register.
                // Every f32 bit pattern is valid, including signaling NaNs.
                unsafe {
                    core::arch::asm!("fabs {value:s}, {value:s}", value = inout(vreg) value, options(pure, nomem, nostack));
                }
                u64::from(value.to_bits())
            } else {
                let mut value = f64::from_bits(input);
                // SAFETY: FABS has no memory operands; all f64 encodings are valid.
                unsafe {
                    core::arch::asm!("fabs {value:d}, {value:d}", value = inout(vreg) value, options(pure, nomem, nostack));
                }
                value.to_bits()
            };
            assert_eq!(
                proof.aarch64_expr.eval(&env(input)),
                EvalResult::Bv(actual),
                "width {width}, bits {input:#x}"
            );
            compared += 1;
        }
    }
    println!("executed AArch64 FABS comparisons: {compared}");
}
