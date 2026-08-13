// trust-cg-verify/tests/reconstruction_wasm.rs — stack-machine operand-
// reconstruction refutation suite (WebAssembly scalar value ops), task #71.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// MIRROR of tests/reconstruction_riscv.rs for the STACK-MACHINE wasm backend.
// These tests are the PROOF THAT THE MECHANISM HAS CONTENT for wasm. The deleted
// static wasm scalar-ALU/divrem/bitwise/float proofs built BOTH sides from the
// same hand-written encoders, so they were structurally X==X and the strict gate
// credits them ZERO — a wrong opcode byte could never refute them. The
// reconstruction path rebuilds the MACHINE side by DECODING the REAL emitted
// opcode BYTE over fresh symbolic VALUE-STACK operands, so:
//
//   (a) a correct i32.add reconstructs to bvadd==bvadd and is credited GENUINELY
//       (provenance Reconstructed), even though the two sides happen to be equal;
//   (b) injecting a WRONG opcode byte (i32.add intended but i32.sub 0x6b decoded)
//       ⇒ REFUTE;
//   (c) wiring a non-commutative op (sub / shift / comparison) with SWAPPED
//       value-stack operands ⇒ REFUTE; commutative families (add/mul/and/or/xor)
//       cannot catch a swap — documented;
//   (d) the reconstructed path performs NO `name.contains` lookup (anti-f81e45b);
//   (e) the shift `amount < width` precondition is LOAD-BEARING (#57): strip it
//       and a shift by exactly width REFUTES.
//
// (b)/(c) construct the BUGGY obligation with the very same public encoders the
// reconstructor uses internally — `encode_trust_ir_*` for the source side and the
// `wasm_semantics::encode_*` for the machine side — so they test the exact
// source-vs-machine comparison the mechanism performs. The opcode BYTE channel is
// exercised directly via `decode_int_binop` (a wrong byte decodes to a different
// op ⇒ a structurally different machine expr ⇒ REFUTE).

use trust_cg_ir::WasmOpcode;

use trust_cg_verify::lowering_proof::MachineSideProvenance;
use trust_cg_verify::smt::SmtExpr;
use trust_cg_verify::trust_ir_semantics::{
    encode_trust_ir_binop, encode_trust_ir_bitcast, encode_trust_ir_bitwise_binop,
    encode_trust_ir_ctpop, encode_trust_ir_cttz, encode_trust_ir_fcvt_from_sint,
    encode_trust_ir_fcvt_from_uint, encode_trust_ir_fcvt_to_sint, encode_trust_ir_icmp,
    encode_trust_ir_shift,
};
use trust_cg_verify::verify::VerificationResult;
use trust_cg_verify::wasm_semantics::{
    WasmAluOp, WasmConvertOp, WasmPopcntOp, WasmReinterpretOp, WasmTruncSatOp, decode_convert,
    decode_int_binop, decode_popcnt, decode_reinterpret, decode_trunc_sat, encode_add, encode_and,
    encode_convert_s, encode_convert_u, encode_lt_s, encode_lt_u, encode_reinterpret, encode_shl,
    encode_shr_u, encode_sub, encode_trunc_sat_s,
};
use trust_cg_verify::{
    ProofObligation, WasmISelInst, reconstruct_wasm_alu_obligation,
    representative_wasm_reconstructable_inst, verify_by_evaluation,
};

use trust_cg_lower::instructions::{IntCC, Opcode};
use trust_cg_lower::types::Type;

// ---------------------------------------------------------------------------
// (a) Correct reconstruction: Valid + Reconstructed provenance
// ---------------------------------------------------------------------------

/// The full reconstructable scalar surface reconstructs Valid + Reconstructed.
#[test]
fn all_reconstructable_scalar_opcodes_reconstruct_valid() {
    // The exhaustive reconstructable set (matches classify_wasm EmittableNeedsProof).
    let ops = [
        // int ALU i32/i64
        WasmOpcode::I32Add,
        WasmOpcode::I64Add,
        WasmOpcode::I32Sub,
        WasmOpcode::I64Sub,
        WasmOpcode::I32Mul,
        WasmOpcode::I64Mul,
        WasmOpcode::I32DivS,
        WasmOpcode::I64DivS,
        WasmOpcode::I32DivU,
        WasmOpcode::I64DivU,
        WasmOpcode::I32RemS,
        WasmOpcode::I64RemS,
        WasmOpcode::I32RemU,
        WasmOpcode::I64RemU,
        WasmOpcode::I32And,
        WasmOpcode::I64And,
        WasmOpcode::I32Or,
        WasmOpcode::I64Or,
        WasmOpcode::I32Xor,
        WasmOpcode::I64Xor,
        WasmOpcode::I32Shl,
        WasmOpcode::I64Shl,
        WasmOpcode::I32ShrS,
        WasmOpcode::I64ShrS,
        WasmOpcode::I32ShrU,
        WasmOpcode::I64ShrU,
        // int cmp i32/i64
        WasmOpcode::I32Eq,
        WasmOpcode::I64Eq,
        WasmOpcode::I32Ne,
        WasmOpcode::I64Ne,
        WasmOpcode::I32LtS,
        WasmOpcode::I64LtS,
        WasmOpcode::I32LtU,
        WasmOpcode::I64LtU,
        WasmOpcode::I32GtS,
        WasmOpcode::I64GtS,
        WasmOpcode::I32GtU,
        WasmOpcode::I64GtU,
        WasmOpcode::I32LeS,
        WasmOpcode::I64LeS,
        WasmOpcode::I32LeU,
        WasmOpcode::I64LeU,
        WasmOpcode::I32GeS,
        WasmOpcode::I64GeS,
        WasmOpcode::I32GeU,
        WasmOpcode::I64GeU,
        // fp arith
        WasmOpcode::F32Add,
        WasmOpcode::F64Add,
        WasmOpcode::F32Sub,
        WasmOpcode::F64Sub,
        WasmOpcode::F32Mul,
        WasmOpcode::F64Mul,
        WasmOpcode::F32Div,
        WasmOpcode::F64Div,
        // fp cmp
        WasmOpcode::F32Eq,
        WasmOpcode::F64Eq,
        WasmOpcode::F32Ne,
        WasmOpcode::F64Ne,
        WasmOpcode::F32Lt,
        WasmOpcode::F64Lt,
        WasmOpcode::F32Gt,
        WasmOpcode::F64Gt,
        WasmOpcode::F32Le,
        WasmOpcode::F64Le,
        WasmOpcode::F32Ge,
        WasmOpcode::F64Ge,
        // fp unary
        WasmOpcode::F32Abs,
        WasmOpcode::F64Abs,
        WasmOpcode::F32Neg,
        WasmOpcode::F64Neg,
        WasmOpcode::F32Sqrt,
        WasmOpcode::F64Sqrt,
        WasmOpcode::F32Ceil,
        WasmOpcode::F64Ceil,
        WasmOpcode::F32Floor,
        WasmOpcode::F64Floor,
        WasmOpcode::F32Trunc,
        WasmOpcode::F64Trunc,
        // casts
        WasmOpcode::I32WrapI64,
        WasmOpcode::I64ExtendI32S,
        WasmOpcode::I64ExtendI32U,
        WasmOpcode::F32DemoteF64,
        WasmOpcode::F64PromoteF32,
    ];
    assert_eq!(
        ops.len(),
        83,
        "the 83 scalar ALU/cmp/fp/cast value opcodes (popcnt + reinterpret are also \
         reconstructable but are exercised by their own dedicated tests below)"
    );
    for op in ops {
        let inst = representative_wasm_reconstructable_inst(op)
            .unwrap_or_else(|| panic!("{op:?} must have a representative"));
        let ob = reconstruct_wasm_alu_obligation(&inst)
            .unwrap_or_else(|| panic!("{op:?} must reconstruct"));
        assert!(ob.is_reconstructed(), "{op:?} must be Reconstructed");
        match &ob.machine_side_provenance {
            MachineSideProvenance::Reconstructed { from_opcode, .. } => {
                assert_eq!(from_opcode, &format!("{op:?}"));
            }
            other => panic!("{op:?} expected Reconstructed, got {other:?}"),
        }
        assert!(
            matches!(verify_by_evaluation(&ob), VerificationResult::Valid),
            "{op:?} correct lowering must be Valid"
        );
    }
}

/// Div/rem reconstruction carries the trap precondition(s).
#[test]
fn divrem_reconstruction_carries_trap_preconditions() {
    // div_s carries TWO preconditions (b != 0, ¬(INT_MIN/-1)); rem_u carries one.
    let divs = reconstruct_wasm_alu_obligation(
        &representative_wasm_reconstructable_inst(WasmOpcode::I32DivS).unwrap(),
    )
    .unwrap();
    assert_eq!(divs.preconditions.len(), 2, "div_s: b!=0 AND ¬(INT_MIN/-1)");
    let remu = reconstruct_wasm_alu_obligation(
        &representative_wasm_reconstructable_inst(WasmOpcode::I32RemU).unwrap(),
    )
    .unwrap();
    assert_eq!(remu.preconditions.len(), 1, "rem_u: b!=0 only");
}

// ---------------------------------------------------------------------------
// (b) Wrong-OPCODE-BYTE refute (the stack-machine analogue of wrong isel opcode)
// ---------------------------------------------------------------------------

fn buggy_binary(
    name: &str,
    from_opcode: &str,
    trust_ir_expr: SmtExpr,
    machine_expr: SmtExpr,
    width: u32,
) -> ProofObligation {
    ProofObligation {
        name: name.to_string(),
        trust_ir_expr,
        aarch64_expr: machine_expr,
        inputs: vec![
            ("recon_a".to_string(), width),
            ("recon_b".to_string(), width),
        ],
        preconditions: vec![],
        fp_inputs: vec![],
        category: None,
        machine_side_provenance: MachineSideProvenance::Reconstructed {
            from_opcode: from_opcode.to_string(),
            arity: 2,
        },
    }
}

#[test]
fn wrong_opcode_byte_i32_sub_for_i32_add_refutes() {
    // The OPCODE-BYTE channel: i32.add (0x6a) was intended, but the emitted byte
    // is i32.sub (0x6b). Decoding 0x6b yields WasmAluOp::Sub ⇒ machine = bvsub,
    // source = bvadd ⇒ REFUTE. This is the wasm analogue of "isel emitted SUB".
    assert_eq!(
        decode_int_binop(0x6b),
        Some(WasmAluOp::Sub),
        "0x6b decodes to SUB"
    );
    let a = SmtExpr::var("recon_a", 32);
    let b = SmtExpr::var("recon_b", 32);
    // Machine side built from the DECODED wrong byte (Sub), exactly as the
    // reconstructor would if the backend emitted 0x6b for an intended add.
    let machine = match decode_int_binop(0x6b).unwrap() {
        WasmAluOp::Sub => encode_sub(a.clone(), b.clone()),
        other => panic!("unexpected decode {other:?}"),
    };
    let buggy = buggy_binary(
        "RECONSTRUCTED wasm Iadd -> i32.sub byte 0x6b (INJECTED wrong opcode byte)",
        "I32Sub",
        encode_trust_ir_binop(&Opcode::Iadd, Type::I32, a, b),
        machine,
        32,
    );
    assert!(
        matches!(
            verify_by_evaluation(&buggy),
            VerificationResult::Invalid { .. }
        ),
        "i32.sub byte for an intended add must REFUTE (bvadd != bvsub)"
    );
    assert!(buggy.is_genuinely_proven());
}

#[test]
fn wrong_opcode_byte_shr_u_for_shl_refutes() {
    // SHIFT family wrong byte: i32.shl (0x74) intended, i32.shr_u (0x76) emitted
    // ⇒ bvshl != bvlshr. Refutes EVEN WITH the in-range precondition.
    let a = SmtExpr::var("recon_a", 8);
    let amt = SmtExpr::var("recon_b", 8);
    let buggy = ProofObligation {
        name: "RECONSTRUCTED wasm Ishl -> i32.shr_u byte 0x76 (INJECTED wrong shift byte)"
            .to_string(),
        trust_ir_expr: encode_trust_ir_shift(&Opcode::Ishl, Type::I8, a.clone(), amt.clone()),
        aarch64_expr: encode_shr_u(a.clone(), amt.clone(), 8), // WRONG: bvlshr (masked)
        inputs: vec![("recon_a".to_string(), 8), ("recon_b".to_string(), 8)],
        preconditions: vec![amt.clone().bvult(SmtExpr::bv_const(8, 8))],
        fp_inputs: vec![],
        category: None,
        machine_side_provenance: MachineSideProvenance::Reconstructed {
            from_opcode: "I32ShrU".to_string(),
            arity: 2,
        },
    };
    assert!(
        matches!(
            verify_by_evaluation(&buggy),
            VerificationResult::Invalid { .. }
        ),
        "shr_u-for-shl byte must REFUTE (bvshl != bvlshr) even WITH the in-range precondition"
    );
}

#[test]
fn wrong_opcode_byte_lt_u_for_signed_lt_s_refutes() {
    // COMPARE family wrong byte: i32.lt_s (0x48, signed) intended, i32.lt_u
    // (0x49, unsigned) emitted. For -1 vs 0: signed -1 < 0 is 1, unsigned is 0.
    let a = SmtExpr::var("recon_a", 32);
    let b = SmtExpr::var("recon_b", 32);
    let buggy = ProofObligation {
        name: "RECONSTRUCTED wasm Icmp_SLT -> i32.lt_u byte 0x49 (INJECTED wrong cmp byte)"
            .to_string(),
        trust_ir_expr: encode_trust_ir_icmp(
            &IntCC::SignedLessThan,
            Type::I32,
            a.clone(),
            b.clone(),
        )
        .zero_ext(31),
        aarch64_expr: encode_lt_u(a, b), // WRONG: unsigned compare i32 result
        inputs: vec![("recon_a".to_string(), 32), ("recon_b".to_string(), 32)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: None,
        machine_side_provenance: MachineSideProvenance::Reconstructed {
            from_opcode: "I32LtU".to_string(),
            arity: 2,
        },
    };
    assert!(
        matches!(
            verify_by_evaluation(&buggy),
            VerificationResult::Invalid { .. }
        ),
        "lt_u-for-signed-lt_s byte must REFUTE (signed vs unsigned differ for negatives)"
    );
    assert!(buggy.is_genuinely_proven());
}

// ---------------------------------------------------------------------------
// (c) Wrong-WIRING refute for NON-commutative stack ops (sub / shift / compare)
// ---------------------------------------------------------------------------

#[test]
fn swapped_stack_operands_on_i32_sub_refutes() {
    // i32.sub is non-commutative: a - b != b - a. wasm consumes the deeper stack
    // operand as the minuend; swapping the binding ⇒ REFUTE.
    let a = SmtExpr::var("recon_a", 32);
    let b = SmtExpr::var("recon_b", 32);
    let buggy = buggy_binary(
        "RECONSTRUCTED wasm Isub -> i32.sub (INJECTED swapped stack wiring)",
        "I32Sub",
        encode_trust_ir_binop(&Opcode::Isub, Type::I32, a.clone(), b.clone()), // a - b
        encode_sub(b, a),                                                      // WRONG: b - a
        32,
    );
    assert!(
        matches!(
            verify_by_evaluation(&buggy),
            VerificationResult::Invalid { .. }
        ),
        "swapped i32.sub stack wiring must REFUTE (a - b != b - a)"
    );
}

#[test]
fn swapped_stack_operands_on_i32_shl_refutes() {
    // A shift is non-commutative in its operands: value << amount != amount <<
    // value. Wrong stack wiring (amount as value, value as amount) ⇒ REFUTE.
    let a = SmtExpr::var("recon_a", 8);
    let amt = SmtExpr::var("recon_b", 8);
    let buggy = ProofObligation {
        name: "RECONSTRUCTED wasm Ishl -> i32.shl (INJECTED swapped stack wiring)".to_string(),
        trust_ir_expr: encode_trust_ir_shift(&Opcode::Ishl, Type::I8, a.clone(), amt.clone()),
        aarch64_expr: encode_shl(amt.clone(), a.clone(), 8), // WRONG wiring
        inputs: vec![("recon_a".to_string(), 8), ("recon_b".to_string(), 8)],
        preconditions: vec![
            amt.clone().bvult(SmtExpr::bv_const(8, 8)),
            a.clone().bvult(SmtExpr::bv_const(8, 8)),
        ],
        fp_inputs: vec![],
        category: None,
        machine_side_provenance: MachineSideProvenance::Reconstructed {
            from_opcode: "I32Shl".to_string(),
            arity: 2,
        },
    };
    assert!(
        matches!(
            verify_by_evaluation(&buggy),
            VerificationResult::Invalid { .. }
        ),
        "swapped i32.shl stack wiring must REFUTE (value<<amt != amt<<value)"
    );
}

#[test]
fn swapped_stack_operands_on_i32_lt_s_refutes() {
    // i32.lt_s is non-commutative: (a < b) != (b < a) in general.
    let a = SmtExpr::var("recon_a", 32);
    let b = SmtExpr::var("recon_b", 32);
    let buggy = ProofObligation {
        name: "RECONSTRUCTED wasm Icmp_SLT -> i32.lt_s (INJECTED swapped stack wiring)".to_string(),
        trust_ir_expr: encode_trust_ir_icmp(
            &IntCC::SignedLessThan,
            Type::I32,
            a.clone(),
            b.clone(),
        )
        .zero_ext(31),
        aarch64_expr: encode_lt_s(b, a), // WRONG wiring: b < a
        inputs: vec![("recon_a".to_string(), 32), ("recon_b".to_string(), 32)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: None,
        machine_side_provenance: MachineSideProvenance::Reconstructed {
            from_opcode: "I32LtS".to_string(),
            arity: 2,
        },
    };
    assert!(
        matches!(
            verify_by_evaluation(&buggy),
            VerificationResult::Invalid { .. }
        ),
        "swapped i32.lt_s stack wiring must REFUTE ((a<b) != (b<a))"
    );
}

// ---------------------------------------------------------------------------
// Commutative families cannot catch an operand swap — DOCUMENTED limitation
// ---------------------------------------------------------------------------

#[test]
fn commutative_families_cannot_catch_stack_swap_by_design() {
    // DOCUMENTED LIMITATION: add/mul/and/or/xor are commutative, so a swapped-
    // stack-operand lowering still proves Valid — exactly like the register
    // backends. The non-commutative sub/shift/compare (above) are the wiring
    // discriminators. Stated explicitly so nobody reads the passing swap as a hole.
    let a = SmtExpr::var("recon_a", 32);
    let b = SmtExpr::var("recon_b", 32);

    let add_swapped = buggy_binary(
        "RECONSTRUCTED wasm Iadd -> i32.add (swapped, still valid: commutative)",
        "I32Add",
        encode_trust_ir_binop(&Opcode::Iadd, Type::I32, a.clone(), b.clone()),
        encode_add(b.clone(), a.clone()),
        32,
    );
    assert!(matches!(
        verify_by_evaluation(&add_swapped),
        VerificationResult::Valid
    ));

    let and_swapped = buggy_binary(
        "RECONSTRUCTED wasm Band -> i32.and (swapped, still valid: commutative)",
        "I32And",
        encode_trust_ir_bitwise_binop(&Opcode::Band, Type::I32, a.clone(), b.clone()),
        encode_and(b, a),
        32,
    );
    assert!(matches!(
        verify_by_evaluation(&and_swapped),
        VerificationResult::Valid
    ));
}

// ---------------------------------------------------------------------------
// (e) The shift amount<width precondition is LOAD-BEARING (#57)
// ---------------------------------------------------------------------------

#[test]
fn shift_precondition_is_load_bearing_strip_it_and_it_refutes() {
    // #57: the amount<width precondition is GENUINELY load-bearing, not cosmetic.
    // At width 8 (exhaustive), WITH the precondition the in-range equivalence is
    // Valid; WITHOUT it, a shift by exactly width (8 & 7 == 0 under wasm's mask vs
    // clamp-to-0 in the in-house SMT bvshl source) is a counterexample ⇒ stripping
    // it REFUTES. The machine side is the FAITHFUL amount-masked wasm encoder.
    let a = SmtExpr::var("recon_a", 8);
    let amt = SmtExpr::var("recon_b", 8);
    let mk = |pre: Vec<SmtExpr>| ProofObligation {
        name: "wasm shift8 load-bearing demo".to_string(),
        trust_ir_expr: encode_trust_ir_shift(&Opcode::Ishl, Type::I8, a.clone(), amt.clone()),
        aarch64_expr: encode_shl(a.clone(), amt.clone(), 8),
        inputs: vec![("recon_a".to_string(), 8), ("recon_b".to_string(), 8)],
        preconditions: pre,
        fp_inputs: vec![],
        category: None,
        machine_side_provenance: MachineSideProvenance::Reconstructed {
            from_opcode: "I32Shl".to_string(),
            arity: 2,
        },
    };
    let with_pre = mk(vec![amt.clone().bvult(SmtExpr::bv_const(8, 8))]);
    let without_pre = mk(vec![]);
    assert!(
        matches!(verify_by_evaluation(&with_pre), VerificationResult::Valid),
        "WITH amount<width precondition: in-range equivalence is Valid"
    );
    assert!(
        matches!(
            verify_by_evaluation(&without_pre),
            VerificationResult::Invalid { .. }
        ),
        "WITHOUT the precondition the shift-by-width case REFUTES — load-bearing (#57)"
    );
}

// ---------------------------------------------------------------------------
// (d) Anti-f81e45b: the reconstructed path does NO name.contains lookup
// ---------------------------------------------------------------------------

#[test]
fn reconstructed_path_does_no_name_contains_lookup() {
    // The wasm reconstruction module must not perform a `name.contains` lookup to
    // bind the source op or the machine encoder — the binding is a TYPED,
    // EXHAUSTIVE opcode match (`opcode_to_source_op`) plus a typed decode of the
    // real opcode byte. Asserted structurally over the whole source file.
    let src = include_str!("../src/wasm_function_verifier.rs");
    assert!(
        !src.contains(".contains("),
        "the wasm reconstruction path must NOT use any .contains() name lookup \
         (anti-f81e45b): the opcode->source-op binding is a typed exhaustive match \
         and the machine side is a typed decode of the real opcode byte"
    );
    assert!(
        src.contains("fn opcode_to_source_op("),
        "reconstruction must resolve the source op via the typed matcher"
    );
    // And it must decode the REAL opcode byte (the stack-machine honest channel).
    assert!(
        src.contains("opcode_byte()") && src.contains("decode_int_binop"),
        "reconstruction must decode the real emitted opcode byte"
    );
}

// ---------------------------------------------------------------------------
// Fail-closed: non-reconstructable opcodes (structural / SIMD)
// ---------------------------------------------------------------------------

#[test]
fn non_reconstructable_opcodes_do_not_reconstruct() {
    // Structural control flow / memory / locals / calls / constants are NOT
    // reconstructable: representative_* returns None and reconstruct returns None.
    // (popcnt + reinterpret + the float<->int CONVERSIONS are reconstructable now —
    // see the dedicated tests. Only SIMD/v128 remains DEFERRED pending lane-vector
    // semantics, surfaced by the gate as DeferredUnfaithfulModel.)
    for op in [
        WasmOpcode::Block,
        WasmOpcode::Loop,
        WasmOpcode::Br,
        WasmOpcode::If,
        WasmOpcode::I32Load,
        WasmOpcode::I32Store,
        WasmOpcode::LocalGet,
        WasmOpcode::LocalSet,
        WasmOpcode::Call,
        WasmOpcode::CallIndirect,
        WasmOpcode::I32Const,
        // f.min/f.max never selected
        WasmOpcode::F32Min,
        // STRUCTURAL v128 (memory + materialization families) — NOT value ops, so
        // NOT reconstructable. (The 4 v128 LANE-WISE value ops i32x4.add/mul,
        // f32x4.add/mul ARE reconstructable — see mod simd_v128.)
        WasmOpcode::V128Load,
        WasmOpcode::V128Store,
        WasmOpcode::V128Const,
    ] {
        assert!(
            representative_wasm_reconstructable_inst(op).is_none(),
            "{op:?} must NOT be reconstructable"
        );
        let inst = WasmISelInst::new(op, 32);
        assert!(
            reconstruct_wasm_alu_obligation(&inst).is_none(),
            "{op:?} must not reconstruct an obligation"
        );
    }
}

// ---------------------------------------------------------------------------
// float<->int CONVERSIONS — now FAITHFULLY reconstructed (the deferred-conversion
// fix): rounding / signedness / saturation are modeled, so a WRONG lowering
// (signed-for-unsigned, saturating-for-wrapping, NaN->wrap) REFUTES.
// ---------------------------------------------------------------------------

/// All 16 float<->int conversions (8 int->FP convert + 8 saturating FP->int
/// trunc_sat) reconstruct Valid with Reconstructed provenance.
#[test]
fn all_conversions_reconstruct_valid() {
    let ops = [
        // int->FP convert (signed + unsigned, i32/i64 source, f32/f64 dest).
        WasmOpcode::F32ConvertI32S,
        WasmOpcode::F32ConvertI32U,
        WasmOpcode::F32ConvertI64S,
        WasmOpcode::F32ConvertI64U,
        WasmOpcode::F64ConvertI32S,
        WasmOpcode::F64ConvertI32U,
        WasmOpcode::F64ConvertI64S,
        WasmOpcode::F64ConvertI64U,
        // saturating FP->int trunc_sat (signed + unsigned, f32/f64 source, i32/i64 dest).
        WasmOpcode::I32TruncSatF32S,
        WasmOpcode::I32TruncSatF32U,
        WasmOpcode::I32TruncSatF64S,
        WasmOpcode::I32TruncSatF64U,
        WasmOpcode::I64TruncSatF32S,
        WasmOpcode::I64TruncSatF32U,
        WasmOpcode::I64TruncSatF64S,
        WasmOpcode::I64TruncSatF64U,
    ];
    assert_eq!(
        ops.len(),
        16,
        "8 int->FP convert + 8 saturating FP->int trunc_sat"
    );
    for op in ops {
        let inst = representative_wasm_reconstructable_inst(op)
            .unwrap_or_else(|| panic!("{op:?} must be reconstructable"));
        let ob = reconstruct_wasm_alu_obligation(&inst)
            .unwrap_or_else(|| panic!("{op:?} must reconstruct"));
        assert!(ob.is_reconstructed(), "{op:?} must be Reconstructed");
        assert!(
            matches!(verify_by_evaluation(&ob), VerificationResult::Valid),
            "{op:?} correct conversion lowering must be Valid"
        );
    }
}

/// Decoders are the typed honest channel: the convert bytes / trunc_sat sub-indices
/// map to the right (width, signedness) and a non-convert byte fails closed.
#[test]
fn conversion_decoders_are_typed_and_fail_closed() {
    assert_eq!(
        decode_convert(0xb2),
        Some(WasmConvertOp {
            src_width: 32,
            fp_width: 32,
            signed: true
        }),
        "0xb2 = f32.convert_i32_s"
    );
    assert_eq!(
        decode_convert(0xba),
        Some(WasmConvertOp {
            src_width: 64,
            fp_width: 64,
            signed: false
        }),
        "0xba = f64.convert_i64_u"
    );
    assert_eq!(
        decode_convert(0x6a),
        None,
        "i32.add byte must NOT decode as a convert"
    );
    assert_eq!(
        decode_trunc_sat(0xfc, 0),
        Some(WasmTruncSatOp {
            fp_width: 32,
            int_width: 32,
            signed: true
        }),
        "0xfc/0 = i32.trunc_sat_f32_s"
    );
    assert_eq!(
        decode_trunc_sat(0xfc, 7),
        Some(WasmTruncSatOp {
            fp_width: 64,
            int_width: 64,
            signed: false
        }),
        "0xfc/7 = i64.trunc_sat_f64_u"
    );
    assert_eq!(
        decode_trunc_sat(0x6a, 0),
        None,
        "non-0xfc prefix must fail closed"
    );
    assert_eq!(
        decode_trunc_sat(0xfc, 99),
        None,
        "undefined sub-index must fail closed"
    );
}

/// REFUTE: a SIGNED-for-UNSIGNED int->FP convert. Source intends UNSIGNED
/// (`f64.convert_i32_u`, zero-extend), machine emitted the SIGNED convert
/// (sign-extend). For an i32 with the high bit set the magnitudes differ
/// (0x80000000: unsigned 2147483648 vs signed -2147483648) ⇒ DIVERGE.
#[test]
fn signed_for_unsigned_convert_refutes() {
    let a = SmtExpr::var("recon_src", 32);
    let buggy = ProofObligation {
        name: "RECONSTRUCTED wasm FcvtFromInt_f64_i32_u -> SIGNED convert (INJECTED)".to_string(),
        // Source: UNSIGNED convert (zero-extend then to_fp).
        trust_ir_expr: encode_trust_ir_fcvt_from_uint(11, 53, a.clone(), 32),
        // Machine: the WRONG SIGNED convert (sign-extend then to_fp).
        aarch64_expr: encode_convert_s(a.clone(), 64),
        inputs: vec![("recon_src".to_string(), 32)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: None,
        machine_side_provenance: MachineSideProvenance::Reconstructed {
            from_opcode: "F64ConvertI32U".to_string(),
            arity: 1,
        },
    };
    assert!(
        matches!(
            verify_by_evaluation(&buggy),
            VerificationResult::Invalid { .. }
        ),
        "signed-for-unsigned int->FP convert must REFUTE"
    );
}

/// REFUTE: an UNSIGNED-for-SIGNED int->FP convert (the mirror direction). Source
/// intends SIGNED (`f64.convert_i32_s`), machine emitted the UNSIGNED convert.
#[test]
fn unsigned_for_signed_convert_refutes() {
    let a = SmtExpr::var("recon_src", 32);
    let buggy = ProofObligation {
        name: "RECONSTRUCTED wasm FcvtFromInt_f64_i32_s -> UNSIGNED convert (INJECTED)".to_string(),
        trust_ir_expr: encode_trust_ir_fcvt_from_sint(11, 53, a.clone()), // SIGNED intended
        aarch64_expr: encode_convert_u(a.clone(), 32, 64), // UNSIGNED machine (WRONG)
        inputs: vec![("recon_src".to_string(), 32)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: None,
        machine_side_provenance: MachineSideProvenance::Reconstructed {
            from_opcode: "F64ConvertI32S".to_string(),
            arity: 1,
        },
    };
    assert!(
        matches!(
            verify_by_evaluation(&buggy),
            VerificationResult::Invalid { .. }
        ),
        "unsigned-for-signed int->FP convert must REFUTE"
    );
}

/// REFUTE: a SATURATING-for-WRAPPING FP->int truncation. Source intends the
/// SATURATING wasm `trunc_sat` (clamp to the int range); a WRAPPING machine
/// (truncate then mask, the non-saturating semantics) DIVERGES for an out-of-range
/// input (e.g. 1e10 -> i32: saturate INT_MAX vs wrap a different masked value).
#[test]
fn saturating_for_wrapping_trunc_refutes() {
    let a = SmtExpr::var("recon_a", 64);
    let buggy = ProofObligation {
        name: "RECONSTRUCTED wasm TruncSat_i32_f64_s -> WRAPPING trunc (INJECTED)".to_string(),
        // Source: the SATURATING trunc_sat (clamp + NaN->0).
        trust_ir_expr: encode_trust_ir_fcvt_to_sint(32, a.clone()),
        // Machine: a WRAPPING fp->int (truncate-then-mask at 64 then take low 32).
        // Built from the 64-bit saturating convert masked to 32 — this WRAPS rather
        // than saturates to the 32-bit range, so it diverges for an out-of-range f64.
        aarch64_expr: encode_trunc_sat_s(a.clone(), 64).extract(31, 0),
        inputs: vec![],
        preconditions: vec![],
        fp_inputs: vec![("recon_a".to_string(), 11, 53)],
        category: None,
        machine_side_provenance: MachineSideProvenance::Reconstructed {
            from_opcode: "I32TruncSatF64S".to_string(),
            arity: 1,
        },
    };
    assert!(
        matches!(
            verify_by_evaluation(&buggy),
            VerificationResult::Invalid { .. }
        ),
        "saturating-for-wrapping FP->int trunc must REFUTE"
    );
}

/// REFUTE: NaN->0 vs NaN->wrap. wasm `trunc_sat` maps NaN to 0; a machine that
/// instead leaves NaN to wrap (here modeled as mapping it to the all-ones / -1
/// pattern a naive cast-without-NaN-guard would produce) DIVERGES on a NaN input.
/// We exercise this by comparing the faithful saturating source (NaN->0) against a
/// machine that ORs in a sentinel for NaN, so the NaN case differs.
#[test]
fn nan_to_zero_vs_wrap_refutes() {
    let a = SmtExpr::var("recon_a", 64);
    // Machine: if the input is NaN, produce 1 (a WRONG NaN result); else the
    // faithful saturating value. wasm requires NaN -> 0, so this diverges on NaN.
    let machine = SmtExpr::ite(
        a.clone().fp_is_nan(),
        SmtExpr::bv_const(1, 32),
        encode_trunc_sat_s(a.clone(), 32),
    );
    let buggy = ProofObligation {
        name: "RECONSTRUCTED wasm TruncSat_i32_f64_s -> NaN-mishandling (INJECTED)".to_string(),
        trust_ir_expr: encode_trust_ir_fcvt_to_sint(32, a.clone()), // NaN -> 0 (faithful)
        aarch64_expr: machine,                                      // NaN -> 1 (WRONG)
        inputs: vec![],
        preconditions: vec![],
        fp_inputs: vec![("recon_a".to_string(), 11, 53)],
        category: None,
        machine_side_provenance: MachineSideProvenance::Reconstructed {
            from_opcode: "I32TruncSatF64S".to_string(),
            arity: 1,
        },
    };
    assert!(
        matches!(
            verify_by_evaluation(&buggy),
            VerificationResult::Invalid { .. }
        ),
        "NaN->nonzero (instead of wasm's NaN->0) must REFUTE"
    );
}

// ---------------------------------------------------------------------------
// popcnt — RECONSTRUCTED (faithful ctpop); popcnt-for-cttz REFUTES
// ---------------------------------------------------------------------------

/// popcnt reconstructs Valid + Reconstructed provenance for both widths.
#[test]
fn popcnt_reconstructs_valid() {
    for op in [WasmOpcode::I32Popcnt, WasmOpcode::I64Popcnt] {
        let inst = representative_wasm_reconstructable_inst(op)
            .unwrap_or_else(|| panic!("{op:?} must be reconstructable"));
        let ob = reconstruct_wasm_alu_obligation(&inst)
            .unwrap_or_else(|| panic!("{op:?} must reconstruct"));
        assert!(ob.is_reconstructed(), "{op:?} must be Reconstructed");
        assert!(
            matches!(verify_by_evaluation(&ob), VerificationResult::Valid),
            "{op:?} correct popcnt lowering must be Valid"
        );
    }
}

/// A non-popcnt byte does not decode as popcnt ⇒ reconstruction fails closed
/// (no fake credit). The popcnt decode is the typed honest channel.
#[test]
fn popcnt_decode_fails_closed_on_non_popcnt_byte() {
    assert_eq!(
        decode_popcnt(0x69),
        Some(WasmPopcntOp::I32),
        "0x69 decodes i32.popcnt"
    );
    assert_eq!(
        decode_popcnt(0x7b),
        Some(WasmPopcntOp::I64),
        "0x7b decodes i64.popcnt"
    );
    // i32.add (0x6a) is NOT a popcnt byte ⇒ None.
    assert_eq!(
        decode_popcnt(0x6a),
        None,
        "i32.add byte must NOT decode as popcnt"
    );
}

/// REFUTE: a popcnt-FOR-cttz machine encoder (the wrong bit-count op) diverges
/// from the trust-ir `Ctpop` reference for almost every input. Built with the very
/// same encoders the reconstructor uses — `encode_trust_ir_ctpop` (source) vs a
/// WRONG `encode_trust_ir_cttz` machine side — to test the source-vs-machine
/// comparison the mechanism performs. (popcount != trailing-zero-count, e.g.
/// popcount(0b110)=2 but cttz(0b110)=1.)
#[test]
fn wrong_bit_count_cttz_for_popcnt_refutes() {
    let a = SmtExpr::var("recon_a", 8);
    let buggy = ProofObligation {
        name: "RECONSTRUCTED wasm Ctpop_i8 -> i32.popcnt (INJECTED cttz machine side)".to_string(),
        trust_ir_expr: encode_trust_ir_ctpop(a.clone()),
        aarch64_expr: encode_trust_ir_cttz(a.clone()), // WRONG: trailing-zero-count
        inputs: vec![("recon_a".to_string(), 8)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: None,
        machine_side_provenance: MachineSideProvenance::Reconstructed {
            from_opcode: "I32Popcnt".to_string(),
            arity: 1,
        },
    };
    assert!(
        matches!(
            verify_by_evaluation(&buggy),
            VerificationResult::Invalid { .. }
        ),
        "cttz-for-popcnt must REFUTE (popcount != trailing-zero-count)"
    );
    assert!(buggy.is_genuinely_proven());
}

// ---------------------------------------------------------------------------
// reinterpret — RECONSTRUCTED (width-preserving bit-identity); wrong WIDTH REFUTES
// ---------------------------------------------------------------------------

/// reinterpret reconstructs Valid + Reconstructed provenance for all 4 forms (both
/// widths × both directions). Bit-reinterpret is a width-preserving bit copy, so a
/// correct lowering reconstructs to `a == a` Valid (credited via the Reconstructed
/// provenance + the decode/width channel, exactly like x86 cross-domain MOVD).
#[test]
fn reinterpret_reconstructs_valid() {
    for op in [
        WasmOpcode::I32ReinterpretF32,
        WasmOpcode::I64ReinterpretF64,
        WasmOpcode::F32ReinterpretI32,
        WasmOpcode::F64ReinterpretI64,
    ] {
        let inst = representative_wasm_reconstructable_inst(op)
            .unwrap_or_else(|| panic!("{op:?} must be reconstructable"));
        let ob = reconstruct_wasm_alu_obligation(&inst)
            .unwrap_or_else(|| panic!("{op:?} must reconstruct"));
        assert!(ob.is_reconstructed(), "{op:?} must be Reconstructed");
        assert!(
            matches!(verify_by_evaluation(&ob), VerificationResult::Valid),
            "{op:?} correct reinterpret lowering must be Valid (bit-identity)"
        );
    }
}

/// REFUTE: a wrong-WIDTH reinterpret byte is the reconstruction discriminator. The
/// decode maps 0xbd to the 64-bit `i64.reinterpret_f64`; feeding that byte where a
/// 32-bit `i32.reinterpret_f32` (0xbc) was intended yields a 64-bit decoded width
/// that mismatches the 32-bit operand width ⇒ the reconstructor FAILS CLOSED
/// (returns None) ⇒ no credit ⇒ REFUTE. This is the wasm analogue of x86's
/// cross-domain MOVD: the WIDTH carries the content (a same-width direction swap is
/// itself a correct no-op bit copy).
#[test]
fn wrong_width_reinterpret_byte_fails_closed() {
    // Sanity: the decode distinguishes widths.
    assert_eq!(
        decode_reinterpret(0xbc).map(WasmReinterpretOp::width),
        Some(32)
    );
    assert_eq!(
        decode_reinterpret(0xbd).map(WasmReinterpretOp::width),
        Some(64)
    );
    // A non-reinterpret byte (i32.add 0x6a) does not decode as reinterpret.
    assert_eq!(
        decode_reinterpret(0x6a),
        None,
        "i32.add byte must NOT decode as reinterpret"
    );

    // i32.reinterpret_f32 is a 32-bit operation; an instruction asserting 32-bit
    // operands but carrying the 64-bit reinterpret opcode mismatches the decoded
    // width ⇒ reconstruction returns None.
    let mismatched = WasmISelInst::new(WasmOpcode::I32ReinterpretF32, 64);
    assert!(
        reconstruct_wasm_alu_obligation(&mismatched).is_none(),
        "a 32-bit reinterpret instruction whose operand width disagrees with the decoded byte \
         width must FAIL CLOSED (no credit)"
    );
}

/// REFUTE: a reinterpret that does NOT preserve bits (e.g. a width-truncating
/// machine side) diverges from the trust-ir `Bitcast` (identity) reference. Built
/// with the same encoders the reconstructor uses: `encode_trust_ir_bitcast`
/// (source identity) vs a WRONG bit-mutating machine side.
#[test]
fn reinterpret_that_mutates_bits_refutes() {
    let a = SmtExpr::var("recon_a", 32);
    let buggy = ProofObligation {
        name: "RECONSTRUCTED wasm Bitcast_w32 -> reinterpret (INJECTED bit-mutating machine side)"
            .to_string(),
        trust_ir_expr: encode_trust_ir_bitcast(Type::I32, Type::I32, a.clone()),
        // WRONG: a reinterpret must be the IDENTITY; XOR-ing bit 0 mutates bits.
        aarch64_expr: encode_reinterpret(a.clone()).bvxor(SmtExpr::bv_const(1, 32)),
        inputs: vec![("recon_a".to_string(), 32)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: None,
        machine_side_provenance: MachineSideProvenance::Reconstructed {
            from_opcode: "I32ReinterpretF32".to_string(),
            arity: 1,
        },
    };
    assert!(
        matches!(
            verify_by_evaluation(&buggy),
            VerificationResult::Invalid { .. }
        ),
        "a bit-mutating reinterpret must REFUTE (reinterpret is the bit-identity)"
    );
    assert!(buggy.is_genuinely_proven());
}

/// The correct reinterpret machine encoder IS the bit-identity (sanity: encode
/// then compare to the operand). Pins that `encode_reinterpret` did not silently
/// become a non-identity that would vacuously pass / arbitrarily fail.
#[test]
fn reinterpret_encoder_is_bit_identity() {
    let a = SmtExpr::var("recon_a", 32);
    assert_eq!(
        encode_reinterpret(a.clone()),
        a,
        "reinterpret must be the identity"
    );
}

// ===========================================================================
// SIMD / v128 lane-wise reconstruction — refutation suite
// ===========================================================================
//
// The 4 v128 lane-wise value ops reconstruct from the REAL 0xfd SUB-opcode:
//   * i32x4.add/mul: lane-wise integer over the full 128-bit vector (a wrong
//     sub-opcode mul-for-add, or a wrong lane WIDTH i16x8 vs i32x4, REFUTES);
//   * f32x4.add/mul: one representative binary32 lane (a wrong op mul-for-add
//     REFUTES under the FP evaluator).

mod simd_v128 {
    use super::*;
    use trust_cg_verify::smt::VectorArrangement as VA;
    use trust_cg_verify::trust_ir_semantics::{
        encode_trust_ir_fp_binop, encode_trust_ir_lanewise_binop,
    };
    use trust_cg_verify::wasm_semantics::{
        encode_f32x4_add_lane, encode_f32x4_mul_lane, encode_i32x4_add, encode_i32x4_mul,
    };

    fn v128(name: &str) -> SmtExpr {
        SmtExpr::var(format!("{name}_hi"), 64).concat(SmtExpr::var(format!("{name}_lo"), 64))
    }

    fn v128_inputs() -> Vec<(String, u32)> {
        vec![
            ("a_lo".to_string(), 64),
            ("a_hi".to_string(), 64),
            ("b_lo".to_string(), 64),
            ("b_hi".to_string(), 64),
        ]
    }

    fn int_ob(name: &str, trust_ir_expr: SmtExpr, machine_expr: SmtExpr) -> ProofObligation {
        ProofObligation {
            name: name.to_string(),
            trust_ir_expr,
            aarch64_expr: machine_expr,
            inputs: v128_inputs(),
            preconditions: vec![],
            fp_inputs: vec![],
            category: None,
            machine_side_provenance: MachineSideProvenance::Reconstructed {
                from_opcode: "SIMD".to_string(),
                arity: 2,
            },
        }
    }

    fn fp_ob(name: &str, trust_ir_expr: SmtExpr, machine_expr: SmtExpr) -> ProofObligation {
        ProofObligation {
            name: name.to_string(),
            trust_ir_expr,
            aarch64_expr: machine_expr,
            inputs: vec![],
            preconditions: vec![],
            fp_inputs: vec![
                ("recon_a".to_string(), 8, 24),
                ("recon_b".to_string(), 8, 24),
            ],
            category: None,
            machine_side_provenance: MachineSideProvenance::Reconstructed {
                from_opcode: "SIMD".to_string(),
                arity: 2,
            },
        }
    }

    // -- positive: each covered SIMD lane op reconstructs Valid -----------------

    #[test]
    fn all_simd_lane_ops_reconstruct_valid() {
        for op in [
            WasmOpcode::I32x4Add,
            WasmOpcode::I32x4Mul,
            WasmOpcode::F32x4Add,
            WasmOpcode::F32x4Mul,
        ] {
            let inst = representative_wasm_reconstructable_inst(op)
                .unwrap_or_else(|| panic!("{op:?} must have a representative"));
            let ob = reconstruct_wasm_alu_obligation(&inst)
                .unwrap_or_else(|| panic!("{op:?} must reconstruct"));
            assert!(ob.is_reconstructed(), "{op:?} must be Reconstructed");
            assert!(
                matches!(verify_by_evaluation(&ob), VerificationResult::Valid),
                "{op:?} correct lane-wise lowering must be Valid"
            );
        }
    }

    // -- (b) WRONG SUB-OPCODE: i32x4.add-as-i32x4.mul refutes -------------------

    #[test]
    fn i32x4_add_as_mul_refutes() {
        let a = v128("a");
        let b = v128("b");
        // SOURCE intends lane-wise ADD; MACHINE is the i32x4.mul encoder.
        let trust_ir_expr =
            encode_trust_ir_lanewise_binop(&Opcode::Iadd, VA::S4, a.clone(), b.clone());
        let machine_expr = encode_i32x4_mul(a, b);
        let ob = int_ob(
            "RECONSTRUCTED wasm I32x4Add -> i32x4.mul sub-opcode (INJECTED wrong op)",
            trust_ir_expr,
            machine_expr,
        );
        assert!(
            !matches!(verify_by_evaluation(&ob), VerificationResult::Valid),
            "i32x4.add-as-i32x4.mul must REFUTE (lane bvadd != lane bvmul)"
        );
    }

    // -- (b) WRONG LANE WIDTH: i16x8 source vs i32x4 machine refutes ------------

    #[test]
    fn i32x4_add_wrong_lane_width_i16x8_refutes() {
        let a = v128("a");
        let b = v128("b");
        // SOURCE treats the vector as i16x8; MACHINE is i32x4.add. Carry crosses
        // the 16-bit boundary where the source has none ⇒ DIVERGE.
        let trust_ir_expr =
            encode_trust_ir_lanewise_binop(&Opcode::Iadd, VA::H8, a.clone(), b.clone());
        let machine_expr = encode_i32x4_add(a, b);
        let ob = int_ob(
            "RECONSTRUCTED wasm i16x8-Add -> i32x4.add (INJECTED wrong lane width)",
            trust_ir_expr,
            machine_expr,
        );
        assert!(
            !matches!(verify_by_evaluation(&ob), VerificationResult::Valid),
            "i16x8-add vs i32x4.add must REFUTE (carry crosses the wrong lane boundary)"
        );
    }

    // -- (b) WRONG FP OP: f32x4.add-as-f32x4.mul refutes ------------------------

    #[test]
    fn f32x4_add_as_mul_refutes() {
        let a = SmtExpr::var("recon_a", 32);
        let b = SmtExpr::var("recon_b", 32);
        // SOURCE intends per-lane FADD; MACHINE is the f32x4.mul lane encoder.
        let trust_ir_expr =
            encode_trust_ir_fp_binop(&Opcode::Fadd, Type::F32, a.clone(), b.clone());
        let machine_expr = encode_f32x4_mul_lane(a, b);
        let ob = fp_ob(
            "RECONSTRUCTED wasm F32x4Add -> f32x4.mul lane (INJECTED wrong fp op)",
            trust_ir_expr,
            machine_expr,
        );
        assert!(
            !matches!(verify_by_evaluation(&ob), VerificationResult::Valid),
            "f32x4.add-as-f32x4.mul must REFUTE (fp.add != fp.mul)"
        );
    }

    // sanity: the correct f32x4.add lane equals fp.add (pins the encoder identity).
    #[test]
    fn f32x4_add_lane_is_fp_add() {
        let a = SmtExpr::var("recon_a", 32);
        let b = SmtExpr::var("recon_b", 32);
        let trust_ir_expr =
            encode_trust_ir_fp_binop(&Opcode::Fadd, Type::F32, a.clone(), b.clone());
        let machine_expr = encode_f32x4_add_lane(a, b);
        let ob = fp_ob(
            "f32x4.add lane == fp.add (sanity)",
            trust_ir_expr,
            machine_expr,
        );
        assert!(
            matches!(verify_by_evaluation(&ob), VerificationResult::Valid),
            "correct f32x4.add lane must equal fp.add"
        );
    }
}
