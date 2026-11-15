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
        // f.min/f.max are emitted only inside the FMin/FMax sequence, whose
        // evidence is the emitted body (wasm_float_binop_proofs), never a
        // per-opcode reconstruction: the bare opcode propagates NaN.
        WasmOpcode::F32Min,
        WasmOpcode::F64Max,
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

// ---------------------------------------------------------------------------
// copysign — reconstructed over the operands' IEEE-754 BIT PATTERNS
// ---------------------------------------------------------------------------

mod copysign {
    use super::*;
    use trust_cg_verify::trust_ir_semantics::encode_trust_ir_fcopysign;
    use trust_cg_verify::wasm_semantics::{WasmCopysignOp, decode_copysign, encode_copysign};

    fn refutes(ob: &ProofObligation) -> bool {
        matches!(verify_by_evaluation(ob), VerificationResult::Invalid { .. })
    }

    fn sign(width: u32) -> SmtExpr {
        SmtExpr::bv_const(1u64 << (width - 1), width)
    }

    /// Both widths reconstruct Valid, Reconstructed, from their real bytes.
    #[test]
    fn copysign_reconstructs_valid_at_both_widths() {
        for (op, width) in [(WasmOpcode::F32Copysign, 32), (WasmOpcode::F64Copysign, 64)] {
            let inst = representative_wasm_reconstructable_inst(op)
                .unwrap_or_else(|| panic!("{op:?} must have a representative"));
            assert_eq!(inst.operand_width_bits, width);
            let ob = reconstruct_wasm_alu_obligation(&inst)
                .unwrap_or_else(|| panic!("{op:?} must reconstruct"));
            assert!(ob.is_reconstructed());
            assert_eq!(ob.inputs.len(), 2, "two bit-pattern leaves");
            assert!(
                ob.fp_inputs.is_empty(),
                "compared as bit patterns, not FP values"
            );
            assert!(
                matches!(verify_by_evaluation(&ob), VerificationResult::Valid),
                "{op:?} must be Valid"
            );
        }
    }

    /// The decoder is typed: each byte names its width, a byte of the other
    /// width fails the reconstruction closed, and a neighbouring FP byte is not
    /// copysign.
    #[test]
    fn copysign_decode_is_typed_and_fails_closed() {
        assert_eq!(decode_copysign(0x98), Some(WasmCopysignOp::F32));
        assert_eq!(decode_copysign(0xa6), Some(WasmCopysignOp::F64));
        for byte in [0x8b, 0x8c, 0x96, 0x97, 0x99, 0x9a, 0xa4, 0xa5] {
            assert_eq!(decode_copysign(byte), None, "0x{byte:02x}");
        }
        assert!(
            reconstruct_wasm_alu_obligation(&WasmISelInst::new(WasmOpcode::F32Copysign, 64))
                .is_none(),
            "an f32.copysign byte at 64-bit operands must fail closed"
        );
        assert!(
            reconstruct_wasm_alu_obligation(&WasmISelInst::new(WasmOpcode::F64Copysign, 32))
                .is_none(),
            "an f64.copysign byte at 32-bit operands must fail closed"
        );
    }

    /// REFUTE: the operands swapped — `copysign(sign, magnitude)`.
    #[test]
    fn swapped_operands_refute() {
        for width in [32, 64] {
            let a = SmtExpr::var("recon_a", width);
            let b = SmtExpr::var("recon_b", width);
            let ob = buggy_binary(
                "FCopySign -> copysign with swapped operands (INJECTED)",
                "Copysign",
                encode_trust_ir_fcopysign(a.clone(), b.clone()),
                encode_copysign(b, a, width),
                width,
            );
            assert!(
                refutes(&ob),
                "swapped copysign operands must REFUTE at {width}"
            );
        }
    }

    /// REFUTE: `fabs` of the magnitude operand in place of copysign.
    #[test]
    fn fabs_for_copysign_refutes() {
        for width in [32, 64] {
            let a = SmtExpr::var("recon_a", width);
            let b = SmtExpr::var("recon_b", width);
            let all = SmtExpr::bv_const(u64::MAX >> (64 - width), width);
            let fabs = a.clone().bvand(sign(width).bvxor(all));
            let ob = buggy_binary(
                "FCopySign -> fabs (INJECTED)",
                "Copysign",
                encode_trust_ir_fcopysign(a, b),
                fabs,
                width,
            );
            assert!(refutes(&ob), "fabs for copysign must REFUTE at {width}");
        }
    }

    /// REFUTE: `fneg` of the magnitude operand in place of copysign.
    #[test]
    fn fneg_for_copysign_refutes() {
        for width in [32, 64] {
            let a = SmtExpr::var("recon_a", width);
            let b = SmtExpr::var("recon_b", width);
            let fneg = a.clone().bvxor(sign(width));
            let ob = buggy_binary(
                "FCopySign -> fneg (INJECTED)",
                "Copysign",
                encode_trust_ir_fcopysign(a, b),
                fneg,
                width,
            );
            assert!(refutes(&ob), "fneg for copysign must REFUTE at {width}");
        }
    }

    /// REFUTE: a machine side that replaces a NaN magnitude by the canonical
    /// NaN (keeping only the transferred sign). trust-ir copySign keeps the
    /// payload, and the bit-pattern obligation sees the difference, which an
    /// NaN-equals-NaN FP comparison would not.
    #[test]
    fn canonicalizing_a_nan_payload_refutes() {
        let width = 32;
        let a = SmtExpr::var("recon_a", width);
        let b = SmtExpr::var("recon_b", width);
        let exp = SmtExpr::bv_const(0x7f80_0000, width);
        let frac = SmtExpr::bv_const(0x007f_ffff, width);
        let is_nan = a.clone().bvand(exp.clone()).eq_expr(exp).and_expr(
            a.clone()
                .bvand(frac)
                .eq_expr(SmtExpr::bv_const(0, width))
                .not_expr(),
        );
        let canonical = SmtExpr::bv_const(0x7fc0_0000, width).bvor(b.clone().bvand(sign(width)));
        let machine = SmtExpr::ite(
            is_nan,
            canonical,
            encode_copysign(a.clone(), b.clone(), width),
        );
        let ob = buggy_binary(
            "FCopySign -> copysign that canonicalizes a NaN magnitude (INJECTED)",
            "F32Copysign",
            encode_trust_ir_fcopysign(a, b),
            machine,
            width,
        );
        assert!(refutes(&ob), "a NaN-canonicalizing copysign must REFUTE");
    }

    /// The captured emitted bodies fix the operand order the representative
    /// reconstruction assumes (magnitude deeper than sign): the body credit
    /// stands for both widths, and swapping the body's operands refutes.
    #[test]
    fn copysign_body_credit_stands_and_its_controls_refute() {
        use trust_cg_verify::wasm_float_binop_proofs::{
            EMITTED_FLOAT_BINOP_BODIES, float_binop_body_discharges_valid,
            float_binop_credit_failures,
        };
        for byte in [0x98u8, 0xa6] {
            assert!(float_binop_body_discharges_valid(byte), "0x{byte:02x}");
            assert!(float_binop_credit_failures(byte, EMITTED_FLOAT_BINOP_BODIES).is_empty());
        }
    }
}

// ---------------------------------------------------------------------------
// f.min / f.max — credited by the emitted FMin/FMax BODY, never per opcode
// ---------------------------------------------------------------------------

mod fminmax_body {
    use trust_cg_verify::wasm_float_binop_proofs::{
        EMITTED_FLOAT_BINOP_BODIES, EmittedFloatBinopBody, FloatBinopControl, FloatBinopKind,
        InputClass, NanChoice, TieReading, check_float_binop_body,
        float_binop_body_discharges_valid, float_binop_credit_failures, run_float_binop_body,
        trust_ir_float_binop_allows,
    };

    fn body(kind: FloatBinopKind, width: u32) -> &'static [u8] {
        EMITTED_FLOAT_BINOP_BODIES
            .iter()
            .find(|(k, w, _)| *k == kind && *w == width)
            .map(|(_, _, e)| *e)
            .expect("captured")
    }

    /// The four rows credit, and every control of every row refutes at its
    /// stated input class (the hook itself demands that).
    #[test]
    fn min_max_rows_credit_with_every_control_refuting() {
        for byte in [0x96u8, 0x97, 0xa4, 0xa5] {
            let failures = float_binop_credit_failures(byte, EMITTED_FLOAT_BINOP_BODIES);
            assert!(failures.is_empty(), "0x{byte:02x}: {failures:#?}");
            assert!(float_binop_body_discharges_valid(byte));
        }
        // Not a float binop row.
        assert!(!float_binop_body_discharges_valid(0x92));
    }

    /// The body's semantics on the cases trust-ir pins: a lone NaN yields the
    /// other operand bit-exactly under every wasm NaN choice, two NaNs yield a
    /// NaN, and the signed-zero tie yields wasm's `-0.0` for min / `+0.0` for
    /// max, which the contract admits (either operand).
    #[test]
    fn body_semantics_at_the_pinned_cases() {
        let (qnan, snan) = (0x7fc0_0000u64, 0xff80_0011u64);
        let (neg_zero, one) = (0x8000_0000u64, 0x3f80_0000u64);
        for nan in NanChoice::ALL {
            let min = body(FloatBinopKind::Min, 32);
            assert_eq!(run_float_binop_body(min, 32, qnan, one, nan), Ok(one));
            assert_eq!(run_float_binop_body(min, 32, one, snan, nan), Ok(one));
            let both = run_float_binop_body(min, 32, qnan, snan, nan).expect("runs");
            assert_eq!(both, snan, "two NaNs: the body returns b, a NaN");
            assert_eq!(
                run_float_binop_body(min, 32, 0, neg_zero, nan),
                Ok(neg_zero)
            );
            assert_eq!(
                run_float_binop_body(min, 32, neg_zero, 0, nan),
                Ok(neg_zero)
            );
            let max = body(FloatBinopKind::Max, 32);
            assert_eq!(run_float_binop_body(max, 32, 0, neg_zero, nan), Ok(0));
            assert_eq!(run_float_binop_body(max, 32, neg_zero, 0, nan), Ok(0));
        }
        assert!(
            trust_ir_float_binop_allows(
                FloatBinopKind::Min,
                32,
                neg_zero,
                0,
                neg_zero,
                TieReading::EitherOperand
            )
            .is_ok()
        );
    }

    /// The tie is REACHED: pinned to the second operand, the real body refutes
    /// at the signed-zero tie and nowhere else.
    #[test]
    fn a_pinned_tie_reading_refutes_only_at_the_tie() {
        for (kind, width) in [
            (FloatBinopKind::Min, 32),
            (FloatBinopKind::Max, 32),
            (FloatBinopKind::Min, 64),
            (FloatBinopKind::Max, 64),
        ] {
            let v =
                check_float_binop_body(kind, width, body(kind, width), TieReading::SecondOperand);
            assert_eq!(
                v.refuted_classes.into_iter().collect::<Vec<_>>(),
                vec![InputClass::SignedZeroTie],
                "{kind:?} f{width}"
            );
        }
    }

    /// The hook refuses a doctored corpus: a body with the opposite op, a
    /// missing body, and a duplicated body.
    #[test]
    fn the_hook_refuses_a_doctored_corpus() {
        let mut swapped: Vec<EmittedFloatBinopBody> = EMITTED_FLOAT_BINOP_BODIES.to_vec();
        let at = swapped
            .iter()
            .position(|(k, w, _)| *k == FloatBinopKind::Min && *w == 32)
            .expect("captured");
        swapped[at].2 = body(FloatBinopKind::Max, 32);
        assert!(!float_binop_credit_failures(0x96, &swapped).is_empty());

        let missing: Vec<EmittedFloatBinopBody> = EMITTED_FLOAT_BINOP_BODIES
            .iter()
            .copied()
            .filter(|(k, w, _)| !(*k == FloatBinopKind::Max && *w == 64))
            .collect();
        assert!(!float_binop_credit_failures(0xa5, &missing).is_empty());

        let mut doubled: Vec<EmittedFloatBinopBody> = EMITTED_FLOAT_BINOP_BODIES.to_vec();
        doubled.push(doubled[at]);
        assert!(!float_binop_credit_failures(0x96, &doubled).is_empty());
    }

    /// Each min/max control, built from the captured body, refutes at its
    /// stated class.
    #[test]
    fn each_min_max_control_refutes_at_its_stated_class() {
        for (kind, width) in [
            (FloatBinopKind::Min, 32),
            (FloatBinopKind::Max, 32),
            (FloatBinopKind::Min, 64),
            (FloatBinopKind::Max, 64),
        ] {
            for control in FloatBinopControl::ALL {
                if !control.applies_to(kind) {
                    continue;
                }
                let (mutated, tie) = control
                    .build(kind, width, body(kind, width))
                    .unwrap_or_else(|| panic!("{control:?} builds on {kind:?} f{width}"));
                let v = check_float_binop_body(kind, width, &mutated, tie);
                let class = control
                    .stated_class()
                    .expect("min/max controls state a class");
                assert!(
                    v.refusal.is_none() && v.refuted_classes.contains(&class),
                    "{control:?} on {kind:?} f{width}: {v:#?}"
                );
            }
        }
    }
}

// ---------------------------------------------------------------------------
// The decoded byte is the byte the backend writes
// ---------------------------------------------------------------------------

/// Every reconstruction decodes `WasmOpcode::opcode_byte()` (and, for a
/// `0xfc` form, `trunc_sat_sub_opcode()` / `bulk_memory_sub_opcode()`), while
/// the wasm encoder writes its own `trust_cg_codegen::wasm::encode::op`
/// constants and never consults that table. A disagreement (say
/// `I32_ROTL = 0x78`, or `I32_TRUNC_SAT_F64_S = 3`) would emit one opcode for
/// every instance while the credit stays green on the other, so the two tables
/// are compared here: every single-byte `WasmOpcode` against the encoder
/// constant of the same name, and every `0xfc` form as the FULL (prefix,
/// sub-index) pair — the sub-index as the value AND as the LEB128 bytes the
/// encoder writes after the prefix. Every reconstructable opcode must be in one
/// of the two comparisons, and so must every emitted `0xfc` form. The `0xfd`
/// SIMD forms have no encoder constant: the lowerer never selects a v128 value.
#[test]
fn decoded_opcode_bytes_match_the_encoder_constants() {
    use WasmOpcode as O;
    use trust_cg_codegen::wasm::encode::op;
    use trust_cg_verify::coverage_gate::ALL_WASM_OPCODES;

    let single_byte: &[(WasmOpcode, u8)] = &[
        (O::I32Add, op::I32_ADD),
        (O::I64Add, op::I64_ADD),
        (O::I32Sub, op::I32_SUB),
        (O::I64Sub, op::I64_SUB),
        (O::I32Mul, op::I32_MUL),
        (O::I64Mul, op::I64_MUL),
        (O::I32DivS, op::I32_DIV_S),
        (O::I64DivS, op::I64_DIV_S),
        (O::I32DivU, op::I32_DIV_U),
        (O::I64DivU, op::I64_DIV_U),
        (O::I32RemS, op::I32_REM_S),
        (O::I64RemS, op::I64_REM_S),
        (O::I32RemU, op::I32_REM_U),
        (O::I64RemU, op::I64_REM_U),
        (O::I32And, op::I32_AND),
        (O::I64And, op::I64_AND),
        (O::I32Or, op::I32_OR),
        (O::I64Or, op::I64_OR),
        (O::I32Xor, op::I32_XOR),
        (O::I64Xor, op::I64_XOR),
        (O::I32Shl, op::I32_SHL),
        (O::I64Shl, op::I64_SHL),
        (O::I32ShrS, op::I32_SHR_S),
        (O::I64ShrS, op::I64_SHR_S),
        (O::I32ShrU, op::I32_SHR_U),
        (O::I64ShrU, op::I64_SHR_U),
        (O::I32Popcnt, op::I32_POPCNT),
        (O::I64Popcnt, op::I64_POPCNT),
        (O::I32Clz, op::I32_CLZ),
        (O::I64Clz, op::I64_CLZ),
        (O::I32Ctz, op::I32_CTZ),
        (O::I64Ctz, op::I64_CTZ),
        (O::I32Rotl, op::I32_ROTL),
        (O::I64Rotl, op::I64_ROTL),
        (O::I32Rotr, op::I32_ROTR),
        (O::I64Rotr, op::I64_ROTR),
        (O::I32Eq, op::I32_EQ),
        (O::I64Eq, op::I64_EQ),
        (O::I32Ne, op::I32_NE),
        (O::I64Ne, op::I64_NE),
        (O::I32LtS, op::I32_LT_S),
        (O::I64LtS, op::I64_LT_S),
        (O::I32LtU, op::I32_LT_U),
        (O::I64LtU, op::I64_LT_U),
        (O::I32GtS, op::I32_GT_S),
        (O::I64GtS, op::I64_GT_S),
        (O::I32GtU, op::I32_GT_U),
        (O::I64GtU, op::I64_GT_U),
        (O::I32LeS, op::I32_LE_S),
        (O::I64LeS, op::I64_LE_S),
        (O::I32LeU, op::I32_LE_U),
        (O::I64LeU, op::I64_LE_U),
        (O::I32GeS, op::I32_GE_S),
        (O::I64GeS, op::I64_GE_S),
        (O::I32GeU, op::I32_GE_U),
        (O::I64GeU, op::I64_GE_U),
        (O::I32Eqz, op::I32_EQZ),
        (O::I64Eqz, op::I64_EQZ),
        (O::F32Add, op::F32_ADD),
        (O::F64Add, op::F64_ADD),
        (O::F32Sub, op::F32_SUB),
        (O::F64Sub, op::F64_SUB),
        (O::F32Mul, op::F32_MUL),
        (O::F64Mul, op::F64_MUL),
        (O::F32Div, op::F32_DIV),
        (O::F64Div, op::F64_DIV),
        (O::F32Min, op::F32_MIN),
        (O::F64Min, op::F64_MIN),
        (O::F32Max, op::F32_MAX),
        (O::F64Max, op::F64_MAX),
        (O::F32Copysign, op::F32_COPYSIGN),
        (O::F64Copysign, op::F64_COPYSIGN),
        (O::F32Eq, op::F32_EQ),
        (O::F64Eq, op::F64_EQ),
        (O::F32Ne, op::F32_NE),
        (O::F64Ne, op::F64_NE),
        (O::F32Lt, op::F32_LT),
        (O::F64Lt, op::F64_LT),
        (O::F32Gt, op::F32_GT),
        (O::F64Gt, op::F64_GT),
        (O::F32Le, op::F32_LE),
        (O::F64Le, op::F64_LE),
        (O::F32Ge, op::F32_GE),
        (O::F64Ge, op::F64_GE),
        (O::F32Abs, op::F32_ABS),
        (O::F64Abs, op::F64_ABS),
        (O::F32Neg, op::F32_NEG),
        (O::F64Neg, op::F64_NEG),
        (O::F32Sqrt, op::F32_SQRT),
        (O::F64Sqrt, op::F64_SQRT),
        (O::F32Ceil, op::F32_CEIL),
        (O::F64Ceil, op::F64_CEIL),
        (O::F32Floor, op::F32_FLOOR),
        (O::F64Floor, op::F64_FLOOR),
        (O::F32Trunc, op::F32_TRUNC),
        (O::F64Trunc, op::F64_TRUNC),
        (O::I32WrapI64, op::I32_WRAP_I64),
        (O::I64ExtendI32S, op::I64_EXTEND_I32_S),
        (O::I64ExtendI32U, op::I64_EXTEND_I32_U),
        (O::F32DemoteF64, op::F32_DEMOTE_F64),
        (O::F64PromoteF32, op::F64_PROMOTE_F32),
        (O::F32ConvertI32S, op::F32_CONVERT_I32_S),
        (O::F32ConvertI32U, op::F32_CONVERT_I32_U),
        (O::F32ConvertI64S, op::F32_CONVERT_I64_S),
        (O::F32ConvertI64U, op::F32_CONVERT_I64_U),
        (O::F64ConvertI32S, op::F64_CONVERT_I32_S),
        (O::F64ConvertI32U, op::F64_CONVERT_I32_U),
        (O::F64ConvertI64S, op::F64_CONVERT_I64_S),
        (O::F64ConvertI64U, op::F64_CONVERT_I64_U),
        (O::I32ReinterpretF32, op::I32_REINTERPRET_F32),
        (O::I64ReinterpretF64, op::I64_REINTERPRET_F64),
        (O::F32ReinterpretI32, op::F32_REINTERPRET_I32),
        (O::F64ReinterpretI64, op::F64_REINTERPRET_I64),
        (O::I32Const, op::I32_CONST),
        (O::I64Const, op::I64_CONST),
        (O::F32Const, op::F32_CONST),
        (O::F64Const, op::F64_CONST),
        (O::LocalGet, op::LOCAL_GET),
        (O::LocalSet, op::LOCAL_SET),
        (O::LocalTee, op::LOCAL_TEE),
        (O::GlobalGet, op::GLOBAL_GET),
        (O::GlobalSet, op::GLOBAL_SET),
        (O::I32Load, op::I32_LOAD),
        (O::I64Load, op::I64_LOAD),
        (O::I32Store, op::I32_STORE),
        (O::I64Store, op::I64_STORE),
        (O::Unreachable, op::UNREACHABLE),
        (O::Nop, op::NOP),
        (O::Block, op::BLOCK),
        (O::Loop, op::LOOP),
        (O::If, op::IF),
        (O::Else, op::ELSE),
        (O::End, op::END),
        (O::Br, op::BR),
        (O::BrIf, op::BR_IF),
        (O::BrTable, op::BR_TABLE),
        (O::Return, op::RETURN),
        (O::Drop, op::DROP),
        (O::Select, op::SELECT),
        (O::Call, op::CALL),
        (O::CallIndirect, op::CALL_INDIRECT),
    ];
    for &(opcode, written) in single_byte {
        assert_eq!(
            opcode.opcode_byte(),
            written,
            "{opcode:?}: the reconstruction decodes {:#04x} but the encoder writes {written:#04x}",
            opcode.opcode_byte()
        );
    }
    let fc_forms: &[(WasmOpcode, u32)] = &[
        (O::I32TruncSatF32S, op::I32_TRUNC_SAT_F32_S),
        (O::I32TruncSatF32U, op::I32_TRUNC_SAT_F32_U),
        (O::I32TruncSatF64S, op::I32_TRUNC_SAT_F64_S),
        (O::I32TruncSatF64U, op::I32_TRUNC_SAT_F64_U),
        (O::I64TruncSatF32S, op::I64_TRUNC_SAT_F32_S),
        (O::I64TruncSatF32U, op::I64_TRUNC_SAT_F32_U),
        (O::I64TruncSatF64S, op::I64_TRUNC_SAT_F64_S),
        (O::I64TruncSatF64U, op::I64_TRUNC_SAT_F64_U),
        (O::MemoryCopy, op::MEMORY_COPY),
        (O::MemoryFill, op::MEMORY_FILL),
    ];
    for &(opcode, written_sub) in fc_forms {
        let decoded_sub = opcode
            .trunc_sat_sub_opcode()
            .or(opcode.bulk_memory_sub_opcode());
        let mut written = vec![op::FC_PREFIX];
        trust_cg_codegen::wasm::encode::write_uleb128(&mut written, u64::from(written_sub));
        let mut decoded = vec![opcode.opcode_byte()];
        if let Some(sub) = decoded_sub {
            trust_cg_codegen::wasm::encode::write_uleb128(&mut decoded, u64::from(sub));
        }
        assert_eq!(
            decoded, written,
            "{opcode:?}: the reconstruction decodes {decoded:02x?} (0xfc sub-index \
             {decoded_sub:?}) but the encoder writes {written:02x?}"
        );
    }
    for &opcode in ALL_WASM_OPCODES {
        let reconstructed = representative_wasm_reconstructable_inst(opcode).is_some();
        match opcode.opcode_byte() {
            0xfc => assert!(
                fc_forms.iter().any(|&(o, _)| o == opcode),
                "{opcode:?} is a 0xfc form with no (prefix, sub-index) encoder cross-check"
            ),
            0xfd => {}
            _ if reconstructed => assert!(
                single_byte.iter().any(|&(o, _)| o == opcode),
                "{opcode:?} is reconstructed from its byte but has no encoder cross-check"
            ),
            _ => {}
        }
    }
}

/// The cross-check above has teeth: a (prefix, sub-index) pair whose sub-index
/// is the other signedness (the swap of `I32_TRUNC_SAT_F64_S` and `_U`) differs
/// from the pair the reconstruction decodes, as does a sub-index of the other
/// width, while the 0xfc prefix alone is identical for all of them.
#[test]
fn a_swapped_trunc_sat_sub_index_is_seen_by_the_full_pair() {
    use trust_cg_codegen::wasm::encode::{op, write_uleb128};
    let pair = |sub: u32| {
        let mut v = vec![op::FC_PREFIX];
        write_uleb128(&mut v, u64::from(sub));
        v
    };
    let decoded = |o: WasmOpcode| {
        let mut v = vec![o.opcode_byte()];
        write_uleb128(&mut v, u64::from(o.trunc_sat_sub_opcode().unwrap()));
        v
    };
    assert_ne!(
        decoded(WasmOpcode::I32TruncSatF64S),
        pair(op::I32_TRUNC_SAT_F64_U)
    );
    assert_ne!(
        decoded(WasmOpcode::I64TruncSatF32S),
        pair(op::I64_TRUNC_SAT_F32_U)
    );
    assert_ne!(
        decoded(WasmOpcode::I32TruncSatF32S),
        pair(op::I64_TRUNC_SAT_F32_S)
    );
    assert_eq!(
        WasmOpcode::I32TruncSatF64S.opcode_byte(),
        WasmOpcode::I32TruncSatF64U.opcode_byte(),
        "the prefix alone cannot tell the forms apart"
    );
}

/// The conversions' SOURCE side is the opcode NAME's intent, not the byte
/// table the machine side decodes, so a table that decoded a signed form as
/// unsigned (both tables swapped consistently, which the encoder cross-check
/// cannot see) REFUTES, and one that decoded another width fails closed.
#[test]
fn a_conversion_whose_decoded_signedness_is_not_its_names_refutes() {
    use trust_cg_verify::trust_ir_semantics::{
        encode_trust_ir_fcvt_to_sint, encode_trust_ir_fcvt_to_uint,
    };
    use trust_cg_verify::wasm_function_verifier::{intended_convert, intended_trunc_sat};
    use trust_cg_verify::wasm_semantics::{encode_trunc_sat_s, encode_trunc_sat_u};

    // Every conversion has a name-derived intent, and the byte tables agree
    // with it today.
    for &opcode in trust_cg_verify::coverage_gate::ALL_WASM_OPCODES {
        if let Some(i) = intended_trunc_sat(opcode) {
            let d = decode_trunc_sat(opcode.opcode_byte(), opcode.trunc_sat_sub_opcode().unwrap())
                .expect("decodes");
            assert_eq!(
                (d.fp_width, d.int_width, d.signed),
                (i.fp_width, i.int_width, i.signed),
                "{opcode:?}"
            );
        }
        if let Some(i) = intended_convert(opcode) {
            let d = decode_convert(opcode.opcode_byte()).expect("decodes");
            assert_eq!(
                (d.src_width, d.fp_width, d.signed),
                (i.int_width, i.fp_width, i.signed),
                "{opcode:?}"
            );
        }
    }
    // The obligation a swapped table would build for I64TruncSatF32S: the
    // machine side decoded as UNSIGNED, the source side the name's SIGNED.
    let a = SmtExpr::var("recon_a", 32);
    let ob = ProofObligation {
        name: "I64TruncSatF32S decoded as _u (INJECTED)".to_string(),
        trust_ir_expr: encode_trust_ir_fcvt_to_sint(64, a.clone()),
        aarch64_expr: encode_trunc_sat_u(a.clone(), 64),
        inputs: vec![],
        fp_inputs: vec![("recon_a".to_string(), 8, 24)],
        preconditions: vec![],
        category: None,
        machine_side_provenance:
            trust_cg_verify::lowering_proof::MachineSideProvenance::Reconstructed {
                from_opcode: "I64TruncSatF32S".to_string(),
                arity: 1,
            },
    };
    assert!(
        matches!(
            verify_by_evaluation(&ob),
            VerificationResult::Invalid { .. }
        ),
        "a signed trunc_sat decoded as unsigned must REFUTE"
    );
    // And the honest pairing stays Valid.
    let ok = ProofObligation {
        name: "I64TruncSatF32S (sanity)".to_string(),
        trust_ir_expr: encode_trust_ir_fcvt_to_uint(64, a.clone()),
        aarch64_expr: encode_trunc_sat_u(a.clone(), 64),
        ..ob.clone()
    };
    assert!(matches!(
        verify_by_evaluation(&ok),
        VerificationResult::Valid
    ));
    // The reconstruction itself builds the honest pairing from the name.
    let inst = representative_wasm_reconstructable_inst(WasmOpcode::I64TruncSatF32S)
        .expect("representative");
    let built = reconstruct_wasm_alu_obligation(&inst).expect("reconstructs");
    assert_eq!(
        built.trust_ir_expr,
        encode_trust_ir_fcvt_to_sint(64, a.clone())
    );
    assert_eq!(built.aarch64_expr, encode_trunc_sat_s(a, 64));
}
