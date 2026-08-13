// trust-cg-verify - carrier-hygiene checker tests (P1.2)
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// These tests build x86-64 ISel machine IR directly and assert the
// carrier-hygiene invariant catches the historical narrow-carrier miscompiles
// (#51, #66) while accepting properly-extended programs.
//
// INTEGRATION: when carrier_hygiene.rs is added as `pub mod carrier_hygiene;`
// in trust-cg-verify/src/lib.rs, move this file's body into
// `#[cfg(test)] mod tests { ... }` at the bottom of carrier_hygiene.rs, OR keep
// it as crates/trust-cg-verify/tests/carrier_hygiene.rs (an integration test)
// and import via `use trust_cg_verify::carrier_hygiene::*;`. As written below it
// targets the latter (integration-test) form.

use std::collections::HashMap;

use trust_cg_ir::regs::{RegClass, VReg};
use trust_cg_ir::x86_64_ops::{X86CondCode, X86Opcode};

use trust_cg_lower::function::Signature;
use trust_cg_lower::instructions::Block;
use trust_cg_lower::x86_64_isel::{X86ISelFunction, X86ISelInst, X86ISelOperand};

use trust_cg_verify::carrier_hygiene::{
    HighBits, NominalWidths, RequiredExtension, check_function,
};

// --------------------------------------------------------------------------
// Builders
// --------------------------------------------------------------------------

/// A 32-bit GPR carrier VReg — the home of i8/i16/i32 values on x86-64, where
/// the narrow-carrier hazard lives.
fn gpr32(id: u32) -> VReg {
    VReg::new(id, RegClass::Gpr32)
}

fn vop(v: VReg) -> X86ISelOperand {
    X86ISelOperand::VReg(v)
}

fn imm(n: i64) -> X86ISelOperand {
    X86ISelOperand::Imm(n)
}

/// Build a single-block function from a list of instructions.
fn func_with(insts: Vec<X86ISelInst>) -> X86ISelFunction {
    let sig = Signature {
        params: vec![],
        returns: vec![],
    };
    let mut f = X86ISelFunction::new("carrier_test".to_string(), sig);
    let entry = Block(0);
    f.ensure_block(entry);
    for inst in insts {
        f.push_inst(entry, inst);
    }
    f
}

fn inst(opcode: X86Opcode, operands: Vec<X86ISelOperand>) -> X86ISelInst {
    X86ISelInst::new(opcode, operands)
}

/// A condition-code operand (for CMOVcc).
fn cc(code: X86CondCode) -> X86ISelOperand {
    X86ISelOperand::CondCode(code)
}

/// Build a multi-block function from `(block, insts, successors)` triples. The
/// first triple's block is the entry. Successors wire the CFG so the checker's
/// fixpoint can join across predecessors (including loop back-edges).
fn func_with_blocks(blocks: Vec<(Block, Vec<X86ISelInst>, Vec<Block>)>) -> X86ISelFunction {
    let sig = Signature {
        params: vec![],
        returns: vec![],
    };
    let mut f = X86ISelFunction::new("carrier_test".to_string(), sig);
    for (block, _, _) in &blocks {
        f.ensure_block(*block);
    }
    for (block, insts, succs) in blocks {
        for inst in insts {
            f.push_inst(block, inst);
        }
        if let Some(b) = f.blocks.get_mut(&block) {
            b.successors = succs;
        }
    }
    f
}

/// Build a nominal-width map (the fact ISel supplies from `value_type`).
/// Each `(vreg, bits)` records the value's narrow width (8/16/32/64).
fn widths(entries: &[(VReg, u32)]) -> NominalWidths {
    let mut m = HashMap::new();
    for &(v, w) in entries {
        m.insert(v, w);
    }
    NominalWidths::new(m)
}

// ==========================================================================
// (a) REJECT the #51 pattern: SAR / IDIV consuming a DIRTY narrow value.
// ==========================================================================
//
// Source shape: a narrow (i8) value is produced by a 32-bit NEG (which dirties
// the high carrier bits), then fed directly to SAR / IDIV which interpret the
// whole 32-bit carrier as a signed value. The ISel fix would insert a MOVSX
// before the consumer; without it this is MISCOMPILE #51.

#[test]
fn rejects_51_sar_consuming_dirty_narrow() {
    // v0 = <some i8 value> (modeled as a MovRI seed, defines Full(32))
    // v1 = NEG v0          ; 32-bit negl dirties high bits for an i8 value
    // v2 = SAR v1, 3       ; arithmetic >> reads the full carrier as signed
    let v0 = gpr32(0);
    let v1 = gpr32(1);
    let v2 = gpr32(2);
    // All three values are nominally i8 (8-bit) carried in Gpr32 — the regime
    // where a 32-bit NEG dirties the high carrier bits.
    let nw = widths(&[(v0, 8), (v1, 8), (v2, 8)]);
    let f = func_with(vec![
        inst(X86Opcode::MovRI, vec![vop(v0), imm(0xF7)]),
        inst(X86Opcode::Neg, vec![vop(v1), vop(v0)]),
        inst(X86Opcode::SarRI, vec![vop(v2), vop(v1), imm(3)]),
    ]);

    let report = check_function(&f, &nw);
    assert!(
        !report.is_clean(),
        "carrier-hygiene must REJECT SAR consuming a dirtied narrow carrier (MISCOMPILE #51)"
    );
    let v = &report.violations[0];
    assert_eq!(v.opcode, X86Opcode::SarRI);
    assert_eq!(v.operand, v1);
    assert_eq!(v.required, RequiredExtension::Sign);
    // The NEG of a narrow value produced Top (dirty), which is NOT a sign-ext.
    assert_eq!(v.actual, HighBits::Top);
}

#[test]
fn rejects_51_idiv_consuming_dirty_narrow_divisor() {
    // v0 = -3i8 carried, then a 32-bit SUB dirties high bits, IDIV reads it
    // signed across the carrier -> wrong quotient (MISCOMPILE #51 divisor case).
    let v0 = gpr32(0);
    let v1 = gpr32(1);
    let divisor = gpr32(2);
    let q = gpr32(3);
    let nw = widths(&[(v0, 8), (v1, 8), (divisor, 8), (q, 8)]);
    let f = func_with(vec![
        inst(X86Opcode::MovRI, vec![vop(v0), imm(0)]),
        // SUB v1 = 0 - 3  -> 0xFFFFFFFD: low byte 0xFD == -3i8, high bits dirty.
        inst(X86Opcode::SubRI, vec![vop(v1), vop(v0), imm(3)]),
        inst(X86Opcode::MovRR, vec![vop(divisor), vop(v1)]),
        // IDIV divisor : explicit operand read signed across the full carrier.
        inst(X86Opcode::Idiv, vec![vop(q), vop(divisor)]),
    ]);

    let report = check_function(&f, &nw);
    assert!(
        !report.is_clean(),
        "carrier-hygiene must REJECT IDIV reading a dirtied narrow divisor (MISCOMPILE #51)"
    );
    assert_eq!(report.violations[0].opcode, X86Opcode::Idiv);
    assert_eq!(report.violations[0].required, RequiredExtension::Sign);
}

// ==========================================================================
// (b) REJECT the #66 pattern: unsigned DIV / SHR consuming a DIRTY narrow value.
// ==========================================================================
//
// Source shape: `!8u8` -> 32-bit NOT leaves 0xFFFFFFF7; SHR / DIV then read the
// dirty high bits. Without a preceding MOVZX this is MISCOMPILE #66.

#[test]
fn rejects_66_shr_consuming_dirty_narrow() {
    // v0 = 8u8 ; v1 = NOT v0 (notl -> 0xFFFFFFF7) ; v2 = SHR v1, 3
    // Correct u8 result is 0x1E; dirty-carrier SHR gives 0xFE (#66).
    let v0 = gpr32(0);
    let v1 = gpr32(1);
    let v2 = gpr32(2);
    let nw = widths(&[(v0, 8), (v1, 8), (v2, 8)]);
    let f = func_with(vec![
        inst(X86Opcode::MovRI, vec![vop(v0), imm(8)]),
        inst(X86Opcode::Not, vec![vop(v1), vop(v0)]),
        inst(X86Opcode::ShrRI, vec![vop(v2), vop(v1), imm(3)]),
    ]);

    let report = check_function(&f, &nw);
    assert!(
        !report.is_clean(),
        "carrier-hygiene must REJECT SHR consuming a dirtied narrow carrier (MISCOMPILE #66)"
    );
    let v = &report.violations[0];
    assert_eq!(v.opcode, X86Opcode::ShrRI);
    assert_eq!(v.operand, v1);
    assert_eq!(v.required, RequiredExtension::Zero);
    assert_eq!(v.actual, HighBits::Top);
}

#[test]
fn rejects_66_unsigned_div_consuming_dirty_narrow() {
    // 65528u16 % 7 == 1 correctly; with a dirty carrier DIV reads the wrong
    // 32-bit value and yields 3 (MISCOMPILE #66 unsigned-DIV case).
    let v0 = gpr32(0);
    let v1 = gpr32(1);
    let divisor = gpr32(2);
    let r = gpr32(3);
    let nw = widths(&[(v0, 16), (v1, 16), (divisor, 16), (r, 16)]);
    let f = func_with(vec![
        inst(X86Opcode::MovRI, vec![vop(v0), imm(7)]),
        // NEG dirties the high carrier of a narrow value.
        inst(X86Opcode::Neg, vec![vop(v1), vop(v0)]),
        inst(X86Opcode::MovRR, vec![vop(divisor), vop(v1)]),
        inst(X86Opcode::Div, vec![vop(r), vop(divisor)]),
    ]);

    let report = check_function(&f, &nw);
    assert!(
        !report.is_clean(),
        "carrier-hygiene must REJECT unsigned DIV reading a dirtied narrow divisor (MISCOMPILE #66)"
    );
    assert_eq!(report.violations[0].opcode, X86Opcode::Div);
    assert_eq!(report.violations[0].required, RequiredExtension::Zero);
}

// ==========================================================================
// (c) ACCEPT a properly-extended program.
// ==========================================================================
//
// This is the SHAPE the ISel fix produces: a MOVSX/MOVZX is inserted between the
// dirtying producer and the wide-reading consumer, so the carrier is provably
// extended at the consumer.

#[test]
fn accepts_properly_sign_extended_sar() {
    // v0 = 8 ; v1 = NEG v0 (dirty) ; v2 = MOVSX v1 (sign-ext fix) ; v3 = SAR v2,3
    let v0 = gpr32(0);
    let v1 = gpr32(1);
    let v2 = gpr32(2);
    let v3 = gpr32(3);
    let nw = widths(&[(v0, 8), (v1, 8), (v2, 8), (v3, 8)]);
    let f = func_with(vec![
        inst(X86Opcode::MovRI, vec![vop(v0), imm(8)]),
        inst(X86Opcode::Neg, vec![vop(v1), vop(v0)]),
        // sign_extend_narrow_operand(I8) -> MOVSXB
        inst(X86Opcode::MovsxB, vec![vop(v2), vop(v1)]),
        inst(X86Opcode::SarRI, vec![vop(v3), vop(v2), imm(3)]),
    ]);

    let report = check_function(&f, &nw);
    assert!(
        report.is_clean(),
        "carrier-hygiene must ACCEPT a SAR whose operand was MOVSX-extended; \
         got violations: {:?}",
        report.violations
    );
}

#[test]
fn accepts_properly_zero_extended_shr() {
    // v0 = 8 ; v1 = NOT v0 (dirty) ; v2 = MOVZX v1 (zero-ext fix) ; v3 = SHR v2,3
    let v0 = gpr32(0);
    let v1 = gpr32(1);
    let v2 = gpr32(2);
    let v3 = gpr32(3);
    let nw = widths(&[(v0, 8), (v1, 8), (v2, 8), (v3, 8)]);
    let f = func_with(vec![
        inst(X86Opcode::MovRI, vec![vop(v0), imm(8)]),
        inst(X86Opcode::Not, vec![vop(v1), vop(v0)]),
        // zero_extend_narrow_operand(I8) -> MOVZX
        inst(X86Opcode::Movzx, vec![vop(v2), vop(v1)]),
        inst(X86Opcode::ShrRI, vec![vop(v3), vop(v2), imm(3)]),
    ]);

    let report = check_function(&f, &nw);
    assert!(
        report.is_clean(),
        "carrier-hygiene must ACCEPT an SHR whose operand was MOVZX-extended; \
         got violations: {:?}",
        report.violations
    );
}

// ==========================================================================
// Lattice / polarity guards.
// ==========================================================================

#[test]
fn zero_ext_does_not_satisfy_signed_consumer() {
    // The polarity matters: a ZERO-extended operand does NOT satisfy SAR/IDIV.
    // This is the exact #51 trigger: select_trunc's MOVZX left a zero-extended
    // carrier and CDQ/IDIV then saw a wrong non-negative dividend.
    let v0 = gpr32(0);
    let v1 = gpr32(1);
    let v2 = gpr32(2);
    let nw = widths(&[(v0, 8), (v1, 8), (v2, 8)]);
    let f = func_with(vec![
        inst(X86Opcode::MovRI, vec![vop(v0), imm(0xFD)]),
        // MOVZX produces ZeroExt(8) — clean, but WRONG polarity for SAR.
        inst(X86Opcode::Movzx, vec![vop(v1), vop(v0)]),
        inst(X86Opcode::SarRI, vec![vop(v2), vop(v1), imm(2)]),
    ]);

    let report = check_function(&f, &nw);
    assert!(
        !report.is_clean(),
        "a ZERO-extended operand must NOT satisfy a SIGNED consumer (SAR/IDIV) — \
         this is the original #51 trigger (MOVZX carrier feeding CDQ/IDIV)"
    );
    assert_eq!(report.violations[0].required, RequiredExtension::Sign);
    assert_eq!(report.violations[0].actual, HighBits::ZeroExt(8));
}

#[test]
fn sign_ext_does_not_satisfy_unsigned_consumer() {
    // Mirror polarity guard: a SIGN-extended operand does NOT satisfy SHR/DIV.
    let v0 = gpr32(0);
    let v1 = gpr32(1);
    let v2 = gpr32(2);
    let nw = widths(&[(v0, 8), (v1, 8), (v2, 8)]);
    let f = func_with(vec![
        inst(X86Opcode::MovRI, vec![vop(v0), imm(0xFD)]),
        inst(X86Opcode::MovsxB, vec![vop(v1), vop(v0)]),
        inst(X86Opcode::ShrRI, vec![vop(v2), vop(v1), imm(2)]),
    ]);

    let report = check_function(&f, &nw);
    assert!(
        !report.is_clean(),
        "a SIGN-extended operand must NOT satisfy an UNSIGNED consumer (SHR/DIV)"
    );
    assert_eq!(report.violations[0].required, RequiredExtension::Zero);
}

#[test]
fn shl_is_not_a_wide_reader() {
    // SHL only writes the low `width` bits the caller reads back, so a dirty
    // carrier into SHL is NOT a violation (matches select_shift's no-fix case).
    let v0 = gpr32(0);
    let v1 = gpr32(1);
    let v2 = gpr32(2);
    let nw = widths(&[(v0, 8), (v1, 8), (v2, 8)]);
    let f = func_with(vec![
        inst(X86Opcode::MovRI, vec![vop(v0), imm(8)]),
        inst(X86Opcode::Not, vec![vop(v1), vop(v0)]),
        inst(X86Opcode::ShlRI, vec![vop(v2), vop(v1), imm(3)]),
    ]);

    let report = check_function(&f, &nw);
    assert!(
        report.is_clean(),
        "SHL does not read the high carrier bits, so a dirty operand is not a \
         carrier-hygiene violation; got: {:?}",
        report.violations
    );
}

#[test]
fn movsxd_i32_to_i64_satisfies_signed_consumer() {
    // #68-cvt analogue: an i32 value sign-extended to i64 via MOVSXD is a clean
    // SignExt(32) and may be read signed by a 64-bit IDIV. (The #68-cvt fix was
    // for CVTSI2SS reading a sign-extended i32; the lattice property is the same
    // — a MOVSXD/Movsx source proves sign-extension, an unextended one does not.)
    let v0 = VReg::new(0, RegClass::Gpr32);
    let v1 = VReg::new(1, RegClass::Gpr64);
    let q = VReg::new(2, RegClass::Gpr64);
    // v1 is an i32 value living in a 64-bit carrier: nominally narrow (32 < 64),
    // so the consumer is checked, and MOVSXD proves SignExt(32) -> accepted.
    let nw = widths(&[(v0, 32), (v1, 32), (q, 64)]);
    let f = func_with(vec![
        inst(X86Opcode::MovRI, vec![vop(v0), imm(-5)]),
        // MOVSXD r64, r32 -> SignExt(32)
        inst(X86Opcode::Movsx, vec![vop(v1), vop(v0)]),
        inst(X86Opcode::Idiv, vec![vop(q), vop(v1)]),
    ]);

    let report = check_function(&f, &nw);
    assert!(
        report.is_clean(),
        "a MOVSXD-extended i32->i64 operand must satisfy a signed 64-bit IDIV; \
         got: {:?}",
        report.violations
    );
}

// ==========================================================================
// No-false-positive guard: a GENUINE i32 SAR/SHR/IDIV (value fills its carrier)
// must NOT be flagged even with no extension move. This is the property that
// keeps the checker from rejecting the overwhelmingly common 32-bit path.
// ==========================================================================

#[test]
fn accepts_genuine_i32_sar_without_extension() {
    // i32 NEG; i32 SAR — both 32-bit values in 32-bit carriers. The NEG fills
    // the carrier cleanly (Full(32)); SAR over a 32-bit value is correct.
    let v0 = gpr32(0);
    let v1 = gpr32(1);
    let v2 = gpr32(2);
    let nw = widths(&[(v0, 32), (v1, 32), (v2, 32)]);
    let f = func_with(vec![
        inst(X86Opcode::MovRI, vec![vop(v0), imm(-9)]),
        inst(X86Opcode::Neg, vec![vop(v1), vop(v0)]),
        inst(X86Opcode::SarRI, vec![vop(v2), vop(v1), imm(3)]),
    ]);

    let report = check_function(&f, &nw);
    assert!(
        report.is_clean(),
        "a genuine i32 SAR (value fills its carrier) must NOT be flagged — \
         this is the no-false-positive property; got: {:?}",
        report.violations
    );
}

#[test]
fn accepts_genuine_i64_unsigned_div_without_extension() {
    // i64 SUB; unsigned DIV — 64-bit values, no narrow hazard.
    let v0 = VReg::new(0, RegClass::Gpr64);
    let v1 = VReg::new(1, RegClass::Gpr64);
    let r = VReg::new(2, RegClass::Gpr64);
    let nw = widths(&[(v0, 64), (v1, 64), (r, 64)]);
    let f = func_with(vec![
        inst(X86Opcode::MovRI, vec![vop(v0), imm(100)]),
        inst(X86Opcode::SubRI, vec![vop(v1), vop(v0), imm(3)]),
        inst(X86Opcode::Div, vec![vop(r), vop(v1)]),
    ]);

    let report = check_function(&f, &nw);
    assert!(
        report.is_clean(),
        "a genuine i64 unsigned DIV must NOT be flagged; got: {:?}",
        report.violations
    );
}

// ==========================================================================
// (d) REJECT a WIDTH-MISMATCHED extension (finding 1).
// ==========================================================================
//
// A MOVSX r, r/m16 sign-extends bit 15 — it copies bits 8..=15 verbatim. For an
// i8 value those bits are the dirty high bits of the i8, NOT the sign of bit 7.
// So a SignExt(16) does NOT make an i8 carrier safe for a signed consumer. A
// width-blind checker (the original bug) would accept this; the width-aware one
// must REJECT it.

#[test]
fn rejects_width_mismatched_signext_feeding_i8_consumer() {
    // v1 = MOVSX16 v0  -> SignExt(16); v2 = SAR v1 over an i8 (n=8) consumer.
    // SignExt(16) does not cover an 8-bit nominal width (16 > 8) -> violation.
    let v0 = gpr32(0);
    let v1 = gpr32(1);
    let v2 = gpr32(2);
    // All three are nominally i8 (8-bit) — the i8 hazard regime.
    let nw = widths(&[(v0, 8), (v1, 8), (v2, 8)]);
    let f = func_with(vec![
        inst(X86Opcode::MovRI, vec![vop(v0), imm(0xF7)]),
        // MOVSXW sign-extends from bit 15 -> SignExt(16), leaving bits 8..=15 of
        // the i8 (garbage) in place.
        inst(X86Opcode::MovsxW, vec![vop(v1), vop(v0)]),
        inst(X86Opcode::SarRI, vec![vop(v2), vop(v1), imm(3)]),
    ]);

    let report = check_function(&f, &nw);
    assert!(
        !report.is_clean(),
        "a SignExt(16) must NOT satisfy an i8 (8-bit) signed consumer — the \
         extension width must cover the value's nominal width (finding 1)"
    );
    let v = &report.violations[0];
    assert_eq!(v.opcode, X86Opcode::SarRI);
    assert_eq!(v.operand, v1);
    assert_eq!(v.required, RequiredExtension::Sign);
    assert_eq!(v.actual, HighBits::SignExt(16));
}

// ==========================================================================
// (e) REJECT a LOOP-CARRIED dirty value (finding 3).
// ==========================================================================
//
// The header reads a value that is clean on the entry edge but DIRTIED by the
// latch on the back-edge. A single forward pass over block order sees only the
// clean entry value and misses the bug. A real worklist fixpoint joins the
// latch's dirty exit back into the header's entry, demoting it to Top, and
// flags the wide read.

#[test]
fn rejects_loop_carried_dirty_value() {
    let v0 = gpr32(0); // loop-invariant seed
    let v1 = gpr32(1); // the loop-carried value: clean in entry, dirty in latch
    let v2 = gpr32(2); // SAR result in the header
    // All i8 (8-bit) — the narrow-carrier regime.
    let nw = widths(&[(v0, 8), (v1, 8), (v2, 8)]);

    let entry = Block(0);
    let header = Block(1);
    let latch = Block(2);

    let f = func_with_blocks(vec![
        // entry: define v1 cleanly (MOVSX -> SignExt(8)), then enter the header.
        (
            entry,
            vec![
                inst(X86Opcode::MovRI, vec![vop(v0), imm(0x10)]),
                inst(X86Opcode::MovsxB, vec![vop(v1), vop(v0)]),
            ],
            vec![header],
        ),
        // header: SAR reads v1 across the full carrier. v1 is clean on the entry
        // edge but DIRTY on the latch back-edge -> the join is Top -> violation.
        (
            header,
            vec![inst(X86Opcode::SarRI, vec![vop(v2), vop(v1), imm(2)])],
            vec![latch],
        ),
        // latch: REDEFINE v1 with a 32-bit NEG (dirties the high carrier of the
        // i8), then branch back to the header (the back-edge).
        (
            latch,
            vec![inst(X86Opcode::Neg, vec![vop(v1), vop(v0)])],
            vec![header],
        ),
    ]);

    let report = check_function(&f, &nw);
    assert!(
        !report.is_clean(),
        "a loop-carried value dirtied by the latch must be flagged at the header \
         wide read — requires a real fixpoint, not a single forward pass \
         (finding 3)"
    );
    let v = &report.violations[0];
    assert_eq!(v.opcode, X86Opcode::SarRI);
    assert_eq!(v.operand, v1);
    assert_eq!(v.required, RequiredExtension::Sign);
    // The back-edge join of SignExt(8) (entry) and Top (latch NEG) is Top.
    assert_eq!(v.actual, HighBits::Top);
}

// ==========================================================================
// (f) ACCEPT the real signed-IDIV divisor shape (finding 6).
// ==========================================================================
//
// ISel's signed-division INT_MIN/-1 overflow guard builds the divisor with:
//   rhs  = MOVSX(orig)            ; SignExt(8) (the divisor sign-extension fix)
//   safe = MOV r32, rhs           ; a copy that must PROPAGATE the proof
//   one  = MOV r32, 1             ; the neutralizing constant
//   CMP rhs, -1
//   CMOVE safe, one               ; safe = (rhs == -1) ? 1 : rhs
//   IDIV safe
// A width-blind / copy-losing checker downgrades `safe` to Top and false-rejects
// this perfectly valid divisor. Modeling MovRR32 as a copy, the constant `1`
// precisely, and CMOV as the JOIN of its two sources keeps it accepted.

#[test]
fn accepts_signed_idiv_divisor_via_movrr32_cmov() {
    let orig = gpr32(0);
    let rhs = gpr32(1);
    let safe = gpr32(2);
    let one = gpr32(3);
    let q = gpr32(4);
    // i8 divisor (8-bit) carried in Gpr32 — the narrow signed-div regime.
    let nw = widths(&[(orig, 8), (rhs, 8), (safe, 8), (one, 8), (q, 8)]);

    let f = func_with(vec![
        inst(X86Opcode::MovRI, vec![vop(orig), imm(0xFD)]), // -3i8
        // sign_extend_narrow_operand(I8) -> MOVSXB : SignExt(8)
        inst(X86Opcode::MovsxB, vec![vop(rhs), vop(orig)]),
        // safe := rhs   (MovRR32 same-width copy propagates SignExt(8))
        inst(X86Opcode::MovRR32, vec![vop(safe), vop(rhs)]),
        // one := 1      (clean constant -> Full(8), refines under join)
        inst(X86Opcode::MovRI, vec![vop(one), imm(1)]),
        // CMP rhs, -1   (no def)
        inst(X86Opcode::CmpRI, vec![vop(rhs), imm(-1)]),
        // CMOVE safe, one  -> safe = join(SignExt(8), Full(8)) = SignExt(8)
        inst(
            X86Opcode::Cmovcc32,
            vec![vop(safe), vop(one), cc(X86CondCode::E)],
        ),
        // IDIV safe : divisor read signed -> SignExt(8) satisfies it.
        inst(X86Opcode::Idiv, vec![vop(q), vop(safe)]),
    ]);

    let report = check_function(&f, &nw);
    assert!(
        report.is_clean(),
        "the real MovRR32 + CMOV signed-IDIV divisor shape must be ACCEPTED — \
         CMOV is the join of its sources and the copy propagates the proof \
         (finding 6); got: {:?}",
        report.violations
    );
}

// ==========================================================================
// (f') ACCEPT a loop-invariant sign-extended divisor hoisted to the PREHEADER
//      (CARRIER-051) — a reachability-aware-fixpoint regression test.
// ==========================================================================
//
// At O2/O3 LICM hoists a loop-invariant narrow signed divisor's sign-extension
// (MOVSXW) out of the loop into the PREHEADER; the IDIV stays in the loop BODY,
// and the loop HEADER joins the preheader edge with the back-edge. The divisor is
// loop-invariant and sign-extended on EVERY real path, so the IDIV is sound — but
// a reachability-BLIND fixpoint (joining a not-yet-computed back-edge predecessor,
// whose pre-seeded empty exit forces every absent key to Top, with the lattice
// only moving towards Top) PERMANENTLY demotes the divisor to Top at the header
// and false-rejects the whole function fail-closed. The fix makes the fixpoint
// reachability-aware (only join COMPUTED predecessors, seeded from the first).
// This mirrors the real `acc.wrapping_rem(black_box(7i16))`-in-a-loop repro that
// compiled+ran correctly at O0 but fail-closed at O2/O3.
#[test]
fn accepts_loop_invariant_hoisted_signext_divisor() {
    let raw = gpr32(0); // raw narrow divisor (e.g. black_box(7i16))
    let div = gpr32(1); // hoisted MOVSXW(raw) -> SignExt(16), defined in preheader
    let one = gpr32(2); // the INT_MIN/-1 guard's neutralizing constant
    let safe = gpr32(3); // the guarded divisor actually fed to IDIV
    let q = gpr32(4); // IDIV result
    let iv = gpr32(5); // loop induction variable (clean i32)
    let nw = widths(&[
        (raw, 16),
        (div, 16),
        (one, 16),
        (safe, 16),
        (q, 16),
        (iv, 32),
    ]);

    let preheader = Block(0);
    let header = Block(1);
    let body = Block(2);
    let latch = Block(3);
    let exit = Block(4);

    let f = func_with_blocks(vec![
        // preheader: materialize the divisor and HOIST its sign-extension here.
        (
            preheader,
            vec![
                inst(X86Opcode::MovRI, vec![vop(raw), imm(7)]),
                inst(X86Opcode::MovsxW, vec![vop(div), vop(raw)]), // SignExt(16)
                inst(X86Opcode::MovRI, vec![vop(one), imm(1)]),
                inst(X86Opcode::MovRI, vec![vop(iv), imm(0)]),
            ],
            vec![header],
        ),
        // header: loop condition; two preds (preheader + latch back-edge).
        (
            header,
            vec![inst(X86Opcode::CmpRI, vec![vop(iv), imm(5)])],
            vec![body, exit],
        ),
        // body: the signed-IDIV INT_MIN/-1 guard reading the hoisted divisor.
        (
            body,
            vec![
                inst(X86Opcode::MovRR32, vec![vop(safe), vop(div)]), // safe := div (SignExt(16))
                inst(X86Opcode::CmpRI, vec![vop(div), imm(-1)]),
                inst(
                    X86Opcode::Cmovcc32,
                    vec![vop(safe), vop(one), cc(X86CondCode::E)],
                ),
                inst(X86Opcode::Idiv, vec![vop(q), vop(safe)]), // divisor read signed
            ],
            vec![latch],
        ),
        // latch: advance the (clean) induction variable; back-edge to the header.
        (
            latch,
            vec![inst(X86Opcode::MovRI, vec![vop(iv), imm(1)])],
            vec![header],
        ),
        (exit, vec![], vec![]),
    ]);

    let report = check_function(&f, &nw);
    assert!(
        report.is_clean(),
        "a loop-invariant sign-extended divisor hoisted to the preheader must be \
         ACCEPTED in the loop body (CARRIER-051): the reachability-aware fixpoint \
         must not demote it to Top via the uncomputed back-edge; got: {:?}",
        report.violations
    );
}

// ==========================================================================
// (g) ACCEPT narrowing AND-mask shapes (finding 7).
// ==========================================================================
//
// `v & 0xFF` zeroes bits >= 8 regardless of v, proving ZeroExt(8). So masking a
// dirty narrow value before an UNSIGNED consumer is safe and must be accepted.

#[test]
fn accepts_and_immediate_mask_before_shr() {
    let v0 = gpr32(0);
    let v1 = gpr32(1);
    let v2 = gpr32(2);
    let v3 = gpr32(3);
    let nw = widths(&[(v0, 8), (v1, 8), (v2, 8), (v3, 8)]);
    let f = func_with(vec![
        inst(X86Opcode::MovRI, vec![vop(v0), imm(8)]),
        // NOT dirties the high carrier (0xFFFFFFF7).
        inst(X86Opcode::Not, vec![vop(v1), vop(v0)]),
        // AND v1, 0xFF -> clears bits >= 8 -> ZeroExt(8).
        inst(X86Opcode::AndRI, vec![vop(v2), vop(v1), imm(0xFF)]),
        // SHR reads a now-clean zero-extended carrier -> accepted.
        inst(X86Opcode::ShrRI, vec![vop(v3), vop(v2), imm(3)]),
    ]);

    let report = check_function(&f, &nw);
    assert!(
        report.is_clean(),
        "an AND-immediate mask (v & 0xFF) proves ZeroExt(8) and must be ACCEPTED \
         before an unsigned consumer (finding 7); got: {:?}",
        report.violations
    );
}

#[test]
fn accepts_and_of_two_zero_extended_operands_before_div() {
    let a0 = gpr32(0);
    let b0 = gpr32(1);
    let a = gpr32(2);
    let b = gpr32(3);
    let m = gpr32(4);
    let r = gpr32(5);
    let nw = widths(&[(a0, 8), (b0, 8), (a, 8), (b, 8), (m, 8), (r, 8)]);
    let f = func_with(vec![
        inst(X86Opcode::MovRI, vec![vop(a0), imm(0x80)]),
        inst(X86Opcode::MovRI, vec![vop(b0), imm(0x7F)]),
        // Both operands zero-extended to 8 bits via MOVZX.
        inst(X86Opcode::Movzx, vec![vop(a), vop(a0)]),
        inst(X86Opcode::Movzx, vec![vop(b), vop(b0)]),
        // AND of two ZeroExt(8) stays ZeroExt(8).
        inst(X86Opcode::AndRR, vec![vop(m), vop(a), vop(b)]),
        // Unsigned DIV reads the zero-extended divisor -> accepted.
        inst(X86Opcode::Div, vec![vop(r), vop(m)]),
    ]);

    let report = check_function(&f, &nw);
    assert!(
        report.is_clean(),
        "AND of two zero-extended operands stays zero-extended and must be \
         ACCEPTED before an unsigned DIV (finding 7); got: {:?}",
        report.violations
    );
}

// ==========================================================================
// (h) Fail-closed on an UNKNOWN-width wide-read source (finding 2).
// ==========================================================================
//
// A narrow live-in / scratch value with no tracked nominal width must NOT be
// blessed by assuming it fills its carrier. An untracked operand feeding IDIV is
// checked fail-closed: with no extension proof it is a violation.

#[test]
fn rejects_unknown_width_dirty_source_feeding_idiv() {
    let v0 = gpr32(0);
    let v1 = gpr32(1);
    let q = gpr32(2);
    // v1 has NO width entry (untracked) -> must be treated as possibly-narrow.
    let nw = widths(&[(v0, 8), (q, 8)]);
    let f = func_with(vec![
        inst(X86Opcode::MovRI, vec![vop(v0), imm(7)]),
        // A 32-bit NEG of an untracked value: with width unknown the result is
        // conservatively dirty (Top), never a clean carrier fill.
        inst(X86Opcode::Neg, vec![vop(v1), vop(v0)]),
        inst(X86Opcode::Idiv, vec![vop(q), vop(v1)]),
    ]);

    let report = check_function(&f, &nw);
    assert!(
        !report.is_clean(),
        "an untracked (unknown-width) operand feeding IDIV must be checked \
         fail-closed, not assumed to fill its carrier (finding 2)"
    );
    assert_eq!(report.violations[0].opcode, X86Opcode::Idiv);
    assert_eq!(report.violations[0].operand, v1);
    assert_eq!(report.violations[0].required, RequiredExtension::Sign);
}
