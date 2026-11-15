// trust-cg-verify/tests/aarch64_select_proofs_encoder_gate.rs
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
//! The `CSEL` words `aarch64_select_proofs` decodes must be the words the
//! COMPILER actually emits.
//!
//! The obligation family's machine side is obtained by decoding a concrete
//! 32-bit instruction word. That is only evidence about the compiler if the
//! word is the compiler's. This gate re-encodes every modeled form with the
//! LIVE encoder (`trust_cg_codegen::aarch64::encode::encode_instruction`) and
//! fails on any difference — the same discipline `CAPTURED_A64_VALUE_WORDS`
//! is held to.
//!
//! It lives in `tests/` because `trust-cg-codegen` depends on
//! `trust-cg-verify`; cargo permits that cycle only through
//! `[dev-dependencies]`, and the `src/` modules must never name the codegen
//! crate (see the note in `Cargo.toml`).

use trust_cg_ir::{AArch64Opcode, MachInst, MachOperand, PReg};
use trust_cg_lower::instructions::IntCC;
use trust_cg_lower::isel::AArch64CC;
use trust_cg_verify::aarch64_select_proofs::csel_word;

const CONDITIONS: [IntCC; 10] = [
    IntCC::Equal,
    IntCC::NotEqual,
    IntCC::SignedLessThan,
    IntCC::SignedGreaterThanOrEqual,
    IntCC::SignedGreaterThan,
    IntCC::SignedLessThanOrEqual,
    IntCC::UnsignedLessThan,
    IntCC::UnsignedGreaterThanOrEqual,
    IntCC::UnsignedGreaterThan,
    IntCC::UnsignedLessThanOrEqual,
];

/// `PReg` encodings: X0.. at base 0, W0.. at base 32 (see
/// `trust_cg_ir::aarch64_regs`).
fn csel_inst(width: u32, cc: AArch64CC) -> MachInst {
    let base = if width == 64 { 0 } else { 32 };
    MachInst::new(
        AArch64Opcode::Csel,
        vec![
            MachOperand::PReg(PReg::new(base)),
            MachOperand::PReg(PReg::new(base + 1)),
            MachOperand::PReg(PReg::new(base + 2)),
            MachOperand::Imm(cc as i64),
        ],
    )
}

#[test]
fn modeled_csel_words_are_the_words_the_encoder_emits() {
    let mut checked = 0;
    for cond in CONDITIONS {
        let cc = AArch64CC::from_intcc(cond);
        for width in [32u32, 64] {
            let emitted =
                trust_cg_codegen::aarch64::encode::encode_instruction(&csel_inst(width, cc))
                    .expect("the encoder accepts a well-formed CSEL");
            assert_eq!(
                emitted,
                csel_word(width, cc),
                "modeled CSEL word for {cc:?} w{width} is not what the encoder emits"
            );
            checked += 1;
        }
    }
    assert_eq!(checked, 20);
}

/// The modeled words must decode back to a plain `CSEL` of the intended width
/// and register layout — not to a `CSINC`/`CSINV`/`CSNEG` sibling, which
/// differ only in bits 30 and 10 and have different false arms.
#[test]
fn modeled_csel_words_decode_as_plain_csel() {
    use trust_cg_verify::aarch64_csel_semantics::{
        ConditionalSelectOperation, DecodedConditionalSelect,
    };
    let mut checked = 0;
    for cond in CONDITIONS {
        let cc = AArch64CC::from_intcc(cond);
        for width in [32u32, 64] {
            let decoded = DecodedConditionalSelect::decode(csel_word(width, cc))
                .expect("a CSEL word decodes");
            assert_eq!(decoded.operation(), ConditionalSelectOperation::Csel);
            assert_eq!(decoded.width().bits(), width);
            assert_eq!(decoded.registers(), (0, 1, 2));
            assert_eq!(u32::from(decoded.condition()), cc as u32);
            checked += 1;
        }
    }
    assert_eq!(checked, 20);
}
