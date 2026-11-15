// trust-cg-verify/fp_ieee_evidence.rs - named IEEE 754 testing evidence
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! The named testing evidence ledger `L04-P3` attaches to the scalar
//! floating-point rows of the AArch64 coverage gate. It is NEVER credit.
//!
//! Two test targets produce it, both against the independent integer-only
//! reference [`crate::ieee754_reference`]:
//!
//! * [`DIFFERENTIAL_TARGET`] runs every emitted scalar FP conversion, rounding
//!   and arithmetic form ([`forms`]) on the host CPU (the live encoder's word,
//!   decoded by ENC-5 first) and compares the result, the untouched other
//!   destination, the zeroed upper register bits and the FPSR cumulative flags
//!   with the reference bit for bit, and the verifier's machine-side model with
//!   the reference (a NaN by class: the models carry one NaN);
//! * [`LOWERING_TARGET`] compiles the TrustIR operations that select those
//!   forms through the proof-grade AOT route at O0-O3 (every FP value word
//!   re-encoded, ENC-5-matched and found in the object) and the host JIT at O1
//!   and O2, and runs the compiled code against the reference's statement of
//!   the TrustIR semantics.
//!
//! Each form reads one [`InputSpace`]; the strength of the evidence over it is
//! [`InputSpace::floor_strength`] for the default run that the Darwin floor
//! repeats, and [`InputSpace::recorded_strength`] for the release-mode run with
//! `TRUST_CG_FP_IEEE_EXHAUSTIVE=1` whose per-form results are committed under
//! [`RECORD_DIR`] (one Apple M4 Max, the revision named in its `run.json`).
//!
//! [`gate_note`] is the text the coverage gate appends to a row's note. The
//! gate never changes a row's class or finding because of it: an accepted row
//! stays accepted on its own obligation, and a RED row (FRINTN) stays RED.
//! Testing on one CPU over named finite inputs is not a proof; the binary32 and
//! binary64 FDIV/FSQRT formal obligations remain refused because the external
//! checker has no floating-point syntax.

use trust_cg_ir::AArch64Opcode;

use crate::ieee754_reference::Format;

/// The instruction-level differential.
pub const DIFFERENTIAL_TARGET: &str = "trust-cg-verify tests/aarch64_fp_ieee_differential.rs";

/// The TrustIR lowering differential.
pub const LOWERING_TARGET: &str = "trust-cg-codegen tests/e2e_aarch64_fp_ieee_lowering.rs";

/// The committed results of the recorded exhaustive (release) run.
pub const RECORD_DIR: &str = "crates/trust-cg-verify/tests/fixtures/fp_ieee_exhaustive";

/// How much of an input space a run covers.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Strength {
    /// Every value of the space.
    Exhaustive,
    /// A structured set (every exponent field with boundary significands,
    /// boundary windows, edge products) plus a stratified random sample.
    Statistical,
}

impl Strength {
    /// `exhaustive` or `statistical`, as the targets print it.
    pub const fn label(self) -> &'static str {
        match self {
            Strength::Exhaustive => "exhaustive",
            Strength::Statistical => "statistical",
        }
    }
}

/// The values a form reads.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum InputSpace {
    /// One binary16, binary32 or binary64 operand.
    Fp(Format),
    /// One 32- or 64-bit integer operand.
    Int(u32),
    /// Two operands of a format.
    Pairs(Format),
    /// Three operands of a format (fused multiply-add).
    Triples(Format),
}

impl InputSpace {
    /// The strength of the default run's set, which the floor repeats.
    pub const fn floor_strength(self) -> Strength {
        match self {
            InputSpace::Fp(Format::Half) => Strength::Exhaustive,
            _ => Strength::Statistical,
        }
    }

    /// The strength of the recorded release run's set.
    pub const fn recorded_strength(self) -> Strength {
        match self {
            InputSpace::Fp(Format::Half)
            | InputSpace::Fp(Format::Single)
            | InputSpace::Int(32)
            | InputSpace::Pairs(Format::Half) => Strength::Exhaustive,
            _ => Strength::Statistical,
        }
    }

    /// The space's size when it is enumerable in the recorded run.
    pub const fn exhaustive_size(self) -> Option<u64> {
        match self {
            InputSpace::Fp(Format::Half) => Some(1 << 16),
            InputSpace::Fp(Format::Single)
            | InputSpace::Int(32)
            | InputSpace::Pairs(Format::Half) => Some(1 << 32),
            _ => None,
        }
    }

    /// A short description.
    pub fn describe(self) -> String {
        match self {
            InputSpace::Fp(f) => format!("{} operands", f.name()),
            InputSpace::Int(width) => format!("{width}-bit integers"),
            InputSpace::Pairs(f) => format!("{} pairs", f.name()),
            InputSpace::Triples(f) => format!("{} triples", f.name()),
        }
    }
}

/// One emitted scalar FP form of the differential.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FormEvidence {
    /// The form, as the differential labels it (`FCVTZS W,S`).
    pub label: String,
    /// The machine opcode the encoder emits for it.
    pub opcode: AArch64Opcode,
    /// The values it reads.
    pub space: InputSpace,
}

fn reg(f: Format) -> char {
    match f {
        Format::Half => 'H',
        Format::Single => 'S',
        Format::Double => 'D',
    }
}

/// Every emitted scalar FP conversion, rounding and arithmetic form the
/// differential runs, in its order.
pub fn forms() -> Vec<FormEvidence> {
    use AArch64Opcode as Op;
    let mut out = Vec::new();
    let mut push = |label: String, opcode, space| {
        out.push(FormEvidence {
            label,
            opcode,
            space,
        })
    };
    for f in Format::ALL {
        let r = reg(f);
        for (op, name) in [
            (Op::FaddRR, "FADD"),
            (Op::FsubRR, "FSUB"),
            (Op::FmulRR, "FMUL"),
            (Op::FdivRR, "FDIV"),
            (Op::FminnmRR, "FMINNM"),
            (Op::FmaxnmRR, "FMAXNM"),
        ] {
            push(format!("{name} {r}"), op, InputSpace::Pairs(f));
        }
        push(format!("FMADD {r}"), Op::FmaddRR, InputSpace::Triples(f));
        for (op, name) in [
            (Op::FnegRR, "FNEG"),
            (Op::FabsRR, "FABS"),
            (Op::FsqrtRR, "FSQRT"),
            (Op::FrintmRR, "FRINTM"),
            (Op::FrintpRR, "FRINTP"),
            (Op::FrintzRR, "FRINTZ"),
            (Op::FrintnRR, "FRINTN"),
        ] {
            push(format!("{name} {r}"), op, InputSpace::Fp(f));
        }
        for width in [32, 64] {
            let g = if width == 32 { 'W' } else { 'X' };
            for (op, name) in [(Op::FcvtzsRR, "FCVTZS"), (Op::FcvtzuRR, "FCVTZU")] {
                push(format!("{name} {g},{r}"), op, InputSpace::Fp(f));
            }
            for (op, name) in [(Op::ScvtfRR, "SCVTF"), (Op::UcvtfRR, "UCVTF")] {
                push(format!("{name} {r},{g}"), op, InputSpace::Int(width));
            }
        }
    }
    for (op, src, dst) in [
        (Op::FcvtSD, Format::Single, Format::Double),
        (Op::FcvtDS, Format::Double, Format::Single),
        (Op::FcvtHS, Format::Half, Format::Single),
        (Op::FcvtHD, Format::Half, Format::Double),
        (Op::FcvtSH, Format::Single, Format::Half),
        (Op::FcvtDH, Format::Double, Format::Half),
    ] {
        push(
            format!("FCVT {},{}", reg(dst), reg(src)),
            op,
            InputSpace::Fp(src),
        );
    }
    out
}

/// The opcodes [`forms`] covers.
pub fn opcodes() -> Vec<AArch64Opcode> {
    let mut ops: Vec<AArch64Opcode> = forms().iter().map(|f| f.opcode).collect();
    ops.sort_by_key(|op| format!("{op:?}"));
    ops.dedup();
    ops
}

/// The note the coverage gate appends to `opcode`'s row, or `None` when this
/// evidence names no form of it.
pub fn gate_note(opcode: AArch64Opcode) -> Option<String> {
    let forms: Vec<FormEvidence> = forms().into_iter().filter(|f| f.opcode == opcode).collect();
    if forms.is_empty() {
        return None;
    }
    let labels: Vec<&str> = forms.iter().map(|f| f.label.as_str()).collect();
    let mut spaces: Vec<InputSpace> = forms.iter().map(|f| f.space).collect();
    spaces.sort();
    spaces.dedup();
    let strengths: Vec<String> = spaces
        .iter()
        .map(|space| {
            let floor = space.floor_strength();
            let recorded = space.recorded_strength();
            if floor == recorded {
                format!("{}: {} in every run", space.describe(), floor.label())
            } else {
                format!(
                    "{}: {} in the floor run, {} in the recorded release run",
                    space.describe(),
                    floor.label(),
                    recorded.label()
                )
            }
        })
        .collect();
    let refused = if matches!(opcode, AArch64Opcode::FdivRR | AArch64Opcode::FsqrtRR) {
        "; the binary32/binary64 formal obligations stay refused (the external checker has no \
         floating-point syntax)"
    } else {
        ""
    };
    Some(format!(
        "L04-P3 named TESTING evidence, NOT credit (this row's status is unchanged): {} form(s) ({}) \
         ran on this CPU against the independent integer-only IEEE 754 reference, value, \
         untouched registers and FPSR flags bit for bit, and against the verifier model (NaN by \
         class), over {} ({DIFFERENTIAL_TARGET}; record {RECORD_DIR}); the TrustIR lowerings \
         selecting it agree with the reference on the AOT O0-O3 proof-grade route (ENC-5-matched \
         words) and the JIT at O1/O2 ({LOWERING_TARGET}){refused}",
        labels.len(),
        labels.join(", "),
        strengths.join("; "),
    ))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn every_format_contributes_the_same_twenty_two_forms() {
        let all = forms();
        assert_eq!(all.len(), 3 * 22 + 6);
        let mut labels: Vec<&str> = all.iter().map(|f| f.label.as_str()).collect();
        labels.sort_unstable();
        labels.dedup();
        assert_eq!(labels.len(), all.len(), "duplicate form label");
        assert_eq!(opcodes().len(), 24);
    }

    #[test]
    fn notes_name_their_strengths_and_disclaim_credit() {
        for op in opcodes() {
            let note = gate_note(op).expect("named");
            assert!(note.contains("NOT credit"), "{op:?}: {note}");
            assert!(note.contains("statistical") || note.contains("exhaustive"));
        }
        let fcvtzs = gate_note(AArch64Opcode::FcvtzsRR).unwrap();
        assert!(
            fcvtzs.contains("f16 operands: exhaustive in every run"),
            "{fcvtzs}"
        );
        assert!(
            fcvtzs.contains(
                "f32 operands: statistical in the floor run, exhaustive in the recorded release run"
            ),
            "{fcvtzs}"
        );
        assert!(
            fcvtzs.contains("f64 operands: statistical in every run"),
            "{fcvtzs}"
        );
        assert!(
            gate_note(AArch64Opcode::FdivRR)
                .unwrap()
                .contains("stay refused")
        );
        assert_eq!(gate_note(AArch64Opcode::AddRR), None);
    }
}
