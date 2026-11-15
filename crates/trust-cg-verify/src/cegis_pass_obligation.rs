// trust-cg-verify/cegis_pass_obligation.rs - AArch64 CEGIS rewrite obligations
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! The equivalence obligation an AArch64 CEGIS payload rewrite discharges.
//!
//! An obligation states that one register, the rewritten consumer's
//! destination, holds the same value after the ORIGINAL window of machine
//! instructions as after the REPLACEMENT window, both run from the same entry
//! state. [`Window`] computes both sides from the instructions themselves:
//!
//! * a move-wide materializer contributes its `imm16` field placed at
//!   `hw * 16`, with the field ranges `trust-cg-codegen` accepts;
//! * a replacement immediate is first encoded the way `trust-cg-codegen`
//!   encodes it (`imm12` with `sh = 0` for `ADD`, `N:immr:imms` for `AND`) and
//!   then decoded from those fields: `ZeroExtend(imm12)` and the Arm ARM
//!   `DecodeBitMasks`, transcribed independently of the encoder's search. An
//!   immediate the encoder cannot represent builds no obligation.
//!
//! Neither side restates the matcher's reading of the window, so a matcher that
//! picks the wrong immediate, register or operation states a false obligation
//! and the solver refutes it. The two sides are never structurally identical:
//! the materializer and the replacement carry their immediates in different
//! fields, and [`window_obligation`] refuses an `X == X` pair outright.
//!
//! What an obligation does not establish: that the window is all that happens
//! to the consumer's operands. That a removed materializer is the reaching
//! definition of its register, and that no other instruction reads that
//! register, are structural facts the matchers decide from the shared
//! operand-role model before an obligation is built; the window takes them as
//! given.

use std::collections::{BTreeSet, HashMap};

use trust_cg_ir::{AArch64Opcode, MachInst, MachOperand, RegClass, VReg};

use crate::aarch64_value_decode_proofs::{decode_logical_imm, move_wide_fields};
use crate::smt::SmtExpr;

/// `source` (the original window) must equal `target` (the replacement
/// window) for every value of `vars`.
#[derive(Debug, Clone, PartialEq)]
pub(super) struct RewriteObligation {
    pub(super) source: SmtExpr,
    pub(super) target: SmtExpr,
    pub(super) vars: Vec<(String, u32)>,
}

/// Build the obligation that `observed` holds the same value after `original`
/// as after `replacement`.
///
/// Returns `None` when either window leaves the modeled fragment (an opcode,
/// operand shape or register class the interpreter does not know, or an
/// immediate the encoder cannot represent), or when the two sides would be
/// structurally identical. A caller must treat `None` as a rejected
/// candidate.
pub(super) fn window_obligation(
    original: &[&MachInst],
    replacement: &[&MachInst],
    observed: VReg,
) -> Option<RewriteObligation> {
    let mut before = Window::new(observed.class)?;
    for inst in original {
        before.step(inst)?;
    }
    let mut after = Window::new(observed.class)?;
    for inst in replacement {
        after.step(inst)?;
    }
    let source = before.value(observed)?;
    let target = after.value(observed)?;
    if source == target {
        return None;
    }
    let width = before.width;
    let vars = before
        .inputs
        .union(&after.inputs)
        .map(|&id| (input_name(id), width))
        .collect();
    Some(RewriteObligation {
        source,
        target,
        vars,
    })
}

/// The free variable standing for `v<id>`'s value on entry to a window.
fn input_name(id: u32) -> String {
    format!("v{id}")
}

fn register_width(class: RegClass) -> Option<u32> {
    match class {
        RegClass::Gpr32 => Some(32),
        RegClass::Gpr64 => Some(64),
        _ => None,
    }
}

fn low_mask(width: u32) -> u64 {
    if width >= 64 {
        u64::MAX
    } else {
        (1u64 << width) - 1
    }
}

/// A straight-line run of machine instructions over general-purpose vregs of
/// one class, interpreted symbolically.
struct Window {
    class: RegClass,
    width: u32,
    /// The value each vreg the window has written holds.
    written: HashMap<u32, SmtExpr>,
    /// Vregs the window read before writing them.
    inputs: BTreeSet<u32>,
}

impl Window {
    fn new(class: RegClass) -> Option<Self> {
        Some(Self {
            class,
            width: register_width(class)?,
            written: HashMap::new(),
            inputs: BTreeSet::new(),
        })
    }

    fn register(&self, operand: &MachOperand) -> Option<VReg> {
        let vreg = operand.as_vreg()?;
        (vreg.class == self.class).then_some(vreg)
    }

    fn value(&mut self, vreg: VReg) -> Option<SmtExpr> {
        self.read(&MachOperand::VReg(vreg))
    }

    fn read(&mut self, operand: &MachOperand) -> Option<SmtExpr> {
        let vreg = self.register(operand)?;
        Some(match self.written.get(&vreg.id) {
            Some(value) => value.clone(),
            None => {
                self.inputs.insert(vreg.id);
                SmtExpr::var(input_name(vreg.id), self.width)
            }
        })
    }

    fn constant(&self, value: u64) -> SmtExpr {
        SmtExpr::bv_const(value & low_mask(self.width), self.width)
    }

    /// Run one instruction. `None` when it is outside the modeled fragment.
    fn step(&mut self, inst: &MachInst) -> Option<()> {
        use AArch64Opcode::*;
        let operands = inst.operands.as_slice();
        let value = match inst.opcode {
            Movz | Movn | Movk => {
                let (imm16, hw) = move_wide_fields(operands, self.width)?;
                // MOVZ/MOVN/MOVK: `pos = UInt(hw:'0000')`, `result<pos+15:pos>
                // = imm16`.
                let pos = 16 * hw;
                let field = SmtExpr::bv_const(imm16, 16)
                    .zero_ext(self.width - 16)
                    .bvshl(self.constant(u64::from(pos)));
                match inst.opcode {
                    Movz => field,
                    Movn => field.bvxor(self.constant(u64::MAX)),
                    // MOVK keeps every other bit of the destination.
                    _ => {
                        let kept = self.read(operands.first()?)?;
                        kept.bvand(self.constant(!(0xFFFFu64 << pos))).bvor(field)
                    }
                }
            }
            AddRR | AndRR | MulRR => {
                let [_, n, m] = operands else {
                    return None;
                };
                let (n, m) = (self.read(n)?, self.read(m)?);
                match inst.opcode {
                    AddRR => n.bvadd(m),
                    AndRR => n.bvand(m),
                    _ => n.bvmul(m),
                }
            }
            AddRI => {
                let [_, n, MachOperand::Imm(imm)] = operands else {
                    return None;
                };
                let (sh, imm12) = encode_add_imm(*imm)?;
                // ADD (immediate): `imm = ZeroExtend(imm12, datasize)`, shifted
                // left by 12 when `sh == 1`.
                let mut imm = SmtExpr::bv_const(u64::from(imm12), 12).zero_ext(self.width - 12);
                if sh == 1 {
                    imm = imm.bvshl(self.constant(12));
                }
                self.read(n)?.bvadd(imm)
            }
            AndRI => {
                let [_, n, MachOperand::Imm(imm)] = operands else {
                    return None;
                };
                let (n_bit, immr, imms) = encode_logical_imm(*imm, self.width)?;
                let mask = decode_logical_imm(n_bit, immr, imms, self.width)?;
                self.read(n)?.bvand(self.constant(mask))
            }
            _ => return None,
        };
        let destination = self.register(operands.first()?)?;
        self.written.insert(destination.id, value);
        Some(())
    }
}

/// The `(sh, imm12)` fields `trust-cg-codegen` encodes for `AddRI`: only the
/// unshifted form, for an immediate in `0..=0xFFF`.
pub(super) fn encode_add_imm(imm: i64) -> Option<(u32, u32)> {
    (0..=0xFFF)
        .contains(&imm)
        .then(|| (0, u32::try_from(imm).expect("range-checked imm12")))
}

fn rotate_right_within(value: u64, rotation: u32, width: u32) -> u64 {
    let rotation = rotation % width;
    let mask = low_mask(width);
    let value = value & mask;
    if rotation == 0 {
        value
    } else {
        ((value >> rotation) | (value << (width - rotation))) & mask
    }
}

fn replicate(element: u64, element_width: u32, width: u32) -> u64 {
    let mut out = 0;
    let mut shift = 0;
    while shift < width {
        out |= element << shift;
        shift += element_width;
    }
    out & low_mask(width)
}

/// The `(N, immr, imms)` fields `trust-cg-codegen` encodes for a logical
/// immediate `raw` of a `width`-bit register: the first element size, run
/// length and rotation, in that search order, whose replication is `raw`
/// masked to the register. `None` for all-zeros, all-ones and every value
/// that is not a rotated run of ones replicated across the register.
pub(super) fn encode_logical_imm(raw: i64, width: u32) -> Option<(u32, u32, u32)> {
    let register_mask = low_mask(width);
    let value = (raw as u64) & register_mask;
    if value == 0 || value == register_mask {
        return None;
    }
    let element_widths: &[u32] = if width == 64 {
        &[2, 4, 8, 16, 32, 64]
    } else {
        &[2, 4, 8, 16, 32]
    };
    for &element_width in element_widths {
        for ones_len in 1..element_width {
            for rotation in 0..element_width {
                let element = rotate_right_within(low_mask(ones_len), rotation, element_width);
                if replicate(element, element_width, width) == value {
                    let n = u32::from(element_width == 64);
                    let immr = rotation & 0x3f;
                    let imms = (!((element_width << 1) - 1) & 0x3f) | (ones_len - 1);
                    return Some((n, immr, imms));
                }
            }
        }
    }
    None
}

#[cfg(test)]
mod tests {
    use super::*;

    fn vreg(id: u32, class: RegClass) -> MachOperand {
        MachOperand::VReg(VReg::new(id, class))
    }

    fn inst(opcode: AArch64Opcode, operands: Vec<MachOperand>) -> MachInst {
        MachInst::new(opcode, operands)
    }

    /// Every `(N, immr, imms)` the decoder accepts names a logical immediate
    /// the encoder finds again, possibly under different fields that decode to
    /// the same value; every value the encoder accepts decodes back to itself.
    #[test]
    fn logical_immediate_fields_round_trip_exhaustively() {
        for width in [32u32, 64] {
            let mut decoded_values = BTreeSet::new();
            for n in 0..2 {
                for immr in 0..64 {
                    for imms in 0..64 {
                        let Some(value) = decode_logical_imm(n, immr, imms, width) else {
                            continue;
                        };
                        decoded_values.insert(value);
                        let (n2, immr2, imms2) = encode_logical_imm(value as i64, width)
                            .unwrap_or_else(|| {
                                panic!("{width}: {value:#x} decodes but not encodes")
                            });
                        assert_eq!(decode_logical_imm(n2, immr2, imms2, width), Some(value));
                    }
                }
            }
            // The Arm ARM counts 1302 32-bit and 5334 64-bit logical immediates.
            let expected = if width == 32 { 1302 } else { 5334 };
            assert_eq!(decoded_values.len(), expected, "width {width}");
        }
        assert_eq!(encode_logical_imm(0, 32), None);
        assert_eq!(encode_logical_imm(0xFFFF_FFFF, 32), None);
        assert_eq!(encode_logical_imm(-1, 64), None);
        assert_eq!(encode_logical_imm(0x1234_5678, 32), None);
    }

    /// The encoder mirrors here must produce the same words as the encoder
    /// `trust-cg-codegen` really runs, over every logical immediate and the
    /// whole `imm12` range, so "as actually encoded" is a checked claim.
    #[test]
    fn encoder_mirrors_match_the_real_aarch64_encoder() {
        use trust_cg_codegen::aarch64::encode::encode_instruction;
        use trust_cg_ir::regs::{W0, W1, X0, X1};

        for (width, rd, rn) in [(32u32, W0, W1), (64, X0, X1)] {
            let sf = u32::from(width == 64);
            let mut checked = 0usize;
            for n in 0..2 {
                for immr in 0..64 {
                    for imms in 0..64 {
                        let Some(value) = decode_logical_imm(n, immr, imms, width) else {
                            continue;
                        };
                        let and = inst(
                            AArch64Opcode::AndRI,
                            vec![
                                MachOperand::PReg(rd),
                                MachOperand::PReg(rn),
                                MachOperand::Imm(value as i64),
                            ],
                        );
                        let word = encode_instruction(&and).expect("encodable logical immediate");
                        let (fn_, fr, fs) = encode_logical_imm(value as i64, width).unwrap();
                        let expected = (sf << 31)
                            | (0b100100 << 23)
                            | (fn_ << 22)
                            | (fr << 16)
                            | (fs << 10)
                            | (1 << 5);
                        assert_eq!(word, expected, "AND #{value:#x} width {width}");
                        // Decode the fields of the word the real encoder emitted.
                        let decoded = decode_logical_imm(
                            (word >> 22) & 1,
                            (word >> 16) & 0x3f,
                            (word >> 10) & 0x3f,
                            width,
                        );
                        assert_eq!(decoded, Some(value));
                        checked += 1;
                    }
                }
            }
            assert!(checked > 1000, "{checked}");

            for imm in [0i64, 1, 7, 0x7FF, 0xFFF, 0x1000, -1] {
                let add = inst(
                    AArch64Opcode::AddRI,
                    vec![
                        MachOperand::PReg(rd),
                        MachOperand::PReg(rn),
                        MachOperand::Imm(imm),
                    ],
                );
                match (encode_instruction(&add), encode_add_imm(imm)) {
                    (Ok(word), Some((sh, imm12))) => {
                        assert_eq!((word >> 22) & 1, sh, "ADD #{imm}");
                        assert_eq!((word >> 10) & 0xFFF, imm12, "ADD #{imm}");
                    }
                    (Err(_), None) => {}
                    (real, mirror) => panic!("ADD #{imm}: encoder {real:?}, mirror {mirror:?}"),
                }
            }

            for (opcode, operands) in [
                (AArch64Opcode::Movz, vec![MachOperand::Imm(0xBEEF)]),
                (
                    AArch64Opcode::Movk,
                    vec![MachOperand::Imm(0x1234), MachOperand::Imm(16)],
                ),
                (AArch64Opcode::Movn, vec![MachOperand::Imm(0x00FF)]),
            ] {
                let mut all = vec![MachOperand::PReg(rd)];
                all.extend(operands);
                let word = encode_instruction(&inst(opcode, all.clone())).expect("move wide");
                let (imm16, hw) = move_wide_fields(&all, width).unwrap();
                assert_eq!(u64::from((word >> 5) & 0xFFFF), imm16, "{opcode:?}");
                assert_eq!((word >> 21) & 0b11, hw, "{opcode:?}");
            }
        }
    }

    #[test]
    fn obligations_are_built_from_the_windows_not_restated() {
        let class = RegClass::Gpr32;
        let movz = inst(
            AArch64Opcode::Movz,
            vec![vreg(10, class), MachOperand::Imm(7)],
        );
        let add = inst(
            AArch64Opcode::AddRR,
            vec![vreg(11, class), vreg(0, class), vreg(10, class)],
        );
        let addri = inst(
            AArch64Opcode::AddRI,
            vec![vreg(11, class), vreg(0, class), MachOperand::Imm(7)],
        );
        let observed = VReg::new(11, class);
        let obligation = window_obligation(&[&movz, &add], &[&addri], observed).unwrap();
        assert_ne!(obligation.source, obligation.target, "never X == X");
        assert_eq!(obligation.vars, vec![("v0".to_string(), 32)]);
        for x in [0u64, 1, 0xFFFF_FFF9, 0xFFFF_FFFF, 0x1234_5678] {
            let env = HashMap::from([("v0".to_string(), x)]);
            let expected = x.wrapping_add(7) & 0xFFFF_FFFF;
            assert_eq!(obligation.source.try_eval(&env).unwrap().as_u64(), expected);
            assert_eq!(obligation.target.try_eval(&env).unwrap().as_u64(), expected);
        }

        // Out-of-fragment windows and unencodable replacements build nothing.
        let wide = inst(
            AArch64Opcode::AddRI,
            vec![vreg(11, class), vreg(0, class), MachOperand::Imm(0x1000)],
        );
        assert!(window_obligation(&[&movz, &add], &[&wide], observed).is_none());
        let cmp = inst(AArch64Opcode::CmpRR, vec![vreg(10, class), vreg(1, class)]);
        assert!(window_obligation(&[&movz, &cmp], &[&addri], observed).is_none());
        let mixed = inst(
            AArch64Opcode::AddRR,
            vec![vreg(11, class), vreg(0, RegClass::Gpr64), vreg(10, class)],
        );
        assert!(window_obligation(&[&movz, &mixed], &[&addri], observed).is_none());
        // Identical windows would be X == X.
        assert!(window_obligation(&[&addri], &[&addri], observed).is_none());
    }

    // -----------------------------------------------------------------------
    // Solver-backed: the payload obligations and their mutation controls
    // -----------------------------------------------------------------------

    use crate::cegis::{CegisLoop, CegisResult};
    use crate::cegis_pass::ReplacementMutation;

    const CHECKER_UNAVAILABLE: &str =
        "solver returned unknown: AY reported UNSAT but it CANNOT BE CHECKED here —";

    /// A payload window: the original instructions, the replacement the
    /// matcher proposes, the observed register and the constant register.
    struct Payload {
        label: &'static str,
        original: Vec<MachInst>,
        replacement: MachInst,
        /// Layer A keeps its `Movz`; it runs in the rewritten window too.
        kept: Option<MachInst>,
        observed: VReg,
        constant: MachOperand,
    }

    impl Payload {
        fn obligation(&self, replacement: &MachInst) -> Option<RewriteObligation> {
            let original: Vec<&MachInst> = self.original.iter().collect();
            let rewritten: Vec<&MachInst> = self.kept.iter().chain([replacement]).collect();
            window_obligation(&original, &rewritten, self.observed)
        }
    }

    fn payloads() -> Vec<Payload> {
        let mut out = Vec::new();
        for (class, width) in [(RegClass::Gpr32, 32u32), (RegClass::Gpr64, 64)] {
            let v = |id| vreg(id, class);
            let zero = inst(AArch64Opcode::Movz, vec![v(10), MachOperand::Imm(0)]);
            out.push(Payload {
                label: if width == 32 {
                    "A/32 MulRR by Movz #0"
                } else {
                    "A/64 MulRR by Movz #0"
                },
                original: vec![
                    zero.clone(),
                    inst(AArch64Opcode::MulRR, vec![v(11), v(0), v(10)]),
                ],
                replacement: inst(AArch64Opcode::Movz, vec![v(11), MachOperand::Imm(0)]),
                kept: Some(zero),
                observed: VReg::new(11, class),
                constant: v(10),
            });
            for value in [7i64, 0xFFF] {
                out.push(Payload {
                    label: if width == 32 {
                        "B/32 Movz+AddRR"
                    } else {
                        "B/64 Movz+AddRR"
                    },
                    original: vec![
                        inst(AArch64Opcode::Movz, vec![v(10), MachOperand::Imm(value)]),
                        inst(AArch64Opcode::AddRR, vec![v(11), v(0), v(10)]),
                    ],
                    replacement: inst(
                        AArch64Opcode::AddRI,
                        vec![v(11), v(0), MachOperand::Imm(value)],
                    ),
                    kept: None,
                    observed: VReg::new(11, class),
                    constant: v(10),
                });
            }
            // revertBits masks: a Movz and a Movk per further halfword.
            let mut chain = vec![inst(
                AArch64Opcode::Movz,
                vec![v(10), MachOperand::Imm(0x5555)],
            )];
            for shift in (16..width).step_by(16) {
                chain.push(inst(
                    AArch64Opcode::Movk,
                    vec![
                        v(10),
                        MachOperand::Imm(0x5555),
                        MachOperand::Imm(i64::from(shift)),
                    ],
                ));
            }
            chain.push(inst(AArch64Opcode::AndRR, vec![v(11), v(0), v(10)]));
            out.push(Payload {
                label: if width == 32 {
                    "C/32 Movz+Movk+AndRR"
                } else {
                    "C/64 Movz+Movk*3+AndRR"
                },
                original: chain,
                replacement: inst(
                    AArch64Opcode::AndRI,
                    vec![
                        v(11),
                        v(0),
                        MachOperand::Imm((0x5555_5555_5555_5555u64 & low_mask(width)) as i64),
                    ],
                ),
                kept: None,
                observed: VReg::new(11, class),
                constant: v(10),
            });
        }
        // A Movn-seeded mask: !0xFF00 = 0xFFFF00FF.
        let v = |id| vreg(id, RegClass::Gpr32);
        out.push(Payload {
            label: "C/32 Movn+AndRR",
            original: vec![
                inst(AArch64Opcode::Movn, vec![v(10), MachOperand::Imm(0xFF00)]),
                inst(AArch64Opcode::AndRR, vec![v(11), v(0), v(10)]),
            ],
            replacement: inst(
                AArch64Opcode::AndRI,
                vec![v(11), v(0), MachOperand::Imm(0xFFFF_00FF)],
            ),
            kept: None,
            observed: VReg::new(11, RegClass::Gpr32),
            constant: v(10),
        });
        out
    }

    /// The solver alone decides: no concrete seeds precede the query.
    fn solve(obligation: &RewriteObligation) -> CegisResult {
        CegisLoop::new(1, 30_000).verify(&obligation.source, &obligation.target, &obligation.vars)
    }

    fn checker_missing(result: &CegisResult) -> bool {
        matches!(result, CegisResult::Error(reason) if reason.starts_with(CHECKER_UNAVAILABLE))
    }

    /// Every payload shape's obligation is non-degenerate and discharged: AY
    /// reports UNSAT and `CegisLoop` returns `Equivalent` only after the
    /// identity-pinned Clean checker accepts AY's Alethe proof of it.
    #[test]
    fn payload_obligations_are_discharged_with_a_checked_certificate() {
        if !crate::ay_bridge::ay_available() {
            eprintln!("SKIP: no AY solver on PATH; the obligations were not discharged");
            return;
        }
        for payload in payloads() {
            let obligation = payload
                .obligation(&payload.replacement)
                .unwrap_or_else(|| panic!("{}: no obligation", payload.label));
            assert_ne!(obligation.source, obligation.target, "{}", payload.label);
            let result = solve(&obligation);
            eprintln!(
                "TCG_CEGIS_OBLIGATION {} vars={:?}\n  source: {}\n  target: {}\n  verdict: {result:?}",
                payload.label, obligation.vars, obligation.source, obligation.target
            );
            if checker_missing(&result) {
                eprintln!("SKIP: AY proved it but no Clean checker is usable here");
                continue;
            }
            assert!(
                matches!(result, CegisResult::Equivalent { .. }),
                "{}: {result:?}",
                payload.label
            );
        }
    }

    /// The mutation control. A matcher that corrupts the replacement's
    /// immediate, register or operation now states a false obligation, and the
    /// solver itself (no concrete seeds) returns a distinguishing model. The
    /// revision 2 obligation, rebuilt from the matcher's constant alone, is
    /// the same `X op k == X op k` whatever the replacement says, so it
    /// accepted every one of these corrupted rewrites.
    #[test]
    fn corrupted_replacements_are_refuted_by_the_solver() {
        if !crate::ay_bridge::ay_available() {
            eprintln!("SKIP: no AY solver on PATH; the mutations were not refuted");
            return;
        }
        let mut refuted = 0usize;
        let mut unencodable = 0usize;
        for payload in payloads() {
            for mutation in [
                ReplacementMutation::Immediate,
                ReplacementMutation::SourceRegister,
                ReplacementMutation::Operation,
            ] {
                let mut corrupted = payload.replacement.clone();
                mutation.apply(&mut corrupted, Some(&payload.constant));
                if (corrupted.opcode, &corrupted.operands)
                    == (payload.replacement.opcode, &payload.replacement.operands)
                {
                    // Layer A's `Movz dst, #0` has no register or operation.
                    continue;
                }
                let label = format!("{} {mutation:?} -> {corrupted:?}", payload.label);
                let Some(obligation) = payload.obligation(&corrupted) else {
                    // An `AddRI` of a logical-immediate mask has no `imm12`
                    // encoding: the candidate is rejected before any query.
                    assert!(
                        mutation == ReplacementMutation::Operation
                            && corrupted.opcode == AArch64Opcode::AddRI,
                        "{label}: no obligation"
                    );
                    unencodable += 1;
                    continue;
                };
                let result = solve(&obligation);
                eprintln!("TCG_CEGIS_MUTATION {label}: {result:?}");
                let CegisResult::NotEquivalent {
                    counterexample,
                    found_by_concrete: false,
                } = &result
                else {
                    panic!("{label}: expected a solver refutation, got {result:?}");
                };
                let source = obligation.source.try_eval(&counterexample.values).unwrap();
                let target = obligation.target.try_eval(&counterexample.values).unwrap();
                assert_ne!(
                    source, target,
                    "{label}: the model must distinguish the sides"
                );
                refuted += 1;
            }
        }
        // A: Immediate at both widths; B: 3 mutations x 2 immediates x 2
        // widths; C: Immediate and SourceRegister for its 3 masks.
        assert_eq!((refuted, unencodable), (2 + 12 + 6, 3));
    }

    /// Revision 2's obligations, rebuilt verbatim: they never read the
    /// replacement, so the solver accepts them for every corrupted rewrite
    /// above. Layer B's and C's were structurally `X == X`.
    #[test]
    fn the_revision_2_obligations_accepted_corrupted_rewrites() {
        if !crate::ay_bridge::ay_available() {
            eprintln!("SKIP: no AY solver on PATH");
            return;
        }
        let width = 32;
        let legacy = [
            (
                "A",
                SmtExpr::var("x", width).bvmul(SmtExpr::bv_const(0, width)),
                SmtExpr::bv_const(0, width),
                "x",
            ),
            (
                "B",
                SmtExpr::var("y", width).bvadd(SmtExpr::bv_const(7, width)),
                SmtExpr::var("y", width).bvadd(SmtExpr::bv_const(7, width)),
                "y",
            ),
            (
                "C",
                SmtExpr::var("x", width).bvand(SmtExpr::bv_const(0x5555_5555, width)),
                SmtExpr::var("x", width).bvand(SmtExpr::bv_const(0x5555_5555, width)),
                "x",
            ),
        ];
        for (layer, source, target, var) in legacy {
            let degenerate = source == target;
            let result =
                CegisLoop::new(1, 30_000).verify(&source, &target, &[(var.to_string(), width)]);
            eprintln!("TCG_CEGIS_LEGACY layer={layer} degenerate={degenerate} verdict={result:?}");
            if checker_missing(&result) {
                continue;
            }
            assert!(
                matches!(result, CegisResult::Equivalent { .. }),
                "{layer}: {result:?}"
            );
            assert_eq!(degenerate, layer != "A");
        }
    }
}
