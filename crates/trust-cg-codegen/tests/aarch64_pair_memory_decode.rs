// Copyright 2026 Andrew Yates | Apache-2.0
//! Six pair-wrapper intent/word controls and finite Linux native comparisons.
//! Independent redundancy and executions, not source binding or formal proof.

use trust_cg_codegen::{
    aarch64::{decode_check::A64DecodeCheck, encode::encode_instruction},
    decode_check::{
        DecodeCheck, DecodeCheckItem, DecodeCheckMode, DecodeCheckOutcome, FixupHole,
        FixupHoleKind, run_decode_check,
    },
};
use trust_cg_ir::{
    AArch64Opcode as Op, MachInst, MachOperand as Arg,
    regs::{self, PReg, RegClass, SpecialReg, VReg},
    types::StackSlotId,
};

#[cfg(all(
    target_arch = "aarch64",
    any(target_os = "macos", all(target_os = "linux", target_env = "gnu"))
))]
#[path = "common/pair_memory_native.rs"]
mod native;
#[cfg(all(
    target_arch = "aarch64",
    any(target_os = "macos", all(target_os = "linux", target_env = "gnu"))
))]
#[path = "common/rosetta.rs"]
mod process;

#[cfg(all(
    target_arch = "aarch64",
    any(target_os = "macos", all(target_os = "linux", target_env = "gnu"))
))]
#[path = "common/native_host.rs"]
mod native_host;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Data {
    W,
    X,
    S,
    D,
    Q,
}
const DATA: [Data; 5] = [Data::W, Data::X, Data::S, Data::D, Data::Q];
const OPS: [Op; 6] = [
    Op::StpRI,
    Op::LdpRI,
    Op::StpPreIndex,
    Op::LdpPostIndex,
    Op::NeonLdpQPost,
    Op::NeonStpQPost,
];

impl Data {
    fn bytes(self) -> i64 {
        match self {
            Self::W | Self::S => 4,
            Self::X | Self::D => 8,
            Self::Q => 16,
        }
    }
    fn fp(self) -> bool {
        !matches!(self, Self::W | Self::X)
    }
    // Only the Linux-gnu native cases below call this; elsewhere it is dead and
    // the crate denies dead code, so it is gated exactly like its callers.
    #[cfg(all(
        target_arch = "aarch64",
        any(target_os = "macos", all(target_os = "linux", target_env = "gnu"))
    ))]
    fn bank(self) -> char {
        match self {
            Self::W => 'w',
            Self::X => 'x',
            Self::S => 's',
            Self::D => 'd',
            Self::Q => 'q',
        }
    }
    fn operand(self, n: u16) -> Arg {
        assert!(n < 32);
        Arg::PReg(match self {
            Self::W if n == 31 => regs::WZR,
            Self::X if n == 31 => regs::XZR,
            Self::W => PReg::new(32 + n),
            Self::X => PReg::new(n),
            Self::S => PReg::new(128 + n),
            Self::D => PReg::new(96 + n),
            Self::Q => PReg::new(64 + n),
        })
    }
}

fn load(op: Op) -> bool {
    matches!(op, Op::LdpRI | Op::LdpPostIndex | Op::NeonLdpQPost)
}
fn mode(op: Op) -> u32 {
    match op {
        Op::StpRI | Op::LdpRI => 2,
        Op::StpPreIndex => 3,
        Op::LdpPostIndex | Op::NeonLdpQPost | Op::NeonStpQPost => 1,
        _ => unreachable!(),
    }
}
fn profiles() -> Vec<(Op, Data)> {
    OPS.into_iter()
        .flat_map(|op| {
            DATA.into_iter()
                .filter(move |d| {
                    !matches!(op, Op::NeonLdpQPost | Op::NeonStpQPost) || *d == Data::Q
                })
                .map(move |d| (op, d))
        })
        .collect()
}
fn inst(op: Op, data: Data, rt: u16, rt2: u16, rn: u16, offset: Option<i64>) -> MachInst {
    let mut args = vec![
        data.operand(rt),
        data.operand(rt2),
        Arg::PReg(PReg::new(rn)),
    ];
    if let Some(n) = offset {
        args.push(Arg::Imm(n));
    }
    MachInst::new(op, args)
}
fn word(op: Op, data: Data, rt: u16, rt2: u16, rn: u16, offset: i64) -> u32 {
    assert!(rt < 32 && rt2 < 32 && rn < 32 && offset % data.bytes() == 0);
    let scaled = offset / data.bytes();
    assert!((-64..=63).contains(&scaled));
    let opc = match data {
        Data::W | Data::S => 0,
        Data::D => 1,
        Data::X | Data::Q => 2,
    };
    // Arm pair format: opc, fixed101, V, fixed0, mode, L, signed imm7,
    // Rt2,Rn,Rt. Scale is one element, never the entire pair size.
    (opc << 30)
        | 0x2800_0000
        | (u32::from(data.fp()) << 26)
        | (mode(op) << 23)
        | (u32::from(load(op)) << 22)
        | (((scaled as u32) & 127) << 15)
        | (u32::from(rt2) << 10)
        | (u32::from(rn) << 5)
        | u32::from(rt)
}
fn legal_fields(op: Op, data: Data, rt: u16, rt2: u16, rn: u16) -> bool {
    // Arm LDP's duplicate destination guard includes field31. Writeback
    // overlap only concerns GPR transfers; equal FP/X fields are distinct.
    !(load(op) && rt == rt2 || mode(op) != 2 && !data.fp() && rn != 31 && (rn == rt || rn == rt2))
}
fn enforce(intent: &MachInst, bytes: &[u8], hole: Option<FixupHole>) -> bool {
    run_decode_check(
        &A64DecodeCheck,
        &[DecodeCheckItem {
            start: 0,
            end: bytes.len(),
            intent: intent.clone(),
            hole,
        }],
        bytes,
        DecodeCheckMode::Enforce,
    )
    .is_ok()
}

#[derive(Default)]
struct Census {
    rows: usize,
    failures: usize,
    first: Vec<String>,
}
impl Census {
    fn record(&mut self, ok: bool, detail: impl FnOnce() -> String) {
        self.rows += 1;
        if !ok {
            self.failures += 1;
            if self.first.len() < 16 {
                self.first.push(detail());
            }
        }
    }
    fn accept(&mut self, intent: &MachInst, expected: u32) {
        let enc = encode_instruction(intent);
        let bytes = expected.to_le_bytes();
        let dec = A64DecodeCheck.check_one(intent, &bytes, None);
        let gate = enforce(intent, &bytes, None);
        self.record(enc.as_ref().is_ok_and(|w| *w==expected) && matches!(dec,DecodeCheckOutcome::Match) && gate,
            || format!("accept {intent:?} expected={expected:08x} encoder={enc:?} decoder={dec:?} enforce={gate}"));
    }
    fn refuse(&mut self, intent: &MachInst, bytes: u32) {
        let enc = encode_instruction(intent);
        let bytes = bytes.to_le_bytes();
        let dec = A64DecodeCheck.check_one(intent, &bytes, None);
        let gate = enforce(intent, &bytes, None);
        self.record(
            enc.is_err() && matches!(dec, DecodeCheckOutcome::Mismatch(_)) && !gate,
            || format!("refuse {intent:?} encoder={enc:?} decoder={dec:?} enforce={gate}"),
        );
    }
    fn reject_bytes(&mut self, intent: &MachInst, bytes: &[u8], hole: Option<FixupHole>) {
        let dec = A64DecodeCheck.check_one(intent, bytes, hole.as_ref());
        let gate = enforce(intent, bytes, hole);
        self.record(matches!(dec,DecodeCheckOutcome::Mismatch(_)) && !gate,
            || format!("reject bytes {intent:?} bytes={bytes:x?} hole={hole:?} decoder={dec:?} enforce={gate}"));
    }
    fn finish(self, expected: usize, name: &str) {
        eprintln!(
            "PAIR_CENSUS {name} attempted={} failures={}",
            self.rows, self.failures
        );
        assert_eq!(self.rows, expected, "{name} denominator");
        assert_eq!(self.failures, 0, "{name}: {}", self.first.join("\n"));
    }
}

#[test]
fn pair_literal_words_and_all_bit_mutations() {
    let mut checks = Census::default();
    for (op, data) in profiles() {
        // Independent literal base words, all Rt9,Rt2=10,Rn11,offset0.
        let literal = match (op, data) {
            (Op::StpRI, Data::W) => 0x29002969,
            (Op::StpRI, Data::X) => 0xa9002969,
            (Op::StpRI, Data::S) => 0x2d002969,
            (Op::StpRI, Data::D) => 0x6d002969,
            (Op::StpRI, Data::Q) => 0xad002969,
            (Op::LdpRI, Data::W) => 0x29402969,
            (Op::LdpRI, Data::X) => 0xa9402969,
            (Op::LdpRI, Data::S) => 0x2d402969,
            (Op::LdpRI, Data::D) => 0x6d402969,
            (Op::LdpRI, Data::Q) => 0xad402969,
            (Op::StpPreIndex, Data::W) => 0x29802969,
            (Op::StpPreIndex, Data::X) => 0xa9802969,
            (Op::StpPreIndex, Data::S) => 0x2d802969,
            (Op::StpPreIndex, Data::D) => 0x6d802969,
            (Op::StpPreIndex, Data::Q) => 0xad802969,
            (Op::LdpPostIndex, Data::W) => 0x28c02969,
            (Op::LdpPostIndex, Data::X) => 0xa8c02969,
            (Op::LdpPostIndex, Data::S) => 0x2cc02969,
            (Op::LdpPostIndex, Data::D) => 0x6cc02969,
            (Op::LdpPostIndex, Data::Q) => 0xacc02969,
            (Op::NeonLdpQPost, Data::Q) => 0xacc02969,
            (Op::NeonStpQPost, Data::Q) => 0xac802969,
            _ => unreachable!(),
        };
        assert_eq!(word(op, data, 9, 10, 11, 0), literal);
        for offset in [None, Some(0)] {
            let intent = inst(op, data, 9, 10, 11, offset);
            checks.accept(&intent, literal);
            for bit in 0..32 {
                checks.reject_bytes(&intent, &(literal ^ (1 << bit)).to_le_bytes(), None);
            }
        }
    }
    checks.finish(44 + 1408, "literal_and_mutants");
}

#[test]
fn pair_all_register_fields_and_architectural_alias_constraints() {
    let mut checks = Census::default();
    let (mut admitted, mut refused) = (0, 0);
    for (op, data) in profiles() {
        for rt in 0..32 {
            for rt2 in 0..32 {
                for rn in 0..32 {
                    let intent = inst(op, data, rt, rt2, rn, Some(0));
                    let bits = word(op, data, rt, rt2, rn, 0);
                    if legal_fields(op, data, rt, rt2, rn) {
                        checks.accept(&intent, bits);
                        admitted += 1;
                    } else {
                        checks.refuse(&intent, bits);
                        refused += 1;
                    }
                }
            }
        }
    }
    assert_eq!((admitted, refused), (701_882, 19_014));
    checks.finish(720_896, "all_register_fields");
}

#[test]
fn pair_every_signed_scaled_immediate_field() {
    let mut checks = Census::default();
    for (op, data) in profiles() {
        for n in -64..=63 {
            let offset = n * data.bytes();
            checks.accept(
                &inst(op, data, 9, 10, 11, Some(offset)),
                word(op, data, 9, 10, 11, offset),
            );
        }
    }
    checks.finish(2_816, "all_imm7");
}

#[test]
fn pair_special_zero_and_sp_spellings_preserve_width() {
    let mut checks = Census::default();
    for op in [Op::StpRI, Op::LdpRI, Op::StpPreIndex, Op::LdpPostIndex] {
        for data in [Data::W, Data::X] {
            let zero = [
                data.operand(31),
                Arg::Special(if data == Data::W {
                    SpecialReg::WZR
                } else {
                    SpecialReg::XZR
                }),
            ];
            for zero_position in [0, 1] {
                for z in &zero {
                    for base in [Arg::PReg(regs::SP), Arg::Special(SpecialReg::SP)] {
                        for offset in [None, Some(0)] {
                            let (rt, rt2) = if zero_position == 0 {
                                (31, 10)
                            } else {
                                (9, 31)
                            };
                            let mut intent = inst(op, data, rt, rt2, 31, offset);
                            intent.operands[zero_position] = z.clone();
                            intent.operands[2] = base.clone();
                            checks.accept(&intent, word(op, data, rt, rt2, 31, 0));
                        }
                    }
                }
            }
            for first in &zero {
                for second in &zero {
                    for base in [Arg::PReg(regs::SP), Arg::Special(SpecialReg::SP)] {
                        for offset in [None, Some(0)] {
                            let mut intent = inst(op, data, 31, 31, 31, offset);
                            intent.operands[0] = first.clone();
                            intent.operands[1] = second.clone();
                            intent.operands[2] = base.clone();
                            let bits = word(op, data, 31, 31, 31, 0);
                            if load(op) {
                                checks.refuse(&intent, bits);
                            } else {
                                checks.accept(&intent, bits);
                            }
                        }
                    }
                }
            }
        }
    }
    for (op, data) in profiles() {
        for offset in [None, Some(0)] {
            let mut intent = inst(op, data, 9, 10, 31, offset);
            intent.operands[2] = Arg::Special(SpecialReg::SP);
            checks.accept(&intent, word(op, data, 9, 10, 31, 0));
        }
    }
    checks.finish(300, "special_aliases");
}

#[test]
fn pair_malformed_banks_arity_and_immediates_refuse() {
    let mut checks = Census::default();
    let mut expected = 0;
    for (op, data) in profiles() {
        let good = inst(op, data, 9, 10, 11, Some(0));
        let bits = word(op, data, 9, 10, 11, 0);
        let mut bad = Vec::new();
        for count in [0, 1, 2] {
            let mut m = good.clone();
            m.operands.truncate(count);
            bad.push(m);
        }
        for extra in [Arg::Imm(0), Arg::PReg(regs::X0)] {
            let mut m = good.clone();
            m.operands.push(extra);
            bad.push(m);
        }
        for position in [0, 1] {
            for operand in [
                Arg::PReg(regs::SP),
                Arg::PReg(regs::WSP),
                Arg::PReg(PReg::new(165)),
                Arg::PReg(PReg::new(197)),
                Arg::PReg(PReg::new(162)),
                Arg::PReg(PReg::new(229)),
                Arg::PReg(PReg::new(u16::MAX)),
                Arg::Special(SpecialReg::SP),
                Arg::Imm(0),
                Arg::VReg(VReg::new(7, RegClass::Gpr64)),
                Arg::StackSlot(StackSlotId(0)),
            ] {
                let mut m = good.clone();
                m.operands[position] = operand;
                bad.push(m);
            }
            for wrong in DATA {
                if wrong != data {
                    let mut m = good.clone();
                    m.operands[position] = wrong.operand(9);
                    bad.push(m);
                }
            }
            for (zero, bank) in [(SpecialReg::WZR, Data::W), (SpecialReg::XZR, Data::X)] {
                if data != bank {
                    let mut m = good.clone();
                    m.operands[position] = Arg::Special(zero);
                    bad.push(m);
                }
            }
        }
        for operand in [
            Arg::PReg(regs::W0),
            Arg::PReg(regs::WSP),
            Arg::PReg(regs::XZR),
            Arg::PReg(regs::WZR),
            Arg::PReg(regs::V0),
            Arg::PReg(regs::D0),
            Arg::PReg(regs::S0),
            Arg::PReg(PReg::new(165)),
            Arg::PReg(PReg::new(197)),
            Arg::PReg(PReg::new(162)),
            Arg::PReg(PReg::new(229)),
            Arg::PReg(PReg::new(u16::MAX)),
            Arg::Special(SpecialReg::XZR),
            Arg::Special(SpecialReg::WZR),
            Arg::Imm(0),
            Arg::VReg(VReg::new(8, RegClass::Gpr64)),
        ] {
            let mut m = good.clone();
            m.operands[2] = operand;
            bad.push(m);
        }
        for operand in [
            Arg::PReg(regs::X0),
            Arg::Special(SpecialReg::SP),
            Arg::VReg(VReg::new(9, RegClass::Gpr64)),
            Arg::StackSlot(StackSlotId(0)),
        ] {
            let mut m = good.clone();
            m.operands[3] = operand;
            bad.push(m);
        }
        let scale = data.bytes();
        for offset in [
            -65 * scale,
            64 * scale,
            i64::MIN,
            i64::MAX,
            -1,
            1,
            scale - 1,
            scale + 1,
        ] {
            let mut m = good.clone();
            m.operands[3] = Arg::Imm(offset);
            bad.push(m);
        }
        expected += bad.len();
        for intent in bad {
            checks.refuse(&intent, bits);
        }
    }
    assert_eq!(expected, 22 * (5 + 30 + 16 + 4 + 8) + 72);
    checks.finish(1_458, "malformed_intents");
}

#[test]
fn pair_relocation_holes_and_inexact_byte_extents_refuse() {
    let mut checks = Census::default();
    for (op, data) in profiles() {
        let intent = inst(op, data, 9, 10, 11, Some(0));
        let bits = word(op, data, 9, 10, 11, 0).to_le_bytes();
        for size in [0, 1, 2, 3, 5, 8] {
            let mut bytes = bits.to_vec();
            bytes.resize(size, 0);
            checks.reject_bytes(&intent, &bytes, None);
        }
        for kind in [
            FixupHoleKind::Branch,
            FixupHoleKind::Call,
            FixupHoleKind::GlobalRef,
            FixupHoleKind::ExternRefGot,
            FixupHoleKind::TlsTlv,
            FixupHoleKind::ConstPool,
        ] {
            for (offset_in_inst, width) in [(0, 4), (1, 2), (0, 0), (4, 8)] {
                checks.reject_bytes(
                    &intent,
                    &bits,
                    Some(FixupHole {
                        offset_in_inst,
                        width,
                        kind,
                    }),
                );
            }
        }
    }
    checks.finish(660, "holes_and_extents");
}

#[cfg(all(
    target_arch = "aarch64",
    any(target_os = "macos", all(target_os = "linux", target_env = "gnu"))
))]
#[test]
fn pair_native_parent_supported_forms_full_state() {
    native::run(false);
}

#[cfg(all(
    target_arch = "aarch64",
    any(target_os = "macos", all(target_os = "linux", target_env = "gnu"))
))]
#[test]
fn pair_native_new_writeback_widths_full_state() {
    native::run(true);
}

/// The proof lane's own pair encoder must agree with the emitter's, field for
/// field, on every shape it credits.
///
/// `trust-cg-verify` cannot depend on `trust-cg-codegen`, so
/// `aarch64_pair_memory_proofs::pair_memory_word` re-derives the Arm DDI0602
/// C4.1 load/store-pair layout independently. That independence is what makes
/// the pair-memory obligation's machine side evidence rather than a restatement
/// — and it is only worth anything if the word the proof reasons about is the
/// word the backend emits. This closes that loop in both directions:
///
/// * every shape the proof lane ADMITS must encode, and to the SAME word; and
/// * every shape the emitter accepts must be admitted by the proof lane, except
///   the two documented fail-closed narrowings (a load whose destination is the
///   discarded zero register, and — not reachable from this corpus — a still
///   virtual operand).
///
/// A divergence here means the proof lane is reasoning about an instruction the
/// backend does not emit, so it is a hard failure, not a census row.
#[test]
fn pair_proof_lane_word_matches_the_emitter() {
    use trust_cg_verify::aarch64_pair_memory_proofs::{pair_memory_intent, pair_memory_word};

    let mut rows = 0usize;
    let mut divergences: Vec<String> = Vec::new();
    for (op, data) in profiles() {
        for (rt, rt2, rn) in [
            (0u16, 1u16, 2u16),
            (1, 2, 31),
            (29, 30, 31),
            (31, 0, 3),
            (0, 31, 3),
            (5, 5, 7),
            (9, 10, 9),
            (30, 29, 30),
        ] {
            for scaled in [-64i64, -1, 0, 1, 63] {
                let offset = scaled * data.bytes();
                let intent_inst = inst(op, data, rt, rt2, rn, Some(offset));
                let emitted = encode_instruction(&intent_inst).ok();
                let proved = pair_memory_intent(&intent_inst).and_then(|i| pair_memory_word(&i));
                rows += 1;

                if let Some(proof_word) = proved {
                    if emitted != Some(proof_word) {
                        divergences.push(format!(
                            "proof admitted {intent_inst:?} as {proof_word:08x}, emitter gave \
                             {emitted:x?}"
                        ));
                    }
                    // Belt and braces: the word must also be the one this
                    // file's own hand-derived layout predicts.
                    if legal_fields(op, data, rt, rt2, rn)
                        && proof_word != word(op, data, rt, rt2, rn, offset)
                    {
                        divergences.push(format!(
                            "proof word {proof_word:08x} != census layout {:08x} for \
                             {intent_inst:?}",
                            word(op, data, rt, rt2, rn, offset)
                        ));
                    }
                    continue;
                }

                // The proof lane refused. That is only allowed when the
                // emitter also refuses, or for the documented zero-register
                // load-destination narrowing.
                let zero_dest_load =
                    load(op) && matches!(data, Data::W | Data::X) && (rt == 31 || rt2 == 31);
                if emitted.is_some() && !zero_dest_load {
                    divergences.push(format!(
                        "emitter encoded {intent_inst:?} as {emitted:x?} but the proof lane \
                         refused it"
                    ));
                }
            }
        }
    }
    eprintln!(
        "PAIR_PROOF_WORD attempted={rows} divergences={}",
        divergences.len()
    );
    assert_eq!(rows, 880, "proof/emitter agreement denominator");
    assert!(
        divergences.is_empty(),
        "{} proof/emitter word divergences; first 12: {:#?}",
        divergences.len(),
        &divergences[..divergences.len().min(12)]
    );
}

#[path = "common/fresh_dir.rs"]
mod fresh_dir;
