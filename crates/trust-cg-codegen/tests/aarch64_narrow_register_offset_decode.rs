// Copyright 2026 Andrew Yates | Apache-2.0
//! Exact byte/halfword RO intent/word controls plus bounded Linux native checks.
//! These finite byte checks do not establish source refinement or proof authority.

use trust_cg_codegen::{
    aarch64::{decode_check::A64DecodeCheck, encode::encode_instruction},
    decode_check::{
        DecodeCheck, DecodeCheckItem, DecodeCheckMode, DecodeCheckOutcome, FixupHole,
        FixupHoleKind, run_decode_check,
    },
    lower::encode_function,
};
use trust_cg_ir::{
    AArch64Opcode as Op, MachFunction, MachInst, MachOperand as Arg, Signature,
    regs::{self, PReg, RegClass, SpecialReg, VReg},
    types::{BlockId, FrameIdx, StackSlotId},
};

const OPS: [Op; 4] = [Op::LdrbRO, Op::LdrhRO, Op::StrbRO, Op::StrhRO];
const MODES: [Option<i64>; 9] = [
    None,
    Some(4),
    Some(5),
    Some(6),
    Some(7),
    Some(12),
    Some(13),
    Some(14),
    Some(15),
];

#[derive(Default)]
struct Census {
    checks: usize,
    failures: usize,
    examples: Vec<String>,
}

impl Census {
    fn record(&mut self, ok: bool, diagnostic: impl FnOnce() -> String) {
        self.checks += 1;
        if !ok {
            self.failures += 1;
            if self.examples.len() < 16 {
                self.examples.push(diagnostic());
            }
        }
    }

    fn finish(self, label: &str, rows: usize, expected_rows: usize, expected_checks: usize) {
        eprintln!(
            "NARROW_RO_CENSUS {label} rows={rows} checks={} failures={}",
            self.checks, self.failures
        );
        assert_eq!(rows, expected_rows, "{label} row census");
        assert_eq!(self.checks, expected_checks, "{label} check census");
        assert_eq!(self.failures, 0, "{label}: {}", self.examples.join("\n"));
    }
}

fn low32(mode: Option<i64>) -> bool {
    matches!(mode, Some(4 | 5 | 12 | 13))
}

fn data(wide: bool, field: u16) -> Arg {
    assert!(field < 32);
    Arg::PReg(match (wide, field) {
        (true, 31) => regs::XZR,
        (false, 31) => regs::WZR,
        (true, _) => PReg::new(field),
        (false, _) => PReg::new(32 + field),
    })
}

fn inst(op: Op, wide: bool, rt: u16, rn: u16, rm: u16, mode: Option<i64>) -> MachInst {
    let mut args = vec![
        data(wide, rt),
        Arg::PReg(PReg::new(rn)),
        data(!low32(mode), rm),
    ];
    if let Some(packed) = mode {
        args.push(Arg::Imm(packed));
    }
    MachInst::new(op, args)
}

fn word(op: Op, rt: u16, rn: u16, rm: u16, mode: Option<i64>) -> u32 {
    assert!(rt < 32 && rn < 32 && rm < 32);
    let packed = mode.unwrap_or(6);
    assert!(matches!(packed, 4 | 5 | 6 | 7 | 12 | 13 | 14 | 15));
    // Independent fixed register-offset words, not an encoder helper. Width
    // is opcode-owned: X spelling does not turn STRB/H into a wide store.
    let base = match op {
        Op::LdrbRO => 0x3860_0800,
        Op::LdrhRO => 0x7860_0800,
        Op::StrbRO => 0x3820_0800,
        Op::StrhRO => 0x7820_0800,
        _ => unreachable!("four narrow opcodes only"),
    };
    base | (u32::from(rm) << 16)
        | (((packed as u32) >> 1) << 13)
        | (((packed as u32) & 1) << 12)
        | (u32::from(rn) << 5)
        | u32::from(rt)
}

fn check(intent: &MachInst, word: u32) -> DecodeCheckOutcome {
    A64DecodeCheck.check_one(intent, &word.to_le_bytes(), None)
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

/// Save/restore of X19-X30 around the fixture body, in frame-lowering shape
/// (`stp x19,x20,[sp,#-96]!` ... `ldp x19,x20,[sp],#96`): the body redefines
/// every carrier, and the final-stream frame net requires callee-saved
/// registers and the return address to be restored at the return.
fn saved_pairs() -> [(PReg, PReg); 6] {
    [(19, 20), (21, 22), (23, 24), (25, 26), (27, 28), (29, 30)]
        .map(|(a, b)| (PReg::new(a), PReg::new(b)))
}

fn pair_inst(op: Op, pair: (PReg, PReg), offset: i64) -> MachInst {
    MachInst::new(
        op,
        vec![
            Arg::PReg(pair.0),
            Arg::PReg(pair.1),
            Arg::Special(SpecialReg::SP),
            Arg::Imm(offset),
        ],
    )
}

fn legacy_prologue() -> Vec<MachInst> {
    saved_pairs()
        .into_iter()
        .enumerate()
        .map(|(i, pair)| {
            if i == 0 {
                pair_inst(Op::StpPreIndex, pair, -96)
            } else {
                pair_inst(Op::StpRI, pair, 16 * i as i64)
            }
        })
        .collect()
}

fn legacy_epilogue() -> Vec<MachInst> {
    saved_pairs()
        .into_iter()
        .enumerate()
        .rev()
        .map(|(i, pair)| {
            if i == 0 {
                pair_inst(Op::LdpPostIndex, pair, 96)
            } else {
                pair_inst(Op::LdpRI, pair, 16 * i as i64)
            }
        })
        .collect()
}

fn frame_words(insts: Vec<MachInst>) -> Vec<u32> {
    insts
        .iter()
        .map(|inst| encode_instruction(inst).expect("frame save/restore word"))
        .collect()
}

// Public already-resolved function encoder reaches the private legacy
// encode_inst route. This does not run allocation, insert a frame, or execute.
fn legacy(intent: &MachInst) -> Result<Vec<u8>, String> {
    let mut function = MachFunction::new("narrow_ro_legacy".into(), Signature::new(vec![], vec![]));
    let mut body = legacy_prologue();
    // Define every X/W carrier explicitly, so the positive fixtures do not
    // depend on disabling the reaching-definition observer. These bytes are
    // never called.
    for field in 0..31 {
        body.push(MachInst::new(
            Op::Movz,
            vec![Arg::PReg(PReg::new(field)), Arg::Imm(0)],
        ));
    }
    body.push(intent.clone());
    body.extend(legacy_epilogue());
    body.push(MachInst::new(Op::Ret, vec![]));
    for item in body {
        let id = function.push_inst(item);
        function.append_inst(BlockId(0), id);
    }
    encode_function(&function).map_err(|error| error.to_string())
}

fn accepted(census: &mut Census, intent: &MachInst, expected: u32, with_legacy: bool) {
    let encoded = encode_instruction(intent);
    census.record(
        encoded.as_ref().is_ok_and(|actual| *actual == expected),
        || format!("unified {intent:?}: expected {expected:08x}, got {encoded:?}"),
    );
    let decoded = check(intent, expected);
    census.record(matches!(decoded, DecodeCheckOutcome::Match), || {
        format!("decoder {intent:?}: {decoded:?}")
    });
    if with_legacy {
        let actual = legacy(intent);
        let expected: Vec<u8> = frame_words(legacy_prologue())
            .into_iter()
            .chain((0..31_u32).map(|field| 0xd280_0000 | field))
            .chain([expected])
            .chain(frame_words(legacy_epilogue()))
            .chain([0xd65f_03c0])
            .flat_map(u32::to_le_bytes)
            .collect();
        census.record(
            actual.as_ref().is_ok_and(|bytes| *bytes == expected),
            || format!("legacy {intent:?}: expected {expected:02x?}, got {actual:?}"),
        );
    }
}

fn refused(census: &mut Census, intent: &MachInst, spoof: u32, with_legacy: bool) {
    let encoded = std::panic::catch_unwind(|| encode_instruction(intent));
    census.record(matches!(encoded, Ok(Err(_))), || {
        format!("unified failed refusal {intent:?}: {encoded:?}")
    });
    let decoded = std::panic::catch_unwind(|| check(intent, spoof));
    census.record(
        matches!(decoded, Ok(DecodeCheckOutcome::Mismatch(_))),
        || format!("decoder failed refusal {intent:?}: {decoded:?}"),
    );
    if with_legacy {
        let actual = std::panic::catch_unwind(|| legacy(intent));
        census.record(matches!(actual, Ok(Err(_))), || {
            format!("legacy failed refusal {intent:?}: {actual:?}")
        });
        census.record(!enforce(intent, &spoof.to_le_bytes(), None), || {
            format!("Enforce admitted {intent:?}")
        });
    }
}

#[test]
fn narrow_register_offset_literals_and_every_single_bit_mutant() {
    let mut census = Census::default();
    let mut rows = 0;
    for (op, anchor) in [
        (Op::LdrbRO, 0x3862_6820),
        (Op::LdrhRO, 0x7862_6820),
        (Op::StrbRO, 0x3822_6820),
        (Op::StrhRO, 0x7822_6820),
    ] {
        for mode in MODES {
            let packed = mode.unwrap_or(6) as u32;
            let expected = (anchor & !0xf000) | ((packed >> 1) << 13) | ((packed & 1) << 12);
            let intent = inst(op, false, 0, 1, 2, mode);
            census.record(word(op, 0, 1, 2, mode) == expected, || {
                format!("literal oracle {op:?}/{mode:?}")
            });
            accepted(&mut census, &intent, expected, true);
            census.record(enforce(&intent, &expected.to_le_bytes(), None), || {
                format!("positive Enforce {intent:?}")
            });
            rows += 1;
            for bit in 0..32 {
                let mutant = expected ^ (1 << bit);
                census.record(
                    matches!(check(&intent, mutant), DecodeCheckOutcome::Mismatch(_)),
                    || format!("decoder mutation {op:?}/{mode:?} bit{bit}"),
                );
                census.record(!enforce(&intent, &mutant.to_le_bytes(), None), || {
                    format!("Enforce mutation {op:?}/{mode:?} bit{bit}")
                });
                rows += 1;
            }
        }
    }
    census.finish("literal_and_mutant", rows, 1_188, 2_484);
}

#[test]
fn narrow_register_offset_all_register_fields_and_modes() {
    let mut census = Census::default();
    let mut rows = 0;
    for op in OPS {
        for wide in [false, true] {
            for mode in MODES {
                for rt in 0..32 {
                    for rn in 0..32 {
                        for rm in 0..32 {
                            // RO has no writeback: equal data/base/index fields
                            // are valid, including cross-width Wt/Xn aliases.
                            let intent = inst(op, wide, rt, rn, rm, mode);
                            accepted(&mut census, &intent, word(op, rt, rn, rm, mode), false);
                            rows += 1;
                        }
                    }
                }
            }
        }
    }
    census.finish("register_fields", rows, 2_359_296, 4_718_592);
}

#[test]
fn narrow_register_offset_legacy_and_special_aliases() {
    let mut census = Census::default();
    let mut rows = 0;
    for op in OPS {
        for wide in [false, true] {
            for mode in MODES {
                for rt in [0, 9, 16, 30, 31] {
                    for rn in [0, 9, 16, 30, 31] {
                        for rm in [0, 9, 16, 30, 31] {
                            let intent = inst(op, wide, rt, rn, rm, mode);
                            accepted(&mut census, &intent, word(op, rt, rn, rm, mode), true);
                            rows += 1;
                        }
                    }
                }
            }
        }
        for transfer in [
            Arg::PReg(regs::WZR),
            Arg::PReg(regs::XZR),
            Arg::Special(SpecialReg::WZR),
            Arg::Special(SpecialReg::XZR),
        ] {
            for base in [Arg::PReg(regs::SP), Arg::Special(SpecialReg::SP)] {
                for index in [
                    Arg::PReg(regs::WZR),
                    Arg::PReg(regs::XZR),
                    Arg::Special(SpecialReg::WZR),
                    Arg::Special(SpecialReg::XZR),
                ] {
                    for mode in MODES {
                        let mut intent = inst(op, false, 31, 31, 31, mode);
                        intent.operands[..3].clone_from_slice(&[
                            transfer.clone(),
                            base.clone(),
                            index.clone(),
                        ]);
                        accepted(&mut census, &intent, word(op, 31, 31, 31, mode), true);
                        rows += 1;
                    }
                }
            }
        }
        for mode in [Some(4), Some(5), Some(12), Some(13)] {
            for rm in 0..31 {
                // An X spelling is a carrier for low32 extension, not a
                // request to consume/sign-extend all 64 bits.
                let mut intent = inst(op, true, 9, 31, rm, mode);
                intent.operands[2] = data(true, rm);
                accepted(&mut census, &intent, word(op, 9, 31, rm, mode), true);
                rows += 1;
            }
        }
    }
    census.finish("legacy_and_aliases", rows, 10_648, 31_944);
}

// Independent raw-domain classification. Do not use preg_class/hw_enc or
// encoder/decoder helpers to decide whether malformed physical banks qualify.
fn valid_raw(position: usize, raw: u16, mode: Option<i64>) -> bool {
    match position {
        0 => matches!(raw, 0..=30 | 32..=62 | 160 | 161),
        1 => raw <= 31,
        2 => matches!(raw, 0..=30 | 160 | 161) || (low32(mode) && (32..=62).contains(&raw)),
        _ => unreachable!(),
    }
}

fn raw_field(raw: u16) -> u16 {
    match raw {
        0..=31 => raw,
        32..=159 => raw & 31,
        160 | 161 => 31,
        165..=196 => raw - 165,
        197..=228 => raw - 197,
        _ => 0,
    }
}

#[test]
fn narrow_register_offset_entire_raw_physical_bank_domain() {
    let mut census = Census::default();
    let mut rows = 0;
    let mut valid = 0;
    for op in OPS {
        // The two independent index-width classes; all nine syntax/mode
        // forms are exercised in the full field matrix and boundary test.
        for mode in [Some(4), Some(6)] {
            for position in 0..3 {
                for raw in 0..=u16::MAX {
                    let mut intent = inst(op, false, 9, 1, 2, mode);
                    intent.operands[position] = Arg::PReg(PReg::new(raw));
                    let mut fields = [9, 1, 2];
                    fields[position] = raw_field(raw);
                    let expected = word(op, fields[0], fields[1], fields[2], mode);
                    if valid_raw(position, raw, mode) {
                        accepted(&mut census, &intent, expected, false);
                        valid += 1;
                    } else {
                        refused(&mut census, &intent, expected, false);
                    }
                    rows += 1;
                }
            }
        }
    }
    assert_eq!(valid, 1_156);
    census.finish("raw_physical_domain", rows, 1_572_864, 3_145_728);
}

#[test]
fn narrow_register_offset_modes_do_not_default_mask_or_truncate() {
    let mut census = Census::default();
    let mut rows = 0;
    for op in OPS {
        for packed in 0..=u16::MAX {
            if matches!(packed, 4 | 5 | 6 | 7 | 12 | 13 | 14 | 15) {
                continue;
            }
            let intent = inst(op, false, 9, 1, 2, Some(i64::from(packed)));
            refused(&mut census, &intent, word(op, 9, 1, 2, Some(6)), false);
            rows += 1;
        }
        for mode in MODES.into_iter().flatten() {
            for bit in 4..63 {
                let intent = inst(op, false, 9, 1, 2, Some(mode | (1_i64 << bit)));
                refused(&mut census, &intent, word(op, 9, 1, 2, Some(mode)), true);
                rows += 1;
            }
            let intent = inst(op, false, 9, 1, 2, Some(mode | i64::MIN));
            refused(&mut census, &intent, word(op, 9, 1, 2, Some(mode)), true);
            rows += 1;
        }
        for packed in [i64::MIN, i64::MAX, -1, -16] {
            let intent = inst(op, false, 9, 1, 2, Some(packed));
            refused(&mut census, &intent, word(op, 9, 1, 2, Some(6)), true);
            rows += 1;
        }
    }
    census.finish("packed_modes", rows, 264_048, 531_968);
}

fn wrong_operands() -> Vec<Arg> {
    vec![
        Arg::Imm(0),
        Arg::FImm(0.0),
        Arg::VReg(VReg::new(0, RegClass::Gpr64)),
        Arg::VReg(VReg::new(1, RegClass::System)),
        Arg::Block(BlockId(0)),
        Arg::StackSlot(StackSlotId(0)),
        Arg::FrameIndex(FrameIdx(0)),
        Arg::MemOp {
            base: regs::X1,
            offset: 0,
        },
        Arg::Symbol("raw".into()),
        Arg::ExactModuleSymbol("raw".into()),
        Arg::JumpTableIndex(0),
        Arg::IncomingArg(0),
    ]
}

#[test]
fn narrow_register_offset_shapes_and_banks_all_modes_refuse() {
    let mut census = Census::default();
    let mut rows = 0;
    for op in OPS {
        for mode in MODES {
            let good = inst(op, false, 9, 1, 2, mode);
            let spoof = word(op, 9, 1, 2, mode);
            let mut malformed = Vec::new();
            for position in 0..3 {
                for operand in wrong_operands() {
                    let mut intent = good.clone();
                    intent.operands[position] = operand;
                    malformed.push(intent);
                }
                for raw in [
                    31,
                    32,
                    62,
                    63,
                    64,
                    95,
                    96,
                    127,
                    128,
                    159,
                    160,
                    161,
                    162,
                    163,
                    164,
                    165,
                    196,
                    197,
                    228,
                    229,
                    u16::MAX,
                ] {
                    if !valid_raw(position, raw, mode) {
                        let mut intent = good.clone();
                        intent.operands[position] = Arg::PReg(PReg::new(raw));
                        malformed.push(intent);
                    }
                }
                for special in [SpecialReg::SP, SpecialReg::WZR, SpecialReg::XZR] {
                    if (position == 1) != (special == SpecialReg::SP) {
                        let mut intent = good.clone();
                        intent.operands[position] = Arg::Special(special);
                        malformed.push(intent);
                    }
                }
            }
            for len in 0..3 {
                malformed.push(MachInst::new(op, good.operands[..len].to_vec()));
            }
            // Three operands plus one actual valid Imm is legal; wrong mode
            // kinds replace it here, and tails always follow four operands.
            let four = inst(op, false, 9, 1, 2, Some(mode.unwrap_or(6)));
            for extra in wrong_operands() {
                let mut tail = four.clone();
                tail.operands.push(extra.clone());
                malformed.push(tail);
                if !matches!(extra, Arg::Imm(_)) {
                    let mut wrong_mode = four.clone();
                    wrong_mode.operands[3] = extra;
                    malformed.push(wrong_mode);
                }
            }
            for operand in [Arg::PReg(regs::X2), Arg::Special(SpecialReg::XZR)] {
                let mut intent = four.clone();
                intent.operands[3] = operand;
                malformed.push(intent);
            }
            for intent in malformed {
                refused(&mut census, &intent, spoof, true);
                rows += 1;
            }
        }
    }
    census.finish("shapes_and_bank_boundaries", rows, 4_432, 17_728);
}

#[test]
fn narrow_register_offset_holes_lengths_and_stream_ranges_refuse() {
    let mut census = Census::default();
    let mut rows = 0;
    for op in OPS {
        for mode in MODES {
            let intent = inst(op, false, 31, 31, 31, mode);
            let expected = word(op, 31, 31, 31, mode);
            for length in [0, 1, 2, 3, 5, 8] {
                let mut bytes = expected.to_le_bytes().to_vec();
                bytes.resize(length, 0);
                census.record(
                    matches!(
                        A64DecodeCheck.check_one(&intent, &bytes, None),
                        DecodeCheckOutcome::Mismatch(_)
                    ),
                    || format!("decoder length {op:?}/{mode:?}/{length}"),
                );
                census.record(!enforce(&intent, &bytes, None), || {
                    format!("Enforce length {op:?}/{mode:?}/{length}")
                });
                rows += 1;
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
                    let hole = FixupHole {
                        offset_in_inst,
                        width,
                        kind,
                    };
                    census.record(
                        matches!(
                            A64DecodeCheck.check_one(&intent, &expected.to_le_bytes(), Some(&hole)),
                            DecodeCheckOutcome::Mismatch(_)
                        ),
                        || format!("decoder hole {op:?}/{mode:?}/{hole:?}"),
                    );
                    census.record(
                        !enforce(&intent, &expected.to_le_bytes(), Some(hole)),
                        || format!("Enforce hole {op:?}/{mode:?}/{hole:?}"),
                    );
                    rows += 1;
                }
            }
            for (start, end) in [(0, 0), (1, 0), (0, 5), (4, 8)] {
                let item = DecodeCheckItem {
                    start,
                    end,
                    intent: intent.clone(),
                    hole: None,
                };
                let result = run_decode_check(
                    &A64DecodeCheck,
                    &[item],
                    &expected.to_le_bytes(),
                    DecodeCheckMode::Enforce,
                );
                census.record(result.is_err(), || {
                    format!("Enforce range {op:?}/{start}..{end}")
                });
                rows += 1;
            }
        }
    }
    census.finish("holes_lengths_ranges", rows, 1_224, 2_304);
}

#[cfg(all(
    target_arch = "aarch64",
    any(target_os = "macos", all(target_os = "linux", target_env = "gnu"))
))]
#[path = "common/narrow_register_offset_native.rs"]
mod native;

#[cfg(all(
    target_arch = "aarch64",
    any(target_os = "macos", all(target_os = "linux", target_env = "gnu"))
))]
#[test]
fn narrow_register_offset_native_words_address_arithmetic_aliases_and_full_state() {
    native::run();
}

#[path = "common/fresh_dir.rs"]
mod fresh_dir;
