// Copyright 2026 Andrew Yates | Apache-2.0
//! Independent LdrRO/StrRO intent/word and finite Linux native controls.
//! No source-refinement, volatile-ordering or proof-required authority follows
//! from these tests. FPR8, narrow RO opcodes and writeback retain other owners.

use trust_cg_codegen::{
    aarch64::{decode_check::A64DecodeCheck, encode::encode_instruction},
    decode_check::{
        DecodeCheck, DecodeCheckItem, DecodeCheckMode, DecodeCheckOutcome, FixupHole,
        FixupHoleKind, run_decode_check,
    },
};
use trust_cg_ir::{
    AArch64Opcode as Op, MachInst, MachOperand as Arg,
    regs::{self, PReg, SpecialReg},
};

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
    H,
    S,
    D,
    Q,
}
const DATA: [Data; 6] = [Data::W, Data::X, Data::H, Data::S, Data::D, Data::Q];
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

impl Data {
    fn fp(self) -> bool {
        !matches!(self, Self::W | Self::X)
    }
    // Only the Linux-gnu native cases below call this; elsewhere it is dead and
    // the crate denies dead code, so it is gated exactly like its callers.
    #[cfg(all(
        target_arch = "aarch64",
        any(target_os = "macos", all(target_os = "linux", target_env = "gnu"))
    ))]
    fn bytes(self) -> u16 {
        match self {
            Self::H => 2,
            Self::W | Self::S => 4,
            Self::X | Self::D => 8,
            Self::Q => 16,
        }
    }
    fn operand(self, rt: u16) -> Arg {
        assert!(rt < 32);
        Arg::PReg(match self {
            Self::W if rt == 31 => regs::WZR,
            Self::X if rt == 31 => regs::XZR,
            Self::W => PReg::new(32 + rt),
            Self::X => PReg::new(rt),
            Self::H => PReg::new(165 + rt),
            Self::S => PReg::new(128 + rt),
            Self::D => PReg::new(96 + rt),
            Self::Q => PReg::new(64 + rt),
        })
    }
}

fn index(rm: u16, mode: Option<i64>) -> Arg {
    let wide = ((mode.unwrap_or(6) >> 1) & 1) != 0;
    (if wide { Data::X } else { Data::W }).operand(rm)
}

fn inst(load: bool, data: Data, rt: u16, rn: u16, rm: u16, mode: Option<i64>) -> MachInst {
    let mut operands = vec![data.operand(rt), Arg::PReg(PReg::new(rn)), index(rm, mode)];
    if let Some(packed) = mode {
        operands.push(Arg::Imm(packed));
    }
    MachInst::new(if load { Op::LdrRO } else { Op::StrRO }, operands)
}

fn word(load: bool, data: Data, rt: u16, rn: u16, rm: u16, mode: Option<i64>) -> u32 {
    assert!(rt < 32 && rn < 32 && rm < 32);
    let packed = mode.unwrap_or(6);
    assert!(matches!(packed, 4 | 5 | 6 | 7 | 12 | 13 | 14 | 15));
    // Independent Arm register-offset transcription: fixed111, V, fixed00,
    // opc, fixed1, Rm, option, S, fixed10, Rn, Rt. Q uses size00/opc1x.
    let (size, high_opc) = match data {
        Data::W | Data::S => (2, 0),
        Data::X | Data::D => (3, 0),
        Data::H => (1, 0),
        Data::Q => (0, 2),
    };
    (size << 30)
        | 0x3820_0800
        | (u32::from(data.fp()) << 26)
        | ((high_opc | u32::from(load)) << 22)
        | (u32::from(rm) << 16)
        | (((packed as u32) >> 1) << 13)
        | (((packed as u32) & 1) << 12)
        | (u32::from(rn) << 5)
        | u32::from(rt)
}

fn check(intent: &MachInst, word: u32) -> DecodeCheckOutcome {
    A64DecodeCheck.check_one(intent, &word.to_le_bytes(), None)
}

fn enforce(intent: MachInst, word: u32, hole: Option<FixupHole>) -> bool {
    run_decode_check(
        &A64DecodeCheck,
        &[DecodeCheckItem {
            start: 0,
            end: 4,
            intent,
            hole,
        }],
        &word.to_le_bytes(),
        DecodeCheckMode::Enforce,
    )
    .is_ok()
}

fn accepted(intent: &MachInst, expected: u32) {
    assert_eq!(encode_instruction(intent).unwrap(), expected, "{intent:?}");
    assert!(
        matches!(check(intent, expected), DecodeCheckOutcome::Match),
        "{intent:?}"
    );
}

fn refused(intent: &MachInst, spoof: u32) {
    assert!(
        encode_instruction(intent).is_err(),
        "encoder admitted {intent:?}"
    );
    assert!(
        matches!(check(intent, spoof), DecodeCheckOutcome::Mismatch(_)),
        "decoder admitted {intent:?}"
    );
    assert!(
        !enforce(intent.clone(), spoof, None),
        "Enforce admitted {intent:?}"
    );
}

#[test]
fn register_offset_literal_words_and_all_bit_mutations() {
    let mut positives = 0;
    let mut mutants = 0;
    for (data, stores, loads) in [
        (Data::W, 0xb822_6820, 0xb862_6820),
        (Data::X, 0xf822_6820, 0xf862_6820),
        (Data::H, 0x7c22_6820, 0x7c62_6820),
        (Data::S, 0xbc22_6820, 0xbc62_6820),
        (Data::D, 0xfc22_6820, 0xfc62_6820),
        (Data::Q, 0x3ca2_6820, 0x3ce2_6820),
    ] {
        for (load, expected) in [(false, stores), (true, loads)] {
            for mode in MODES {
                let intent = inst(load, data, 0, 1, 2, mode);
                let packed = mode.unwrap_or(6) as u32;
                let expected = (expected & !0xf000) | ((packed >> 1) << 13) | ((packed & 1) << 12);
                assert_eq!(word(load, data, 0, 1, 2, mode), expected);
                accepted(&intent, expected);
                assert!(enforce(intent.clone(), expected, None));
                positives += 1;
                for bit in 0..32 {
                    let mutant = expected ^ (1 << bit);
                    assert!(
                        matches!(check(&intent, mutant), DecodeCheckOutcome::Mismatch(_)),
                        "{intent:?} bit{bit}"
                    );
                    assert!(!enforce(intent.clone(), mutant, None));
                    mutants += 1;
                }
            }
        }
    }
    assert_eq!((positives, mutants), (108, 3456));
}

#[test]
fn register_offset_all_register_fields_modes_and_legal_overlaps() {
    let mut count = 0;
    for load in [false, true] {
        for data in DATA {
            for mode in MODES {
                for rt in 0..32 {
                    for rn in 0..32 {
                        for rm in 0..32 {
                            // No writeback: equality of data/base/index fields
                            // is legal, including Wt/Xn aliases and all-three.
                            let intent = inst(load, data, rt, rn, rm, mode);
                            accepted(&intent, word(load, data, rt, rn, rm, mode));
                            count += 1;
                        }
                    }
                }
            }
        }
    }
    assert_eq!(count, 3_538_944);
}

#[test]
fn register_offset_special_zero_spellings_and_w_extension_x_carriers() {
    let mut zeros = 0;
    let mut carriers = 0;
    for load in [false, true] {
        for data in DATA {
            let mut transfers = vec![data.operand(31)];
            if !data.fp() {
                transfers.push(Arg::Special(if data == Data::W {
                    SpecialReg::WZR
                } else {
                    SpecialReg::XZR
                }));
            }
            for rt in transfers {
                for base in [Arg::PReg(regs::SP), Arg::Special(SpecialReg::SP)] {
                    for rm in [
                        Arg::PReg(regs::WZR),
                        Arg::PReg(regs::XZR),
                        Arg::Special(SpecialReg::WZR),
                        Arg::Special(SpecialReg::XZR),
                    ] {
                        for mode in MODES {
                            let mut intent = inst(load, data, 31, 31, 31, mode);
                            intent.operands[0] = rt.clone();
                            intent.operands[1] = base.clone();
                            intent.operands[2] = rm.clone();
                            let expected = word(load, data, 31, 31, 31, mode);
                            accepted(&intent, expected);
                            assert!(enforce(intent, expected, None));
                            zeros += 1;
                        }
                    }
                }
            }
            for mode in [Some(4), Some(5), Some(12), Some(13)] {
                for rn in [0, 31] {
                    for rm in [0, 30] {
                        let mut intent = inst(load, data, 9, rn, rm, mode);
                        intent.operands[2] = Data::X.operand(rm);
                        // Option selects low32; X is an admitted carrier, not
                        // a request to read/sign-extend all 64 bits.
                        let expected = word(load, data, 9, rn, rm, mode);
                        accepted(&intent, expected);
                        assert!(enforce(intent, expected, None));
                        carriers += 1;
                    }
                }
            }
        }
    }
    assert_eq!((zeros, carriers), (1152, 192));
}

#[test]
fn register_offset_malformed_banks_and_shapes_refuse() {
    let mut count = 0;
    for load in [false, true] {
        for data in DATA {
            let good = inst(load, data, 9, 0, 4, Some(6));
            let mut bad = Vec::new();
            for id in [31, 63, 162, 163, 164, 197, 228, 229, u16::MAX] {
                let mut intent = good.clone();
                intent.operands[0] = Arg::PReg(PReg::new(id));
                bad.push(intent);
            }
            for pos in [1, 2] {
                for id in [
                    32,
                    63,
                    64,
                    95,
                    96,
                    127,
                    128,
                    159,
                    162,
                    164,
                    165,
                    196,
                    197,
                    228,
                    229,
                    u16::MAX,
                ] {
                    let mut intent = good.clone();
                    intent.operands[pos] = Arg::PReg(PReg::new(id));
                    bad.push(intent);
                }
            }
            // Rn31 means SP, not a zero register. Rm31 means zero, not SP.
            for base in [
                Arg::PReg(regs::WZR),
                Arg::PReg(regs::XZR),
                Arg::Special(SpecialReg::WZR),
                Arg::Special(SpecialReg::XZR),
            ] {
                let mut intent = good.clone();
                intent.operands[1] = base;
                bad.push(intent);
            }
            for idx in [Arg::PReg(regs::SP), Arg::Special(SpecialReg::SP)] {
                let mut intent = good.clone();
                intent.operands[2] = idx;
                bad.push(intent);
            }
            let mut sp_data = good.clone();
            sp_data.operands[0] = Arg::Special(SpecialReg::SP);
            bad.push(sp_data);
            for pos in 0..3 {
                for wrong in [
                    Arg::Imm(0),
                    Arg::VReg(regs::VReg::new(0, regs::RegClass::Gpr64)),
                    Arg::MemOp {
                        base: regs::X0,
                        offset: 0,
                    },
                ] {
                    let mut intent = good.clone();
                    intent.operands[pos] = wrong;
                    bad.push(intent);
                }
            }
            for len in 0..3 {
                bad.push(MachInst::new(good.opcode, good.operands[..len].to_vec()));
            }
            for extra in [Arg::Imm(0), Arg::PReg(regs::X0)] {
                let mut intent = good.clone();
                intent.operands.push(extra);
                bad.push(intent);
            }
            for wrong in [Arg::PReg(regs::X0), Arg::Special(SpecialReg::XZR)] {
                let mut intent = good.clone();
                intent.operands[3] = wrong;
                bad.push(intent);
            }
            assert_eq!(bad.len(), 64);
            for intent in bad {
                let field = |arg: Option<&Arg>, fallback| match arg {
                    Some(Arg::PReg(p)) => u16::from(p.hw_enc()),
                    Some(Arg::Special(_)) => 31,
                    _ => fallback,
                };
                let spoof = word(
                    load,
                    data,
                    field(intent.operands.first(), 9),
                    field(intent.operands.get(1), 0),
                    field(intent.operands.get(2), 4),
                    Some(6),
                );
                refused(&intent, spoof);
                count += 1;
            }
        }
    }
    assert_eq!(count, 768);
}

#[test]
fn register_offset_packed_modes_never_default_mask_or_truncate() {
    let mut modes = 0;
    let mut wrong_width = 0;
    let mut invalid_indexes = 0;
    for load in [false, true] {
        for data in DATA {
            for packed in [
                0,
                1,
                2,
                3,
                8,
                9,
                10,
                11,
                16,
                22,
                -1,
                i64::MIN,
                i64::MAX,
                (1_i64 << 32) + 6,
            ] {
                let mut intent = inst(load, data, 9, 0, 4, Some(6));
                intent.operands[3] = Arg::Imm(packed);
                refused(&intent, word(load, data, 9, 0, 4, Some(6)));
                modes += 1;
            }
            for mode in [None, Some(6), Some(7), Some(14), Some(15)] {
                for rm in [0, 30] {
                    let mut intent = inst(load, data, 9, 1, rm, mode);
                    intent.operands[2] = Data::W.operand(rm);
                    refused(&intent, word(load, data, 9, 1, rm, mode));
                    wrong_width += 1;
                }
            }
            for mode in MODES {
                for rm in [
                    31,
                    63,
                    64,
                    95,
                    96,
                    127,
                    128,
                    159,
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
                    let mut intent = inst(load, data, 9, 0, 4, mode);
                    intent.operands[2] = Arg::PReg(PReg::new(rm));
                    refused(
                        &intent,
                        word(load, data, 9, 0, u16::from(PReg::new(rm).hw_enc()), mode),
                    );
                    invalid_indexes += 1;
                }
                let mut intent = inst(load, data, 9, 0, 31, mode);
                intent.operands[2] = Arg::Special(SpecialReg::SP);
                refused(&intent, word(load, data, 9, 0, 31, mode));
                invalid_indexes += 1;
            }
        }
    }
    assert_eq!((modes, wrong_width, invalid_indexes), (168, 120, 1944));
}

#[test]
fn register_offset_holes_and_byte_lengths_are_not_authority() {
    let mut holes = 0;
    let mut lengths = 0;
    for load in [false, true] {
        for data in DATA {
            let intent = inst(load, data, 31, 31, 31, Some(7));
            let expected = word(load, data, 31, 31, 31, Some(7));
            for length in [0, 1, 2, 3, 5, 8] {
                let mut bytes = expected.to_le_bytes().to_vec();
                bytes.resize(length, 0);
                assert!(matches!(
                    A64DecodeCheck.check_one(&intent, &bytes, None),
                    DecodeCheckOutcome::Mismatch(_)
                ));
                lengths += 1;
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
                    assert!(matches!(
                        A64DecodeCheck.check_one(&intent, &expected.to_le_bytes(), Some(&hole)),
                        DecodeCheckOutcome::Mismatch(_)
                    ));
                    assert!(!enforce(intent.clone(), expected, Some(hole)));
                    holes += 1;
                }
            }
        }
    }
    assert_eq!((holes, lengths), (288, 72));
}

#[cfg(all(
    target_arch = "aarch64",
    any(target_os = "macos", all(target_os = "linux", target_env = "gnu"))
))]
mod native {
    use super::*;
    use sha2::{Digest, Sha256};
    use std::{fmt::Write, fs, io::Read, path::Path, process::Command, time::Duration};
    const CASES: usize = 648;
    const CALLS: usize = CASES * 4 * 4;
    const CHECKS: usize = CASES * 2 + CALLS * 2 * (1024 + 16 + 2);

    fn snapshot(directory: &Path) {
        let mut rows = Vec::new();
        for entry in fs::read_dir(directory).unwrap() {
            let path = entry.unwrap().path();
            if path.file_name().unwrap() == "SHA256SUMS" {
                continue;
            }
            let mut input = fs::File::open(&path).unwrap();
            let mut hash = Sha256::new();
            let mut buffer = [0; 65536];
            loop {
                let n = input.read(&mut buffer).unwrap();
                if n == 0 {
                    break;
                }
                hash.update(&buffer[..n]);
            }
            rows.push(format!(
                "{:x}  {}\n",
                hash.finalize(),
                path.file_name().unwrap().to_str().unwrap()
            ));
        }
        rows.sort();
        fs::write(directory.join("SHA256SUMS"), rows.concat()).unwrap();
    }

    fn run_command(
        directory: &Path,
        label: &str,
        command: &mut Command,
        bound: Duration,
        expected: i32,
    ) -> std::process::Output {
        fs::write(
            directory.join(format!("{label}.argv")),
            format!("{command:?}\ntimeout={bound:?}\n"),
        )
        .unwrap();
        let result = match process::command_output_with_timeout(command, bound) {
            Ok(result) => result,
            Err(error) => {
                fs::write(
                    directory.join(format!("{label}.spawn-error")),
                    error.to_string(),
                )
                .unwrap();
                snapshot(directory);
                panic!("required process could not launch: {error}; {directory:?}");
            }
        };
        fs::write(
            directory.join(format!("{label}.stdout")),
            &result.output.stdout,
        )
        .unwrap();
        fs::write(
            directory.join(format!("{label}.stderr")),
            &result.output.stderr,
        )
        .unwrap();
        fs::write(
            directory.join(format!("{label}.status")),
            format!(
                "status={}\ntimed_out={}\n",
                result.output.status, result.timed_out
            ),
        )
        .unwrap();
        snapshot(directory);
        assert!(!result.timed_out, "{label} timed out; {directory:?}");
        assert_eq!(
            result.output.status.code(),
            Some(expected),
            "{label}; {directory:?}: {}",
            String::from_utf8_lossy(&result.output.stderr)
        );
        result.output
    }

    #[derive(Clone, Copy)]
    struct Case {
        load: bool,
        data: Data,
        zero: bool,
        sp: bool,
        mode: Option<i64>,
        index_zero: bool,
        alias: u8,
    }

    fn cases() -> Vec<Case> {
        let mut cases = Vec::new();
        for load in [false, true] {
            for (data, zero) in [
                (Data::W, false),
                (Data::X, false),
                (Data::H, false),
                (Data::S, false),
                (Data::D, false),
                (Data::Q, false),
                (Data::W, true),
                (Data::X, true),
            ] {
                for sp in [false, true] {
                    for mode in MODES {
                        for index_zero in [false, true] {
                            cases.push(Case {
                                load,
                                data,
                                zero,
                                sp,
                                mode,
                                index_zero,
                                alias: 0,
                            });
                        }
                    }
                }
            }
        }
        assert_eq!(cases.len(), 576);
        for load in [false, true] {
            for data in [Data::W, Data::X] {
                for alias in [1, 2] {
                    for mode in MODES {
                        cases.push(Case {
                            load,
                            data,
                            zero: false,
                            sp: false,
                            mode,
                            index_zero: false,
                            alias,
                        });
                    }
                }
            }
        }
        assert_eq!(cases.len(), CASES);
        cases
    }

    fn oracle(case: Case, rt: u16) -> String {
        let bank = match case.data {
            Data::W => 'w',
            Data::X => 'x',
            Data::H => 'h',
            Data::S => 's',
            Data::D => 'd',
            Data::Q => 'q',
        };
        let target = if case.zero {
            format!("{bank}zr")
        } else {
            format!("{bank}{rt}")
        };
        let base = if case.sp { "sp" } else { "x0" };
        let mode = case.mode.unwrap_or(6);
        let option = mode >> 1;
        let index_bank = if option == 2 || option == 6 { 'w' } else { 'x' };
        let rm = if case.index_zero {
            format!("{index_bank}zr")
        } else {
            format!("{index_bank}4")
        };
        let extension = match option {
            2 => "uxtw",
            3 => "lsl",
            6 => "sxtw",
            7 => "sxtx",
            _ => unreachable!(),
        };
        let amount = if mode & 1 == 0 {
            0
        } else {
            case.data.bytes().ilog2()
        };
        format!(
            "{} {target},[{base},{rm},{extension} #{amount}]",
            if case.load { "ldr" } else { "str" }
        )
    }

    fn wrapper(
        assembly: &mut String,
        prefix: char,
        id: usize,
        case: Case,
        rt: u16,
        instruction: &str,
    ) {
        let name = format!("{prefix}{id}");
        // void f(base=x0, raw_index=x1, seed=x2, Snapshot*=x3).
        // Only caller-saved x0/x4-x17 and v0 change. No BL or LR modification;
        // output-pointer ABI avoids hidden aggregate return conventions.
        writeln!(assembly, ".p2align 2\n.global {name}\n.type {name},%function\n{name}:\nmov x4,x1\nldr x9,[x2]\nldr q0,[x2]").unwrap();
        if case.sp {
            // SP stays at the bottom of an allocated frame. These rows use
            // nonnegative indexes only; signed-negative coverage uses X bases.
            // No read relies on inactive storage below current SP.
            writeln!(assembly, "mov x10,sp\nsub sp,sp,#2048\nmov x11,sp\nmov x12,x0\nmov x13,x12\nmov x14,x11\nmov x15,#64\n.L{name}_in:\nldp x16,x17,[x13],#16\nstp x16,x17,[x14],#16\nsubs x15,x15,#1\nb.ne .L{name}_in").unwrap();
        }
        // Aliases are intentional: Rt=Rn starts with the base pointer value,
        // Rt=Rm with raw index, not with the distinct-transfer seed.
        writeln!(assembly, ".global {name}_word\n{name}_word:\n{instruction}").unwrap();
        if case.sp {
            // There is no RO writeback. Capture actual SP anyway, restore
            // frame SP immediately, then map it to the original C buffer.
            writeln!(assembly, "mov x5,sp\nmov sp,x11\nsub x5,x5,x11\nadd x5,x12,x5\nmov x13,x11\nmov x14,x12\nmov x15,#64\n.L{name}_out:\nldp x16,x17,[x13],#16\nstp x16,x17,[x14],#16\nsubs x15,x15,#1\nb.ne .L{name}_out\nmov sp,x10").unwrap();
        } else {
            assembly.push_str("mov x5,x0\n");
        }
        if case.data.fp() {
            assembly.push_str("str q0,[x3]\n");
        } else {
            writeln!(assembly, "stp x{},xzr,[x3]", if case.zero { 9 } else { rt }).unwrap();
        }
        writeln!(assembly, "stp x5,x4,[x3,#16]\nret\n.size {name},.-{name}").unwrap();
    }

    pub fn run() {
        // Host gate, constant by design: `cfg!` fixes the compile target, so clippy sees a
        // constant where this harness needs a runtime refusal.
        #[allow(clippy::assertions_on_constants)]
        {
            assert!(cfg!(target_endian = "little"));
        }
        let directory_scratch = crate::fresh_dir::create("trust-cg-register-offset-native-");
        let directory = directory_scratch.to_path_buf();
        eprintln!("register-offset native evidence={directory:?}");
        let mut assembly = String::from(".text\n");
        let mut driver = String::from(DRIVER);
        let mut rows = Vec::new();
        for (id, case) in cases().into_iter().enumerate() {
            let rt = if case.zero {
                31
            } else if case.data.fp() || case.alias == 1 {
                0
            } else if case.alias == 2 {
                4
            } else {
                9
            };
            let rn = if case.sp { 31 } else { 0 };
            let rm = if case.index_zero { 31 } else { 4 };
            let intent = inst(case.load, case.data, rt, rn, rm, case.mode);
            let expected = word(case.load, case.data, rt, rn, rm, case.mode);
            let encoded = encode_instruction(&intent).unwrap();
            assert_eq!(encoded, expected, "case{id}");
            for (prefix, instruction) in [
                ('g', format!(".inst 0x{encoded:08x}")),
                ('a', oracle(case, rt)),
            ] {
                wrapper(&mut assembly, prefix, id, case, rt, &instruction);
                writeln!(driver, "extern void {prefix}{id}(unsigned char*,uint64_t,const unsigned char*,struct Snapshot*); extern const uint32_t {prefix}{id}_word[];").unwrap();
            }
            rows.push(format!(
                "{{g{id},a{id},g{id}_word,a{id}_word,0x{expected:08x}u,{},{},{},{},{},{},{},{}}}",
                case.data.bytes(),
                u8::from(case.data.fp()),
                u8::from(case.load),
                u8::from(case.zero),
                case.mode.unwrap_or(6),
                u8::from(case.index_zero),
                case.alias,
                u8::from(case.sp)
            ));
        }
        assert_eq!(rows.len(), CASES);
        assembly.push_str(".section .note.GNU-stack,\"\",%progbits\n");
        writeln!(
            driver,
            "static const struct Case cases[]={{ {} }};",
            rows.join(",\n")
        )
        .unwrap();
        driver.push_str(MAIN);
        fs::write(directory.join("words.S"), native_host::assembly(&assembly)).unwrap();
        fs::write(directory.join("driver.c"), driver).unwrap();
        snapshot(&directory);
        let executable = directory.join("native");
        run_command(
            &directory,
            "link",
            Command::new("cc")
                .args(["-std=c11", "-O2", "-Wall", "-Wextra", "-Werror"])
                .arg(directory.join("driver.c"))
                .arg(directory.join("words.S"))
                .arg("-o")
                .arg(&executable),
            process::codegen_link_timeout(),
            0,
        );
        let output = run_command(
            &directory,
            "native",
            &mut Command::new(&executable),
            process::codegen_run_timeout(),
            0,
        );
        assert_eq!(
            String::from_utf8(output.stdout).unwrap(),
            format!(
                "REGISTER_OFFSET_NATIVE_PASS cases={CASES} cg_calls={CALLS} asm_calls={CALLS} checks={CHECKS}\n"
            )
        );
        assert!(output.stderr.is_empty());
        for (label, stderr) in [
            (
                "poison-transfer",
                "EXPECTED_TRANSFER_MISMATCH case=0 route=0 byte=0\n",
            ),
            ("poison-base", "EXPECTED_BASE_MISMATCH case=0 route=0\n"),
            (
                "poison-byte",
                "EXPECTED_BYTE_MISMATCH case=0 route=0 byte=512\n",
            ),
        ] {
            let output = run_command(
                &directory,
                label,
                Command::new(&executable).arg(format!("--{label}")),
                process::codegen_run_timeout(),
                97,
            );
            assert!(output.stdout.is_empty(), "{label}: {directory:?}");
            assert_eq!(output.stderr, stderr.as_bytes(), "{label}: {directory:?}");
        }
    }

    const DRIVER: &str = r#"
#include <stddef.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>
#define SIZE 1024
struct Snapshot { unsigned char data[16]; uint64_t base,index; };
_Static_assert(sizeof(struct Snapshot)==32 && offsetof(struct Snapshot,base)==16 && offsetof(struct Snapshot,index)==24,"assembly Snapshot layout");
typedef void (*Fn)(unsigned char*,uint64_t,const unsigned char*,struct Snapshot*);
struct Case { Fn cg,oracle; const uint32_t *cg_word,*asm_word; uint32_t word; unsigned bytes,fp,load,zero,mode,index_zero,alias,sp; };
static _Alignas(16) unsigned char buffers[2][SIZE],expected[SIZE],seed[16];
static unsigned long checks,calls[2];
static uint64_t read_le(const unsigned char *p,unsigned n) {
    uint64_t v=0; for(unsigned j=0;j<n;++j) v|=(uint64_t)p[j]<<(8*j); return v;
}
static void write_le(unsigned char *p,uint64_t v,unsigned n) {
    for(unsigned j=0;j<n;++j) p[j]=(unsigned char)(v>>(8*j));
}
static uint64_t raw_index(unsigned option,unsigned profile,unsigned sp) {
    const uint64_t u[]={0,1,7,UINT64_C(0xa5a5a5a500000007)};
    const uint64_t s[]={0,1,UINT64_C(0xa5a5a5a5ffffffff),UINT64_C(0x5a5a5a5afffffff9)};
    const uint64_t x[]={0,1,UINT64_MAX,UINT64_MAX-6};
    const uint64_t positive[]={0,1,7,3};
    if(sp) return option==2 || option==6?u[profile]:positive[profile];
    return option==2?u[profile]:option==6?s[profile]:x[profile];
}
static int address_index(const struct Case *c,uint64_t raw,size_t *address) {
    const unsigned option=c->mode>>1;
    uint64_t ext=c->index_zero?0:raw;
    if(option==2 || option==6) {
        ext&=UINT64_C(0xffffffff);
        if(option==6 && (ext&UINT64_C(0x80000000))) ext|=UINT64_C(0xffffffff00000000);
    }
    unsigned shift=0;
    if(c->mode&1) { for(unsigned n=c->bytes;n>1;n>>=1) ++shift; }
    const uint64_t delta=ext<<shift; /* unsigned modular shift, never signed UB */
    const size_t base=c->sp?0:512;
    size_t pos;
    if(delta>>63) {
        const uint64_t magnitude=(~delta)+1;
        if(c->sp || magnitude>496) return 0;
        pos=base-(size_t)magnitude;
    } else {
        if(delta>496) return 0;
        pos=base+(size_t)delta;
    }
    if((!c->sp && pos<16) || pos+c->bytes>SIZE-16) return 0;
    *address=pos; return 1;
}
"#;

    const MAIN: &str = r#"
int main(int argc,char **argv) {
    const int poison_transfer=argc==2 && strcmp(argv[1],"--poison-transfer")==0;
    const int poison_base=argc==2 && strcmp(argv[1],"--poison-base")==0;
    const int poison_byte=argc==2 && strcmp(argv[1],"--poison-byte")==0;
    if(argc!=1 && !(poison_transfer || poison_base || poison_byte)) return 96;
    if(sizeof(cases)/sizeof(cases[0])!=648) return 98;
    const unsigned char edges[]={0,0x7f,0x80,0xff};
    for(size_t i=0;i<648;++i) {
        const struct Case *c=&cases[i]; checks+=2;
        if(*c->cg_word!=c->word || *c->asm_word!=c->word) return 95;
        for(unsigned profile=0;profile<4;++profile) {
            const uint64_t raw=raw_index(c->mode>>1,profile,c->sp);
            const size_t base=c->sp?0:512;
            size_t address=0; if(!address_index(c,raw,&address)) return 98;
            for(unsigned pattern=0;pattern<4;++pattern) {
                for(unsigned j=0;j<16;++j) seed[j]=(unsigned char)(0x97+j*31+pattern*73);
                for(unsigned route=0;route<2;++route) {
                    unsigned char *buffer=buffers[route];
                    for(size_t j=0;j<SIZE;++j) expected[j]=(unsigned char)((j*37+pattern*71)^(j>>3));
                    for(unsigned j=0;j<c->bytes;++j) expected[address+j]=edges[pattern];
                    memcpy(buffer,expected,SIZE);
                    struct Snapshot wanted={{0},(uint64_t)(uintptr_t)(buffer+base),raw}, actual;
                    memset(&actual,0xa6,sizeof(actual));
                    if(c->fp) {
                        memcpy(wanted.data,seed,16);
                        if(c->load) { memset(wanted.data,0,16); memcpy(wanted.data,expected+address,c->bytes); }
                        else memcpy(expected+address,seed,c->bytes);
                    } else {
                        const uint64_t input=c->alias==1?wanted.base:c->alias==2?raw:read_le(seed,8);
                        uint64_t value=input;
                        if(c->load && !c->zero) value=read_le(expected+address,c->bytes);
                        else if(!c->load) write_le(expected+address,c->zero?0:input,c->bytes);
                        write_le(wanted.data,value,8); /* observes full X, including W-load high zero */
                        if(c->load && c->alias==1) wanted.base=value;
                        if(c->load && c->alias==2) wanted.index=value;
                    }
                    if(i==0 && profile==0 && pattern==0) {
                        if(poison_transfer) wanted.data[0]^=1;
                        if(poison_base) wanted.base^=1;
                        if(poison_byte) expected[address]^=1;
                    }
                    const Fn fn=route?c->oracle:c->cg;
                    fn(buffer+base,raw,seed,&actual); ++calls[route];
                    checks+=2;
                    if(actual.base!=wanted.base) { fprintf(stderr,"EXPECTED_BASE_MISMATCH case=%zu route=%u\n",i,route); return 97; }
                    if(actual.index!=wanted.index) { fprintf(stderr,"EXPECTED_INDEX_MISMATCH case=%zu route=%u\n",i,route); return 97; }
                    for(unsigned j=0;j<16;++j) {
                        ++checks; if(actual.data[j]!=wanted.data[j]) { fprintf(stderr,"EXPECTED_TRANSFER_MISMATCH case=%zu route=%u byte=%u\n",i,route,j); return 97; }
                    }
                    for(size_t j=0;j<SIZE;++j) {
                        ++checks; if(buffer[j]!=expected[j]) { fprintf(stderr,"EXPECTED_BYTE_MISMATCH case=%zu route=%u byte=%zu\n",i,route,j); return 97; }
                    }
                }
            }
        }
    }
    if(calls[0]!=10368 || calls[1]!=10368 || checks!=648UL*2+10368UL*2*(1024+16+2)) return 98;
    printf("REGISTER_OFFSET_NATIVE_PASS cases=648 cg_calls=%lu asm_calls=%lu checks=%lu\n",calls[0],calls[1],checks);
    return 0;
}
"#;
}

#[cfg(all(
    target_arch = "aarch64",
    any(target_os = "macos", all(target_os = "linux", target_env = "gnu"))
))]
#[test]
fn register_offset_native_words_address_arithmetic_aliases_and_full_state() {
    native::run();
}

#[path = "common/fresh_dir.rs"]
mod fresh_dir;
