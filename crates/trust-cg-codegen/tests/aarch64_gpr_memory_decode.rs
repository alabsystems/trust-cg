// Copyright 2026 Andrew Yates | Apache-2.0
//! Independent immediate-GPR word and finite native memory controls. Neither
//! opcode correspondence nor these native executions establish lowering proofs
//! or volatile ordering. FP transfers and other address classes retain owners.

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

const OPS: [Op; 14] = [
    Op::LdrRI,
    Op::StrRI,
    Op::LdrbRI,
    Op::StrbRI,
    Op::LdrhRI,
    Op::StrhRI,
    Op::VolatileLdrRI,
    Op::VolatileStrRI,
    Op::VolatileLdrbRI,
    Op::VolatileStrbRI,
    Op::VolatileLdrhRI,
    Op::VolatileStrhRI,
    Op::LdrsbRI,
    Op::LdrshRI,
];

fn properties(op: Op, width: u16) -> (u32, u32, bool, bool) {
    assert!(matches!(width, 32 | 64));
    match op {
        Op::LdrRI | Op::VolatileLdrRI => (if width == 64 { 3 } else { 2 }, 1, true, false),
        Op::StrRI | Op::VolatileStrRI => (if width == 64 { 3 } else { 2 }, 0, false, false),
        Op::LdrbRI | Op::VolatileLdrbRI => (0, 1, true, false),
        Op::StrbRI | Op::VolatileStrbRI => (0, 0, false, false),
        Op::LdrhRI | Op::VolatileLdrhRI => (1, 1, true, false),
        Op::StrhRI | Op::VolatileStrhRI => (1, 0, false, false),
        Op::LdrsbRI => (0, if width == 64 { 2 } else { 3 }, true, true),
        Op::LdrshRI => (1, if width == 64 { 2 } else { 3 }, true, true),
        _ => panic!("outside the closed fourteen-opcode inventory"),
    }
}

fn transfer(width: u16, rt: u16) -> Arg {
    assert!(rt < 32);
    Arg::PReg(if rt == 31 {
        if width == 64 { regs::XZR } else { regs::WZR }
    } else {
        PReg::new(rt + if width == 64 { 0 } else { 32 })
    })
}

fn inst(op: Op, width: u16, rt: u16, rn: u16, offset: i64, mem: bool) -> MachInst {
    let mut args = vec![transfer(width, rt)];
    if mem {
        args.push(Arg::MemOp {
            base: PReg::new(rn),
            offset,
        });
    } else {
        args.extend([Arg::PReg(PReg::new(rn)), Arg::Imm(offset)]);
    }
    MachInst::new(op, args)
}

fn word(op: Op, width: u16, rt: u16, rn: u16, offset: i64) -> u32 {
    // Arm unsigned-offset/unscaled-immediate format, independently transcribed:
    // size[31:30], fixed111[29:27], V=0, opc[23:22], imm, Rn, Rt.
    let (size, opc, _, _) = properties(op, width);
    let scale = 1_i64 << size;
    let base = (size << 30) | 0x3800_0000 | (opc << 22) | (u32::from(rn) << 5) | u32::from(rt);
    if offset >= 0 && offset % scale == 0 && offset / scale <= 4095 {
        base | 0x0100_0000 | (((offset / scale) as u32) << 10)
    } else {
        assert!((-256..=255).contains(&offset));
        base | (((offset as u32) & 0x1ff) << 12)
    }
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

#[test]
fn gpr_memory_literal_words_and_all_single_bit_mutations() {
    let mut accepted = 0;
    let mut rejected = 0;
    for op in OPS {
        // Literal encodings for Rt=0,Rn=1,#0, separately from `word` above.
        let literals = match op {
            Op::LdrRI | Op::VolatileLdrRI => [0xb940_0020, 0xf940_0020],
            Op::StrRI | Op::VolatileStrRI => [0xb900_0020, 0xf900_0020],
            Op::LdrbRI | Op::VolatileLdrbRI => [0x3940_0020; 2],
            Op::StrbRI | Op::VolatileStrbRI => [0x3900_0020; 2],
            Op::LdrhRI | Op::VolatileLdrhRI => [0x7940_0020; 2],
            Op::StrhRI | Op::VolatileStrhRI => [0x7900_0020; 2],
            Op::LdrsbRI => [0x39c0_0020, 0x3980_0020],
            Op::LdrshRI => [0x79c0_0020, 0x7980_0020],
            _ => unreachable!(),
        };
        for (width, expected) in [32, 64].into_iter().zip(literals) {
            assert_eq!(word(op, width, 0, 1, 0), expected);
            for mem in [false, true] {
                let intent = inst(op, width, 0, 1, 0, mem);
                assert_eq!(encode_instruction(&intent).unwrap(), expected, "{intent:?}");
                assert!(
                    matches!(check(&intent, expected), DecodeCheckOutcome::Match),
                    "{intent:?}"
                );
                assert!(enforce(intent.clone(), expected, None));
                accepted += 1;
                for bit in 0..32 {
                    let mutant = expected ^ (1 << bit);
                    assert!(
                        matches!(check(&intent, mutant), DecodeCheckOutcome::Mismatch(_)),
                        "{intent:?} bit{bit}"
                    );
                    assert!(!enforce(intent.clone(), mutant, None));
                    rejected += 1;
                }
            }
        }
    }
    assert_eq!((accepted, rejected), (56, 1792));
}

#[test]
fn gpr_memory_all_registers_and_address_layouts_at_boundaries() {
    let mut count = 0;
    for op in OPS {
        for width in [32, 64] {
            let scale = 1_i64 << properties(op, width).0;
            for rt in 0..32 {
                for rn in 0..32 {
                    for offset in [-256, 0, 255, 4095 * scale] {
                        for mem in [false, true] {
                            let intent = inst(op, width, rt, rn, offset, mem);
                            let expected = word(op, width, rt, rn, offset);
                            assert_eq!(
                                encode_instruction(&intent).unwrap(),
                                expected,
                                "{intent:?}"
                            );
                            assert!(
                                matches!(check(&intent, expected), DecodeCheckOutcome::Match),
                                "{intent:?}"
                            );
                            count += 1;
                        }
                    }
                }
            }
        }
    }
    assert_eq!(count, 229_376);
}

#[test]
fn gpr_memory_every_canonical_immediate_field() {
    let mut count = 0;
    let mut expected_count = 0;
    for op in OPS {
        for width in [32, 64] {
            let scale = 1_i64 << properties(op, width).0;
            // UI owns every nonnegative aligned value; only the remaining
            // signed-nine-bit offsets use the unscaled encoding.
            expected_count += 2 * (4096 + 256 + 256 - 256 / scale);
            for offset in (0..4096)
                .map(|n| n * scale)
                .chain((-256..=255).filter(|n| *n < 0 || n % scale != 0))
            {
                for mem in [false, true] {
                    let intent = inst(op, width, 31, 31, offset, mem);
                    let expected = word(op, width, 31, 31, offset);
                    assert_eq!(encode_instruction(&intent).unwrap(), expected, "{intent:?}");
                    assert!(
                        matches!(check(&intent, expected), DecodeCheckOutcome::Match),
                        "{intent:?}"
                    );
                    count += 1;
                }
            }
        }
    }
    assert_eq!(count, expected_count);
    assert_eq!(count, 249_600);
}

#[test]
fn gpr_memory_special_zero_and_sp_spellings_preserve_narrow_aliases() {
    let mut count = 0;
    for op in OPS {
        for width in [32, 64] {
            for rt in [
                transfer(width, 31),
                Arg::Special(if width == 64 {
                    SpecialReg::XZR
                } else {
                    SpecialReg::WZR
                }),
            ] {
                for base in [Arg::PReg(regs::SP), Arg::Special(SpecialReg::SP)] {
                    for explicit in [false, true] {
                        let mut args = vec![rt.clone(), base.clone()];
                        if explicit {
                            args.push(Arg::Imm(0));
                        }
                        let intent = MachInst::new(op, args);
                        let expected = word(op, width, 31, 31, 0);
                        assert_eq!(encode_instruction(&intent).unwrap(), expected, "{intent:?}");
                        assert!(
                            matches!(check(&intent, expected), DecodeCheckOutcome::Match),
                            "{intent:?}"
                        );
                        count += 1;
                    }
                }
            }
        }
    }
    // Bool/B1 producers can use X registers with Ldrb/Strb. Those aliases are
    // included above; physical FPR B registers are a different bank entirely.
    assert_eq!(count, 224);
}

#[test]
fn gpr_memory_malformed_banks_shapes_and_arity_refuse() {
    let mut tested = 0;
    for op in OPS {
        for width in [32, 64] {
            let good = inst(op, width, 0, 1, 0, false);
            let expected = word(op, width, 0, 1, 0);
            let mut bad = Vec::new();
            for base in [
                32,
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
                164,
                165,
                196,
                197,
                228,
                229,
                u16::MAX,
            ] {
                let base = PReg::new(base);
                for address in [Arg::PReg(base), Arg::MemOp { base, offset: 0 }] {
                    bad.push((
                        MachInst::new(op, vec![transfer(width, 0), address]),
                        word(op, width, 0, u16::from(base.hw_enc()), 0),
                    ));
                }
            }
            for transfer in [
                Arg::PReg(regs::SP),
                Arg::PReg(regs::WSP),
                Arg::PReg(regs::NZCV),
                Arg::PReg(PReg::new(164)),
                Arg::PReg(PReg::new(229)),
                Arg::PReg(PReg::new(u16::MAX)),
                Arg::Special(SpecialReg::SP),
                Arg::Imm(0),
                Arg::VReg(regs::VReg::new(0, regs::RegClass::Gpr64)),
            ] {
                let mut intent = good.clone();
                intent.operands[0] = transfer;
                bad.push((intent, expected));
            }
            for base in [
                Arg::Special(SpecialReg::XZR),
                Arg::Special(SpecialReg::WZR),
                Arg::Imm(0),
                Arg::VReg(regs::VReg::new(0, regs::RegClass::Gpr64)),
            ] {
                bad.push((
                    MachInst::new(op, vec![transfer(width, 0), base]),
                    word(op, width, 0, 31, 0),
                ));
            }
            bad.push((MachInst::new(op, vec![]), expected));
            bad.push((MachInst::new(op, vec![transfer(width, 0)]), expected));
            let mut wrong = good.clone();
            wrong.operands[2] = Arg::PReg(regs::X0);
            bad.push((wrong, expected));
            for mem in [false, true] {
                for extra in [Arg::Imm(0), Arg::PReg(regs::X1)] {
                    let mut wrong = inst(op, width, 0, 1, 0, mem);
                    wrong.operands.push(extra);
                    bad.push((wrong, expected));
                }
            }
            for (intent, matching_low_fields) in bad {
                assert!(
                    encode_instruction(&intent).is_err(),
                    "encoder admitted {intent:?}"
                );
                assert!(
                    matches!(
                        check(&intent, matching_low_fields),
                        DecodeCheckOutcome::Mismatch(_)
                    ),
                    "decoder admitted {intent:?}"
                );
                assert!(!enforce(intent, matching_low_fields, None));
                tested += 1;
            }
            for id in [64, 95, 96, 127, 128, 159, 165, 196, 197, 228] {
                let mut wrong = good.clone();
                wrong.operands[0] = Arg::PReg(PReg::new(id));
                // Full LDR/STR own valid H/S/D/Q transfers elsewhere. Narrow
                // integer opcodes do not: matching GPR low bits must not hide it.
                let full = matches!(
                    op,
                    Op::LdrRI | Op::StrRI | Op::VolatileLdrRI | Op::VolatileStrRI
                );
                if !full || id >= 197 {
                    assert!(
                        encode_instruction(&wrong).is_err(),
                        "encoder admitted {wrong:?}"
                    );
                }
                let spoof = word(op, width, u16::from(PReg::new(id).hw_enc()), 1, 0);
                assert!(
                    matches!(check(&wrong, spoof), DecodeCheckOutcome::Mismatch(_)),
                    "{wrong:?}"
                );
                assert!(!enforce(wrong, spoof, None));
                tested += 1;
            }
        }
    }
    assert_eq!(tested, 1848);
}

#[test]
fn gpr_memory_huge_offsets_and_noncanonical_words_refuse() {
    let mut count = 0;
    for op in OPS {
        for width in [32, 64] {
            let scale = 1_i64 << properties(op, width).0;
            for mem in [false, true] {
                let good = inst(op, width, 0, 1, 0, mem);
                let expected = word(op, width, 0, 1, 0);
                assert!(matches!(
                    check(&good, expected & !0x0100_0000),
                    DecodeCheckOutcome::Mismatch(_)
                ));
                for offset in [
                    -257,
                    i64::MIN,
                    i64::MAX,
                    4096 * scale,
                    (1_i64 << 32) * scale,
                    ((1_i64 << 32) + 4095) * scale,
                ] {
                    let wrong = inst(op, width, 0, 1, offset, mem);
                    assert!(encode_instruction(&wrong).is_err(), "{wrong:?}");
                    assert!(
                        matches!(check(&wrong, expected), DecodeCheckOutcome::Mismatch(_)),
                        "{wrong:?}"
                    );
                    assert!(!enforce(wrong, expected, None));
                    count += 1;
                }
            }
        }
    }
    assert_eq!(count, 336);
}

#[test]
fn gpr_memory_relocation_holes_and_byte_lengths_refuse() {
    let mut holes = 0;
    let mut lengths = 0;
    for op in OPS {
        for width in [32, 64] {
            let intent = inst(op, width, 31, 31, 0, false);
            let expected = word(op, width, 31, 31, 0);
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
    assert_eq!((holes, lengths), (672, 168));
}

#[cfg(all(
    target_arch = "aarch64",
    any(target_os = "macos", all(target_os = "linux", target_env = "gnu"))
))]
mod native {
    use super::*;
    use sha2::{Digest, Sha256};
    use std::{fmt::Write, fs, io::Read, path::Path, process::Command, time::Duration};

    const CASES: usize = 224;
    const PATTERNS: usize = 4;
    const SIZE: usize = 33792;

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
        let result = process::command_output_with_timeout(command, bound)
            .expect("required native tool must launch");
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
        assert!(!result.timed_out, "{label} timeout; {directory:?}");
        assert_eq!(
            result.output.status.code(),
            Some(expected),
            "{label}; {directory:?}: {}",
            String::from_utf8_lossy(&result.output.stderr)
        );
        result.output
    }

    fn mnemonic(op: Op, unscaled: bool) -> &'static str {
        match (op, unscaled) {
            (Op::LdrRI | Op::VolatileLdrRI, false) => "ldr",
            (Op::LdrRI | Op::VolatileLdrRI, true) => "ldur",
            (Op::StrRI | Op::VolatileStrRI, false) => "str",
            (Op::StrRI | Op::VolatileStrRI, true) => "stur",
            (Op::LdrbRI | Op::VolatileLdrbRI, false) => "ldrb",
            (Op::LdrbRI | Op::VolatileLdrbRI, true) => "ldurb",
            (Op::StrbRI | Op::VolatileStrbRI, false) => "strb",
            (Op::StrbRI | Op::VolatileStrbRI, true) => "sturb",
            (Op::LdrhRI | Op::VolatileLdrhRI, false) => "ldrh",
            (Op::LdrhRI | Op::VolatileLdrhRI, true) => "ldurh",
            (Op::StrhRI | Op::VolatileStrhRI, false) => "strh",
            (Op::StrhRI | Op::VolatileStrhRI, true) => "sturh",
            (Op::LdrsbRI, false) => "ldrsb",
            (Op::LdrsbRI, true) => "ldursb",
            (Op::LdrshRI, false) => "ldrsh",
            (Op::LdrshRI, true) => "ldursh",
            _ => unreachable!(),
        }
    }

    pub fn run() {
        // Host gate, constant by design: `cfg!` fixes the compile target, so clippy sees a
        // constant where this harness needs a runtime refusal (the emitted `.inst` words and
        // the C driver's byte comparisons both assume a little-endian host).
        #[allow(clippy::assertions_on_constants)]
        {
            assert!(cfg!(target_endian = "little"));
        }
        let directory_scratch = crate::fresh_dir::create("trust-cg-gpr-memory-native-");
        let directory = directory_scratch.to_path_buf();
        eprintln!("GPR memory native evidence={directory:?}");
        let mut assembly = String::from(".text\n");
        let mut driver = String::from(DRIVER);
        let mut rows = Vec::new();
        for op in OPS {
            for width in [32, 64] {
                let (size, _, load, signed) = properties(op, width);
                let scale = 1_i64 << size;
                for rt in [9, 31] {
                    for offset in [-256, 1, 255, 4095 * scale] {
                        let index = rows.len();
                        let expected = word(op, width, rt, 0, offset);
                        let encoded =
                            encode_instruction(&inst(op, width, rt, 0, offset, false)).unwrap();
                        assert_eq!(encoded, expected);
                        let unscaled = offset < 0 || offset % scale != 0;
                        // Narrow unsigned aliases always spell architectural Wt,
                        // even when MachIR selected X for a Bool/B1 carrier.
                        let arch_width = if signed || scale >= 4 { width } else { 32 };
                        let bank = if arch_width == 64 { 'x' } else { 'w' };
                        let register = if rt == 31 {
                            format!("{bank}zr")
                        } else {
                            format!("{bank}9")
                        };
                        let oracle =
                            format!("{} {register},[x0,#{offset}]", mnemonic(op, unscaled));
                        for (prefix, instruction) in
                            [('g', format!(".inst 0x{encoded:08x}")), ('a', oracle)]
                        {
                            // Leaf ABI: x0=buffer base, x1=seed; only caller-saved
                            // x9 changes. Return full X9 to expose W-load clearing.
                            writeln!(assembly, ".p2align 2\n.global {prefix}{index}\n.type {prefix}{index},%function\n{prefix}{index}:\nmov x9,x1\n.global {prefix}{index}_word\n{prefix}{index}_word:\n{instruction}\nmov x0,{}\nret\n.size {prefix}{index},.-{prefix}{index}", if rt == 31 { "xzr" } else { "x9" }).unwrap();
                            writeln!(driver, "extern uint64_t {prefix}{index}(unsigned char*,uint64_t); extern const uint32_t {prefix}{index}_word[];").unwrap();
                        }
                        rows.push(format!("{{g{index},a{index},g{index}_word,a{index}_word,0x{expected:08x}u,{scale},{width},{},{},{},{offset}}}", u8::from(load), u8::from(signed), u8::from(rt==31)));
                    }
                }
            }
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
        let result = run_command(
            &directory,
            "native",
            &mut Command::new(&executable),
            process::codegen_run_timeout(),
            0,
        );
        let checks = CASES * 2 + CASES * PATTERNS * (2 * SIZE + 2);
        assert_eq!(
            String::from_utf8(result.stdout).unwrap(),
            format!(
                "GPR_MEMORY_NATIVE_PASS cases={CASES} cg_calls=896 asm_calls=896 checks={checks}\n"
            )
        );
        let poisoned = run_command(
            &directory,
            "poison",
            Command::new(&executable).arg("--poison"),
            process::codegen_run_timeout(),
            97,
        );
        assert!(String::from_utf8_lossy(&poisoned.stderr).contains("EXPECTED_RETURN_MISMATCH"));
    }

    const DRIVER: &str = r#"
#include <stdint.h>
#include <stdio.h>
#include <string.h>
#define SIZE 33792
typedef uint64_t (*Fn)(unsigned char *,uint64_t);
struct Case { Fn cg,oracle; const uint32_t *cg_word,*asm_word; uint32_t expected_word; unsigned bytes,width,load,is_signed,zero; int offset; };
static unsigned char cg[SIZE],oracle[SIZE],expected[SIZE];
static unsigned long checks,cg_calls,asm_calls;
"#;

    const MAIN: &str = r#"
int main(int argc,char **argv) {
    const int poison=argc==2 && strcmp(argv[1],"--poison")==0;
    if(argc!=1 && !poison) return 96;
    const unsigned char edges[]={0,0x7f,0x80,0xff};
    if(sizeof(cases)/sizeof(cases[0])!=224) return 98;
    for(size_t i=0;i<224;++i) {
        const struct Case *c=&cases[i];
        checks+=2;
        if(*c->cg_word!=c->expected_word || *c->asm_word!=c->expected_word) return 95;
        for(size_t p=0;p<4;++p) {
            const size_t address=(size_t)(512+c->offset);
            if(address+c->bytes>SIZE || address<16) return 98;
            for(size_t j=0;j<SIZE;++j) expected[j]=(unsigned char)((j*37+p*71)^(j>>3));
            for(size_t j=0;j<c->bytes;++j) expected[address+j]=edges[p];
            memcpy(cg,expected,SIZE); memcpy(oracle,expected,SIZE);
            const uint64_t seed=UINT64_C(0xfedcba9876543200)|edges[p];
            uint64_t wanted=c->zero?0:seed;
            if(c->load && !c->zero) {
                wanted=0;
                for(size_t j=0;j<c->bytes;++j) wanted|=(uint64_t)expected[address+j]<<(j*8);
                if(c->is_signed && (expected[address+c->bytes-1]&0x80)) wanted|=UINT64_MAX<<(c->bytes*8);
                if(c->width==32) wanted&=UINT64_C(0xffffffff);
            } else if(!c->load) {
                const uint64_t stored=c->zero?0:seed;
                for(size_t j=0;j<c->bytes;++j) expected[address+j]=(unsigned char)(stored>>(j*8));
            }
            if(poison && i==0 && p==0) wanted^=1;
            const uint64_t a=c->cg(cg+512,seed); ++cg_calls;
            const uint64_t b=c->oracle(oracle+512,seed); ++asm_calls;
            checks+=2;
            if(a!=wanted || b!=wanted) { fprintf(stderr,"EXPECTED_RETURN_MISMATCH case=%zu pattern=%zu\n",i,p); return 97; }
            for(size_t j=0;j<SIZE;++j) {
                checks+=2;
                if(cg[j]!=expected[j] || oracle[j]!=expected[j]) { fprintf(stderr,"EXPECTED_BYTE_MISMATCH case=%zu offset=%zu\n",i,j); return 97; }
            }
        }
    }
    if(cg_calls!=896 || asm_calls!=896 || checks!=224UL*2+224UL*4*(2*SIZE+2)) return 98;
    printf("GPR_MEMORY_NATIVE_PASS cases=224 cg_calls=%lu asm_calls=%lu checks=%lu\n",cg_calls,asm_calls,checks);
    return 0;
}
"#;
}

#[cfg(all(
    target_arch = "aarch64",
    any(target_os = "macos", all(target_os = "linux", target_env = "gnu"))
))]
#[test]
fn gpr_memory_native_words_and_exact_byte_effects() {
    native::run();
}

#[path = "common/fresh_dir.rs"]
mod fresh_dir;
