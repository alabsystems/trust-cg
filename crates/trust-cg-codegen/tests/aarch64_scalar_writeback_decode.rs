// Copyright 2026 Andrew Yates | Apache-2.0
//! Independent scalar W/X pre/post-index encoding and finite native controls.
//! These tests do not confer source-binding proof authority. Native SP cases
//! use a private aligned stack frame, never a heap-backed stack pointer.
//! Pairs, FP/NEON, register-offset and narrow signed loads retain other owners.

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

const OPS: [Op; 4] = [
    Op::LdrPreIndex,
    Op::StrPreIndex,
    Op::LdrPostIndex,
    Op::StrPostIndex,
];

fn properties(op: Op) -> (bool, bool) {
    match op {
        Op::LdrPreIndex => (true, true),
        Op::StrPreIndex => (false, true),
        Op::LdrPostIndex => (true, false),
        Op::StrPostIndex => (false, false),
        _ => panic!("outside the four scalar writeback opcodes"),
    }
}

fn transfer(width: u16, rt: u16) -> Arg {
    assert!(matches!(width, 32 | 64) && rt < 32);
    Arg::PReg(if rt == 31 {
        if width == 64 { regs::XZR } else { regs::WZR }
    } else {
        PReg::new(rt + if width == 64 { 0 } else { 32 })
    })
}

fn inst(op: Op, width: u16, rt: u16, rn: u16, offset: i64) -> MachInst {
    MachInst::new(
        op,
        vec![
            transfer(width, rt),
            Arg::PReg(PReg::new(rn)),
            Arg::Imm(offset),
        ],
    )
}

fn word(op: Op, width: u16, rt: u16, rn: u16, offset: i64) -> u32 {
    assert!(matches!(width, 32 | 64) && rt < 32 && rn < 32);
    assert!((-256..=255).contains(&offset));
    let (load, pre) = properties(op);
    // Arm LDR/STR (immediate), printed pp509-511/910-912, v2025-03:
    // size[31:30]=10/11, fixed111[29:27], V=0, fixed00[25:24],
    // opc[23:22]=00/01, fixed0[21], signed imm9[20:12], mode=11/01.
    // Independent of all production encoder and decoder helpers.
    (if width == 64 {
        0xf800_0000
    } else {
        0xb800_0000
    }) | (u32::from(load) << 22)
        | (((offset as u32) & 0x1ff) << 12)
        | (if pre { 0xc00 } else { 0x400 })
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
fn scalar_writeback_literal_words_and_all_bit_mutations() {
    let mut positives = 0;
    let mut mutants = 0;
    for op in OPS {
        let literals = match op {
            Op::LdrPreIndex => [0xb840_0c20, 0xf840_0c20],
            Op::StrPreIndex => [0xb800_0c20, 0xf800_0c20],
            Op::LdrPostIndex => [0xb840_0420, 0xf840_0420],
            Op::StrPostIndex => [0xb800_0420, 0xf800_0420],
            _ => unreachable!(),
        };
        for (width, expected) in [32, 64].into_iter().zip(literals) {
            let intent = inst(op, width, 0, 1, 0);
            assert_eq!(word(op, width, 0, 1, 0), expected);
            accepted(&intent, expected);
            assert!(enforce(intent.clone(), expected, None));
            positives += 1;
            for bit in 0..32 {
                let mutant = expected ^ (1 << bit);
                assert!(
                    matches!(check(&intent, mutant), DecodeCheckOutcome::Mismatch(_)),
                    "{intent:?} bit={bit}"
                );
                assert!(!enforce(intent.clone(), mutant, None));
                mutants += 1;
            }
        }
    }
    assert_eq!((positives, mutants), (8, 256));
}

#[test]
fn scalar_writeback_all_register_pairs_and_cross_width_overlap() {
    let mut positives = 0;
    let mut overlaps = 0;
    for op in OPS {
        for width in [32, 64] {
            for rt in 0..32 {
                for rn in 0..32 {
                    for offset in [-256, 0, 255] {
                        let intent = inst(op, width, rt, rn, offset);
                        let expected = word(op, width, rt, rn, offset);
                        // Rt denotes W/X/ZR, whereas Rn31 denotes SP. Wt/Xn
                        // overlap is constrained-unpredictable too, even #0.
                        if rt == rn && rn != 31 {
                            refused(&intent, expected);
                            overlaps += 1;
                        } else {
                            accepted(&intent, expected);
                            positives += 1;
                        }
                    }
                }
            }
        }
    }
    assert_eq!((positives, overlaps), (23_832, 744));
}

#[test]
fn scalar_writeback_every_signed_immediate_field() {
    let mut count = 0;
    for op in OPS {
        for width in [32, 64] {
            for (rt, rn) in [(0, 1), (31, 31)] {
                for offset in -256..=255 {
                    let intent = inst(op, width, rt, rn, offset);
                    accepted(&intent, word(op, width, rt, rn, offset));
                    count += 1;
                }
            }
        }
    }
    assert_eq!(count, 8192);
}

#[test]
fn scalar_writeback_physical_and_special_zero_sp_spellings() {
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
                for rn in [Arg::PReg(regs::SP), Arg::Special(SpecialReg::SP)] {
                    for offset in [-256, 0, 255] {
                        let intent =
                            MachInst::new(op, vec![rt.clone(), rn.clone(), Arg::Imm(offset)]);
                        let expected = word(op, width, 31, 31, offset);
                        accepted(&intent, expected);
                        assert!(enforce(intent, expected, None));
                        count += 1;
                    }
                }
            }
        }
    }
    assert_eq!(count, 96);
}

#[test]
fn scalar_writeback_malformed_banks_and_exact_arity_refuse() {
    let mut count = 0;
    for op in OPS {
        for width in [32, 64] {
            let good = inst(op, width, 0, 1, 0);
            let mut bad = Vec::new();
            for id in [
                31,
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
                intent.operands[0] = Arg::PReg(PReg::new(id));
                bad.push(intent);
            }
            for id in [
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
                let mut intent = good.clone();
                intent.operands[1] = Arg::PReg(PReg::new(id));
                bad.push(intent);
            }
            let vreg = Arg::VReg(regs::VReg::new(0, regs::RegClass::Gpr64));
            for rt in [Arg::Special(SpecialReg::SP), Arg::Imm(0), vreg.clone()] {
                let mut intent = good.clone();
                intent.operands[0] = rt;
                bad.push(intent);
            }
            for rn in [
                Arg::Special(SpecialReg::XZR),
                Arg::Special(SpecialReg::WZR),
                Arg::Imm(0),
                vreg,
            ] {
                let mut intent = good.clone();
                intent.operands[1] = rn;
                bad.push(intent);
            }
            for arity in 0..3 {
                bad.push(MachInst::new(op, good.operands[..arity].to_vec()));
            }
            for extra in [Arg::Imm(0), Arg::PReg(regs::X1)] {
                let mut intent = good.clone();
                intent.operands.push(extra);
                bad.push(intent);
            }
            let mut wrong_imm = good.clone();
            wrong_imm.operands[2] = Arg::PReg(regs::X2);
            bad.push(wrong_imm);
            // MemOp belongs to non-writeback addressing; no implicit default
            // offset or trailing split immediate may silently reinterpret it.
            for trailing in [false, true] {
                let mut args = vec![
                    transfer(width, 0),
                    Arg::MemOp {
                        base: regs::X1,
                        offset: 0,
                    },
                ];
                if trailing {
                    args.push(Arg::Imm(0));
                }
                bad.push(MachInst::new(op, args));
            }
            assert_eq!(bad.len(), 49);
            for intent in bad {
                // Preserve the malformed bank's actual low field: a mismatch
                // must not depend on accidentally comparing Rt/Rn=0 instead.
                let field = |arg: Option<&Arg>, fallback| match arg {
                    Some(Arg::PReg(reg)) => u16::from(reg.hw_enc()),
                    Some(Arg::Special(_)) => 31,
                    _ => fallback,
                };
                let spoof = word(
                    op,
                    width,
                    field(intent.operands.first(), 0),
                    field(intent.operands.get(1), 1),
                    0,
                );
                refused(&intent, spoof);
                count += 1;
            }
        }
    }
    assert_eq!(count, 392);
}

#[test]
fn scalar_writeback_out_of_range_offsets_refuse_without_truncation() {
    let mut count = 0;
    for op in OPS {
        for width in [32, 64] {
            for offset in [
                -257,
                256,
                -32769,
                32768,
                i64::MIN,
                i64::MAX,
                1_i64 << 32,
                (1_i64 << 32) + 255,
            ] {
                refused(&inst(op, width, 0, 1, offset), word(op, width, 0, 1, 0));
                count += 1;
            }
        }
    }
    assert_eq!(count, 64);
}

#[test]
fn scalar_writeback_relocation_holes_and_byte_lengths_refuse() {
    let mut holes = 0;
    let mut lengths = 0;
    for op in OPS {
        for width in [32, 64] {
            let intent = inst(op, width, 31, 31, 0);
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
    assert_eq!((holes, lengths), (192, 48));
}

#[cfg(all(
    target_arch = "aarch64",
    any(target_os = "macos", all(target_os = "linux", target_env = "gnu"))
))]
mod native {
    use super::*;
    use sha2::{Digest, Sha256};
    use std::{fmt::Write, fs, io::Read, path::Path, process::Command, time::Duration};

    const CASES: usize = 160;
    const PATTERNS: usize = 4;
    const SIZE: usize = 1024;

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
                panic!("required native process could not launch: {error}; {directory:?}");
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
        assert!(!result.timed_out, "{label} timeout; {directory:?}");
        assert_eq!(
            result.output.status.code(),
            Some(expected),
            "{label}; {directory:?}: {}",
            String::from_utf8_lossy(&result.output.stderr)
        );
        result.output
    }

    pub fn run() {
        // Host gate, constant by design: `cfg!` fixes the compile target, so clippy sees a
        // constant where this harness needs a runtime refusal.
        #[allow(clippy::assertions_on_constants)]
        {
            assert!(cfg!(target_endian = "little"));
        }
        let directory_scratch = crate::fresh_dir::create("trust-cg-scalar-writeback-native-");
        let directory = directory_scratch.to_path_buf();
        eprintln!("scalar writeback native evidence={directory:?}");
        let mut assembly = String::from(".text\n");
        let mut driver = String::from(DRIVER);
        let mut rows = Vec::new();
        for op in OPS {
            let (load, pre) = properties(op);
            for width in [32, 64] {
                for rt in [9, 31] {
                    for sp_base in [false, true] {
                        let offsets = if sp_base {
                            [-256, -16, 0, 16, 240]
                        } else {
                            [-256, -1, 0, 1, 255]
                        };
                        for offset in offsets {
                            let index = rows.len();
                            let rn = if sp_base { 31 } else { 0 };
                            let expected = word(op, width, rt, rn, offset);
                            let encoded =
                                encode_instruction(&inst(op, width, rt, rn, offset)).unwrap();
                            assert_eq!(encoded, expected);
                            let bank = if width == 64 { 'x' } else { 'w' };
                            let register = if rt == 31 {
                                format!("{bank}zr")
                            } else {
                                format!("{bank}9")
                            };
                            let mnemonic = if load { "ldr" } else { "str" };
                            let base = if sp_base { "sp" } else { "x0" };
                            let oracle = if pre {
                                format!("{mnemonic} {register},[{base},#{offset}]!")
                            } else {
                                format!("{mnemonic} {register},[{base}],#{offset}")
                            };
                            for (prefix, instruction) in
                                [('g', format!(".inst 0x{encoded:08x}")), ('a', oracle)]
                            {
                                // AAPCS64 leaf: x0=input base, x1=seed; caller-saved
                                // registers only, LR untouched, no BL on any path.
                                // A 16-byte integer result is returned in x0/x1.
                                // X9 stays seeded for ZR transfers (discard witness).
                                writeln!(assembly, ".p2align 2\n.global {prefix}{index}\n.type {prefix}{index},%function\n{prefix}{index}:\nmov x9,x1").unwrap();
                                if sp_base {
                                    // Allocate real stack storage first. Both the
                                    // temporary SP and every writeback are aligned
                                    // and inside this frame. Save original SP and
                                    // frame bottom in registers, not below the
                                    // temporary SP. No calls while SP is shifted.
                                    writeln!(assembly, "mov x10,sp\nsub sp,sp,#2048\nmov x11,sp\nsub x12,x0,#512\nmov x13,x12\nmov x14,x11\nmov x15,#64\n.L{prefix}{index}_in:\nldp x16,x17,[x13],#16\nstp x16,x17,[x14],#16\nsubs x15,x15,#1\nb.ne .L{prefix}{index}_in\nadd sp,x11,#512").unwrap();
                                }
                                writeln!(assembly, ".global {prefix}{index}_word\n{prefix}{index}_word:\n{instruction}").unwrap();
                                if sp_base {
                                    // Straight-line capture/restoration immediately
                                    // after the tested word. Map its updated stack
                                    // address back to the corresponding C buffer.
                                    writeln!(assembly, "mov x1,sp\nmov sp,x11\nsub x1,x1,x11\nadd x1,x12,x1\nmov x13,x11\nmov x14,x12\nmov x15,#64\n.L{prefix}{index}_out:\nldp x16,x17,[x13],#16\nstp x16,x17,[x14],#16\nsubs x15,x15,#1\nb.ne .L{prefix}{index}_out\nmov sp,x10").unwrap();
                                } else {
                                    assembly.push_str("mov x1,x0\n");
                                }
                                writeln!(
                                    assembly,
                                    "mov x0,x9\nret\n.size {prefix}{index},.-{prefix}{index}"
                                )
                                .unwrap();
                                writeln!(driver, "extern struct Result {prefix}{index}(unsigned char*,uint64_t); extern const uint32_t {prefix}{index}_word[];").unwrap();
                            }
                            rows.push(format!("{{g{index},a{index},g{index}_word,a{index}_word,0x{expected:08x}u,{},{},{},{},{offset}}}", width / 8, u8::from(load), u8::from(pre), u8::from(rt == 31)));
                        }
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
        let checks = CASES * 2 + CASES * PATTERNS * (2 * SIZE + 4);
        assert_eq!(
            String::from_utf8(result.stdout).unwrap(),
            format!(
                "SCALAR_WRITEBACK_NATIVE_PASS cases={CASES} cg_calls=640 asm_calls=640 checks={checks}\n"
            )
        );
        let poisoned = run_command(
            &directory,
            "poison",
            Command::new(&executable).arg("--poison"),
            process::codegen_run_timeout(),
            97,
        );
        assert!(String::from_utf8_lossy(&poisoned.stderr).contains("EXPECTED_BASE_MISMATCH"));
    }

    const DRIVER: &str = r#"
#include <stdint.h>
#include <stdio.h>
#include <string.h>
#define SIZE 1024
struct Result { uint64_t transfer; uintptr_t base; };
_Static_assert(sizeof(struct Result)==16,"AAPCS64 two-GPR result");
typedef struct Result (*Fn)(unsigned char *,uint64_t);
struct Case { Fn cg,oracle; const uint32_t *cg_word,*asm_word; uint32_t expected_word; unsigned bytes,load,pre,zero; int offset; };
static _Alignas(16) unsigned char cg[SIZE],oracle[SIZE],expected[SIZE];
static unsigned long checks,cg_calls,asm_calls;
"#;

    const MAIN: &str = r#"
int main(int argc,char **argv) {
    const int poison=argc==2 && strcmp(argv[1],"--poison")==0;
    if(argc!=1 && !poison) return 96;
    const unsigned char edges[]={0,0x7f,0x80,0xff};
    if(sizeof(cases)/sizeof(cases[0])!=160) return 98;
    for(size_t i=0;i<160;++i) {
        const struct Case *c=&cases[i];
        checks+=2;
        if(*c->cg_word!=c->expected_word || *c->asm_word!=c->expected_word) return 95;
        for(size_t p=0;p<4;++p) {
            const int final_index=512+c->offset;
            const int access_index=c->pre?final_index:512;
            if(final_index<16 || final_index>=SIZE-16 || access_index<16 || (unsigned)access_index+c->bytes>SIZE-16) return 98;
            const size_t address=(size_t)access_index;
            for(size_t j=0;j<SIZE;++j) expected[j]=(unsigned char)((j*37+p*71)^(j>>3));
            for(size_t j=0;j<c->bytes;++j) expected[address+j]=edges[p];
            memcpy(cg,expected,SIZE); memcpy(oracle,expected,SIZE);
            const uint64_t seed=UINT64_C(0xfedcba9876543200)|edges[p];
            uint64_t wanted=seed;
            if(c->load && !c->zero) {
                wanted=0;
                for(size_t j=0;j<c->bytes;++j) wanted|=(uint64_t)expected[address+j]<<(j*8);
            } else if(!c->load) {
                const uint64_t stored=c->zero?0:seed;
                for(size_t j=0;j<c->bytes;++j) expected[address+j]=(unsigned char)(stored>>(j*8));
            }
            uintptr_t cg_base=(uintptr_t)(cg+final_index),asm_base=(uintptr_t)(oracle+final_index);
            if(poison && i==0 && p==0) { cg_base^=1; asm_base^=1; }
            const struct Result a=c->cg(cg+512,seed); ++cg_calls;
            const struct Result b=c->oracle(oracle+512,seed); ++asm_calls;
            checks+=4;
            if(a.base!=cg_base || b.base!=asm_base) { fprintf(stderr,"EXPECTED_BASE_MISMATCH case=%zu pattern=%zu\n",i,p); return 97; }
            if(a.transfer!=wanted || b.transfer!=wanted) { fprintf(stderr,"EXPECTED_TRANSFER_MISMATCH case=%zu pattern=%zu\n",i,p); return 97; }
            for(size_t j=0;j<SIZE;++j) {
                checks+=2;
                if(cg[j]!=expected[j] || oracle[j]!=expected[j]) { fprintf(stderr,"EXPECTED_BYTE_MISMATCH case=%zu offset=%zu\n",i,j); return 97; }
            }
        }
    }
    if(cg_calls!=640 || asm_calls!=640 || checks!=160UL*2+160UL*4*(2*SIZE+4)) return 98;
    printf("SCALAR_WRITEBACK_NATIVE_PASS cases=160 cg_calls=%lu asm_calls=%lu checks=%lu\n",cg_calls,asm_calls,checks);
    return 0;
}
"#;
}

#[cfg(all(
    target_arch = "aarch64",
    any(target_os = "macos", all(target_os = "linux", target_env = "gnu"))
))]
#[test]
fn scalar_writeback_native_memory_transfer_and_updated_base() {
    native::run();
}

#[path = "common/fresh_dir.rs"]
mod fresh_dir;
