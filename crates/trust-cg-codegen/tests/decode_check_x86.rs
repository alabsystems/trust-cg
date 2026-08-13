// trust-cg-codegen — ENC-3: standalone validation of the x86 decode-check gate.
//
// Author: Andrew Yates | Copyright 2026 Andrew Yates | License: Apache-2.0
//
// Validates the INDEPENDENT decoder + intent-renderer that back the per-emission
// decode-check gate, WITHOUT running the whole pipeline:
//
//   * `decode_check_corpus_replay` — for every covered family, generate
//     instruction instances over register / immediate / displacement edge cases
//     (r8-r15, RSP/RBP/R12/R13 addressing edges, spl/bpl/sil/dil byte regs,
//     boundary immediates), encode them with the REAL `X86Encoder`, then decode
//     the bytes with the gate's decoder and structurally compare against the
//     intent. Because ENC-2 independently pins `X86Encoder`'s bytes == an
//     external disassembler for these families, decoder-agreement here anchors
//     the decoder to the external disassembler transitively.
//
//   * `decode_check_positive_faithful_encoding_passes` — a faithful encoding is
//     accepted.
//
//   * `decode_check_refutation_*` — the committed mutation negative controls:
//     corrupting a single ModR/M or immediate byte of a known-good encoding is
//     REJECTED (fail-closed), while the un-mutated bytes pass.

use trust_cg_codegen::decode_check::{FixupHole, FixupHoleKind};
use trust_cg_codegen::x86_64::decode_check::{X86IntentInst, check_one_for_test};
use trust_cg_codegen::x86_64::{X86Encoder, X86InstOperands};
use trust_cg_ir::x86_64_ops::{X86CondCode, X86Opcode};
use trust_cg_ir::x86_64_regs::{
    AL, BL, CL, DIL, DL, EAX, EBP, ECX, EDX, ESI, R8, R8B, R8D, R9, R11, R12, R13, R13D, R14, R15,
    R15B, R15D, RAX, RBP, RBX, RCX, RDI, RDX, RSI, RSP, SIL, SPL, X86PReg,
};

fn encode(op: X86Opcode, ops: &X86InstOperands) -> Option<Vec<u8>> {
    let mut enc = X86Encoder::new();
    enc.encode_instruction(op, ops).ok()?;
    Some(enc.finish())
}

/// Encode + decode-check a single (opcode, ops). Returns Err with context on a
/// structural mismatch; skips (Ok) when the encoder itself rejects the operands.
fn roundtrip(op: X86Opcode, ops: &X86InstOperands, hole: Option<FixupHole>) -> Result<(), String> {
    let Some(bytes) = encode(op, ops) else {
        return Ok(()); // encoder rejected these operands — not a decode-check case
    };
    let intent = X86IntentInst {
        opcode: op,
        ops: ops.clone(),
    };
    match check_one_for_test(&intent, &bytes, hole.as_ref()) {
        Ok(_) => Ok(()),
        Err(e) => Err(format!("{op:?} {ops:?} -> bytes {bytes:02x?}: {e}")),
    }
}

const GPR64: &[X86PReg] = &[
    RAX, RCX, RDX, RBX, RSP, RBP, RSI, RDI, R8, R11, R12, R13, R14, R15,
];
const GPR64_NOSP: &[X86PReg] = &[RAX, RCX, RDX, RBX, RBP, RSI, RDI, R8, R11, R12, R13, R15];
const GPR32: &[X86PReg] = &[EAX, ECX, EDX, ESI, EBP, R8D, R13D, R15D];
const GPR8: &[X86PReg] = &[AL, CL, DL, BL, SPL, SIL, DIL, R8B, R15B];
const DISPS: &[i64] = &[0, 1, -1, 8, 127, 128, -128, -129, 4096, -4096, 0x0012_3456];
const IMM32S: &[i64] = &[
    0,
    1,
    -1,
    127,
    128,
    -128,
    -129,
    1000,
    0x1234_5678,
    -0x1234_5678,
    i32::MAX as i64,
    i32::MIN as i64,
];

/// The main corpus-replay validation of the decoder against the real encoder.
#[test]
fn decode_check_corpus_replay() {
    let mut count = 0usize;
    let mut fails: Vec<String> = Vec::new();
    let mut check = |op: X86Opcode, ops: &X86InstOperands| {
        count += 1;
        if let Err(e) = roundtrip(op, ops, None) {
            fails.push(e);
        }
    };

    // ALU reg-reg + MOV + TEST (64-bit and 32-bit).
    let alu_rr = [
        X86Opcode::AddRR,
        X86Opcode::SubRR,
        X86Opcode::AdcRR,
        X86Opcode::SbbRR,
        X86Opcode::AndRR,
        X86Opcode::OrRR,
        X86Opcode::XorRR,
        X86Opcode::CmpRR,
        X86Opcode::TestRR,
        X86Opcode::MovRR,
        X86Opcode::ImulRR,
    ];
    for &op in &alu_rr {
        for &d in GPR64 {
            for &s in GPR64 {
                check(op, &X86InstOperands::rr(d, s));
            }
        }
    }
    for &d in GPR32 {
        for &s in GPR32 {
            check(X86Opcode::MovRR32, &X86InstOperands::rr(d, s));
            check(X86Opcode::AddRR, &X86InstOperands::rr(d, s));
            check(X86Opcode::ImulRR, &X86InstOperands::rr(d, s));
        }
    }

    // ALU reg-imm (auto 81/83) + TEST imm + CmpRI8.
    let alu_ri = [
        X86Opcode::AddRI,
        X86Opcode::SubRI,
        X86Opcode::AndRI,
        X86Opcode::OrRI,
        X86Opcode::XorRI,
        X86Opcode::CmpRI,
        X86Opcode::TestRI,
    ];
    for &op in &alu_ri {
        for &d in GPR64 {
            for &imm in IMM32S {
                check(op, &X86InstOperands::ri(d, imm));
            }
        }
    }
    for &d in GPR32 {
        for &imm in IMM32S {
            check(X86Opcode::AddRI, &X86InstOperands::ri(d, imm));
        }
    }
    for &d in GPR64 {
        for &imm in &[0i64, 1, -1, 127, -128] {
            check(X86Opcode::CmpRI8, &X86InstOperands::ri(d, imm));
        }
    }

    // Unary (NEG/NOT/INC/DEC/IDIV/DIV/MUL) 64 + 32.
    for &op in &[
        X86Opcode::Neg,
        X86Opcode::Not,
        X86Opcode::Inc,
        X86Opcode::Dec,
        X86Opcode::Idiv,
        X86Opcode::Div,
        X86Opcode::Mul,
    ] {
        for &d in GPR64 {
            check(op, &X86InstOperands::r(d));
        }
        for &d in GPR32 {
            check(op, &X86InstOperands::r(d));
        }
    }
    check(X86Opcode::Cdq, &X86InstOperands::none());
    check(X86Opcode::Cqo, &X86InstOperands::none());

    // Shifts by imm8 + by CL.
    for &op in &[X86Opcode::ShlRI, X86Opcode::ShrRI, X86Opcode::SarRI] {
        for &d in GPR64 {
            for &sh in &[0i64, 1, 7, 31, 63] {
                check(op, &X86InstOperands::ri(d, sh));
            }
        }
    }
    for &op in &[X86Opcode::ShlRR, X86Opcode::ShrRR, X86Opcode::SarRR] {
        for &d in GPR64 {
            check(op, &X86InstOperands::r(d));
        }
    }

    // MOV r, imm (byte / word-alias / dword / movabs).
    for &d in GPR64 {
        for &imm in &[
            0i64,
            1,
            5,
            255,
            0x1234_5678,
            -1,
            i64::from(i32::MIN),
            0x1_0000_0000,
        ] {
            check(X86Opcode::MovRI, &X86InstOperands::ri(d, imm));
        }
    }
    for &d in GPR32 {
        for &imm in &[0i64, 1, 0x1234_5678] {
            check(X86Opcode::MovRI, &X86InstOperands::ri(d, imm));
        }
    }
    for &d in GPR8 {
        for &imm in &[0i64, 1, 127, -1] {
            check(X86Opcode::MovRI, &X86InstOperands::ri(d, imm));
        }
    }

    // MOVZX / MOVSX (all width variants).
    for &op in &[
        X86Opcode::Movzx,
        X86Opcode::MovzxW,
        X86Opcode::MovsxB,
        X86Opcode::MovsxW,
        X86Opcode::Movsx,
    ] {
        for &d in GPR64 {
            for &s in GPR64 {
                check(op, &X86InstOperands::rr(d, s));
            }
        }
    }

    // Bit manipulation.
    for &op in &[
        X86Opcode::Bsf,
        X86Opcode::Bsr,
        X86Opcode::Tzcnt,
        X86Opcode::Lzcnt,
        X86Opcode::Popcnt,
    ] {
        for &d in GPR64 {
            for &s in GPR64 {
                check(op, &X86InstOperands::rr(d, s));
            }
        }
    }
    for &d in GPR64 {
        for &bit in &[0i64, 1, 31, 63] {
            check(X86Opcode::BtRI, &X86InstOperands::ri(d, bit));
        }
        check(X86Opcode::Bswap, &X86InstOperands::r(d));
    }

    // Memory loads / stores (reg + [base + disp]) over addressing-mode edges.
    let mem_load_ops = [
        (X86Opcode::MovRM, RAX),
        (X86Opcode::MovRM32, EAX),
        (X86Opcode::MovRM16, RAX),
        (X86Opcode::MovRM8, RAX),
        (X86Opcode::AddRM, RAX),
        (X86Opcode::SubRM, RAX),
        (X86Opcode::CmpRM, RAX),
        (X86Opcode::ImulRM, RAX),
        (X86Opcode::Lea, RAX),
    ];
    for &d in &[RAX, RCX, R8, R13] {
        for &base in GPR64 {
            for &disp in DISPS {
                for &(op, _) in &mem_load_ops {
                    let reg = if op == X86Opcode::MovRM32 {
                        // 32-bit dst for a 32-bit load.
                        match d {
                            RAX => EAX,
                            RCX => ECX,
                            R8 => R8D,
                            _ => R13D,
                        }
                    } else {
                        d
                    };
                    check(op, &X86InstOperands::rm(reg, base, disp));
                }
                check(X86Opcode::MovMR, &X86InstOperands::rm(d, base, disp));
                check(X86Opcode::MovMR32, &X86InstOperands::rm(d, base, disp));
                check(X86Opcode::MovMR8, &X86InstOperands::rm(d, base, disp));
                check(X86Opcode::TestRM, &X86InstOperands::rm(d, base, disp));
            }
        }
    }

    // SIB (scaled-index) loads/stores + LEA.
    for &d in &[RAX, R8] {
        for &base in &[RAX, RSP, RBP, R12, R13] {
            for &index in &[RAX, RCX, R9, R12, R14] {
                for &scale in &[1u8, 2, 4, 8] {
                    for &disp in &[0i64, 16, 200] {
                        check(
                            X86Opcode::MovRMSib,
                            &X86InstOperands::rm_sib(d, base, index, scale, disp),
                        );
                        check(
                            X86Opcode::MovMRSib,
                            &X86InstOperands::rm_sib(d, base, index, scale, disp),
                        );
                        check(
                            X86Opcode::LeaSib,
                            &X86InstOperands::rm_sib(d, base, index, scale, disp),
                        );
                    }
                }
            }
        }
    }

    // Push / pop / ret / indirect call.
    for &d in GPR64 {
        check(X86Opcode::Push, &X86InstOperands::r(d));
        check(X86Opcode::Pop, &X86InstOperands::r(d));
        check(X86Opcode::CallR, &X86InstOperands::r(d));
    }
    check(X86Opcode::Ret, &X86InstOperands::none());
    for &base in GPR64_NOSP {
        for &disp in &[0i64, 24] {
            check(X86Opcode::CallM, &X86InstOperands::rm(RAX, base, disp));
        }
    }

    // SETcc / CMOVcc over all condition codes.
    let ccs = [
        X86CondCode::O,
        X86CondCode::B,
        X86CondCode::E,
        X86CondCode::NE,
        X86CondCode::BE,
        X86CondCode::A,
        X86CondCode::S,
        X86CondCode::L,
        X86CondCode::GE,
        X86CondCode::LE,
        X86CondCode::G,
    ];
    for &cc in &ccs {
        for &d in GPR8 {
            let mut ops = X86InstOperands::r(d);
            ops.cc = Some(cc);
            check(X86Opcode::Setcc, &ops);
        }
        for &d in &[RAX, R8, R13] {
            for &s in &[RCX, R11, RBP] {
                let mut ops = X86InstOperands::rr(d, s);
                ops.cc = Some(cc);
                check(X86Opcode::Cmovcc, &ops);
            }
        }
        for &d in &[EAX, R8D] {
            let mut ops = X86InstOperands::rr(d, ECX);
            ops.cc = Some(cc);
            check(X86Opcode::Cmovcc32, &ops);
        }
    }

    // XCHG / CMPXCHG / MFENCE / UD2 / multi-byte NOP padding.
    for &d in &[RAX, RCX, R8] {
        for &s in &[RDX, R11] {
            check(X86Opcode::Xchg, &X86InstOperands::rr(d, s));
            check(X86Opcode::Cmpxchg, &X86InstOperands::rr(d, s));
        }
    }
    check(X86Opcode::Mfence, &X86InstOperands::none());
    check(X86Opcode::Ud2, &X86InstOperands::none());
    for size in 1..=15 {
        let mut ops = X86InstOperands::none();
        ops.imm = size;
        check(X86Opcode::NopMulti, &ops);
    }

    // IMUL r, r, imm.
    for &d in &[RAX, R8] {
        for &s in &[RCX, R13] {
            for &imm in &[1i64, 127, 128, -1, 0x1234] {
                check(X86Opcode::ImulRRI, &X86InstOperands::rri(d, s, imm));
            }
        }
    }

    assert!(
        fails.is_empty(),
        "decode-check disagreed with the encoder on {} of {count} instances:\n{}",
        fails.len(),
        fails.join("\n")
    );
    eprintln!("decode_check_corpus_replay: {count} instances, 0 disagreements");
    assert!(count > 2000, "corpus too small ({count})");
}

/// The RIP-relative + branch fixup-hole families: hole placement is checked, the
/// sentinel value is not.
#[test]
fn decode_check_fixup_holes() {
    // Jcc rel32: 0F 8x + rel32 (6 bytes) -> hole at offset 2, width 4.
    let mut jcc = X86InstOperands::none();
    jcc.cc = Some(X86CondCode::E);
    jcc.disp = 0;
    let bytes = encode(X86Opcode::Jcc, &jcc).unwrap();
    let hole = FixupHole {
        offset_in_inst: bytes.len() - 4,
        width: 4,
        kind: FixupHoleKind::Branch,
    };
    let intent = X86IntentInst {
        opcode: X86Opcode::Jcc,
        ops: jcc,
    };
    check_one_for_test(&intent, &bytes, Some(&hole)).expect("Jcc hole should pass");

    // A WRONG hole offset must be rejected.
    let bad_hole = FixupHole {
        offset_in_inst: 0,
        width: 4,
        kind: FixupHoleKind::Branch,
    };
    assert!(
        check_one_for_test(&intent, &bytes, Some(&bad_hole)).is_err(),
        "a mis-placed branch hole must fail closed"
    );

    // LEA rip-relative (LeaRip): REX.W 8D /05 disp32 -> disp hole checked.
    let mut lea = X86InstOperands::none();
    lea.dst = Some(RAX);
    lea.disp = 0;
    let bytes = encode(X86Opcode::LeaRip, &lea).unwrap();
    let hole = FixupHole {
        offset_in_inst: bytes.len() - 4,
        width: 4,
        kind: FixupHoleKind::GlobalRef,
    };
    let intent = X86IntentInst {
        opcode: X86Opcode::LeaRip,
        ops: lea,
    };
    check_one_for_test(&intent, &bytes, Some(&hole)).expect("LeaRip hole should pass");
}

#[test]
fn decode_check_positive_faithful_encoding_passes() {
    // mov rax, rcx  ->  48 89 c8
    let ops = X86InstOperands::rr(RAX, RCX);
    let bytes = encode(X86Opcode::MovRR, &ops).unwrap();
    assert_eq!(bytes, vec![0x48, 0x89, 0xC8]);
    let intent = X86IntentInst {
        opcode: X86Opcode::MovRR,
        ops,
    };
    assert!(matches!(
        check_one_for_test(&intent, &bytes, None),
        Ok(true)
    ));
}

#[test]
fn decode_check_refutation_wrong_modrm_register() {
    // Faithful: mov rax, rcx = 48 89 C8 (ModR/M C8: reg=RCX(1), rm=RAX(0)).
    let ops = X86InstOperands::rr(RAX, RCX);
    let mut bytes = encode(X86Opcode::MovRR, &ops).unwrap();
    let intent = X86IntentInst {
        opcode: X86Opcode::MovRR,
        ops,
    };
    // Sanity: faithful bytes pass.
    check_one_for_test(&intent, &bytes, None).expect("faithful mov passes");

    // Corrupt the ModR/M byte so the destination register becomes RDX (rm=2):
    // C8 (11 001 000) -> CA (11 001 010). Now the bytes decode to
    // `mov rdx, rcx`, disagreeing with the intended `mov rax, rcx`.
    assert_eq!(bytes[2], 0xC8);
    bytes[2] = 0xCA;
    let err = check_one_for_test(&intent, &bytes, None)
        .expect_err("a corrupted ModR/M register MUST fail closed");
    assert!(
        err.contains("operand") || err.contains("Reg"),
        "unexpected error text: {err}"
    );
}

#[test]
fn decode_check_refutation_wrong_immediate() {
    // add rax, 0x11223344  ->  48 05? No: ALU/RI uses 81 /0. Force the imm32
    // form with a value that does not fit imm8.
    let ops = X86InstOperands::ri(RAX, 0x1122_3344);
    let mut bytes = encode(X86Opcode::AddRI, &ops).unwrap();
    let intent = X86IntentInst {
        opcode: X86Opcode::AddRI,
        ops,
    };
    check_one_for_test(&intent, &bytes, None).expect("faithful add r,imm32 passes");

    // Flip the least-significant immediate byte (last byte of the encoding).
    let last = bytes.len() - 1;
    bytes[last] ^= 0xFF;
    let err = check_one_for_test(&intent, &bytes, None)
        .expect_err("a corrupted immediate MUST fail closed");
    assert!(
        err.contains("Imm") || err.contains("operand"),
        "unexpected: {err}"
    );
}

#[test]
fn decode_check_refutation_wrong_opcode_byte() {
    // sub rax, rcx = 48 29 C8. Corrupt the opcode 29 (SUB) -> 01 (ADD): the
    // decoded mnemonic disagrees with the intended SUB.
    let ops = X86InstOperands::rr(RAX, RCX);
    let mut bytes = encode(X86Opcode::SubRR, &ops).unwrap();
    assert_eq!(bytes[1], 0x29);
    bytes[1] = 0x01;
    let intent = X86IntentInst {
        opcode: X86Opcode::SubRR,
        ops,
    };
    let err =
        check_one_for_test(&intent, &bytes, None).expect_err("a corrupted opcode MUST fail closed");
    assert!(err.contains("mnemonic"), "unexpected: {err}");
}

#[test]
fn decode_check_refutation_nop_wrong_modrm_extension() {
    let mut ops = X86InstOperands::none();
    ops.imm = 3;
    let intent = X86IntentInst {
        opcode: X86Opcode::NopMulti,
        ops,
    };

    // 0F 1F /0 is NOP. Changing the ModR/M extension to /1 must not be
    // accepted merely because it shares the 0F 1F opcode bytes.
    let err = check_one_for_test(&intent, &[0x0F, 0x1F, 0xC8], None)
        .expect_err("a non-/0 0F 1F encoding MUST fail closed");
    assert!(err.contains("non-canonical"), "unexpected: {err}");
}

#[test]
fn decode_check_refutation_nop_prefix_mutations() {
    let reject = |size, bytes: &[u8], mutation: &str| {
        let mut ops = X86InstOperands::none();
        ops.imm = size;
        let intent = X86IntentInst {
            opcode: X86Opcode::NopMulti,
            ops,
        };
        let err = check_one_for_test(&intent, bytes, None)
            .expect_err(&format!("{mutation} NOP mutation MUST fail closed"));
        assert!(err.contains("non-canonical"), "{mutation}: {err}");
    };

    // 41 90 is XCHG RAX,R8, F3 90 is PAUSE, and F0 90 is invalid. None is
    // interchangeable with the canonical two-byte 66 90 padding sequence.
    reject(2, &[0x41, 0x90], "REX.B");
    reject(2, &[0xF3, 0x90], "REP");
    reject(2, &[0xF0, 0x90], "LOCK");

    // Prefix mutations of the ModR/M form are rejected just as strictly.
    reject(4, &[0xF3, 0x0F, 0x1F, 0x00], "REP 0F1F");
    reject(4, &[0xF0, 0x0F, 0x1F, 0x00], "LOCK 0F1F");
}
