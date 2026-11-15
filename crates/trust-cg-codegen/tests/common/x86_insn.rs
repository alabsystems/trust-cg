#![allow(dead_code)]
// x86_insn.rs — an instruction-boundary walk over emitted x86-64 machine code,
// so "this stream is legacy-encoded (no VEX)" can be asserted structurally.
//
// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0
//
// A VEX prefix is a 0xC4 or 0xC5 byte AT AN INSTRUCTION BOUNDARY: in 64-bit
// mode those two opcodes are unconditionally VEX (the LES/LDS they encoded in
// 32-bit mode do not exist), while the same byte values are ordinary ModR/M,
// SIB, displacement or immediate bytes inside other instructions —
// `66 0F 6F C4` is `movdqa %xmm4,%xmm0`, `66 0F 6F C5` is `movdqa %xmm5,%xmm0`
// and `48 83 C4 08` is `addq $0x8,%rsp`. A raw byte scan therefore cannot tell
// a VEX prefix from a register operand; only an instruction-length walk can.
//
// This walker implements the Intel SDM Volume 2 byte layout for 64-bit mode:
// legacy prefixes, REX, the one-byte, 0F, 0F38 and 0F3A opcode maps, ModR/M +
// SIB + displacement, and the immediate width each opcode carries. It FAILS
// CLOSED: an opcode outside its tables is an error, never a guessed length, so
// a new instruction shape cannot be walked over silently — the assertion that
// uses it reports the unknown byte and the test fails until the table is
// extended and re-anchored.
//
// EVIDENCE LANE. This is a test-side structural decoder, not a proof, and its
// tables are anchored the way the encoder's decode-check gate is anchored: to
// an external disassembler. Whenever GNU objdump is on PATH (every Linux floor
// host), `assert_legacy_encoded` cross-checks every boundary it computed
// against `objdump -b binary -m i386:x86-64 -D`, so a table error in this file
// surfaces as a boundary disagreement rather than as a wrong verdict. Where no
// GNU objdump exists the walk still runs, unanchored, and says so once.

use std::process::Command;
use std::sync::OnceLock;

use super::disasm::disasm_scratch_dir;

/// One walked instruction: its start offset and length, and whether its
/// opcode byte was a VEX prefix. For a VEX instruction `len` covers only the
/// prefix byte and the walk stops there — a VEX stream is what callers refuse,
/// so nothing past the prefix is ever claimed.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct WalkedInsn {
    pub start: usize,
    pub len: usize,
    pub vex: bool,
}

/// Walk `code` from offset 0 to its end, stopping at (and including) the
/// first VEX-prefixed instruction. `Err` names the offset and why the walk
/// could not continue.
pub fn walk(code: &[u8]) -> Result<Vec<WalkedInsn>, String> {
    let mut out = Vec::new();
    let mut at = 0usize;
    while at < code.len() {
        let (len, vex) = instruction_length(&code[at..])
            .map_err(|reason| format!("offset {at:#x}: {reason}"))?;
        out.push(WalkedInsn {
            start: at,
            len,
            vex,
        });
        if vex {
            break;
        }
        at += len;
    }
    Ok(out)
}

/// Offset of the first VEX-prefixed instruction in `code`, or `None` when the
/// whole stream walks as legacy encodings. `Err` when a boundary could not be
/// established, which is never a "no VEX" verdict.
pub fn first_vex_instruction(code: &[u8]) -> Result<Option<usize>, String> {
    Ok(walk(code)?
        .iter()
        .find(|insn| insn.vex)
        .map(|insn| insn.start))
}

/// Panic unless `code` walks end to end as legacy-encoded instructions, and,
/// where GNU objdump is present, unless every boundary agrees with it.
pub fn assert_legacy_encoded(code: &[u8], label: &str) {
    let insns = walk(code).unwrap_or_else(|reason| {
        panic!(
            "{label}: the instruction-boundary walk cannot establish that this stream is \
             legacy-encoded — {reason}; code={code:02X?}"
        )
    });
    if let Some(vex) = insns.iter().find(|insn| insn.vex) {
        panic!(
            "{label}: a VEX prefix ({:#04x}) begins the instruction at offset {:#x}, so the stream \
             is not legacy-encoded: code={code:02X?}",
            code[vex.start], vex.start
        );
    }
    let starts: Vec<usize> = insns.iter().map(|insn| insn.start).collect();
    if let Some(anchor) = gnu_objdump_boundaries(code) {
        assert_eq!(
            starts, anchor,
            "{label}: the walker's instruction boundaries disagree with GNU objdump's; its tables \
             must be corrected before its verdict counts: code={code:02X?}"
        );
    }
}

fn instruction_length(b: &[u8]) -> Result<(usize, bool), String> {
    let mut i = 0usize;
    let mut opsize16 = false;
    let mut addr32 = false;
    // Legacy prefixes (groups 1–4), any order and count.
    while let Some(&prefix) = b.get(i) {
        match prefix {
            0xF0 | 0xF2 | 0xF3 | 0x2E | 0x36 | 0x3E | 0x26 | 0x64 | 0x65 => {}
            0x66 => opsize16 = true,
            0x67 => addr32 = true,
            _ => break,
        }
        i += 1;
    }
    let mut rex_w = false;
    if let Some(&rex) = b.get(i)
        && (0x40..=0x4F).contains(&rex)
    {
        rex_w = rex & 0x08 != 0;
        i += 1;
    }
    let op = *b.get(i).ok_or("truncated before the opcode byte")?;
    i += 1;
    // The "iz" immediate: 32 bits, narrowed to 16 by `66`; REX.W keeps 32
    // (sign-extended) and overrides `66`.
    let imm_z = if rex_w || !opsize16 { 4 } else { 2 };
    let (modrm, imm): (bool, usize) = match op {
        0xC4 | 0xC5 => return Ok((1, true)),
        0x0F => return map_0f(b, i, imm_z),
        // Rows 0..3: ALU `r/m,r` | `r,r/m` | `AL,ib` | `rAX,iz`; the x6/x7
        // columns (push/pop seg, BCD adjusts) do not exist in 64-bit mode.
        0x00..=0x3F => match op & 7 {
            0..=3 => (true, 0),
            4 => (false, 1),
            5 => (false, imm_z),
            _ => return Err(format!("opcode {op:#04x} is not valid in 64-bit mode")),
        },
        0x40..=0x4F => return Err("a second REX prefix; hardware ignores the first".into()),
        0x50..=0x5F => (false, 0),
        0x63 => (true, 0),
        0x68 => (false, imm_z),
        0x69 => (true, imm_z),
        0x6A => (false, 1),
        0x6B => (true, 1),
        0x6C..=0x6F => (false, 0),
        0x70..=0x7F => (false, 1),
        0x80 | 0x83 => (true, 1),
        0x81 => (true, imm_z),
        0x84..=0x8F => (true, 0),
        0x90..=0x99 | 0x9B..=0x9F => (false, 0),
        0xA0..=0xA3 => (false, if addr32 { 4 } else { 8 }),
        0xA4..=0xA7 => (false, 0),
        0xA8 => (false, 1),
        0xA9 => (false, imm_z),
        0xAA..=0xAF => (false, 0),
        0xB0..=0xB7 => (false, 1),
        0xB8..=0xBF => (
            false,
            if rex_w {
                8
            } else if opsize16 {
                2
            } else {
                4
            },
        ),
        0xC0 | 0xC1 | 0xC6 => (true, 1),
        0xC2 | 0xCA => (false, 2),
        0xC3 | 0xC9 | 0xCB | 0xCC | 0xCF => (false, 0),
        0xC7 => (true, imm_z),
        0xC8 => (false, 3),
        0xCD => (false, 1),
        0xD0..=0xD3 => (true, 0),
        0xD7 => (false, 0),
        0xD8..=0xDF => (true, 0),
        0xE0..=0xE7 => (false, 1),
        0xE8 | 0xE9 => (false, 4),
        0xEB => (false, 1),
        0xEC..=0xEF => (false, 0),
        0xF1 | 0xF4 | 0xF5 | 0xF8..=0xFD => (false, 0),
        // Group 3: only TEST (/0, /1) carries an immediate.
        0xF6 | 0xF7 => {
            let modrm = *b.get(i).ok_or("truncated before ModR/M")?;
            let is_test = (modrm >> 3) & 7 <= 1;
            let imm = match (is_test, op) {
                (false, _) => 0,
                (true, 0xF6) => 1,
                (true, _) => imm_z,
            };
            (true, imm)
        }
        0xFE | 0xFF => (true, 0),
        _ => {
            return Err(format!(
                "opcode {op:#04x} is not in the walker's one-byte map"
            ));
        }
    };
    finish(b, i, modrm, imm)
}

fn map_0f(b: &[u8], mut i: usize, imm_z: usize) -> Result<(usize, bool), String> {
    let _ = imm_z;
    let op = *b.get(i).ok_or("truncated after the 0F escape")?;
    i += 1;
    let (modrm, imm): (bool, usize) = match op {
        // Three-byte maps: every 0F38 opcode is ModR/M-only; every 0F3A
        // opcode carries ModR/M plus an imm8.
        0x38 | 0x3A => {
            b.get(i).ok_or("truncated after the 0F38/0F3A escape")?;
            i += 1;
            (true, usize::from(op == 0x3A))
        }
        0x00..=0x03
        | 0x0D
        | 0x10..=0x23
        | 0x28..=0x2F
        | 0x40..=0x6F
        | 0x74..=0x76
        | 0x7C..=0x7F
        | 0x90..=0x9F
        | 0xA3
        | 0xA5
        | 0xAB
        | 0xAD..=0xB1
        | 0xB2..=0xB9
        | 0xBB..=0xC1
        | 0xC3
        | 0xC7
        | 0xD0..=0xFF => (true, 0),
        0x05..=0x09
        | 0x0B
        | 0x0E
        | 0x30..=0x37
        | 0x77
        | 0xA0..=0xA2
        | 0xA8..=0xAA
        | 0xC8..=0xCF => (false, 0),
        0x70..=0x73 | 0xA4 | 0xAC | 0xBA | 0xC2 | 0xC4..=0xC6 => (true, 1),
        0x80..=0x8F => (false, 4),
        _ => return Err(format!("opcode 0F {op:02X} is not in the walker's 0F map")),
    };
    finish(b, i, modrm, imm)
}

fn finish(b: &[u8], mut i: usize, modrm: bool, imm: usize) -> Result<(usize, bool), String> {
    if modrm {
        let modrm = *b.get(i).ok_or("truncated before ModR/M")?;
        i += 1;
        let mode = modrm >> 6;
        let rm = modrm & 7;
        if mode != 3 {
            let mut disp = match mode {
                0 => 0,
                1 => 1,
                _ => 4,
            };
            if rm == 4 {
                let sib = *b.get(i).ok_or("truncated before SIB")?;
                i += 1;
                if mode == 0 && sib & 7 == 5 {
                    disp = 4;
                }
            } else if mode == 0 && rm == 5 {
                // RIP-relative.
                disp = 4;
            }
            i += disp;
        }
    }
    i += imm;
    if i > b.len() {
        return Err(format!(
            "the instruction runs {} byte(s) past the end of the stream",
            i - b.len()
        ));
    }
    Ok((i, false))
}

/// Instruction start offsets according to GNU objdump's decode of `code` as a
/// raw 64-bit binary, or `None` when no GNU objdump is on PATH (LLVM objdump
/// has no raw-binary input mode).
fn gnu_objdump_boundaries(code: &[u8]) -> Option<Vec<usize>> {
    static GNU_PRESENT: OnceLock<bool> = OnceLock::new();
    let present = *GNU_PRESENT.get_or_init(|| {
        Command::new("objdump")
            .arg("--version")
            .output()
            .map(|o| o.status.success() && String::from_utf8_lossy(&o.stdout).contains("GNU"))
            .unwrap_or(false)
    });
    if !present {
        static ANNOUNCED: OnceLock<()> = OnceLock::new();
        ANNOUNCED.get_or_init(|| {
            eprintln!(
                "[x86_insn] no GNU objdump on PATH: instruction boundaries are walked but not \
                 cross-checked against an external disassembler on this host"
            );
        });
        return None;
    }
    let dir = disasm_scratch_dir();
    std::fs::create_dir_all(&dir).expect("create objdump scratch dir");
    let path = dir.join("code.bin");
    std::fs::write(&path, code).expect("write raw code for objdump");
    let output = Command::new("objdump")
        .args([
            "-b",
            "binary",
            "-m",
            "i386:x86-64",
            "-D",
            "--no-show-raw-insn",
        ])
        .arg(&path)
        .output()
        .expect("GNU objdump must spawn on raw code");
    let _ = std::fs::remove_dir_all(&dir);
    assert!(
        output.status.success(),
        "GNU objdump refused the raw code stream: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    let text = String::from_utf8_lossy(&output.stdout);
    let mut starts = Vec::new();
    for line in text.lines() {
        let Some((addr, rest)) = line.split_once(':') else {
            continue;
        };
        let addr = addr.trim();
        if addr.is_empty() || !addr.chars().all(|c| c.is_ascii_hexdigit()) || rest.trim().is_empty()
        {
            continue;
        }
        if let Ok(offset) = usize::from_str_radix(addr, 16) {
            starts.push(offset);
        }
    }
    Some(starts)
}
