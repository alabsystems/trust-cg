#![allow(dead_code)]
// disasm.rs — a thin, host-portable x86-64 disassembly oracle for the guard
// link/run proofs.
//
// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0
//
// The guard-elimination link/run proofs need to reason about the ACTUAL emitted
// x86-64 instruction stream, not fragile fixed-byte windows. We get that by
// running an INDEPENDENT decoder — the LLVM `objdump` already present in the
// toolchain that links the e2e corpus — over the emitted Mach-O object and
// parsing its `objdump -d --no-show-raw-insn` output into structured
// `(mnemonic, operands)` instructions. Decoding x86-64 with the same disassembler
// a developer would use makes the assertions semantic ("there is a `cmpq $0x8`
// guard compare followed by a `jae` to a `ud2` block") rather than byte-pattern
// guesses that silently rot when register allocation shifts an encoding.
//
// This is a cross-disassembler: LLVM `objdump` decodes an x86-64 Mach-O object
// correctly on an arm64 macOS host (the object never has to be executed), so the
// oracle runs on every host. When `objdump` is unavailable the caller falls back
// to the always-present raw-byte oracle, so coverage is never lost.

use std::process::Command;

/// One decoded instruction from `objdump`: its byte offset within the section,
/// the lower-cased mnemonic (e.g. `cmpq`, `jae`, `ud2`, `leaq`), and the raw
/// operand text exactly as `objdump` printed it (AT&T syntax, e.g.
/// `$0x8, %rbx` or `(%rcx,%rbx,8), %rax`).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DisasmInsn {
    pub offset: u64,
    pub mnemonic: String,
    pub operands: String,
}

impl DisasmInsn {
    /// True when this is any conditional/unconditional branch (`j*`) whose
    /// printed target resolves to `target_offset`. `objdump` prints jump targets
    /// as an absolute hex address optionally followed by a `<sym+0x..>` comment;
    /// we parse the leading hex token.
    pub fn jumps_to(&self, target_offset: u64) -> bool {
        if !self.mnemonic.starts_with('j') {
            return false;
        }
        let tok = self.operands.split_whitespace().next().unwrap_or("");
        parse_hex(tok) == Some(target_offset)
    }
}

fn parse_hex(tok: &str) -> Option<u64> {
    let t = tok.trim();
    let t = t.strip_prefix("0x").unwrap_or(t);
    u64::from_str_radix(t, 16).ok()
}

/// Disassembler candidates, most-capable first. The emitted objects under
/// test are Mach-O (the guard proofs pin `x86_64-apple-darwin` for a stable
/// container), and only LLVM's objdump decodes Mach-O on every host: GNU
/// binutils `objdump` — the plain `objdump` on a Linux box — rejects Mach-O
/// with "file format not recognized". On macOS, plain `objdump` IS LLVM
/// objdump, so the fallback candidate keeps the historical behavior there.
const DISASM_CANDIDATES: &[&str] = &["llvm-objdump", "objdump"];

/// True if a disassembler capable of the e2e link corpus is available. When
/// false, callers fall back to the raw-byte oracle.
pub fn has_objdump() -> bool {
    disasm_binary().is_some()
}

/// First candidate that is an LLVM-family objdump. The `--version` banner is
/// the capability probe: LLVM and Apple objdump both print "LLVM" (and both
/// decode Mach-O); GNU binutils prints "GNU objdump" and cannot, so its mere
/// presence must not make `has_objdump()` promise a decode the raw-byte floor
/// would otherwise cover.
fn disasm_binary() -> Option<&'static str> {
    DISASM_CANDIDATES.iter().copied().find(|bin| {
        Command::new(bin)
            .arg("--version")
            .output()
            .map(|o| o.status.success() && String::from_utf8_lossy(&o.stdout).contains("LLVM"))
            .unwrap_or(false)
    })
}

/// Disassemble the `__TEXT,__text` section of an emitted x86-64 Mach-O object via
/// `objdump -d` and return the decoded instruction stream in offset order.
///
/// Returns `None` if `objdump` is unavailable or fails to decode (the object is
/// never executed — this is a pure decode on an arm64 host). Parsing is tolerant:
/// only lines of the shape `   <hex>: \t<mnemonic>\t<operands>` are kept; section
/// headers, the symbol line, and blank lines are skipped.
pub fn disassemble_x86_text(obj: &[u8]) -> Option<Vec<DisasmInsn>> {
    let dir = std::env::temp_dir().join(format!(
        "trust_cg_disasm_{}_{}",
        std::process::id(),
        std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap_or_default()
            .as_nanos()
    ));
    std::fs::create_dir_all(&dir).ok()?;
    let path = dir.join("g.o");
    std::fs::write(&path, obj).ok()?;

    // Try every candidate: a binary can exist yet be unable to decode this
    // container (GNU objdump vs Mach-O), so capability is decided by the
    // decode itself — success status AND at least one parsed instruction.
    let mut parsed: Option<Vec<DisasmInsn>> = None;
    for bin in DISASM_CANDIDATES {
        let Ok(output) = Command::new(bin)
            .args(["-d", "--no-show-raw-insn", path.to_str()?])
            .output()
        else {
            continue;
        };
        if !output.status.success() {
            continue;
        }
        let text = String::from_utf8_lossy(&output.stdout);
        let insns = parse_objdump(&text);
        if !insns.is_empty() {
            parsed = Some(insns);
            break;
        }
    }
    let _ = std::fs::remove_dir_all(&dir);
    parsed
}

/// Parse `objdump -d --no-show-raw-insn` output into structured instructions.
/// Lines look like:
///
/// ```text
///        0:      \tpushq\t%rbp
///       52:      \tcmpq\t$0x8, %rbx
///       56:      \tjae\t0x6d <_probe+0x6d>
///       6d:      \tud2
/// ```
///
/// The offset is the leading token before `:`; the rest is tab-delimited
/// `<mnemonic>` then (optionally) `<operands>`.
fn parse_objdump(text: &str) -> Vec<DisasmInsn> {
    let mut out = Vec::new();
    for line in text.lines() {
        // An instruction line must contain a `:` separating the offset from the
        // (tab-indented) mnemonic. Skip headers / symbol lines / blanks.
        let Some((addr_part, rest)) = line.split_once(':') else {
            continue;
        };
        let addr_tok = addr_part.trim();
        if addr_tok.is_empty() || !addr_tok.chars().all(|c| c.is_ascii_hexdigit()) {
            continue;
        }
        let Some(offset) = u64::from_str_radix(addr_tok, 16).ok() else {
            continue;
        };
        // The mnemonic/operands are tab-delimited after some leading whitespace.
        let body = rest.trim_start_matches([' ', '\t']);
        if body.is_empty() {
            continue;
        }
        let mut parts = body.splitn(2, '\t');
        let mnemonic = parts.next().unwrap_or("").trim().to_ascii_lowercase();
        if mnemonic.is_empty() {
            continue;
        }
        let operands = parts.next().unwrap_or("").trim().to_string();
        out.push(DisasmInsn {
            offset,
            mnemonic,
            operands,
        });
    }
    out
}

/// True if any instruction is a `ud2` trap.
pub fn has_ud2(insns: &[DisasmInsn]) -> bool {
    insns.iter().any(|i| i.mnemonic == "ud2")
}

/// True if the stream contains a complete bounds-check GUARD against `bound`:
/// a `cmp`-family compare whose immediate operand is `bound`, immediately
/// followed by a `j*` conditional branch whose target is the offset of a `ud2`
/// instruction. This is the exact `cmpq $bound, idx ; jae trap ; trap: ud2`
/// shape `expand_x86_bounds_check_carriers` emits, identified structurally so it
/// is robust to which registers regalloc picked.
pub fn has_bounds_guard(insns: &[DisasmInsn], bound: u64) -> bool {
    let imm = format!("$0x{bound:x}");
    let ud2_offsets: Vec<u64> = insns
        .iter()
        .filter(|i| i.mnemonic == "ud2")
        .map(|i| i.offset)
        .collect();
    if ud2_offsets.is_empty() {
        return false;
    }
    for win in insns.windows(2) {
        let cmp = &win[0];
        let jcc = &win[1];
        let is_cmp = cmp.mnemonic.starts_with("cmp")
            && cmp
                .operands
                .split(',')
                .next()
                .map(|first| first.trim() == imm)
                .unwrap_or(false);
        if !is_cmp {
            continue;
        }
        if !jcc.mnemonic.starts_with('j') {
            continue;
        }
        if ud2_offsets.iter().any(|&u| jcc.jumps_to(u)) {
            return true;
        }
    }
    false
}

/// True if the stream contains the result-computing indexed-load access: a scaled
/// `lea` of the form `(base, index, 8), reg` (objdump prints the `,8` scale)
/// followed by a `mov` that dereferences a plain register address. We require
/// both the scaled address computation and the load to be present. This is what
/// materializes `arr[idx]` and must survive guard elimination untouched.
pub fn has_indexed_load_access(insns: &[DisasmInsn]) -> bool {
    let scaled_lea = insns.iter().any(|i| {
        i.mnemonic.starts_with("lea")
            // a SIB form with index*scale-8 and a base+index pair: `(%base,%index,8)`
            && i.operands.contains(",8)")
            && i.operands.matches('%').count() >= 2
    });
    scaled_lea && insns.iter().any(is_plain_mem_load)
}

/// `movq (%reg), %reg` — a plain (non-SIB) memory load: the source operand is a
/// single-register memory reference `(%...)` with no scale/index commas inside the
/// parentheses.
fn is_plain_mem_load(i: &DisasmInsn) -> bool {
    if !i.mnemonic.starts_with("mov") {
        return false;
    }
    let ops = i.operands.trim();
    let Some(open) = ops.find('(') else {
        return false;
    };
    let Some(close) = ops.find(')') else {
        return false;
    };
    if close < open {
        return false;
    }
    let inside = &ops[open + 1..close];
    // plain base-only memory ref at the start of the operand list (a load):
    // `(%reg)` with no `,` => no index/scale.
    ops[..open].trim().is_empty() && inside.starts_with('%') && !inside.contains(',')
}
