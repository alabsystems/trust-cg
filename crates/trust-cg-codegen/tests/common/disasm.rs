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

/// The container format of the bytes a caller will hand to
/// [`disassemble_x86_text`].
///
/// Capability is a property of the FORMAT, not of the objdump's vendor, and not
/// of the host OS: `e2e_x86_64_callee_saved` decodes a host-default object AND a
/// `x86_64-pc-windows-msvc` one, and the guard-kernel gates decode a
/// `x86_64-apple-darwin` object even when running on Linux.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ObjFormat {
    /// ELF, as the host default emits on Linux.
    Elf,
    /// PE/COFF, as `x86_64-pc-windows-msvc` emits.
    Coff,
    /// Mach-O, as `x86_64-apple-darwin` emits.
    MachO,
}

impl ObjFormat {
    /// The format the HOST default target emits, for a caller that compiles for
    /// the host triple rather than a named one.
    pub const fn native() -> Self {
        if cfg!(target_os = "macos") {
            ObjFormat::MachO
        } else if cfg!(target_os = "windows") {
            ObjFormat::Coff
        } else {
            ObjFormat::Elf
        }
    }

    /// The BFD target names GNU binutils lists in `objdump --info` for this
    /// format on x86-64. Any one of them is enough.
    fn gnu_bfd_targets(self) -> &'static [&'static str] {
        match self {
            ObjFormat::Elf => &["elf64-x86-64"],
            ObjFormat::Coff => &["pe-x86-64", "pei-x86-64"],
            ObjFormat::MachO => &["mach-o-x86-64"],
        }
    }
}

/// True if some objdump on this host can decode `format`. When false, callers
/// fall back to the raw-byte oracle.
pub fn has_objdump_for(format: ObjFormat) -> bool {
    disasm_binary_for(format).is_some()
}

/// True only if EVERY format in `formats` is decodable, for a caller whose
/// obligation reads several subjects and must not run on a partial set.
pub fn has_objdump_for_all(formats: &[ObjFormat]) -> bool {
    formats.iter().copied().all(has_objdump_for)
}

/// First candidate that can decode `format`.
///
/// An LLVM-family objdump (LLVM's or Apple's; both print "LLVM" in `--version`)
/// decodes every format this corpus emits. GNU binutils is built with a CHOSEN
/// set of BFD targets, so it is ASKED rather than assumed: `objdump --info`
/// lists them one per line. On this project's Linux hosts that set contains
/// `elf64-x86-64` and `pe-x86-64` but NO Mach-O, which is exactly why a Mach-O
/// subject must keep falling back to the raw-byte oracle there.
///
/// Gating on the VENDOR instead (accept only "LLVM") made every (E2)
/// INDEPENDENT-DECODE control skip on a GNU-only host, which the Linux x86-64
/// floor correctly recorded as a vacuous pass. Gating on the HOST OS instead is
/// also wrong, and was measured to be: it let the Mach-O-decoding guard-kernel
/// gates enter their objdump branch on Linux, where the decode cannot work.
fn disasm_binary_for(format: ObjFormat) -> Option<&'static str> {
    DISASM_CANDIDATES
        .iter()
        .copied()
        .find(|bin| objdump_handles(bin, format))
}

fn objdump_handles(bin: &str, format: ObjFormat) -> bool {
    if is_llvm_objdump(bin) {
        return true;
    }
    if !is_gnu_objdump(bin) {
        return false;
    }
    let Ok(out) = Command::new(bin).arg("--info").output() else {
        return false;
    };
    if !out.status.success() {
        return false;
    }
    let text = String::from_utf8_lossy(&out.stdout);
    format
        .gnu_bfd_targets()
        .iter()
        .any(|target| text.lines().any(|line| line.trim() == *target))
}

/// Whether ANY candidate on this host is an LLVM-family objdump. Lets a test say
/// "this host is GNU-only" without duplicating the candidate list.
pub fn disasm_has_llvm_family_objdump() -> bool {
    DISASM_CANDIDATES.iter().any(|bin| is_llvm_objdump(bin))
}

/// True if `bin` runs and identifies itself as GNU binutils objdump.
fn is_gnu_objdump(bin: &str) -> bool {
    Command::new(bin)
        .arg("--version")
        .output()
        .map(|o| o.status.success() && String::from_utf8_lossy(&o.stdout).contains("GNU objdump"))
        .unwrap_or(false)
}

fn is_llvm_objdump(bin: &str) -> bool {
    Command::new(bin)
        .arg("--version")
        .output()
        .map(|o| o.status.success() && String::from_utf8_lossy(&o.stdout).contains("LLVM"))
        .unwrap_or(false)
}

/// A scratch directory that is unique per CALL, not merely per process and
/// wall-clock instant.
///
/// ⚠ This exists because of a real, measured defect. The path used to be
/// `trust_cg_disasm_<pid>_<nanos>`, and `SystemTime::now().as_nanos()` has
/// MICROSECOND resolution on macOS (every reading ends in `000`), so two test
/// threads disassembling at the same time collided on one directory roughly 1
/// call in 10: each wrote its own object to the SAME `g.o`, and whichever
/// `objdump` ran second decoded the OTHER thread's object. In
/// `e2e_x86_64_callee_saved` that surfaced as a ~11% flake in which the System V
/// lane read a Windows x64 frame (and so saw `pushq %rsi`) and the Windows x64
/// lane read a System V frame (and so saw the body reading arguments out of
/// RDI/RSI). A decode of the wrong object is not a flaky test — it is EVIDENCE
/// ABOUT THE WRONG SUBJECT.
///
/// The process-wide counter is what makes the path unique; the clock component
/// is kept only so paths from different processes never look alike.
pub fn disasm_scratch_dir() -> std::path::PathBuf {
    static SEQ: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);
    std::env::temp_dir().join(format!(
        "trust_cg_disasm_{}_{}_{}",
        std::process::id(),
        SEQ.fetch_add(1, std::sync::atomic::Ordering::Relaxed),
        std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap_or_default()
            .as_nanos()
    ))
}

/// Disassemble the `__TEXT,__text` section of an emitted x86-64 Mach-O object via
/// `objdump -d` and return the decoded instruction stream in offset order.
///
/// Returns `None` if `objdump` is unavailable or fails to decode (the object is
/// never executed — this is a pure decode on an arm64 host). Parsing is tolerant:
/// only lines of the shape `   <hex>: \t<mnemonic>\t<operands>` are kept; section
/// headers, the symbol line, and blank lines are skipped.
pub fn disassemble_x86_text(obj: &[u8]) -> Option<Vec<DisasmInsn>> {
    let dir = disasm_scratch_dir();
    std::fs::create_dir_all(&dir).ok()?;
    let path = dir.join("g.o");
    std::fs::write(&path, obj).ok()?;
    // PROVENANCE. Decoding a file that is not the object we were handed would
    // attribute another subject's frame to this one, so the identity of the
    // bytes about to be decoded is CHECKED rather than assumed.
    let readback = std::fs::read(&path).ok()?;
    assert!(
        readback == obj,
        "disassemble_x86_text: {path:?} does not contain the object it was given \
         ({} bytes written, {} bytes read back) — the decode would describe the WRONG subject",
        obj.len(),
        readback.len(),
    );

    // Try every candidate: a binary can exist yet be unable to decode this
    // container (GNU objdump vs Mach-O), so capability is decided by the
    // decode itself — success status AND at least one parsed instruction.
    let mut parsed: Option<Vec<DisasmInsn>> = None;
    for bin in DISASM_CANDIDATES {
        let mut command = Command::new(bin);
        command.args(["-d", "--no-show-raw-insn"]);
        // `-M suffix` is what makes GNU objdump print the AT&T mnemonic
        // suffixes LLVM's objdump prints unconditionally (`pushq %rbp`, not
        // `push %rbp`). Without it a GNU-only host decodes correctly but every
        // mnemonic reads one token short, and the frame parser that requires
        // `pushq` rejects a perfectly good prologue. It goes to a non-LLVM
        // objdump only: Apple's LLVM objdump (LLVM 21) refuses the whole
        // decode with "Unrecognized disassembler option: suffix".
        //
        // `--print-imm-hex` pins the immediate radix for an LLVM objdump, whose
        // default differs by version: Apple LLVM 14.0.3's objdump prints `cmpq
        // $8, %rdi` (decimal is its documented default), LLVM 22.1.2's prints
        // `cmpq $0x8, %rdi`, and GNU objdump prints hex. The matchers below
        // (`has_bounds_guard`) read hex, so without the flag the older objdump
        // made a present guard look absent.
        if is_llvm_objdump(bin) {
            command.arg("--print-imm-hex");
        } else {
            command.args(["-M", "suffix"]);
        }
        let Ok(output) = command.arg(path.to_str()?).output() else {
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
        // Split the mnemonic from its operands on the first WHITESPACE RUN, not
        // on a tab: LLVM's objdump separates them with a tab, GNU's pads the
        // mnemonic with spaces (`pushq  %rbp`). Keying on the tab alone swallowed
        // the operands into the mnemonic on a GNU-only host, so every frame read
        // failed with a mnemonic that looked like `pushq  %rbp`.
        let body = rest.trim_start_matches([' ', '\t']);
        if body.is_empty() {
            continue;
        }
        let (head, tail) = match body.find([' ', '\t']) {
            Some(cut) => (&body[..cut], &body[cut..]),
            None => (body, ""),
        };
        let mut parts = [head, tail].into_iter();
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
