// trust-cg-codegen — ENC-2: external-disassembler differential lane (x86_64)
//
// Author: Andrew Yates | Copyright 2026 Andrew Yates | License: Apache-2.0
//
// WHAT THIS IS
// ------------
// An INTERIM, INDEPENDENT detection lane over the trusted x86_64 byte encoder
// (trust-cg-codegen/src/x86_64/encode.rs, golden-tested but otherwise trusted):
// for every instruction family the encoder can emit, this suite
//
//   1. generates instruction instances (registers incl. r8-r15 / REX edges,
//      spl/bpl/sil/dil byte regs, immediate boundary widths, SIB
//      scale/index/disp combinations, RIP-relative forms),
//   2. encodes them with the REAL encoder (X86Encoder::encode_instruction),
//   3. packs the bytes into a minimal ELF64 relocatable object,
//   4. disassembles that object with an EXTERNAL disassembler — the
//      llvm-objdump shipped inside the PINNED rustc toolchain
//      (nightly-2026-04-20; see PINNED_* consts below), and
//   5. structurally compares mnemonic + operands against an independently
//      derived expected rendering of the INTENDED instruction.
//
// A disagreement is P0 evidence of a misencoding (or of an intent
// mis-derivation) — the test FAILS LOUDLY and prints the intended rendering,
// the objdump rendering, and the raw bytes. Per the soundness doctrine this
// lane is DETECTION, not proof: it feeds (and later validates) the ENC-3
// reference decoder; it never replaces it.
//
// PINNING
// -------
// The disassembler is pinned to the nightly-2026-04-20 toolchain's own
// llvm-objdump (the only external disassembler present on the dev hosts —
// llvm-mc is NOT shipped; /usr/bin/otool is not pinned). Exact recorded
// version at pin time (x86_64-apple-darwin host):
//
//     LLVM version 22.1.2-rust-1.97.0-nightly
//
// If the toolchain-resolved objdump reports a DIFFERENT version the test
// fails (the pin was violated). `TCG_LLVM_OBJDUMP=<path>` overrides the
// resolution for externally provisioned disassemblers (warn-only on version
// drift in that case). If no objdump can be found at all the suite SKIPS
// GRACEFULLY with an eprintln (a missing external tool must not turn this
// detection lane into a false red on minimal hosts).
//
// AARCH64 ANALOGUE (note for the AS lane / ENC-5)
// -----------------------------------------------
// The same llvm-objdump binary disassembles aarch64 (`--triple
// aarch64-apple-darwin` / an EM_AARCH64 ELF). The aarch64 twin of this lane
// should drive crates/trust-cg-codegen/src/aarch64/encode.rs + the
// encoding_{fp,mem,neon}.rs families through the identical
// object-write/disassemble/compare skeleton below (the ELF container and the
// parser are ISA-agnostic; only the case generators and the expected-rendering
// tables are per-arch).
//
// SCOPE
// -----
// Covered here (per-family tests): alu, mov, branch, shift, mul, div, lea,
// setcc, cmov, pushpop + bonus bitmanip and sync (xchg/cmpxchg/mfence/ud2).
// Every X86Opcode variant is classified in `lane_status` with NO wildcard
// arm, so ADDING a new opcode without a lane entry breaks this test's build
// (mirrors the emitted-opcode-inventory fail-closed pattern). SSE scalar/
// packed families are explicitly skip-listed as the follow-up extension.

use std::collections::HashMap;
use std::path::{Path, PathBuf};
use std::process::Command;

use trust_cg_codegen::x86_64::{X86Encoder, X86InstOperands};
use trust_cg_ir::x86_64_ops::{X86CondCode, X86Opcode};
use trust_cg_ir::x86_64_regs::{
    AL, BL, CL, DIL, DL, EAX, EBP, ECX, EDI, EDX, ESI, R8, R8B, R8D, R9, R10, R11, R12, R13, R13D,
    R14, R15, R15B, R15D, RAX, RBP, RBX, RCX, RDI, RDX, RSI, RSP, SIL, SPL, X86PReg,
};

// ---------------------------------------------------------------------------
// Pinned external disassembler
// ---------------------------------------------------------------------------

const PINNED_TOOLCHAIN: &str = "nightly-2026-04-20";
/// Exact `llvm-objdump --version` "LLVM version" line content recorded when
/// this lane was pinned (2026-07-02, x86_64-apple-darwin host).
const PINNED_OBJDUMP_VERSION: &str = "22.1.2-rust-1.97.0-nightly";

struct Disasm {
    path: PathBuf,
    version_line: String,
    from_pinned_toolchain: bool,
}

/// Resolve the pinned llvm-objdump. Order:
///   1. TCG_LLVM_OBJDUMP env override (externally provisioned; warn-only pin).
///   2. `rustup which --toolchain nightly-2026-04-20 rustc` -> sibling
///      lib/rustlib/<triple>/bin/llvm-objdump.
///   3. Direct scan of ~/.rustup/toolchains/nightly-2026-04-20-*/....
fn find_pinned_objdump() -> Option<Disasm> {
    if let Ok(p) = std::env::var("TCG_LLVM_OBJDUMP") {
        let p = PathBuf::from(p);
        if p.is_file() {
            let v = objdump_version_line(&p)?;
            return Some(Disasm {
                path: p,
                version_line: v,
                from_pinned_toolchain: false,
            });
        }
        eprintln!("ENC-2: TCG_LLVM_OBJDUMP set but not a file; falling back to pinned toolchain");
    }

    // rustup which -> toolchain root
    let mut roots: Vec<PathBuf> = Vec::new();
    if let Ok(out) = Command::new("rustup")
        .args(["which", "--toolchain", PINNED_TOOLCHAIN, "rustc"])
        .output()
        && out.status.success()
    {
        let rustc = PathBuf::from(String::from_utf8_lossy(&out.stdout).trim().to_string());
        // <root>/bin/rustc -> <root>
        if let Some(root) = rustc.parent().and_then(Path::parent) {
            roots.push(root.to_path_buf());
        }
    }
    // Fallback: scan ~/.rustup/toolchains for the pinned toolchain dir.
    if let Some(home) = std::env::var_os("HOME") {
        let tc_dir = PathBuf::from(home).join(".rustup/toolchains");
        if let Ok(rd) = std::fs::read_dir(&tc_dir) {
            for e in rd.flatten() {
                if e.file_name()
                    .to_string_lossy()
                    .starts_with(PINNED_TOOLCHAIN)
                {
                    roots.push(e.path());
                }
            }
        }
    }
    for root in roots {
        let rustlib = root.join("lib/rustlib");
        if let Ok(rd) = std::fs::read_dir(&rustlib) {
            for e in rd.flatten() {
                let cand = e.path().join("bin/llvm-objdump");
                if cand.is_file() {
                    let v = objdump_version_line(&cand)?;
                    return Some(Disasm {
                        path: cand,
                        version_line: v,
                        from_pinned_toolchain: true,
                    });
                }
            }
        }
    }
    None
}

fn objdump_version_line(path: &Path) -> Option<String> {
    let out = Command::new(path).arg("--version").output().ok()?;
    if !out.status.success() {
        return None;
    }
    let text = String::from_utf8_lossy(&out.stdout);
    text.lines()
        .find(|l| l.contains("LLVM version"))
        .map(|l| l.trim().to_string())
}

/// Resolve objdump or skip. Returns None after printing the skip notice.
/// Enforces the version pin when resolved from the pinned toolchain.
fn objdump_or_skip(test_name: &str) -> Option<Disasm> {
    match find_pinned_objdump() {
        Some(d) => {
            if d.from_pinned_toolchain && !d.version_line.contains(PINNED_OBJDUMP_VERSION) {
                panic!(
                    "ENC-2 [{test_name}]: pinned-toolchain llvm-objdump version drift.\n  \
                     expected to contain: {PINNED_OBJDUMP_VERSION}\n  got: {}\n  path: {}\n\
                     The pin ({PINNED_TOOLCHAIN}) was violated — re-record the version \
                     deliberately or restore the toolchain.",
                    d.version_line,
                    d.path.display()
                );
            }
            if !d.from_pinned_toolchain && !d.version_line.contains(PINNED_OBJDUMP_VERSION) {
                eprintln!(
                    "ENC-2 [{test_name}]: WARNING — TCG_LLVM_OBJDUMP override reports '{}' \
                     (pinned lane was recorded against {PINNED_OBJDUMP_VERSION})",
                    d.version_line
                );
            }
            Some(d)
        }
        None => {
            eprintln!(
                "ENC-2 [{test_name}]: SKIP — llvm-objdump not found (toolchain \
                 {PINNED_TOOLCHAIN} not installed and TCG_LLVM_OBJDUMP unset). \
                 The external-disassembler differential lane did not run."
            );
            None
        }
    }
}

// ---------------------------------------------------------------------------
// Minimal ELF64 relocatable object container (x86-64), so llvm-objdump can
// disassemble raw encoder output. Hand-rolled on purpose: this lane must not
// depend on the (trusted) Mach-O writer it is meant to be independent of.
// ---------------------------------------------------------------------------

fn elf64_x86_object(text: &[u8]) -> Vec<u8> {
    fn shdr(name: u32, typ: u32, flags: u64, off: u64, size: u64, align: u64) -> Vec<u8> {
        let mut v = Vec::with_capacity(64);
        v.extend_from_slice(&name.to_le_bytes());
        v.extend_from_slice(&typ.to_le_bytes());
        v.extend_from_slice(&flags.to_le_bytes());
        v.extend_from_slice(&0u64.to_le_bytes()); // sh_addr
        v.extend_from_slice(&off.to_le_bytes());
        v.extend_from_slice(&size.to_le_bytes());
        v.extend_from_slice(&0u32.to_le_bytes()); // sh_link
        v.extend_from_slice(&0u32.to_le_bytes()); // sh_info
        v.extend_from_slice(&align.to_le_bytes());
        v.extend_from_slice(&0u64.to_le_bytes()); // sh_entsize
        v
    }

    let shstrtab: &[u8] = b"\0.text\0.shstrtab\0";
    let ehsize: usize = 64;
    let text_off = ehsize;
    let shstr_off = text_off + text.len();
    let mut shoff = shstr_off + shstrtab.len();
    shoff += (8 - (shoff % 8)) % 8;

    let mut eh = Vec::with_capacity(ehsize);
    eh.extend_from_slice(b"\x7fELF");
    eh.push(2); // ELFCLASS64
    eh.push(1); // little-endian
    eh.push(1); // EV_CURRENT
    eh.push(0); // OSABI none
    eh.push(0); // ABI version
    eh.extend_from_slice(&[0u8; 7]); // padding
    eh.extend_from_slice(&1u16.to_le_bytes()); // ET_REL
    eh.extend_from_slice(&0x3eu16.to_le_bytes()); // EM_X86_64
    eh.extend_from_slice(&1u32.to_le_bytes()); // version
    eh.extend_from_slice(&0u64.to_le_bytes()); // entry
    eh.extend_from_slice(&0u64.to_le_bytes()); // phoff
    eh.extend_from_slice(&(shoff as u64).to_le_bytes()); // shoff
    eh.extend_from_slice(&0u32.to_le_bytes()); // flags
    eh.extend_from_slice(&(ehsize as u16).to_le_bytes()); // ehsize
    eh.extend_from_slice(&0u16.to_le_bytes()); // phentsize
    eh.extend_from_slice(&0u16.to_le_bytes()); // phnum
    eh.extend_from_slice(&64u16.to_le_bytes()); // shentsize
    eh.extend_from_slice(&3u16.to_le_bytes()); // shnum
    eh.extend_from_slice(&2u16.to_le_bytes()); // shstrndx
    assert_eq!(eh.len(), ehsize);

    let mut buf = eh;
    buf.extend_from_slice(text);
    buf.extend_from_slice(shstrtab);
    while buf.len() < shoff {
        buf.push(0);
    }
    buf.extend_from_slice(&shdr(0, 0, 0, 0, 0, 0));
    buf.extend_from_slice(&shdr(1, 1, 0x6, text_off as u64, text.len() as u64, 16)); // .text AX
    buf.extend_from_slice(&shdr(7, 3, 0, shstr_off as u64, shstrtab.len() as u64, 1)); // .shstrtab
    buf
}

// ---------------------------------------------------------------------------
// objdump invocation + parsing
// ---------------------------------------------------------------------------

/// Disassembled row: (offset, byte_len, instruction text).
fn run_objdump(objdump: &Path, object: &[u8], tag: &str) -> Vec<(usize, usize, String)> {
    let dir = std::env::temp_dir().join(format!("tcg_enc2_{}", std::process::id()));
    std::fs::create_dir_all(&dir).expect("create temp dir");
    let obj_path = dir.join(format!("{tag}.o"));
    std::fs::write(&obj_path, object).expect("write object");

    let out = Command::new(objdump)
        .arg("-d")
        .arg("--x86-asm-syntax=intel")
        .arg(&obj_path)
        .output()
        .expect("spawn llvm-objdump");
    assert!(
        out.status.success(),
        "llvm-objdump failed on {}: {}",
        obj_path.display(),
        String::from_utf8_lossy(&out.stderr)
    );
    let stdout = String::from_utf8_lossy(&out.stdout);
    parse_disasm(&stdout)
}

fn parse_disasm(stdout: &str) -> Vec<(usize, usize, String)> {
    let mut rows: Vec<(usize, usize, String)> = Vec::new();
    for line in stdout.lines() {
        let Some((addr_part, rest)) = line.split_once(':') else {
            continue;
        };
        let addr = addr_part.trim();
        if addr.is_empty() || !addr.chars().all(|c| c.is_ascii_hexdigit()) {
            continue;
        }
        let Ok(offset) = usize::from_str_radix(addr, 16) else {
            continue;
        };
        // rest = "<bytes field> \t <text>"; the bytes field is hex pairs.
        let mut parts = rest.splitn(2, '\t');
        let bytes_field = parts.next().unwrap_or("");
        let text = parts.next().unwrap_or("").trim();
        let nbytes = bytes_field
            .split_whitespace()
            .filter(|t| t.len() == 2 && t.chars().all(|c| c.is_ascii_hexdigit()))
            .count();
        if nbytes == 0 {
            continue;
        }
        rows.push((offset, nbytes, text.replace('\t', " ")));
    }
    // Merge a standalone `lock` prefix row into the following instruction row
    // (llvm-objdump prints the F0 prefix as its own line).
    let mut merged: Vec<(usize, usize, String)> = Vec::new();
    let mut i = 0;
    while i < rows.len() {
        let (off, n, ref t) = rows[i];
        if t == "lock" && i + 1 < rows.len() && rows[i + 1].0 == off + n {
            let (_, n2, ref t2) = rows[i + 1];
            merged.push((off, n + n2, format!("lock {t2}")));
            i += 2;
        } else {
            merged.push((off, n, t.clone()));
            i += 1;
        }
    }
    merged
}

/// Canonicalize an instruction rendering for comparison:
/// strip `#` comments and `<...>` target annotations, lowercase, remove ALL
/// whitespace. Both the objdump side and the expected side go through this.
fn canon(text: &str) -> String {
    let t = match text.find('#') {
        Some(i) => &text[..i],
        None => text,
    };
    let mut s = String::with_capacity(t.len());
    let mut depth = 0usize;
    for c in t.chars() {
        match c {
            '<' => depth += 1,
            '>' => depth = depth.saturating_sub(1),
            _ if depth == 0 => s.push(c),
            _ => {}
        }
    }
    s.chars()
        .filter(|c| !c.is_whitespace())
        .collect::<String>()
        .to_lowercase()
}

// ---------------------------------------------------------------------------
// Expected-rendering helpers (independent re-derivation of intent)
// ---------------------------------------------------------------------------

const N64: [&str; 16] = [
    "rax", "rcx", "rdx", "rbx", "rsp", "rbp", "rsi", "rdi", "r8", "r9", "r10", "r11", "r12", "r13",
    "r14", "r15",
];
const N32: [&str; 16] = [
    "eax", "ecx", "edx", "ebx", "esp", "ebp", "esi", "edi", "r8d", "r9d", "r10d", "r11d", "r12d",
    "r13d", "r14d", "r15d",
];
const N16: [&str; 16] = [
    "ax", "cx", "dx", "bx", "sp", "bp", "si", "di", "r8w", "r9w", "r10w", "r11w", "r12w", "r13w",
    "r14w", "r15w",
];
// REX-style byte-register names (the encoder always forces REX for hw 4..=7
// byte operands, so spl/bpl/sil/dil are the intended renderings — if the REX
// is MISSING, objdump prints ah/ch/dh/bh and the lane flags it. That is a bug,
// not a formatting difference.)
const N8: [&str; 16] = [
    "al", "cl", "dl", "bl", "spl", "bpl", "sil", "dil", "r8b", "r9b", "r10b", "r11b", "r12b",
    "r13b", "r14b", "r15b",
];

fn n64(r: X86PReg) -> &'static str {
    N64[r.hw_enc() as usize]
}
fn n32(r: X86PReg) -> &'static str {
    N32[r.hw_enc() as usize]
}
fn n16(r: X86PReg) -> &'static str {
    N16[r.hw_enc() as usize]
}
fn n8(r: X86PReg) -> &'static str {
    N8[r.hw_enc() as usize]
}

/// Render an immediate the ways llvm-objdump may legitimately print the SAME
/// bit pattern at the given operand width: signed and unsigned hex. A wrong
/// immediate value matches neither variant.
fn imm_vars(v: i64, width: u32) -> Vec<String> {
    let mut out: Vec<String> = Vec::with_capacity(3);
    let signed = |x: i64| -> String {
        if x < 0 {
            format!("-0x{:x}", (x as i128).unsigned_abs())
        } else {
            format!("0x{:x}", x)
        }
    };
    out.push(signed(v));
    let bits: u64 = if width >= 64 {
        v as u64
    } else {
        (v as u64) & ((1u64 << width) - 1)
    };
    let uns = format!("0x{bits:x}");
    if !out.contains(&uns) {
        out.push(uns);
    }
    let shift = 64 - width.min(64);
    let sv = ((bits << shift) as i64) >> shift;
    let ss = signed(sv);
    if !out.contains(&ss) {
        out.push(ss);
    }
    out
}

/// `[base]`, `[base + 0xd]`, `[base - 0xd]` (canonical; whitespace-free).
fn mem(base: X86PReg, disp: i64) -> String {
    if disp == 0 {
        format!("[{}]", n64(base))
    } else if disp > 0 {
        format!("[{}+0x{:x}]", n64(base), disp)
    } else {
        format!("[{}-0x{:x}]", n64(base), (disp as i128).unsigned_abs())
    }
}

/// `[base + s*index + 0xd]` with scale 1 rendered without `1*`.
fn mem_sib(base: X86PReg, index: X86PReg, scale: u8, disp: i64) -> String {
    let idx = if scale == 1 {
        n64(index).to_string()
    } else {
        format!("{}*{}", scale, n64(index))
    };
    if disp == 0 {
        format!("[{}+{}]", n64(base), idx)
    } else if disp > 0 {
        format!("[{}+{}+0x{:x}]", n64(base), idx, disp)
    } else {
        format!(
            "[{}+{}-0x{:x}]",
            n64(base),
            idx,
            (disp as i128).unsigned_abs()
        )
    }
}

fn mem_rip(disp: i64) -> String {
    if disp == 0 {
        "[rip]".to_string()
    } else if disp > 0 {
        format!("[rip+0x{disp:x}]")
    } else {
        format!("[rip-0x{:x}]", (disp as i128).unsigned_abs())
    }
}

const CCS: [(X86CondCode, &str); 16] = [
    (X86CondCode::O, "o"),
    (X86CondCode::NO, "no"),
    (X86CondCode::B, "b"),
    (X86CondCode::AE, "ae"),
    (X86CondCode::E, "e"),
    (X86CondCode::NE, "ne"),
    (X86CondCode::BE, "be"),
    (X86CondCode::A, "a"),
    (X86CondCode::S, "s"),
    (X86CondCode::NS, "ns"),
    (X86CondCode::P, "p"),
    (X86CondCode::NP, "np"),
    (X86CondCode::L, "l"),
    (X86CondCode::GE, "ge"),
    (X86CondCode::LE, "le"),
    (X86CondCode::G, "g"),
];

// ---------------------------------------------------------------------------
// Case model + the differential driver
// ---------------------------------------------------------------------------

enum Expect {
    /// Acceptable canonical renderings (usually 1; >1 only for equivalent
    /// signed/unsigned immediate spellings or operand-order-symmetric forms).
    Fixed(Vec<String>),
    /// PC-relative: rendered target = offset_of_next_instruction + disp.
    Branch { mnem: String, disp: i64 },
}

struct Case {
    op: X86Opcode,
    ops: X86InstOperands,
    expect: Expect,
    desc: String,
}

impl Case {
    fn fixed(op: X86Opcode, ops: X86InstOperands, renderings: Vec<String>, desc: String) -> Self {
        Case {
            op,
            ops,
            expect: Expect::Fixed(renderings),
            desc,
        }
    }
    fn branch(op: X86Opcode, ops: X86InstOperands, mnem: String, disp: i64, desc: String) -> Self {
        Case {
            op,
            ops,
            expect: Expect::Branch { mnem, disp },
            desc,
        }
    }
}

/// Encode all cases into one .text buffer (each case padded to a 16-byte
/// boundary with int3 so a length disagreement cannot cascade), objdump it,
/// and compare row-by-row. Returns (instance_count, disagreements).
fn run_family(
    objdump: &Path,
    family: &str,
    cases: Vec<Case>,
    lead_pad: usize,
) -> (usize, Vec<String>) {
    let mut text: Vec<u8> = vec![0xCC; lead_pad];
    let mut placed: Vec<(usize, usize, &Case)> = Vec::new();
    let mut disagreements: Vec<String> = Vec::new();

    for case in &cases {
        let mut enc = X86Encoder::new();
        match enc.encode_instruction(case.op, &case.ops) {
            Ok(_) => {}
            Err(e) => {
                disagreements.push(format!("[{family}] ENCODE ERROR for {}: {e}", case.desc));
                continue;
            }
        }
        let bytes = enc.finish();
        if bytes.is_empty() {
            disagreements.push(format!("[{family}] EMPTY ENCODING for {}", case.desc));
            continue;
        }
        let offset = text.len();
        text.extend_from_slice(&bytes);
        while !text.len().is_multiple_of(16) {
            text.push(0xCC); // int3 inter-case padding
        }
        placed.push((offset, bytes.len(), case));
    }

    let object = elf64_x86_object(&text);
    let rows = run_objdump(objdump, &object, family);
    let by_offset: HashMap<usize, (usize, String)> =
        rows.into_iter().map(|(off, n, t)| (off, (n, t))).collect();

    for (offset, len, case) in &placed {
        let Some((dec_len, dec_text)) = by_offset.get(offset) else {
            disagreements.push(format!(
                "[{family}] off=0x{offset:x} {}: NO instruction decoded at this offset \
                 (length drift / undecodable bytes) — bytes {}",
                case.desc,
                hex_at(&text, *offset, *len)
            ));
            continue;
        };
        if dec_len != len {
            disagreements.push(format!(
                "[{family}] off=0x{offset:x} {}: LENGTH drift — encoder emitted {} bytes, \
                 objdump decoded {} — bytes {} — objdump: '{}'",
                case.desc,
                len,
                dec_len,
                hex_at(&text, *offset, *len),
                dec_text
            ));
            continue;
        }
        let actual = canon(dec_text);
        let accepted: Vec<String> = match &case.expect {
            Expect::Fixed(v) => v.iter().map(|s| canon(s)).collect(),
            Expect::Branch { mnem, disp } => {
                let target = (*offset as i64 + *len as i64).wrapping_add(*disp) as u64;
                vec![canon(&format!("{mnem} 0x{target:x}"))]
            }
        };
        if !accepted.contains(&actual) {
            disagreements.push(format!(
                "[{family}] off=0x{offset:x} {}:\n    intended: {}\n    objdump : '{}' \
                 (canonical '{}')\n    bytes   : {}",
                case.desc,
                accepted.join("  |  "),
                dec_text,
                actual,
                hex_at(&text, *offset, *len)
            ));
        }
    }
    (placed.len(), disagreements)
}

fn hex_at(buf: &[u8], off: usize, len: usize) -> String {
    buf[off..(off + len).min(buf.len())]
        .iter()
        .map(|b| format!("{b:02x}"))
        .collect::<Vec<_>>()
        .join(" ")
}

fn assert_family_green(family: &str, count: usize, disagreements: Vec<String>) {
    eprintln!("ENC-2 [{family}]: {count} instances compared against llvm-objdump");
    assert!(
        disagreements.is_empty(),
        "\n==================== ENC-2 P0 EVIDENCE ({family}) ====================\n\
         {} mnemonic/operand disagreement(s) between the x86 encoder and the pinned\n\
         external disassembler. DO NOT silently 'fix' the encoder: each row below is\n\
         evidence to be triaged (encoder bug vs expected-rendering bug) and reported.\n\n{}\n",
        disagreements.len(),
        disagreements.join("\n")
    );
}

// ---------------------------------------------------------------------------
// Register selections
// ---------------------------------------------------------------------------

const G64: [X86PReg; 16] = [
    RAX, RCX, RDX, RBX, RSP, RBP, RSI, RDI, R8, R9, R10, R11, R12, R13, R14, R15,
];
const G32: [X86PReg; 16] = [
    EAX,
    ECX,
    EDX,
    trust_cg_ir::x86_64_regs::EBX,
    trust_cg_ir::x86_64_regs::ESP,
    EBP,
    ESI,
    EDI,
    R8D,
    trust_cg_ir::x86_64_regs::R9D,
    trust_cg_ir::x86_64_regs::R10D,
    trust_cg_ir::x86_64_regs::R11D,
    trust_cg_ir::x86_64_regs::R12D,
    R13D,
    trust_cg_ir::x86_64_regs::R14D,
    R15D,
];
/// REX-edge-heavy source selection (low, stack, high regs).
const SEL64: [X86PReg; 9] = [RAX, RBX, RSP, RBP, RSI, R8, R12, R13, R15];
const SEL32: [X86PReg; 4] = [EAX, EBP, R8D, R13D];
const BYTE_REGS: [X86PReg; 8] = [AL, CL, DL, BL, SPL, SIL, DIL, R8B];

const DISPS: [i64; 9] = [0, 8, -8, 127, -128, 128, -129, 0x7fff, -0x8000];

// ---------------------------------------------------------------------------
// Family generators + tests
// ---------------------------------------------------------------------------

#[test]
fn enc2_family_alu() {
    let Some(d) = objdump_or_skip("alu") else {
        return;
    };
    let mut cases: Vec<Case> = Vec::new();

    // reg-reg (rm=dst printed first, reg=src second)
    let rr_ops: [(X86Opcode, &str); 9] = [
        (X86Opcode::AddRR, "add"),
        (X86Opcode::SubRR, "sub"),
        (X86Opcode::AdcRR, "adc"),
        (X86Opcode::SbbRR, "sbb"),
        (X86Opcode::AndRR, "and"),
        (X86Opcode::OrRR, "or"),
        (X86Opcode::XorRR, "xor"),
        (X86Opcode::CmpRR, "cmp"),
        (X86Opcode::TestRR, "test"),
    ];
    for (op, m) in rr_ops {
        for dst in G64 {
            for src in SEL64 {
                cases.push(Case::fixed(
                    op,
                    X86InstOperands::rr(dst, src),
                    vec![format!("{m} {}, {}", n64(dst), n64(src))],
                    format!("{op:?} {},{}", n64(dst), n64(src)),
                ));
            }
        }
        for dst in G32 {
            for src in SEL32 {
                cases.push(Case::fixed(
                    op,
                    X86InstOperands::rr(dst, src),
                    vec![format!("{m} {}, {}", n32(dst), n32(src))],
                    format!("{op:?} {},{}", n32(dst), n32(src)),
                ));
            }
        }
    }

    // reg-imm (imm8/imm32 auto-select in the encoder; 64-bit sign-extended)
    let ri_ops: [(X86Opcode, &str); 6] = [
        (X86Opcode::AddRI, "add"),
        (X86Opcode::SubRI, "sub"),
        (X86Opcode::AndRI, "and"),
        (X86Opcode::OrRI, "or"),
        (X86Opcode::XorRI, "xor"),
        (X86Opcode::CmpRI, "cmp"),
    ];
    let imms: [i64; 9] = [
        0,
        1,
        -1,
        0x7f,
        -0x80,
        0x80,
        -0x81,
        0x7fff_ffff,
        -0x8000_0000,
    ];
    for (op, m) in ri_ops {
        for dst in G64 {
            for imm in imms {
                cases.push(Case::fixed(
                    op,
                    X86InstOperands::ri(dst, imm),
                    imm_vars(imm, 64)
                        .into_iter()
                        .map(|i| format!("{m} {}, {i}", n64(dst)))
                        .collect(),
                    format!("{op:?} {},{imm}", n64(dst)),
                ));
            }
        }
        for dst in SEL32 {
            for imm in [0i64, 1, -1, 0x7f, 0x80, 0x7fff_ffff] {
                cases.push(Case::fixed(
                    op,
                    X86InstOperands::ri(dst, imm),
                    imm_vars(imm, 32)
                        .into_iter()
                        .map(|i| format!("{m} {}, {i}", n32(dst)))
                        .collect(),
                    format!("{op:?} {},{imm}", n32(dst)),
                ));
            }
        }
    }
    // TEST r/m64, imm32 (always the F7 /0 id form, 64-bit)
    for dst in G64 {
        for imm in [0i64, 1, -1, 0xff, -0x100, 0x7fff_ffff] {
            cases.push(Case::fixed(
                X86Opcode::TestRI,
                X86InstOperands::ri(dst, imm),
                imm_vars(imm, 64)
                    .into_iter()
                    .map(|i| format!("test {}, {i}", n64(dst)))
                    .collect(),
                format!("TestRI {},{imm}", n64(dst)),
            ));
        }
    }
    // CMP r/m64, imm8 (dedicated 83 /7 ib form)
    for dst in G64 {
        for imm in [-128i64, -1, 0, 1, 127] {
            cases.push(Case::fixed(
                X86Opcode::CmpRI8,
                X86InstOperands::ri(dst, imm),
                imm_vars(imm, 64)
                    .into_iter()
                    .map(|i| format!("cmp {}, {i}", n64(dst)))
                    .collect(),
                format!("CmpRI8 {},{imm}", n64(dst)),
            ));
        }
    }

    // reg-mem forms: ADD/SUB/CMP r64, [base+disp] (reg first);
    // TEST r/m64, r64 with memory rm (either operand order accepted — TEST
    // is symmetric and disassemblers differ on the printed order).
    for (op, m) in [
        (X86Opcode::AddRM, "add"),
        (X86Opcode::SubRM, "sub"),
        (X86Opcode::CmpRM, "cmp"),
    ] {
        for dst in [RAX, R9] {
            for base in G64 {
                for disp in DISPS {
                    cases.push(Case::fixed(
                        op,
                        X86InstOperands::rm(dst, base, disp),
                        vec![format!("{m} {}, qword ptr {}", n64(dst), mem(base, disp))],
                        format!("{op:?} {},{}", n64(dst), mem(base, disp)),
                    ));
                }
            }
        }
    }
    for dst in [RAX, R9] {
        for base in G64 {
            for disp in [0i64, 8, -8, 0x100] {
                cases.push(Case::fixed(
                    X86Opcode::TestRM,
                    X86InstOperands::rm(dst, base, disp),
                    vec![
                        format!("test qword ptr {}, {}", mem(base, disp), n64(dst)),
                        format!("test {}, qword ptr {}", n64(dst), mem(base, disp)),
                    ],
                    format!("TestRM {},{}", n64(dst), mem(base, disp)),
                ));
            }
        }
    }

    // unary ALU
    for (op, m) in [
        (X86Opcode::Neg, "neg"),
        (X86Opcode::Not, "not"),
        (X86Opcode::Inc, "inc"),
        (X86Opcode::Dec, "dec"),
    ] {
        for r in G64 {
            cases.push(Case::fixed(
                op,
                X86InstOperands::r(r),
                vec![format!("{m} {}", n64(r))],
                format!("{op:?} {}", n64(r)),
            ));
        }
        for r in SEL32 {
            cases.push(Case::fixed(
                op,
                X86InstOperands::r(r),
                vec![format!("{m} {}", n32(r))],
                format!("{op:?} {}", n32(r)),
            ));
        }
    }

    let (count, dis) = run_family(&d.path, "alu", cases, 0);
    assert_family_green("alu", count, dis);
}

#[test]
fn enc2_family_mov() {
    let Some(d) = objdump_or_skip("mov") else {
        return;
    };
    let mut cases: Vec<Case> = Vec::new();

    // MOV r64, r64 / r32, r32
    for dst in G64 {
        for src in SEL64 {
            cases.push(Case::fixed(
                X86Opcode::MovRR,
                X86InstOperands::rr(dst, src),
                vec![format!("mov {}, {}", n64(dst), n64(src))],
                format!("MovRR {},{}", n64(dst), n64(src)),
            ));
        }
    }
    for dst in G32 {
        for src in SEL32 {
            cases.push(Case::fixed(
                X86Opcode::MovRR32,
                X86InstOperands::rr(dst, src),
                vec![format!("mov {}, {}", n32(dst), n32(src))],
                format!("MovRR32 {},{}", n32(dst), n32(src)),
            ));
        }
    }

    // MOV r, imm — including the documented zero-extending 32-bit alias for
    // 64-bit destinations with imm in [0, u32::MAX], and movabs beyond it.
    for dst in G64 {
        // alias region: encoder emits the 32-bit form (intent: zext move)
        for imm in [0i64, 1, 0x7f, 0x80, 0xffff, 0x7fff_ffff, 0xffff_ffff] {
            cases.push(Case::fixed(
                X86Opcode::MovRI,
                X86InstOperands::ri(dst, imm),
                imm_vars(imm, 32)
                    .into_iter()
                    .map(|i| format!("mov {}, {i}", n32(dst)))
                    .collect(),
                format!("MovRI(zext-alias) {},{imm}", n64(dst)),
            ));
        }
        // true 64-bit immediates: movabs
        for imm in [
            -1i64,
            -0x80,
            0x1_0000_0000,
            0x1122_3344_5566_7788,
            i64::MAX,
            i64::MIN,
        ] {
            cases.push(Case::fixed(
                X86Opcode::MovRI,
                X86InstOperands::ri(dst, imm),
                imm_vars(imm, 64)
                    .into_iter()
                    .map(|i| format!("movabs {}, {i}", n64(dst)))
                    .collect(),
                format!("MovRI(movabs) {},{imm}", n64(dst)),
            ));
        }
    }
    for dst in SEL32 {
        for imm in [0i64, 0x7f, 0x8000_0000u32 as i64, 0xffff_ffff] {
            cases.push(Case::fixed(
                X86Opcode::MovRI,
                X86InstOperands::ri(dst, imm),
                imm_vars(imm, 32)
                    .into_iter()
                    .map(|i| format!("mov {}, {i}", n32(dst)))
                    .collect(),
                format!("MovRI {},{imm}", n32(dst)),
            ));
        }
    }
    for dst in [
        trust_cg_ir::x86_64_regs::AX,
        trust_cg_ir::x86_64_regs::CX,
        trust_cg_ir::x86_64_regs::R8W,
        trust_cg_ir::x86_64_regs::R15W,
    ] {
        for imm in [0i64, 0x1234, 0x8000, 0xffff] {
            cases.push(Case::fixed(
                X86Opcode::MovRI,
                X86InstOperands::ri(dst, imm),
                imm_vars(imm, 16)
                    .into_iter()
                    .map(|i| format!("mov {}, {i}", n16(dst)))
                    .collect(),
                format!("MovRI {},{imm}", n16(dst)),
            ));
        }
    }
    for dst in BYTE_REGS {
        for imm in [0i64, 1, 0x7f, 0x80, 0xff] {
            cases.push(Case::fixed(
                X86Opcode::MovRI,
                X86InstOperands::ri(dst, imm),
                imm_vars(imm, 8)
                    .into_iter()
                    .map(|i| format!("mov {}, {i}", n8(dst)))
                    .collect(),
                format!("MovRI {},{imm}", n8(dst)),
            ));
        }
    }

    // MOV loads/stores at all four widths. The register operand is passed as
    // a GPR64; the opcode determines the operand width and therefore the
    // intended sub-register rendering.
    let mem_regs: [X86PReg; 7] = [RAX, RCX, RSP, RBP, RSI, R8, R13];
    type LoadStoreCase = (
        X86Opcode,
        X86Opcode,
        &'static str,
        fn(X86PReg) -> &'static str,
    );
    let ldst: [LoadStoreCase; 8] = [
        (X86Opcode::MovRM8, X86Opcode::MovMR8, "byte ptr", n8),
        (X86Opcode::MovRM16, X86Opcode::MovMR16, "word ptr", n16),
        (X86Opcode::MovRM32, X86Opcode::MovMR32, "dword ptr", n32),
        (X86Opcode::MovRM, X86Opcode::MovMR, "qword ptr", n64),
        (
            X86Opcode::VolatileMovRM8,
            X86Opcode::VolatileMovMR8,
            "byte ptr",
            n8,
        ),
        (
            X86Opcode::VolatileMovRM16,
            X86Opcode::VolatileMovMR16,
            "word ptr",
            n16,
        ),
        (
            X86Opcode::VolatileMovRM32,
            X86Opcode::VolatileMovMR32,
            "dword ptr",
            n32,
        ),
        (
            X86Opcode::VolatileMovRM,
            X86Opcode::VolatileMovMR,
            "qword ptr",
            n64,
        ),
    ];
    for (ld, st, ptr, name) in ldst {
        for reg in mem_regs {
            for base in G64 {
                for disp in [0i64, 8, -8, 0x100] {
                    cases.push(Case::fixed(
                        ld,
                        X86InstOperands::rm(reg, base, disp),
                        vec![format!("mov {}, {ptr} {}", name(reg), mem(base, disp))],
                        format!("{ld:?} {},{}", name(reg), mem(base, disp)),
                    ));
                    cases.push(Case::fixed(
                        st,
                        X86InstOperands::rm(reg, base, disp),
                        vec![format!("mov {ptr} {}, {}", mem(base, disp), name(reg))],
                        format!("{st:?} {},{}", mem(base, disp), name(reg)),
                    ));
                }
            }
        }
    }

    // SIB loads/stores
    let sib_bases: [X86PReg; 5] = [RAX, RBP, RSP, R12, R13];
    let sib_indexes: [X86PReg; 5] = [RCX, RBP, R9, R12, R14];
    for dst in [RAX, R10] {
        for base in sib_bases {
            for index in sib_indexes {
                for scale in [1u8, 2, 4, 8] {
                    for disp in [0i64, 8, -8, 0x100] {
                        cases.push(Case::fixed(
                            X86Opcode::MovRMSib,
                            X86InstOperands::rm_sib(dst, base, index, scale, disp),
                            vec![format!(
                                "mov {}, qword ptr {}",
                                n64(dst),
                                mem_sib(base, index, scale, disp)
                            )],
                            format!(
                                "MovRMSib {},{}",
                                n64(dst),
                                mem_sib(base, index, scale, disp)
                            ),
                        ));
                        cases.push(Case::fixed(
                            X86Opcode::MovMRSib,
                            X86InstOperands::rm_sib(dst, base, index, scale, disp),
                            vec![format!(
                                "mov qword ptr {}, {}",
                                mem_sib(base, index, scale, disp),
                                n64(dst)
                            )],
                            format!(
                                "MovMRSib {},{}",
                                mem_sib(base, index, scale, disp),
                                n64(dst)
                            ),
                        ));
                        cases.push(Case::fixed(
                            X86Opcode::MovsxdRMSib,
                            X86InstOperands::rm_sib(dst, base, index, scale, disp),
                            vec![format!(
                                "movsxd {}, dword ptr {}",
                                n64(dst),
                                mem_sib(base, index, scale, disp)
                            )],
                            format!(
                                "MovsxdRMSib {},{}",
                                n64(dst),
                                mem_sib(base, index, scale, disp)
                            ),
                        ));
                    }
                }
            }
        }
    }

    // Byte-width SIB loads/stores. Keep the byte-register set deliberately
    // REX-heavy: SIL needs an otherwise-empty REX prefix to avoid decoding as
    // DH, while R8B/R13B exercise REX.R alongside extended base/index bits.
    for reg in [RAX, RSI, R8, R13] {
        for base in [RAX, RBP, R12, R13] {
            for index in [RCX, R9, R14] {
                for scale in [1u8, 4] {
                    for disp in [0i64, -8, 0x100] {
                        cases.push(Case::fixed(
                            X86Opcode::MovRM8Sib,
                            X86InstOperands::rm_sib(reg, base, index, scale, disp),
                            vec![format!(
                                "mov {}, byte ptr {}",
                                n8(reg),
                                mem_sib(base, index, scale, disp)
                            )],
                            format!(
                                "MovRM8Sib {},{}",
                                n8(reg),
                                mem_sib(base, index, scale, disp)
                            ),
                        ));
                        cases.push(Case::fixed(
                            X86Opcode::MovMR8Sib,
                            X86InstOperands::rm_sib(reg, base, index, scale, disp),
                            vec![format!(
                                "mov byte ptr {}, {}",
                                mem_sib(base, index, scale, disp),
                                n8(reg)
                            )],
                            format!(
                                "MovMR8Sib {},{}",
                                mem_sib(base, index, scale, disp),
                                n8(reg)
                            ),
                        ));
                    }
                }
            }
        }
    }

    // RIP-relative load
    for dst in [RAX, RBP, R8, R15] {
        for disp in [0i64, 0x10, -0x10, 0x1000] {
            cases.push(Case::fixed(
                X86Opcode::MovRipRel,
                X86InstOperands::rip_rel(dst, disp),
                vec![format!("mov {}, qword ptr {}", n64(dst), mem_rip(disp))],
                format!("MovRipRel {},{}", n64(dst), mem_rip(disp)),
            ));
            cases.push(Case::fixed(
                X86Opcode::MovRipRelTlv,
                X86InstOperands::rip_rel(dst, disp),
                vec![format!("mov {}, qword ptr {}", n64(dst), mem_rip(disp))],
                format!("MovRipRelTlv {},{}", n64(dst), mem_rip(disp)),
            ));
        }
    }

    // MOVZX / MOVSX family (dst 64-bit; source sub-register width per opcode)
    for (op, m, srcname) in [
        (X86Opcode::Movzx, "movzx", n8 as fn(X86PReg) -> &'static str),
        (X86Opcode::MovzxW, "movzx", n16),
        (X86Opcode::MovsxB, "movsx", n8),
        (X86Opcode::MovsxW, "movsx", n16),
        (X86Opcode::Movsx, "movsxd", n32),
    ] {
        for dst in [RAX, RBP, R8, R13] {
            for src in G64 {
                cases.push(Case::fixed(
                    op,
                    X86InstOperands::rr(dst, src),
                    vec![format!("{m} {}, {}", n64(dst), srcname(src))],
                    format!("{op:?} {},{}", n64(dst), srcname(src)),
                ));
            }
        }
    }

    let (count, dis) = run_family(&d.path, "mov", cases, 0);
    assert_family_green("mov", count, dis);
}

#[test]
fn enc2_family_branch() {
    let Some(d) = objdump_or_skip("branch") else {
        return;
    };
    let mut cases: Vec<Case> = Vec::new();
    let disps: [i64; 6] = [0, 8, 0x40, 0x1000, -0x10, -0x100];

    for disp in disps {
        let mut o = X86InstOperands::none();
        o.disp = disp;
        cases.push(Case::branch(
            X86Opcode::Jmp,
            o,
            "jmp".to_string(),
            disp,
            format!("Jmp rel32={disp}"),
        ));
    }
    for (cc, suffix) in CCS {
        for disp in disps {
            let mut o = X86InstOperands::none();
            o.cc = Some(cc);
            o.disp = disp;
            cases.push(Case::branch(
                X86Opcode::Jcc,
                o,
                format!("j{suffix}"),
                disp,
                format!("Jcc({suffix}) rel32={disp}"),
            ));
        }
    }
    for disp in disps {
        let mut o = X86InstOperands::none();
        o.disp = disp;
        cases.push(Case::branch(
            X86Opcode::Call,
            o,
            "call".to_string(),
            disp,
            format!("Call rel32={disp}"),
        ));
    }
    for r in G64 {
        cases.push(Case::fixed(
            X86Opcode::CallR,
            X86InstOperands::r(r),
            vec![format!("call {}", n64(r))],
            format!("CallR {}", n64(r)),
        ));
        cases.push(Case::fixed(
            X86Opcode::JmpR,
            X86InstOperands::r(r),
            vec![format!("jmp {}", n64(r))],
            format!("JmpR {}", n64(r)),
        ));
    }
    for base in G64 {
        for disp in [0i64, 8, -8] {
            let mut o = X86InstOperands::none();
            o.base = Some(base);
            o.disp = disp;
            cases.push(Case::fixed(
                X86Opcode::CallM,
                o,
                vec![format!("call qword ptr {}", mem(base, disp))],
                format!("CallM {}", mem(base, disp)),
            ));
        }
    }
    cases.push(Case::fixed(
        X86Opcode::Ret,
        X86InstOperands::none(),
        vec!["ret".to_string()],
        "Ret".to_string(),
    ));

    // 512 bytes of leading int3 padding so negative branch displacements keep
    // resolved targets non-negative (objdump renders targets as u64).
    let (count, dis) = run_family(&d.path, "branch", cases, 512);
    assert_family_green("branch", count, dis);
}

#[test]
fn enc2_family_shift() {
    let Some(d) = objdump_or_skip("shift") else {
        return;
    };
    let mut cases: Vec<Case> = Vec::new();
    for (opi, opr, m) in [
        (X86Opcode::ShlRI, X86Opcode::ShlRR, "shl"),
        (X86Opcode::ShrRI, X86Opcode::ShrRR, "shr"),
        (X86Opcode::SarRI, X86Opcode::SarRR, "sar"),
    ] {
        for dst in G64 {
            for imm in [1i64, 5, 31, 63] {
                cases.push(Case::fixed(
                    opi,
                    X86InstOperands::ri(dst, imm),
                    imm_vars(imm, 8)
                        .into_iter()
                        .map(|i| format!("{m} {}, {i}", n64(dst)))
                        .collect(),
                    format!("{opi:?} {},{imm}", n64(dst)),
                ));
            }
            cases.push(Case::fixed(
                opr,
                X86InstOperands::r(dst),
                vec![format!("{m} {}, cl", n64(dst))],
                format!("{opr:?} {},cl", n64(dst)),
            ));
        }
        for dst in SEL32 {
            for imm in [1i64, 31] {
                cases.push(Case::fixed(
                    opi,
                    X86InstOperands::ri(dst, imm),
                    imm_vars(imm, 8)
                        .into_iter()
                        .map(|i| format!("{m} {}, {i}", n32(dst)))
                        .collect(),
                    format!("{opi:?} {},{imm}", n32(dst)),
                ));
            }
            cases.push(Case::fixed(
                opr,
                X86InstOperands::r(dst),
                vec![format!("{m} {}, cl", n32(dst))],
                format!("{opr:?} {},cl", n32(dst)),
            ));
        }
    }
    // ROL has an immediate form but no CL-count sibling. Exercise both REX.W
    // and 32-bit encodings independently of the byte-golden encoder tests.
    for dst in G64 {
        for imm in [4i64, 9, 31, 63] {
            cases.push(Case::fixed(
                X86Opcode::RolRI,
                X86InstOperands::ri(dst, imm),
                imm_vars(imm, 8)
                    .into_iter()
                    .map(|i| format!("rol {}, {i}", n64(dst)))
                    .collect(),
                format!("RolRI {},{imm}", n64(dst)),
            ));
        }
    }
    for dst in SEL32 {
        for imm in [4i64, 9, 31] {
            cases.push(Case::fixed(
                X86Opcode::RolRI,
                X86InstOperands::ri(dst, imm),
                imm_vars(imm, 8)
                    .into_iter()
                    .map(|i| format!("rol {}, {i}", n32(dst)))
                    .collect(),
                format!("RolRI {},{imm}", n32(dst)),
            ));
        }
    }
    let (count, dis) = run_family(&d.path, "shift", cases, 0);
    assert_family_green("shift", count, dis);
}

#[test]
fn enc2_family_mul() {
    let Some(d) = objdump_or_skip("mul") else {
        return;
    };
    let mut cases: Vec<Case> = Vec::new();

    for dst in G64 {
        for src in SEL64 {
            cases.push(Case::fixed(
                X86Opcode::ImulRR,
                X86InstOperands::rr(dst, src),
                vec![format!("imul {}, {}", n64(dst), n64(src))],
                format!("ImulRR {},{}", n64(dst), n64(src)),
            ));
        }
    }
    for dst in G32 {
        for src in SEL32 {
            cases.push(Case::fixed(
                X86Opcode::ImulRR,
                X86InstOperands::rr(dst, src),
                vec![format!("imul {}, {}", n32(dst), n32(src))],
                format!("ImulRR {},{}", n32(dst), n32(src)),
            ));
        }
    }
    for dst in [RAX, RBP, R9, R15] {
        for src in [RAX, RBX, R8, R13] {
            for imm in [1i64, 5, 127, -128, 128, 0x7fff, -1] {
                cases.push(Case::fixed(
                    X86Opcode::ImulRRI,
                    X86InstOperands::rri(dst, src, imm),
                    imm_vars(imm, 64)
                        .into_iter()
                        .map(|i| format!("imul {}, {}, {i}", n64(dst), n64(src)))
                        .collect(),
                    format!("ImulRRI {},{},{imm}", n64(dst), n64(src)),
                ));
            }
        }
    }
    for dst in [RAX, R11] {
        for base in G64 {
            for disp in [0i64, 8, -8, 0x100] {
                cases.push(Case::fixed(
                    X86Opcode::ImulRM,
                    X86InstOperands::rm(dst, base, disp),
                    vec![format!("imul {}, qword ptr {}", n64(dst), mem(base, disp))],
                    format!("ImulRM {},{}", n64(dst), mem(base, disp)),
                ));
            }
        }
    }
    // scaled-index two-operand IMUL (SIB sibling of ImulRM)
    {
        let sib_bases: [X86PReg; 5] = [RAX, RBP, RSP, R12, R13];
        let sib_indexes: [X86PReg; 5] = [RCX, RBP, R9, R12, R14];
        for dst in [RAX, R11] {
            for base in sib_bases {
                for index in sib_indexes {
                    for scale in [1u8, 2, 4, 8] {
                        for disp in [0i64, 8, -8, 0x100] {
                            cases.push(Case::fixed(
                                X86Opcode::ImulRMSib,
                                X86InstOperands::rm_sib(dst, base, index, scale, disp),
                                vec![format!(
                                    "imul {}, qword ptr {}",
                                    n64(dst),
                                    mem_sib(base, index, scale, disp)
                                )],
                                format!(
                                    "ImulRMSib {},{}",
                                    n64(dst),
                                    mem_sib(base, index, scale, disp)
                                ),
                            ));
                        }
                    }
                }
            }
        }
    }
    // 32-bit SIB MOV load/store (X10 siblings)
    {
        let sib_bases: [X86PReg; 4] = [RAX, RBP, R12, R13];
        let sib_indexes: [X86PReg; 4] = [RCX, RBP, R9, R14];
        for reg in [RAX, R10] {
            for base in sib_bases {
                for index in sib_indexes {
                    for scale in [1u8, 4] {
                        for disp in [0i64, 8, 0x100] {
                            cases.push(Case::fixed(
                                X86Opcode::MovRM32Sib,
                                X86InstOperands::rm_sib(reg, base, index, scale, disp),
                                vec![format!(
                                    "mov {}, dword ptr {}",
                                    n32(reg),
                                    mem_sib(base, index, scale, disp)
                                )],
                                format!(
                                    "MovRM32Sib {},{}",
                                    n32(reg),
                                    mem_sib(base, index, scale, disp)
                                ),
                            ));
                            cases.push(Case::fixed(
                                X86Opcode::MovMR32Sib,
                                X86InstOperands::rm_sib(reg, base, index, scale, disp),
                                vec![format!(
                                    "mov dword ptr {}, {}",
                                    mem_sib(base, index, scale, disp),
                                    n32(reg)
                                )],
                                format!(
                                    "MovMR32Sib {},{}",
                                    mem_sib(base, index, scale, disp),
                                    n32(reg)
                                ),
                            ));
                        }
                    }
                }
            }
        }
    }
    // one-operand unsigned MUL (RDX:RAX = RAX * r/m)
    for r in G64 {
        cases.push(Case::fixed(
            X86Opcode::Mul,
            X86InstOperands::r(r),
            vec![format!("mul {}", n64(r))],
            format!("Mul {}", n64(r)),
        ));
    }
    for r in SEL32 {
        cases.push(Case::fixed(
            X86Opcode::Mul,
            X86InstOperands::r(r),
            vec![format!("mul {}", n32(r))],
            format!("Mul {}", n32(r)),
        ));
    }
    let (count, dis) = run_family(&d.path, "mul", cases, 0);
    assert_family_green("mul", count, dis);
}

#[test]
fn enc2_family_div() {
    let Some(d) = objdump_or_skip("div") else {
        return;
    };
    let mut cases: Vec<Case> = Vec::new();
    for (op, m) in [(X86Opcode::Idiv, "idiv"), (X86Opcode::Div, "div")] {
        for r in G64 {
            cases.push(Case::fixed(
                op,
                X86InstOperands::r(r),
                vec![format!("{m} {}", n64(r))],
                format!("{op:?} {}", n64(r)),
            ));
        }
        for r in SEL32 {
            cases.push(Case::fixed(
                op,
                X86InstOperands::r(r),
                vec![format!("{m} {}", n32(r))],
                format!("{op:?} {}", n32(r)),
            ));
        }
    }
    cases.push(Case::fixed(
        X86Opcode::Cdq,
        X86InstOperands::none(),
        vec!["cdq".to_string()],
        "Cdq".to_string(),
    ));
    cases.push(Case::fixed(
        X86Opcode::Cqo,
        X86InstOperands::none(),
        vec!["cqo".to_string()],
        "Cqo".to_string(),
    ));
    let (count, dis) = run_family(&d.path, "div", cases, 0);
    assert_family_green("div", count, dis);
}

#[test]
fn enc2_family_lea() {
    let Some(d) = objdump_or_skip("lea") else {
        return;
    };
    let mut cases: Vec<Case> = Vec::new();
    for dst in [RAX, RBP, R11] {
        for base in G64 {
            for disp in DISPS {
                cases.push(Case::fixed(
                    X86Opcode::Lea,
                    X86InstOperands::rm(dst, base, disp),
                    vec![format!("lea {}, {}", n64(dst), mem(base, disp))],
                    format!("Lea {},{}", n64(dst), mem(base, disp)),
                ));
            }
        }
    }
    let sib_bases: [X86PReg; 5] = [RAX, RBP, RSP, R12, R13];
    let sib_indexes: [X86PReg; 5] = [RCX, RBP, R9, R12, R14];
    for dst in [RAX, R10] {
        for base in sib_bases {
            for index in sib_indexes {
                for scale in [1u8, 2, 4, 8] {
                    for disp in [0i64, 4, -4, 0x200] {
                        cases.push(Case::fixed(
                            X86Opcode::LeaSib,
                            X86InstOperands::rm_sib(dst, base, index, scale, disp),
                            vec![format!(
                                "lea {}, {}",
                                n64(dst),
                                mem_sib(base, index, scale, disp)
                            )],
                            format!("LeaSib {},{}", n64(dst), mem_sib(base, index, scale, disp)),
                        ));
                    }
                }
            }
        }
    }
    for dst in [RAX, RBP, R8, R15] {
        for disp in [0i64, 0x10, -0x10, 0x1000] {
            cases.push(Case::fixed(
                X86Opcode::LeaRip,
                X86InstOperands::rip_rel(dst, disp),
                vec![format!("lea {}, {}", n64(dst), mem_rip(disp))],
                format!("LeaRip {},{}", n64(dst), mem_rip(disp)),
            ));
        }
    }
    let (count, dis) = run_family(&d.path, "lea", cases, 0);
    assert_family_green("lea", count, dis);
}

#[test]
fn enc2_family_setcc() {
    let Some(d) = objdump_or_skip("setcc") else {
        return;
    };
    let mut cases: Vec<Case> = Vec::new();
    // Explicit byte registers AND gpr64 aliases (the encoder takes the hw
    // encoding; the instruction always operates on the byte register).
    let dsts: [X86PReg; 11] = [AL, CL, DL, BL, SPL, SIL, DIL, R8B, R15B, RAX, R13];
    for (cc, suffix) in CCS {
        for dst in dsts {
            let mut o = X86InstOperands::r(dst);
            o.cc = Some(cc);
            cases.push(Case::fixed(
                X86Opcode::Setcc,
                o,
                vec![format!("set{suffix} {}", n8(dst))],
                format!("Setcc({suffix}) {}", n8(dst)),
            ));
        }
    }
    let (count, dis) = run_family(&d.path, "setcc", cases, 0);
    assert_family_green("setcc", count, dis);
}

#[test]
fn enc2_family_cmov() {
    let Some(d) = objdump_or_skip("cmov") else {
        return;
    };
    let mut cases: Vec<Case> = Vec::new();
    let pairs64: [(X86PReg, X86PReg); 8] = [
        (RAX, RBX),
        (RCX, RSP),
        (RBP, RSI),
        (RDI, R8),
        (R9, R12),
        (R13, RAX),
        (R14, R15),
        (R15, RBP),
    ];
    for (cc, suffix) in CCS {
        for (dst, src) in pairs64 {
            let mut o = X86InstOperands::rr(dst, src);
            o.cc = Some(cc);
            cases.push(Case::fixed(
                X86Opcode::Cmovcc,
                o,
                vec![format!("cmov{suffix} {}, {}", n64(dst), n64(src))],
                format!("Cmovcc({suffix}) {},{}", n64(dst), n64(src)),
            ));
        }
        for (dst, src) in [(EAX, EBP), (ECX, R8D), (R13D, ESI), (R15D, EDX)] {
            let mut o = X86InstOperands::rr(dst, src);
            o.cc = Some(cc);
            cases.push(Case::fixed(
                X86Opcode::Cmovcc32,
                o,
                vec![format!("cmov{suffix} {}, {}", n32(dst), n32(src))],
                format!("Cmovcc32({suffix}) {},{}", n32(dst), n32(src)),
            ));
        }
    }
    let (count, dis) = run_family(&d.path, "cmov", cases, 0);
    assert_family_green("cmov", count, dis);
}

#[test]
fn enc2_family_pushpop() {
    let Some(d) = objdump_or_skip("pushpop") else {
        return;
    };
    let mut cases: Vec<Case> = Vec::new();
    // Exhaustive over the operand space (16 GPR64 each) — fewer than 200
    // instances exist for this family, so full enumeration is the lane.
    for r in G64 {
        cases.push(Case::fixed(
            X86Opcode::Push,
            X86InstOperands::r(r),
            vec![format!("push {}", n64(r))],
            format!("Push {}", n64(r)),
        ));
        cases.push(Case::fixed(
            X86Opcode::Pop,
            X86InstOperands::r(r),
            vec![format!("pop {}", n64(r))],
            format!("Pop {}", n64(r)),
        ));
    }
    let (count, dis) = run_family(&d.path, "pushpop", cases, 0);
    assert_family_green("pushpop", count, dis);
}

#[test]
fn enc2_family_bitmanip() {
    let Some(d) = objdump_or_skip("bitmanip") else {
        return;
    };
    let mut cases: Vec<Case> = Vec::new();
    for (op, m) in [
        (X86Opcode::Bsf, "bsf"),
        (X86Opcode::Bsr, "bsr"),
        (X86Opcode::Tzcnt, "tzcnt"),
        (X86Opcode::Lzcnt, "lzcnt"),
    ] {
        for dst in [RAX, RBP, R8, R13] {
            for src in SEL64 {
                cases.push(Case::fixed(
                    op,
                    X86InstOperands::rr(dst, src),
                    vec![format!("{m} {}, {}", n64(dst), n64(src))],
                    format!("{op:?} {},{}", n64(dst), n64(src)),
                ));
            }
        }
    }
    for dst in G64 {
        for src in SEL64 {
            cases.push(Case::fixed(
                X86Opcode::Popcnt,
                X86InstOperands::rr(dst, src),
                vec![format!("popcnt {}, {}", n64(dst), n64(src))],
                format!("Popcnt {},{}", n64(dst), n64(src)),
            ));
        }
    }
    for dst in SEL32 {
        for src in SEL32 {
            cases.push(Case::fixed(
                X86Opcode::Popcnt,
                X86InstOperands::rr(dst, src),
                vec![format!("popcnt {}, {}", n32(dst), n32(src))],
                format!("Popcnt {},{}", n32(dst), n32(src)),
            ));
        }
    }
    for dst in G64 {
        for imm in [0i64, 1, 33, 63] {
            cases.push(Case::fixed(
                X86Opcode::BtRI,
                X86InstOperands::ri(dst, imm),
                imm_vars(imm, 8)
                    .into_iter()
                    .map(|i| format!("bt {}, {i}", n64(dst)))
                    .collect(),
                format!("BtRI {},{imm}", n64(dst)),
            ));
        }
        cases.push(Case::fixed(
            X86Opcode::Bswap,
            X86InstOperands::r(dst),
            vec![format!("bswap {}", n64(dst))],
            format!("Bswap {}", n64(dst)),
        ));
    }
    let (count, dis) = run_family(&d.path, "bitmanip", cases, 0);
    assert_family_green("bitmanip", count, dis);
}

#[test]
fn enc2_family_sync() {
    let Some(d) = objdump_or_skip("sync") else {
        return;
    };
    let mut cases: Vec<Case> = Vec::new();

    // XCHG rr: encoder puts src in ModRM.reg, dst in ModRM.rm; llvm-objdump
    // prints the reg operand first for the register-register form.
    for dst in G64 {
        for src in SEL64 {
            cases.push(Case::fixed(
                X86Opcode::Xchg,
                X86InstOperands::rr(dst, src),
                vec![
                    format!("xchg {}, {}", n64(src), n64(dst)),
                    format!("xchg {}, {}", n64(dst), n64(src)),
                ],
                format!("Xchg {},{}", n64(dst), n64(src)),
            ));
        }
    }
    // XCHG with memory (dst field register, [base+disp])
    for reg in [RAX, RBP, R9] {
        for base in [RAX, RBP, RSP, R12, R13] {
            for disp in [0i64, 8, -8] {
                cases.push(Case::fixed(
                    X86Opcode::Xchg,
                    X86InstOperands::rm(reg, base, disp),
                    vec![format!("xchg qword ptr {}, {}", mem(base, disp), n64(reg))],
                    format!("Xchg {},{}", mem(base, disp), n64(reg)),
                ));
            }
        }
    }
    // LOCK CMPXCHG rr + mem
    for dst in [RAX, RBX, RBP, R8, R13] {
        for src in [RCX, RSI, R9, R15] {
            cases.push(Case::fixed(
                X86Opcode::Cmpxchg,
                X86InstOperands::rr(dst, src),
                vec![format!("lock cmpxchg {}, {}", n64(dst), n64(src))],
                format!("Cmpxchg {},{}", n64(dst), n64(src)),
            ));
        }
    }
    for src in [RCX, R9] {
        for base in [RAX, RBP, RSP, R13] {
            for disp in [0i64, 8, -8] {
                cases.push(Case::fixed(
                    X86Opcode::Cmpxchg,
                    X86InstOperands::rm(src, base, disp),
                    vec![format!(
                        "lock cmpxchg qword ptr {}, {}",
                        mem(base, disp),
                        n64(src)
                    )],
                    format!("Cmpxchg {},{}", mem(base, disp), n64(src)),
                ));
            }
        }
    }
    for (op, ptr, name) in [
        (
            X86Opcode::Cmpxchg8,
            "byte ptr",
            n8 as fn(X86PReg) -> &'static str,
        ),
        (X86Opcode::Cmpxchg16, "word ptr", n16),
    ] {
        for src in [RCX, RSI, R9] {
            // No RAX base: the narrow-CAS encoder fail-closes any source/base
            // overlapping the fixed AL/AX accumulator (the CAS wrapper owns it).
            for base in [RBX, RBP, RSP, R13] {
                for disp in [0i64, 8, -8] {
                    cases.push(Case::fixed(
                        op,
                        X86InstOperands::rm(src, base, disp),
                        vec![format!(
                            "lock cmpxchg {ptr} {}, {}",
                            mem(base, disp),
                            name(src)
                        )],
                        format!("{op:?} {},{}", mem(base, disp), name(src)),
                    ));
                }
            }
        }
    }
    cases.push(Case::fixed(
        X86Opcode::Mfence,
        X86InstOperands::none(),
        vec!["mfence".to_string()],
        "Mfence".to_string(),
    ));
    cases.push(Case::fixed(
        X86Opcode::Ud2,
        X86InstOperands::none(),
        vec!["ud2".to_string()],
        "Ud2".to_string(),
    ));
    let (count, dis) = run_family(&d.path, "sync", cases, 0);
    assert_family_green("sync", count, dis);
}

// ---------------------------------------------------------------------------
// Negative controls
// ---------------------------------------------------------------------------

/// Mutation control: corrupt one ModRM bit of a known-good encoding and
/// assert the lane's comparison machinery FLAGS it. Proves the lane is not
/// vacuous (would catch a real misencoding of this shape).
#[test]
fn enc2_mutation_negative_control() {
    let Some(d) = objdump_or_skip("mutation") else {
        return;
    };

    let mut enc = X86Encoder::new();
    enc.encode_instruction(X86Opcode::AddRR, &X86InstOperands::rr(RAX, RBX))
        .expect("encode add rax, rbx");
    let mut bytes = enc.finish();
    let last = bytes.len() - 1;
    bytes[last] ^= 0x01; // ModRM rm bit flip: add rax,rbx -> add rcx,rbx

    let object = elf64_x86_object(&bytes);
    let rows = run_objdump(&d.path, &object, "mutation");
    assert!(!rows.is_empty(), "mutation control: nothing decoded");
    let (_, _, text) = &rows[0];
    let actual = canon(text);
    let expected = canon("add rax, rbx");
    assert_ne!(
        actual, expected,
        "mutation control FAILED: a flipped ModRM bit was NOT distinguished \
         by the comparison — the lane would be vacuous"
    );
    eprintln!(
        "ENC-2 [mutation]: control OK — corrupted byte decoded as '{text}', \
         which the lane distinguishes from 'add rax, rbx'"
    );
}

/// Determinism control: the same object disassembles identically twice.
#[test]
fn enc2_determinism_control() {
    let Some(d) = objdump_or_skip("determinism") else {
        return;
    };
    let mut enc = X86Encoder::new();
    for (op, ops) in [
        (X86Opcode::AddRR, X86InstOperands::rr(RAX, RBX)),
        (X86Opcode::MovRI, X86InstOperands::ri(RCX, 0x1234)),
        (X86Opcode::Lea, X86InstOperands::rm(RDX, RSP, 8)),
        (X86Opcode::Ret, X86InstOperands::none()),
    ] {
        enc.encode_instruction(op, &ops).expect("encode");
    }
    let object = elf64_x86_object(&enc.finish());
    let a = run_objdump(&d.path, &object, "det_a");
    let b = run_objdump(&d.path, &object, "det_b");
    assert_eq!(a, b, "objdump output not deterministic across replays");
}

/// Proof-only trap carriers and mask-extract pseudos must FAIL CLOSED at the
/// encoder (reaching the encoder means an expansion pass was skipped). This
/// pins that behavior — a carrier silently encoding to bytes would drop a
/// bounds/null/div-zero/shift-range check.
#[test]
fn enc2_fail_closed_pseudos_reject() {
    for op in [
        X86Opcode::TrapBoundsCheckExact,
        X86Opcode::TrapNullIfZeroExact,
        X86Opcode::TrapDivZeroExact,
        X86Opcode::TrapShiftRangeExact,
        X86Opcode::V4I32MaskExtract,
        X86Opcode::V16I8MaskExtract,
        X86Opcode::V8I16MaskExtract,
        X86Opcode::V2I64MaskExtract,
        X86Opcode::V128BoolSelect,
    ] {
        let mut enc = X86Encoder::new();
        let r = enc.encode_instruction(op, &X86InstOperands::rr(RAX, RBX));
        assert!(
            r.is_err(),
            "{op:?} must fail closed at the encoder, but it encoded to bytes"
        );
    }
}

// ---------------------------------------------------------------------------
// Lane inventory: EVERY X86Opcode variant is either covered by a family test
// above or explicitly skip-listed with a reason. NO wildcard arm — adding a
// new opcode to X86Opcode without classifying it here is a COMPILE ERROR
// (the emitted-opcode-inventory fail-closed pattern applied to this lane).
// ---------------------------------------------------------------------------

#[allow(dead_code)]
enum LaneStatus {
    Covered(&'static str),
    Skipped(&'static str),
}

#[allow(clippy::too_many_lines)]
fn lane_status(op: X86Opcode) -> LaneStatus {
    use LaneStatus::{Covered, Skipped};
    use X86Opcode as O;
    const SSE_FP: &str = "SSE scalar/packed FP — follow-up extension of this lane (same skeleton)";
    const SSE2_PACKED: &str =
        "SSE2 packed integer — follow-up extension of this lane (same skeleton)";
    const XMM_XFER: &str = "GPR<->XMM transfer — follow-up with the SSE extension";
    const PSEUDO_NO_BYTES: &str = "pseudo-instruction: encodes to zero bytes by design";
    const PSEUDO_FAIL_CLOSED: &str =
        "fail-closed pseudo: encoder rejects (pinned by enc2_fail_closed_pseudos_reject)";
    const PSEUDO_EXPANSION: &str = "pseudo multi-instruction expansion (CAS loop) — component opcodes covered; \
         sequence-level lane is a follow-up";
    const PADDING: &str = "alignment padding NOP (0F 1F multi-byte forms) — rendering varies by size; \
         covered by golden tests";
    match op {
        // alu
        O::AddRR
        | O::AddRI
        | O::AddRM
        | O::SubRR
        | O::SubRI
        | O::SubRM
        | O::AndRR
        | O::AndRI
        | O::OrRR
        | O::OrRI
        | O::XorRR
        | O::XorRI
        | O::Not
        | O::Neg
        | O::Inc
        | O::Dec
        | O::CmpRR
        | O::CmpRI
        | O::CmpRI8
        | O::CmpRM
        | O::TestRR
        | O::TestRI
        | O::TestRM
        | O::AdcRR
        | O::SbbRR => Covered("alu"),
        // mov
        O::MovRR
        | O::MovRR32
        | O::MovRI
        | O::MovRM8
        | O::MovRM16
        | O::MovRM32
        | O::MovRM
        | O::MovMR8
        | O::MovMR16
        | O::MovMR32
        | O::MovMR
        | O::VolatileMovRM8
        | O::VolatileMovRM16
        | O::VolatileMovRM32
        | O::VolatileMovRM
        | O::VolatileMovMR8
        | O::VolatileMovMR16
        | O::VolatileMovMR32
        | O::VolatileMovMR
        | O::Movzx
        | O::MovzxW
        | O::MovsxB
        | O::MovsxW
        | O::Movsx
        | O::MovRMSib
        | O::MovRM8Sib
        | O::MovsxdRMSib
        | O::MovMRSib
        | O::MovMR8Sib
        | O::MovRM32Sib
        | O::MovMR32Sib
        | O::MovRipRel
        | O::MovRipRelTlv => Covered("mov"),
        // branch
        O::Jmp | O::JmpR | O::Jcc | O::Call | O::CallR | O::CallM | O::Ret => Covered("branch"),
        // shift
        O::ShlRR | O::ShlRI | O::ShrRR | O::ShrRI | O::SarRR | O::SarRI | O::RolRI => {
            Covered("shift")
        }
        // mul / div
        O::ImulRR | O::ImulRRI | O::ImulRM | O::ImulRMSib | O::Mul => Covered("mul"),
        O::Idiv | O::Div | O::Cdq | O::Cqo => Covered("div"),
        // lea
        O::Lea | O::LeaSib | O::LeaRip => Covered("lea"),
        // setcc / cmov
        O::Setcc => Covered("setcc"),
        O::Cmovcc | O::Cmovcc32 => Covered("cmov"),
        // push/pop
        O::Push | O::Pop => Covered("pushpop"),
        // bit manipulation
        O::Bsf | O::Bsr | O::Tzcnt | O::Lzcnt | O::Popcnt | O::BtRI | O::Bswap => {
            Covered("bitmanip")
        }
        // sync / misc
        O::Xchg | O::Cmpxchg | O::Cmpxchg8 | O::Cmpxchg16 | O::Mfence | O::Ud2 => Covered("sync"),

        // ---- skip-listed with reasons ----
        O::Addsd
        | O::Subsd
        | O::Mulsd
        | O::Divsd
        | O::Sqrtsd
        | O::Andpd
        | O::MovsdRR
        | O::MovsdRM
        | O::MovsdMR
        // Scaled-index scalar-FP loads: same SSE_FP follow-up lane as the plain
        // MovsdRM/MovssRM forms they extend.
        | O::MovsdRMSib
        | O::MovssRMSib
        | O::Ucomisd
        | O::MovdquRM
        | O::MovdquMR
        | O::Addss
        | O::Subss
        | O::Mulss
        | O::Divss
        | O::Sqrtss
        | O::Andps
        | O::MovssRR
        | O::MovssRM
        | O::MovssMR
        | O::Ucomiss
        | O::Roundsd
        | O::Roundss
        | O::Minsd
        | O::Maxsd
        | O::Minss
        | O::Maxss
        | O::Cmpsd
        | O::Cmpss
        | O::MovssRipRel
        | O::MovsdRipRel
        | O::VolatileMovssRM
        | O::VolatileMovssMR
        | O::VolatileMovsdRM
        | O::VolatileMovsdMR
        | O::Cvtsi2sd
        | O::Cvtsd2si
        | O::Cvtsi2ss
        | O::Cvtss2si
        | O::Cvtsd2ss
        | O::Cvtss2sd
        | O::Cvttsd2si
        | O::Cvttss2si
        | O::Addps
        | O::Subps
        | O::Mulps
        | O::Divps
        | O::Addpd
        | O::Subpd
        | O::Mulpd
        | O::Divpd => Skipped(SSE_FP),
        O::Pand
        | O::Pandn
        | O::Por
        | O::Pxor
        | O::Pcmpeqd
        | O::Pshufd
        | O::Pmovmskb
        | O::MovdqaRR
        | O::Pcmpgtd
        | O::MovdqaRM
        | O::MovdqaMR
        | O::VolatileMovdquRM
        | O::VolatileMovdquMR
        | O::VolatileMovdqaRM
        | O::VolatileMovdqaMR
        | O::Paddd
        | O::Psubd
        | O::Punpckldq
        | O::Punpcklqdq
        | O::Paddq
        | O::Psubq
        | O::Paddb
        | O::Paddw
        | O::Psubb
        | O::Psubw
        | O::Pinsrd
        | O::Pextrd
        | O::Pmulld
        | O::Pcmpeqq
        | O::Pcmpgtq
        | O::Ptest
        | O::Pinsrq
        | O::Pextrq
        | O::Pblendvb
        | O::Pmuludq
        | O::Pmullw
        | O::Pcmpeqb
        | O::Pcmpeqw
        | O::Pcmpgtb
        | O::Pcmpgtw
        | O::Pslld
        | O::Psrld
        | O::Psrad
        | O::Psllq
        | O::Psrlq
        | O::Punpcklbw
        | O::Punpckhbw
        | O::Packuswb
        | O::Psadbw => Skipped(SSE2_PACKED),
        O::MovdToXmm | O::MovdFromXmm | O::MovqToXmm | O::MovqFromXmm => Skipped(XMM_XFER),
        O::Phi | O::StackAlloc | O::Nop => Skipped(PSEUDO_NO_BYTES),
        O::NopMulti => Skipped(PADDING),
        O::V4I32MaskExtract
        | O::V16I8MaskExtract
        | O::V8I16MaskExtract
        | O::V2I64MaskExtract
        | O::V128BoolSelect
        | O::TrapBoundsCheckExact
        | O::TrapNullIfZeroExact
        | O::TrapDivZeroExact
        | O::TrapShiftRangeExact => Skipped(PSEUDO_FAIL_CLOSED),
        O::AtomicRmwCasLoop | O::AtomicRmwCasLoop8 | O::AtomicRmwCasLoop16 => {
            Skipped(PSEUDO_EXPANSION)
        }
    }
}

/// Prints the lane inventory (coverage/skip table). The real enforcement is
/// the exhaustive match in `lane_status` (compile error on a new opcode).
#[test]
fn enc2_lane_inventory() {
    // Representative probe of one opcode per covered family, so the table has
    // a live row per family; the per-family instance counts are printed by
    // the family tests themselves.
    let probes = [
        X86Opcode::AddRR,
        X86Opcode::MovRR,
        X86Opcode::Jmp,
        X86Opcode::ShlRI,
        X86Opcode::ImulRR,
        X86Opcode::Idiv,
        X86Opcode::Lea,
        X86Opcode::Setcc,
        X86Opcode::Cmovcc,
        X86Opcode::Push,
        X86Opcode::Popcnt,
        X86Opcode::Cmpxchg,
    ];
    for p in probes {
        match lane_status(p) {
            LaneStatus::Covered(fam) => eprintln!("ENC-2 inventory: {p:?} -> covered [{fam}]"),
            LaneStatus::Skipped(r) => {
                panic!("ENC-2 inventory: probe {p:?} unexpectedly skip-listed: {r}")
            }
        }
    }
    eprintln!(
        "ENC-2 inventory: every X86Opcode variant is classified in lane_status() \
         (exhaustive match — a NEW opcode without a lane entry fails this test's build)."
    );
}
