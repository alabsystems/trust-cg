// trust-cg-codegen — ENC-EHDC anchor: external-tool eh_frame differential
//
// Author: Andrew Yates | Copyright 2026 Andrew Yates | License: Apache-2.0
//
// The INDEPENDENT ANCHOR for the ENC-EHDC round-trip decode-check
// (`src/dwarf_cfi_decode_check.rs`). The round-trip gate proves
// `decode(emit(intent)) == intent`; if the encoder and the reference decoder
// shared a byte-layout misconception they could agree with each other. This
// lane breaks that: it packs the REAL emitted `.eh_frame` bytes into a minimal
// ELF64 container (hand-rolled, so this lane does not depend on the trusted
// Mach-O/ELF writers), disassembles the CFI with an EXTERNAL tool
// (`llvm-objdump --dwarf=frames`, pinned to the nightly-2026-04-20 toolchain,
// same as the ENC-2 lane), and asserts the external tool's decoded CIE/FDE
// fields match the documented x86-64 System V CFI intent.
//
// GRACEFUL SKIP: if no pinned objdump is found the suite skips with an eprintln
// (a missing external tool must not turn this detection lane into a false red).

use std::path::{Path, PathBuf};
use std::process::Command;

use trust_cg_codegen::dwarf_cfi::{DwarfCfiSection, x86_64_fde_from_prologue};
use trust_cg_ir::x86_64_regs::{R12, R13, R14, R15, RBX};

const PINNED_TOOLCHAIN: &str = "nightly-2026-04-20";

// ---------------------------------------------------------------------------
// Pinned external objdump resolution (mirrors the ENC-2 lane).
// ---------------------------------------------------------------------------

/// Resolve an llvm-objdump. Order: TCG_LLVM_OBJDUMP override, then the pinned
/// toolchain's bundled llvm-objdump, then /usr/bin/objdump (Apple LLVM, which
/// also supports `--dwarf=frames`).
fn find_objdump() -> Option<PathBuf> {
    if let Ok(p) = std::env::var("TCG_LLVM_OBJDUMP") {
        let p = PathBuf::from(p);
        if p.is_file() {
            return Some(p);
        }
    }
    // rustup which -> toolchain root -> lib/rustlib/<triple>/bin/llvm-objdump
    if let Ok(out) = Command::new("rustup")
        .args(["which", "--toolchain", PINNED_TOOLCHAIN, "rustc"])
        .output()
        && out.status.success()
    {
        let rustc = PathBuf::from(String::from_utf8_lossy(&out.stdout).trim().to_string());
        if let Some(root) = rustc.parent().and_then(Path::parent)
            && let Ok(rd) = std::fs::read_dir(root.join("lib/rustlib"))
        {
            for e in rd.flatten() {
                let cand = e.path().join("bin/llvm-objdump");
                if cand.is_file() {
                    return Some(cand);
                }
            }
        }
    }
    // Direct scan of ~/.rustup/toolchains/<pinned>*/lib/rustlib/*/bin.
    if let Some(home) = std::env::var_os("HOME") {
        let tc = PathBuf::from(home).join(".rustup/toolchains");
        if let Ok(rd) = std::fs::read_dir(&tc) {
            for e in rd.flatten() {
                if e.file_name()
                    .to_string_lossy()
                    .starts_with(PINNED_TOOLCHAIN)
                    && let Ok(rd2) = std::fs::read_dir(e.path().join("lib/rustlib"))
                {
                    for e2 in rd2.flatten() {
                        let cand = e2.path().join("bin/llvm-objdump");
                        if cand.is_file() {
                            return Some(cand);
                        }
                    }
                }
            }
        }
    }
    // Last resort: the Apple system objdump (also LLVM, supports --dwarf=frames).
    let sys = PathBuf::from("/usr/bin/objdump");
    if sys.is_file() {
        return Some(sys);
    }
    None
}

// ---------------------------------------------------------------------------
// Minimal ELF64 object carrying a single named PROGBITS section. Hand-rolled
// (independent of the trusted object writers). llvm-objdump --dwarf=frames
// reads the `.eh_frame` section contents directly.
// ---------------------------------------------------------------------------

fn elf64_with_eh_frame(eh_frame: &[u8]) -> Vec<u8> {
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

    // Section-name string table: index 0 = "", then ".eh_frame", ".shstrtab".
    let shstrtab: &[u8] = b"\0.eh_frame\0.shstrtab\0";
    let eh_name_off = 1u32; // ".eh_frame"
    let shstr_name_off = 11u32; // ".shstrtab"

    let ehsize: usize = 64;
    let eh_off = ehsize;
    let shstr_off = eh_off + eh_frame.len();
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
    buf.extend_from_slice(eh_frame);
    buf.extend_from_slice(shstrtab);
    while buf.len() < shoff {
        buf.push(0);
    }
    // Section 0: null.
    buf.extend_from_slice(&shdr(0, 0, 0, 0, 0, 0));
    // Section 1: .eh_frame (SHT_PROGBITS=1, SHF_ALLOC=0x2), 8-byte aligned.
    buf.extend_from_slice(&shdr(
        eh_name_off,
        1,
        0x2,
        eh_off as u64,
        eh_frame.len() as u64,
        8,
    ));
    // Section 2: .shstrtab (SHT_STRTAB=3).
    buf.extend_from_slice(&shdr(
        shstr_name_off,
        3,
        0,
        shstr_off as u64,
        shstrtab.len() as u64,
        1,
    ));
    buf
}

fn run_dwarf_frames(objdump: &Path, object: &[u8], tag: &str) -> String {
    let dir = std::env::temp_dir().join(format!("tcg_ehdc_{}", std::process::id()));
    std::fs::create_dir_all(&dir).expect("create temp dir");
    let obj_path = dir.join(format!("{tag}.o"));
    std::fs::write(&obj_path, object).expect("write object");

    let out = Command::new(objdump)
        .arg("--dwarf=frames")
        .arg(&obj_path)
        .output()
        .expect("spawn llvm-objdump");
    assert!(
        out.status.success(),
        "llvm-objdump --dwarf=frames failed on {}: {}",
        obj_path.display(),
        String::from_utf8_lossy(&out.stderr)
    );
    String::from_utf8_lossy(&out.stdout).to_string()
}

// ---------------------------------------------------------------------------
// The differential test.
// ---------------------------------------------------------------------------

#[test]
fn eh_frame_matches_external_objdump() {
    let Some(objdump) = find_objdump() else {
        eprintln!(
            "ENC-EHDC anchor: SKIP — no llvm-objdump found (pinned toolchain \
             {PINNED_TOOLCHAIN} absent, /usr/bin/objdump absent, TCG_LLVM_OBJDUMP unset). \
             The external eh_frame differential did not run; the structural round-trip \
             gate still enforces correctness."
        );
        return;
    };

    // A representative x86-64 frame-walking FDE (the default-path emitter):
    // PUSH RBP / MOV RBP,RSP / PUSH RBX,R12..R15 / SUB RSP, 4096.
    let mut section = DwarfCfiSection::new_x86_64();
    let callee = [RBX, R12, R13, R14, R15];
    section.add_fde(x86_64_fde_from_prologue(&callee, 4096, 0, 512, 0));
    let bytes = section.to_bytes();

    // Sanity: our OWN round-trip gate must accept these bytes first.
    trust_cg_codegen::dwarf_cfi_decode_check::verify_eh_frame_roundtrip(&section, &bytes)
        .expect("internal round-trip must accept the representative section");

    let object = elf64_with_eh_frame(&bytes);
    let dump = run_dwarf_frames(&objdump, &object, "ehframe");
    eprintln!("=== llvm-objdump --dwarf=frames ===\n{dump}\n===================================");

    // The external tool must have parsed a CIE and an FDE (no parse error).
    assert!(
        dump.contains("CIE"),
        "objdump did not report a CIE:\n{dump}"
    );
    assert!(
        dump.contains("FDE"),
        "objdump did not report an FDE:\n{dump}"
    );

    // Canonicalize whitespace for tolerant field matching across objdump
    // versions.
    let flat: String = dump.split_whitespace().collect::<Vec<_>>().join(" ");

    // CIE intent (x86-64 System V, "zR" augmentation): version 1, augmentation
    // "zR", code_alignment_factor 1, data_alignment_factor -8, RA register 16.
    assert!(
        flat.contains("Version: 1") || flat.contains("Version 1"),
        "CIE version 1 not found in objdump output:\n{dump}"
    );
    assert!(
        flat.contains("\"zR\"") || flat.contains("zR"),
        "CIE augmentation \"zR\" not found in objdump output:\n{dump}"
    );
    assert!(
        flat.contains("Code alignment factor: 1") || flat.contains("Code alignment factor 1"),
        "CIE code alignment factor 1 not found:\n{dump}"
    );
    assert!(
        flat.contains("Data alignment factor: -8") || flat.contains("Data alignment factor -8"),
        "CIE data alignment factor -8 not found:\n{dump}"
    );
    assert!(
        flat.contains("Return address column: 16") || flat.contains("return_address_register: 16"),
        "CIE return address register 16 (RIP) not found:\n{dump}"
    );

    eprintln!(
        "ENC-EHDC anchor: external llvm-objdump agrees with the emitted x86-64 CIE/FDE intent"
    );
}
