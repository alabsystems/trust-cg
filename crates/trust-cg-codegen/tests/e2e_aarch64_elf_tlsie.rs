// trust-cg-codegen/tests/e2e_aarch64_elf_tlsie.rs - AArch64 ELF initial-exec
// TLS object emission, byte-golden against gcc ground truth.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// Ground truth (Debian aarch64 container, 2026-07-17):
//
//   $ cat tls_ie.c
//   extern __thread long x __attribute__((tls_model("initial-exec")));
//   long *addr_of_x(void) { return &x; }
//   $ gcc -O1 -c tls_ie.c && objdump -dr tls_ie.o
//   0:  90000000  adrp  x0, 0        R_AARCH64_TLSIE_ADR_GOTTPREL_PAGE21   x
//   4:  f9400000  ldr   x0, [x0]     R_AARCH64_TLSIE_LD64_GOTTPREL_LO12_NC x
//   8:  d53bd041  mrs   x1, tpidr_el0
//   c:  8b000020  add   x0, x1, x0
//
// EXECUTION-VERIFIED (same container, same date): the trust-cg-emitted object
// below, linked with (a) a gcc driver defining the thread-local — GNU ld
// RELAXED the pair IE->LE (adrp->movz, ldr->movk), i.e. ld's own
// pattern-matcher recognized the canonical instruction forms — and (b) a
// shared library defining it — UNRELAXED: the linker created the GOT slot
// (dynamic `R_AARCH64_TLS_TPREL64`), patched the ADRP page + 8-scaled LDR
// imm12, and the probe verified per-thread addresses/values across two
// threads. Both drivers ran to EXIT=0.
//
// This test pins the RELOCATABLE-OBJECT half of that evidence so it can run
// in CI without a Linux box: the .text skeleton words and the .rela.text
// relocation types/offsets/target must match the gcc ground truth exactly.

use trust_cg_codegen::pipeline::{ObjectGlobal, OptLevel, Pipeline, PipelineConfig};
use trust_cg_ir::TlsModel;
use trust_cg_lower::function::{BasicBlock, Function as LowerFunction, Signature};
use trust_cg_lower::instructions::{Block, Instruction, Opcode, Value};
use trust_cg_lower::types::Type as LowerType;

const R_AARCH64_TLSIE_ADR_GOTTPREL_PAGE21: u32 = 0x21d;
const R_AARCH64_TLSIE_LD64_GOTTPREL_LO12_NC: u32 = 0x21e;
const STT_TLS: u8 = 6;

/// Build the IE probe object: one function returning `&tls_probe_var` with
/// `TlsModel::InitialExec`, the thread-local itself an import (defined in
/// another object — the cross-object shape that cannot use local-exec).
fn emit_tlsie_object() -> Vec<u8> {
    let mut func = LowerFunction::new(
        "trust_cg_tls_ie_addr".to_string(),
        Signature {
            params: vec![],
            returns: vec![LowerType::I64],
        },
    );
    func.entry_block = Block(0);
    func.block_order = vec![Block(0)];
    func.blocks.insert(
        Block(0),
        BasicBlock {
            params: vec![],
            instructions: vec![
                Instruction {
                    opcode: Opcode::TlsRef {
                        name: "tls_probe_var".to_string(),
                        model: TlsModel::InitialExec,
                        local_exec_offset: None,
                    },
                    args: vec![],
                    results: vec![Value(0)],
                },
                Instruction {
                    opcode: Opcode::Return,
                    args: vec![Value(0)],
                    results: vec![],
                },
            ],
            source_locs: vec![],
        },
    );

    let pipeline = Pipeline::new(PipelineConfig {
        target_triple: "aarch64-unknown-linux-gnu".to_string(),
        opt_level: OptLevel::O0,
        ..PipelineConfig::default()
    });

    // prepare_function runs the FULL pipeline (isel + regalloc + frame
    // lowering) — this is also the regression guard for the regalloc opcode
    // round-trip sentinel (`regalloc_opcode_to_ir` MAX_AARCH64_OPCODE), which
    // failed closed on `LdrGottprel` until it was bumped to the new last
    // variant.
    let prepared = pipeline.prepare_function(&func).expect("prepare");
    let globals = vec![ObjectGlobal {
        name: "tls_probe_var".to_string(),
        data: vec![],
        mutable: true,
        is_external: true,
        symbol_refs: vec![],
        is_thread_local: true,
        is_import: true,
        is_weak: false,
        align: 8,
    }];
    pipeline
        .compile_module_with_globals(&[prepared], &globals)
        .expect("compile ELF object with TLSIE fixups")
}

// --- minimal ELF64 little-endian reader (fixed trusted test input) ---------

fn u16le(b: &[u8], off: usize) -> u16 {
    u16::from_le_bytes([b[off], b[off + 1]])
}
fn u32le(b: &[u8], off: usize) -> u32 {
    u32::from_le_bytes([b[off], b[off + 1], b[off + 2], b[off + 3]])
}
fn u64le(b: &[u8], off: usize) -> u64 {
    u64::from_le_bytes(b[off..off + 8].try_into().unwrap())
}

struct Section {
    name: String,
    sh_type: u32,
    offset: usize,
    size: usize,
    link: u32,
    entsize: usize,
}

fn parse_sections(obj: &[u8]) -> Vec<Section> {
    assert_eq!(&obj[..4], b"\x7fELF", "not an ELF object");
    let shoff = u64le(obj, 0x28) as usize;
    let shentsize = u16le(obj, 0x3a) as usize;
    let shnum = u16le(obj, 0x3c) as usize;
    let shstrndx = u16le(obj, 0x3e) as usize;

    let strtab_hdr = shoff + shstrndx * shentsize;
    let shstr_off = u64le(obj, strtab_hdr + 0x18) as usize;

    (0..shnum)
        .map(|i| {
            let hdr = shoff + i * shentsize;
            let name_off = shstr_off + u32le(obj, hdr) as usize;
            let name_end = obj[name_off..].iter().position(|&c| c == 0).unwrap() + name_off;
            Section {
                name: String::from_utf8_lossy(&obj[name_off..name_end]).into_owned(),
                sh_type: u32le(obj, hdr + 4),
                offset: u64le(obj, hdr + 0x18) as usize,
                size: u64le(obj, hdr + 0x20) as usize,
                link: u32le(obj, hdr + 0x28),
                entsize: u64le(obj, hdr + 0x38) as usize,
            }
        })
        .collect()
}

fn find<'a>(sections: &'a [Section], name: &str) -> &'a Section {
    sections
        .iter()
        .find(|s| s.name == name)
        .unwrap_or_else(|| panic!("section {name} missing"))
}

/// The relocatable-object half of the execution-verified TLSIE evidence:
/// .text carries the gcc-canonical ADRP/LDR/MRS/ADD skeleton and .rela.text
/// carries exactly the TLSIE relocation pair against the undefined STT_TLS
/// import.
#[test]
fn tlsie_object_matches_gcc_ground_truth() {
    let obj = emit_tlsie_object();
    let sections = parse_sections(&obj);

    // --- .text skeleton words ---
    let text = find(&sections, ".text");
    let words: Vec<u32> = obj[text.offset..text.offset + text.size]
        .chunks_exact(4)
        .map(|c| u32::from_le_bytes(c.try_into().unwrap()))
        .collect();
    assert!(words.len() >= 4, "IE sequence needs at least 4 words");

    // [0] ADRP Xd, #0 placeholder (gcc: 90000000). op|immlo|10000|immhi|Rd,
    // imm MUST be the zero placeholder (the linker owns the page delta).
    let adrp = words[0];
    assert_eq!(
        adrp & 0x9FFF_FFE0,
        0x9000_0000,
        "word0 must be an ADRP with zero placeholder immediate: {adrp:#010x}"
    );
    let adrp_rd = adrp & 0x1F;

    // [1] LDR Xt, [Xn, #0] 64-bit unsigned-offset placeholder (gcc:
    // f9400000), base register = the ADRP destination (TLSIE pairing).
    let ldr = words[1];
    assert_eq!(
        ldr & 0xFFFF_FC00,
        0xF940_0000,
        "word1 must be LDR64-ui with zero placeholder imm12: {ldr:#010x}"
    );
    assert_eq!(
        (ldr >> 5) & 0x1F,
        adrp_rd,
        "LDR base must be the paired ADRP destination"
    );

    // [2] MRS Xt, TPIDR_EL0 (gcc: d53bd041 for x1).
    let mrs = words[2];
    assert_eq!(
        mrs & 0xFFFF_FFE0,
        0xD53B_D040,
        "word2 must be MRS Xt, TPIDR_EL0: {mrs:#010x}"
    );

    // [3] ADD Xd, Xn, Xm (gcc: 8b000020) — TP + TPREL.
    let add = words[3];
    assert_eq!(
        add & 0xFFE0_FC00,
        0x8B00_0000,
        "word3 must be ADD (shifted register, LSL #0): {add:#010x}"
    );

    // --- .rela.text: exactly the TLSIE pair at offsets 0 and 4 ---
    let rela = find(&sections, ".rela.text");
    assert_eq!(rela.entsize, 24);
    let n = rela.size / 24;
    assert_eq!(n, 2, "IE read must emit exactly 2 text relocations");
    let mut entries = Vec::new();
    for i in 0..n {
        let e = rela.offset + i * 24;
        let r_offset = u64le(&obj, e);
        let r_info = u64le(&obj, e + 8);
        let r_addend = u64le(&obj, e + 16);
        entries.push((
            r_offset,
            (r_info & 0xFFFF_FFFF) as u32,
            r_info >> 32,
            r_addend,
        ));
    }
    entries.sort();
    assert_eq!(
        (entries[0].0, entries[0].1, entries[0].3),
        (0, R_AARCH64_TLSIE_ADR_GOTTPREL_PAGE21, 0),
        "ADRP must carry R_AARCH64_TLSIE_ADR_GOTTPREL_PAGE21 at offset 0"
    );
    assert_eq!(
        (entries[1].0, entries[1].1, entries[1].3),
        (4, R_AARCH64_TLSIE_LD64_GOTTPREL_LO12_NC, 0),
        "LDR must carry R_AARCH64_TLSIE_LD64_GOTTPREL_LO12_NC at offset 4"
    );
    assert_eq!(
        entries[0].2, entries[1].2,
        "both relocations must target the same symbol"
    );

    // --- the target symbol is the undefined STT_TLS import ---
    let symtab = find(&sections, ".symtab");
    assert_eq!(symtab.sh_type, 2 /* SHT_SYMTAB */);
    let strtab = &sections[symtab.link as usize];
    let sym_index = entries[0].2 as usize;
    let sym = symtab.offset + sym_index * 24;
    let name_off = strtab.offset + u32le(&obj, sym) as usize;
    let name_end = obj[name_off..].iter().position(|&c| c == 0).unwrap() + name_off;
    let name = &obj[name_off..name_end];
    assert_eq!(name, b"tls_probe_var", "relocation target symbol name");
    let st_info = obj[sym + 4];
    assert_eq!(
        st_info & 0xF,
        STT_TLS,
        "TLSIE relocation target must be STT_TLS (link-time kind match)"
    );
    let st_shndx = u16le(&obj, sym + 6);
    assert_eq!(st_shndx, 0 /* SHN_UNDEF */, "import must be undefined");
}
