// trust-cg-codegen/tests/e2e_aarch64_elf_tlsie.rs - AArch64 ELF initial-exec
// TLS object emission, checked against a retained gcc instruction golden.
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
// Historical execution report (same container, same date): the trust-cg-emitted object
// below, linked with (a) a gcc driver defining the thread-local — GNU ld
// RELAXED the pair IE->LE (adrp->movz, ldr->movk), i.e. ld's own
// pattern-matcher recognized the canonical instruction forms — and (b) a
// shared library defining it — UNRELAXED: the linker created the GOT slot
// (dynamic `R_AARCH64_TLS_TPREL64`), patched the ADRP page + 8-scaled LDR
// imm12, and the probe verified per-thread addresses/values across two
// threads. Both drivers ran to EXIT=0.
//
// The object test runs on every host. On Linux AArch64, the native tests also
// link and execute both relaxed and shared-provider initial-exec references,
// and cross-object local-exec references including a nonzero high12 offset,
// checking the address and independent values in three live threads at O0-O3.
// A shared-object control checks that local-exec objects are refused by name
// (by the host linker's classified diagnostic and by the link driver) and
// that initial-exec objects link `-shared`.
// Executable-side controls check that a local-exec import of a thread-local a
// shared library defines fails with the classified TLS-model mismatch (both
// GNU ld forms). The `-Wl` spellings GNU ld reads as `--shared` are refused
// before anything runs, and a shared object that a `cc -shared` driver
// writes for an executable request is refused at the driver's staging path
// when it would carry local-exec TLS, leaving the requested output as it
// was.

use trust_cg_codegen::pipeline::{ObjectGlobal, OptLevel, Pipeline, PipelineConfig};
use trust_cg_ir::TlsModel;
use trust_cg_lower::function::{BasicBlock, Function as LowerFunction, Signature};
use trust_cg_lower::instructions::{Block, Instruction, Opcode, Value};
use trust_cg_lower::types::Type as LowerType;

const R_AARCH64_TLSIE_ADR_GOTTPREL_PAGE21: u32 = 0x21d;
const R_AARCH64_TLSIE_LD64_GOTTPREL_LO12_NC: u32 = 0x21e;
const R_AARCH64_TLSLE_ADD_TPREL_HI12: u32 = 0x225;
const R_AARCH64_TLSLE_ADD_TPREL_LO12_NC: u32 = 0x227;
const STT_TLS: u8 = 6;

/// Build the IE probe object: one function returning `&tls_probe_var` with
/// `TlsModel::InitialExec`, the thread-local itself an import (defined in
/// another object or a startup-loaded shared library).
fn emit_tlsie_object(opt_level: OptLevel) -> Vec<u8> {
    emit_tls_object(opt_level, TlsModel::InitialExec)
}

fn emit_tls_object(opt_level: OptLevel, model: TlsModel) -> Vec<u8> {
    let func = tls_addr_function("trust_cg_tls_ie_addr", "tls_probe_var", model);
    let pipeline = Pipeline::new(PipelineConfig {
        target_triple: "aarch64-unknown-linux-gnu".to_string(),
        opt_level,
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
        visibility: trust_ir::Visibility::Default,
        retained: false,
        section: None,
        comdat: false,
    }];
    pipeline
        .compile_module_with_globals(&[prepared], &globals)
        .expect("compile ELF object with TLS fixups")
}

fn tls_addr_function(name: &str, symbol: &str, model: TlsModel) -> LowerFunction {
    let mut func = LowerFunction::new(
        name.to_owned(),
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
                        name: symbol.to_owned(),
                        model,
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

    func
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

fn assert_tlsie_sequence(text_words: &[u32], byte_offset: u64) {
    assert_eq!(byte_offset % 4, 0, "TLSIE site must be instruction-aligned");
    let start = usize::try_from(byte_offset / 4).expect("TLSIE site fits host usize");
    let words = text_words
        .get(start..)
        .and_then(|tail| tail.get(..4))
        .expect("TLSIE relocation must identify four complete instructions");
    // [0] ADRP Xd, #0 placeholder (gcc: 90000000). op|immlo|10000|immhi|Rd,
    // imm MUST be the zero placeholder (the linker owns the page delta).
    let adrp = words[0];
    assert_eq!(
        adrp & 0xFFFF_FFE0,
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
    let offset_reg = ldr & 0x1F;
    let thread_reg = mrs & 0x1F;
    assert_ne!(
        offset_reg, thread_reg,
        "MRS must not overwrite the TLS offset"
    );
    assert_ne!(adrp_rd, 31, "ADRP must not discard the GOT page");
    assert_ne!(offset_reg, 31, "LDR must not discard the TLS offset");
    assert_ne!(thread_reg, 31, "MRS must not discard the thread pointer");
    assert_ne!(add & 0x1F, 31, "ADD must not discard the TLS address");
    assert_eq!(
        (add >> 5) & 0x1F,
        thread_reg,
        "ADD must consume the thread pointer"
    );
    assert_eq!(
        (add >> 16) & 0x1F,
        offset_reg,
        "ADD must consume the TLS offset"
    );
}

/// Check the current relocatable object, not a Linux execution result.
#[test]
fn tlsie_object_matches_gcc_ground_truth() {
    let obj = emit_tlsie_object(OptLevel::O0);
    let sections = parse_sections(&obj);
    let text = find(&sections, ".text");
    assert_eq!(
        text.size % 4,
        0,
        "AArch64 text contains complete instructions"
    );
    let words: Vec<u32> = obj[text.offset..text.offset + text.size]
        .as_chunks::<4>()
        .0
        .iter()
        .map(|c| u32::from_le_bytes(*c))
        .collect();

    // Exactly two adjacent TLSIE relocations, independent of frame size.
    let rela = find(&sections, ".rela.text");
    assert_eq!(rela.entsize, 24);
    assert_eq!(rela.size % 24, 0, "complete ELF64 Rela entries");
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
        (entries[0].1, entries[0].3),
        (R_AARCH64_TLSIE_ADR_GOTTPREL_PAGE21, 0),
        "ADRP must carry the TLSIE page relocation with a zero addend"
    );
    assert_eq!(
        (entries[1].1, entries[1].3),
        (R_AARCH64_TLSIE_LD64_GOTTPREL_LO12_NC, 0),
        "LDR must carry the TLSIE low relocation with a zero addend"
    );
    assert_eq!(
        entries[0].0.checked_add(4),
        Some(entries[1].0),
        "TLSIE relocation pair must be adjacent"
    );
    assert_tlsie_sequence(&words, entries[0].0);
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

/// Independent instruction/relocation interpretation for our fixed-size ELF
/// fixture. This does not use production relocation enums or encoder helpers.
fn validate_tlsle_object(obj: &[u8]) -> Result<(), &'static str> {
    let sections = parse_sections(obj);
    let text = find(&sections, ".text");
    let words: Vec<u32> = obj[text.offset..text.offset + text.size]
        .as_chunks::<4>()
        .0
        .iter()
        .map(|c| u32::from_le_bytes(*c))
        .collect();
    let sequence = words
        .windows(3)
        .position(|w| w[0] & 0xffff_ffe0 == 0xd53b_d040)
        .ok_or("missing TPIDR_EL0 read")?;
    let dst = words[sequence] & 31;
    if dst == 31 {
        // MRS discards a write to XZR, while the ADD-immediate form interprets
        // register 31 as SP. Equal encodings would not imply equal values.
        return Err("TPIDR_EL0 read must not discard its result into XZR");
    }
    // Each ADD must read/write the same TP-derived register; the linker owns
    // both zero placeholders. In particular, HI12 must really have LSL #12.
    let hi = 0x9140_0000 | dst << 5 | dst;
    let lo = 0x9100_0000 | dst << 5 | dst;
    if words[sequence + 1..sequence + 3] != [hi, lo] {
        return Err("wrong LE instruction, shift, immediate or register flow");
    }
    let rela = find(&sections, ".rela.text");
    if rela.entsize != 24 || rela.size != 48 {
        return Err("LE read must have exactly two relocations");
    }
    let mut entries: Vec<_> = (0..2)
        .map(|i| {
            let e = rela.offset + i * 24;
            (u64le(obj, e), u64le(obj, e + 8), u64le(obj, e + 16))
        })
        .collect();
    entries.sort();
    for (entry, (word, kind)) in entries.iter().zip([
        (sequence + 1, R_AARCH64_TLSLE_ADD_TPREL_HI12),
        (sequence + 2, R_AARCH64_TLSLE_ADD_TPREL_LO12_NC),
    ]) {
        if entry.0 != (word * 4) as u64 || entry.1 as u32 != kind || entry.2 != 0 {
            return Err("wrong LE relocation offset, kind or addend");
        }
    }
    if entries[0].1 >> 32 != entries[1].1 >> 32 {
        return Err("LE relocation symbols disagree");
    }
    let symtab = find(&sections, ".symtab");
    let symbol = symtab.offset + ((entries[0].1 >> 32) as usize) * 24;
    if obj[symbol + 4] & 15 != STT_TLS || u16le(obj, symbol + 6) != 0 {
        return Err("LE relocation must name an undefined TLS import");
    }
    let strtab = &sections[symtab.link as usize];
    let name = strtab.offset + u32le(obj, symbol) as usize;
    if !obj[name..].starts_with(b"tls_probe_var\0") {
        return Err("wrong LE symbol name");
    }
    Ok(())
}

#[test]
fn tlsle_object_has_exact_linker_owned_tprel_pair_and_mutations_reject() {
    for opt in [OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::O3] {
        let obj = emit_tls_object(opt, TlsModel::LocalExec);
        assert_eq!(validate_tlsle_object(&obj), Ok(()), "{opt:?}");
        let sections = parse_sections(&obj);
        let text = find(&sections, ".text");
        let rela = find(&sections, ".rela.text");
        let symtab = find(&sections, ".symtab");
        let first_instruction = text.offset + u64le(&obj, rela.offset) as usize;
        let symbol = symtab.offset + ((u64le(&obj, rela.offset + 8) >> 32) as usize) * 24;
        let strtab = &sections[symtab.link as usize];
        let name = strtab.offset + u32le(&obj, symbol) as usize;
        // Fixed-size mutations preserve a readable ELF fixture, so rejection
        // must concern the instruction/relocation contract, not parser failure.
        for (label, offset, mask) in [
            ("hi12 shift", first_instruction + 2, 0x40),
            ("relocation offset", rela.offset, 4),
            ("relocation kind", rela.offset + 8, 1),
            ("relocation addend", rela.offset + 16, 1),
            ("symbol type", symbol + 4, 1),
            ("symbol name", name, 1),
        ] {
            let mut corrupt = obj.clone();
            corrupt[offset] ^= mask;
            assert!(validate_tlsle_object(&corrupt).is_err(), "{opt:?} {label}");
        }
        let mut corrupt = obj.clone();
        for (offset, word) in [
            (first_instruction - 4, 0xd53b_d05fu32),
            (first_instruction, 0x9140_03ff),
            (first_instruction + 4, 0x9100_03ff),
        ] {
            corrupt[offset..offset + 4].copy_from_slice(&word.to_le_bytes());
        }
        assert!(
            validate_tlsle_object(&corrupt).is_err(),
            "{opt:?} coordinated XZR/SP substitution must reject"
        );
    }
}

#[cfg(all(target_arch = "aarch64", target_os = "linux", target_env = "gnu"))]
#[path = "common/rosetta.rs"]
mod native_process;

#[path = "common/fresh_dir.rs"]
mod fresh_dir;

#[cfg(all(target_arch = "aarch64", target_os = "linux", target_env = "gnu"))]
mod native {
    use super::{
        ObjectGlobal, OptLevel, Pipeline, PipelineConfig, TlsModel, emit_tls_object,
        native_process, tls_addr_function,
    };
    use std::fs;
    use std::process::Command;
    use std::time::Duration;

    const PROVIDER: &str = r#"
__thread long tls_probe_var = 19;
long *gcc_tls_addr(void) { return &tls_probe_var; }
"#;

    const DRIVER: &str = r#"
#define _GNU_SOURCE
#include <pthread.h>
#include <stdint.h>
#include <stdio.h>
extern long *trust_cg_tls_ie_addr(void);
extern long *gcc_tls_addr(void);
static pthread_barrier_t barrier;
static uintptr_t addresses[2];

static void *worker(void *arg) {
    intptr_t id = (intptr_t)arg;
    long *expected = gcc_tls_addr();
    long *actual = trust_cg_tls_ie_addr();
    int failed = actual != expected || *expected != 19;
    addresses[id] = (uintptr_t)actual;
    *expected = 101 * (id + 1);
    pthread_barrier_wait(&barrier);
    for (int i = 0; i < 100; ++i) {
        if (trust_cg_tls_ie_addr() != expected || *expected != 101 * (id + 1) + i)
            failed = 1;
        ++*expected;
    }
    pthread_barrier_wait(&barrier);
    if (addresses[0] == addresses[1]) failed = 1;
    return (void *)(intptr_t)failed;
}

int main(void) {
    long *main_addr = gcc_tls_addr();
    if (trust_cg_tls_ie_addr() != main_addr || *main_addr != 19) return 1;
    *main_addr = 333;
    if (pthread_barrier_init(&barrier, 0, 2)) return 2;
    pthread_t threads[2];
    for (intptr_t i = 0; i < 2; ++i)
        if (pthread_create(&threads[i], 0, worker, (void *)i)) return 3;
    for (int i = 0; i < 2; ++i) {
        void *result;
        if (pthread_join(threads[i], &result) || result) return 4;
    }
    if (*main_addr != 333 || trust_cg_tls_ie_addr() != main_addr) return 5;
    if (addresses[0] == (uintptr_t)main_addr || addresses[1] == (uintptr_t)main_addr)
        return 6;
    if (pthread_barrier_destroy(&barrier)) return 7;
    puts("TLS addresses and values matched in three independent threads");
    return 0;
}
"#;

    const DEFINED_DRIVER: &str = r#"
#define _GNU_SOURCE
#include <pthread.h>
#include <stdint.h>
#include <stdio.h>
extern __thread uint64_t cg_tls_init[4];
extern __thread uint64_t cg_tls_zero[4];
extern uint64_t *cg_tls_init_addr(void);
extern uint64_t *cg_tls_zero_addr(void);
static const uint64_t initial[4] = {
    UINT64_C(0x0123456789abcdef), UINT64_C(0xfedcba9876543210),
    UINT64_C(0x8000000000000001), UINT64_C(0x55aa55aa55aa55aa)
};
static pthread_barrier_t barrier;
static uintptr_t init_addresses[3], zero_addresses[3];
static int check_initial(int id) {
    uint64_t *a = cg_tls_init_addr(), *b = cg_tls_zero_addr();
    if (a != cg_tls_init || b != cg_tls_zero || a == b ||
        (uintptr_t)a % 64 || (uintptr_t)b % 128) return 1;
    init_addresses[id] = (uintptr_t)a;
    zero_addresses[id] = (uintptr_t)b;
    for (int j = 0; j < 4; ++j)
        if (a[j] != initial[j] || b[j] != 0) return 2;
    return 0;
}
static void *worker(void *arg) {
    int id = (int)(intptr_t)arg;
    int failed = check_initial(id);
    // Even a failed check participates in the barrier: no accidental timeout
    // may replace the value/identity counterexample.
    pthread_barrier_wait(&barrier);
    for (int round = 0; round < 100; ++round) {
        for (int j = 0; j < 4; ++j) {
            uint64_t value = initial[j] ^ ((uint64_t)id << 48) ^ (uint64_t)round;
            cg_tls_init[j] = value;
            cg_tls_zero[j] = ~value;
        }
        for (int j = 0; j < 4; ++j) {
            uint64_t expected = initial[j] ^ ((uint64_t)id << 48) ^ (uint64_t)round;
            if (cg_tls_init_addr()[j] != expected ||
                cg_tls_zero_addr()[j] != ~expected ||
                cg_tls_init[j] != expected || cg_tls_zero[j] != ~expected) failed = 3;
        }
    }
    pthread_barrier_wait(&barrier);
    for (int other = 0; other < 3; ++other)
        if (other != id && (init_addresses[id] == init_addresses[other] ||
                           zero_addresses[id] == zero_addresses[other])) failed = 4;
    return (void *)(intptr_t)failed;
}
int main(void) {
    if (check_initial(0)) return 1;
    for (int j = 0; j < 4; ++j) {
        cg_tls_init[j] = 333 + j;
        cg_tls_zero[j] = 777 + j;
    }
    if (pthread_barrier_init(&barrier, 0, 2)) return 2;
    pthread_t threads[2];
    for (intptr_t i = 0; i < 2; ++i)
        if (pthread_create(&threads[i], 0, worker, (void *)(i + 1))) return 3;
    for (int i = 0; i < 2; ++i) {
        void *result;
        if (pthread_join(threads[i], &result) || result) return 4;
    }
    for (int j = 0; j < 4; ++j)
        if (cg_tls_init_addr()[j] != (uint64_t)(333 + j) ||
            cg_tls_zero_addr()[j] != (uint64_t)(777 + j)) return 5;
    if (pthread_barrier_destroy(&barrier)) return 6;
    puts("CG initialized and zero TLS templates matched in three independent threads");
    return 0;
}
"#;

    fn checked(cmd: &mut Command, timeout: Duration) -> std::process::Output {
        let result = native_process::command_output_with_timeout(cmd, timeout)
            .unwrap_or_else(|error| panic!("required native command {cmd:?}: {error}"));
        assert!(
            !result.timed_out && result.output.status.success(),
            "{cmd:?}: {}\nstdout={}\nstderr={}",
            result.output.status,
            String::from_utf8_lossy(&result.output.stdout),
            String::from_utf8_lossy(&result.output.stderr),
        );
        result.output
    }

    fn link_and_run(shared_provider: bool, model: TlsModel, large_alignment: bool) {
        // A new, owned directory; never reuse or erase another test's files.
        let dir = crate::fresh_dir::create(&format!(
            "trust-cg-linux-tls-{shared_provider}-{model:?}-{large_alignment}-"
        ));
        let provider_source = dir.join("provider.c");
        let driver_source = dir.join("driver.c");
        let provider = dir.join(if shared_provider {
            "libtlsprobe.so"
        } else {
            "provider.o"
        });
        let provider_text = if large_alignment {
            assert_eq!(
                PROVIDER
                    .matches("__thread long tls_probe_var = 19;")
                    .count(),
                1
            );
            PROVIDER.replace(
                "__thread long tls_probe_var = 19;",
                "__thread long tls_probe_var __attribute__((aligned(8192))) = 19;",
            )
        } else {
            PROVIDER.to_owned()
        };
        let driver_text = if large_alignment {
            assert_eq!(
                DRIVER.matches("long *main_addr = gcc_tls_addr();").count(),
                1
            );
            DRIVER.replace(
                "long *main_addr = gcc_tls_addr();",
                "long *main_addr = gcc_tls_addr();\n\
                 uintptr_t tp;\n\
                 __asm__ volatile(\"mrs %0, tpidr_el0\" : \"=r\"(tp));\n\
                 if ((uintptr_t)main_addr < tp + 4096 ||\n\
                     (uintptr_t)main_addr % 8192 != 0) return 8;",
            )
        } else {
            DRIVER.to_owned()
        };
        fs::write(&provider_source, provider_text).unwrap();
        fs::write(&driver_source, driver_text).unwrap();
        let mut cc = Command::new("cc");
        cc.args(["-O2", "-fPIC"]);
        cc.arg(if shared_provider { "-shared" } else { "-c" });
        cc.arg(&provider_source).arg("-o").arg(&provider);
        checked(&mut cc, native_process::codegen_link_timeout());
        for opt in [OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::O3] {
            let object = dir.join(format!("probe-{opt:?}.o"));
            let binary = dir.join(format!("probe-{opt:?}"));
            let bytes = emit_tls_object(opt, model);
            assert_eq!(&bytes[..4], b"\x7fELF");
            assert_eq!(u16::from_le_bytes([bytes[18], bytes[19]]), 183);
            fs::write(&object, bytes).unwrap();
            let mut link = Command::new("cc");
            link.args(["-O2", "-pthread"])
                .arg(&driver_source)
                .arg(&object)
                .arg(&provider)
                .arg("-o")
                .arg(&binary);
            checked(&mut link, native_process::codegen_link_timeout());
            let output = checked(
                &mut Command::new(&binary),
                native_process::codegen_run_timeout(),
            );
            assert_eq!(
                String::from_utf8_lossy(&output.stdout).trim(),
                "TLS addresses and values matched in three independent threads",
                "{opt:?} {model:?} shared_provider={shared_provider}: native oracle did not finish"
            );
        }
        fs::remove_dir_all(&dir).unwrap();
    }

    /// Local-exec TLS in a shared-object link, through the system link driver.
    ///
    /// The host linker refuses a trust-cg local-exec access to an undefined
    /// thread-local (GNU ld: `TLS relocation R_AARCH64_TLSLE_ADD_TPREL_HI12
    /// against undefined symbol`), and `classify_linker_stderr` names it
    /// `TlsModelMismatch`. `run_link` refuses the same request, and one whose
    /// object defines the thread-local (which GNU ld 2.42 links), by name
    /// before the linker runs. Positive twin: initial-exec objects link into a
    /// shared object through `run_link`.
    #[test]
    fn local_exec_tls_in_a_shared_link_is_refused_by_name() {
        use trust_cg_codegen::link_driver::{
            LinkDiagnosticKind, LinkError, LinkOutputKind, LinkRequest, classify_linker_stderr,
            run_link,
        };
        use trust_cg_codegen::target::TargetSpec;

        let dir = tempfile::Builder::new()
            .prefix("tcg-linux-tls-shared-")
            .tempdir()
            .unwrap();
        let dir = dir.path();
        let shared = |object: &std::path::Path, output: &str| {
            let mut request = LinkRequest::executable(
                TargetSpec::parse("aarch64-unknown-linux-gnu").unwrap(),
                vec![object.to_path_buf()],
                dir.join(output),
            );
            request.kind = LinkOutputKind::SharedLibrary;
            request
        };
        let expect_refused = |request: &LinkRequest| match run_link(request, "cc") {
            Err(LinkError::InputRefused(diagnostics)) => {
                let named: Vec<_> = diagnostics
                    .iter()
                    .map(|d| (d.kind, d.subject.as_deref(), d.relocation.as_deref()))
                    .collect();
                assert_eq!(
                    named,
                    [(
                        LinkDiagnosticKind::TlsModelMismatch,
                        Some("tls_probe_var"),
                        Some("R_AARCH64_TLSLE_ADD_TPREL_HI12")
                    )]
                );
                assert!(
                    diagnostics[0].line.starts_with("[TCG-LINK-TLS-MODEL] "),
                    "{}",
                    diagnostics[0].line
                );
                assert!(!request.output.exists());
            }
            other => panic!("expected a refusal before the linker ran, got {other:?}"),
        };

        // Local-exec access to an undefined thread-local: the linker's own
        // refusal is classified, and run_link refuses it first.
        let import = dir.join("le_import.o");
        fs::write(&import, emit_tls_object(OptLevel::O0, TlsModel::LocalExec)).unwrap();
        let request = shared(&import, "libleimport.so");
        let mut command = request.command("cc").unwrap();
        let linked = native_process::command_output_with_timeout(
            &mut command,
            native_process::codegen_link_timeout(),
        )
        .unwrap();
        assert!(!linked.timed_out, "link timed out");
        let stderr = String::from_utf8_lossy(&linked.output.stderr).into_owned();
        assert!(!linked.output.status.success(), "{stderr}");
        let diagnostics = classify_linker_stderr(&stderr);
        assert_eq!(
            diagnostics
                .iter()
                .map(|d| (d.kind, d.subject.as_deref(), d.relocation.as_deref()))
                .collect::<Vec<_>>(),
            [(
                LinkDiagnosticKind::TlsModelMismatch,
                Some("tls_probe_var"),
                Some("R_AARCH64_TLSLE_ADD_TPREL_HI12")
            )],
            "{stderr}"
        );
        expect_refused(&request);

        // Local-exec access to a thread-local the object defines.
        let pipeline = Pipeline::new(PipelineConfig {
            target_triple: "aarch64-unknown-linux-gnu".to_owned(),
            opt_level: OptLevel::O0,
            ..PipelineConfig::default()
        });
        let definition = |model| {
            let function = pipeline
                .prepare_function(&tls_addr_function(
                    "trust_cg_tls_addr",
                    "tls_probe_var",
                    model,
                ))
                .unwrap();
            let global = ObjectGlobal {
                name: "tls_probe_var".to_owned(),
                data: 19u64.to_le_bytes().to_vec(),
                mutable: true,
                is_external: true,
                symbol_refs: vec![],
                is_thread_local: true,
                is_import: false,
                is_weak: false,
                align: 8,
                visibility: trust_ir::Visibility::Default,
                retained: false,
                section: None,
                comdat: false,
            };
            pipeline
                .compile_module_with_globals(&[function], &[global])
                .unwrap()
        };
        let defined = dir.join("le_defined.o");
        fs::write(&defined, definition(TlsModel::LocalExec)).unwrap();
        expect_refused(&shared(&defined, "libledefined.so"));

        // Positive twins: initial-exec, imported or defined, links -shared.
        let ie_defined = dir.join("ie_defined.o");
        fs::write(&ie_defined, definition(TlsModel::InitialExec)).unwrap();
        let ie_import = dir.join("ie_import.o");
        fs::write(
            &ie_import,
            emit_tls_object(OptLevel::O0, TlsModel::InitialExec),
        )
        .unwrap();
        for (object, output) in [
            (&ie_defined, "libiedefined.so"),
            (&ie_import, "libieimport.so"),
        ] {
            let request = shared(object, output);
            if let Err(error) = run_link(&request, "cc") {
                panic!("{output}: {error}");
            }
            let bytes = fs::read(&request.output).unwrap();
            assert_eq!(&bytes[..4], b"\x7fELF");
            assert_eq!(u16::from_le_bytes([bytes[16], bytes[17]]), 3, "ET_DYN");
        }
    }

    /// An object defining `tls_probe_var` (19) and `trust_cg_tls_addr`,
    /// which returns its address under `model`.
    fn emit_tls_definition(model: TlsModel) -> Vec<u8> {
        let pipeline = Pipeline::new(PipelineConfig {
            target_triple: "aarch64-unknown-linux-gnu".to_owned(),
            opt_level: OptLevel::O0,
            ..PipelineConfig::default()
        });
        let function = pipeline
            .prepare_function(&tls_addr_function(
                "trust_cg_tls_addr",
                "tls_probe_var",
                model,
            ))
            .unwrap();
        let global = ObjectGlobal {
            name: "tls_probe_var".to_owned(),
            data: 19u64.to_le_bytes().to_vec(),
            mutable: true,
            is_external: true,
            symbol_refs: vec![],
            is_thread_local: true,
            is_import: false,
            is_weak: false,
            align: 8,
            visibility: trust_ir::Visibility::Default,
            retained: false,
            section: None,
            comdat: false,
        };
        pipeline
            .compile_module_with_globals(&[function], &[global])
            .unwrap()
    }

    fn named(
        diagnostics: &[trust_cg_codegen::link_driver::LinkDiagnostic],
    ) -> Vec<(
        trust_cg_codegen::link_driver::LinkDiagnosticKind,
        Option<&str>,
        Option<&str>,
    )> {
        diagnostics
            .iter()
            .map(|d| (d.kind, d.subject.as_deref(), d.relocation.as_deref()))
            .collect()
    }

    /// Local-exec TLS in an executable, against a thread-local a shared
    /// library defines, through `run_link` and the host GNU ld.
    ///
    /// A trust-cg local-exec import of `tls_probe_var`, which only
    /// `libtlsprobe.so` defines, cannot be resolved: GNU ld 2.42 refuses it
    /// against an undefined symbol when the executable has no TLS segment and
    /// reports a truncated `R_AARCH64_TLSLE_ADD_TPREL_HI12` against the
    /// library's `.tdata` when it has one. Both classify as exactly one
    /// `TlsModelMismatch` and write no executable. Positive twins: the
    /// initial-exec import links against the same library and returns 42.
    #[test]
    fn local_exec_tls_against_a_shared_library_thread_local_is_named() {
        use trust_cg_codegen::link_driver::{LinkDiagnosticKind, LinkError, LinkRequest, run_link};
        use trust_cg_codegen::target::TargetSpec;

        const MAIN: &str = "extern long *trust_cg_tls_ie_addr(void);\n\
             int main(void) { return *trust_cg_tls_ie_addr() == 19 ? 42 : 1; }\n";
        const MAIN_WITH_TLS: &str = "extern long *trust_cg_tls_ie_addr(void);\n\
             __thread long main_tls = 23;\n\
             int main(void) { return *trust_cg_tls_ie_addr() == 19 && main_tls == 23 ? 42 : 1; }\n";
        let directory = tempfile::Builder::new()
            .prefix("tcg-linux-tls-exe-")
            .tempdir()
            .unwrap();
        let dir = directory.path();
        fs::write(dir.join("provider.c"), PROVIDER).unwrap();
        checked(
            Command::new("cc")
                .args(["-O2", "-fPIC", "-shared"])
                .arg(dir.join("provider.c"))
                .arg("-o")
                .arg(dir.join("libtlsprobe.so")),
            native_process::codegen_link_timeout(),
        );
        let le_import = dir.join("le_import.o");
        fs::write(
            &le_import,
            emit_tls_object(OptLevel::O0, TlsModel::LocalExec),
        )
        .unwrap();
        let ie_import = dir.join("ie_import.o");
        fs::write(
            &ie_import,
            emit_tls_object(OptLevel::O0, TlsModel::InitialExec),
        )
        .unwrap();
        let executable = |main: &std::path::Path, probe: &std::path::Path, output: &str| {
            let mut request = LinkRequest::executable(
                TargetSpec::parse("aarch64-unknown-linux-gnu").unwrap(),
                vec![main.to_path_buf(), probe.to_path_buf()],
                dir.join(output),
            );
            request.lib_paths = vec![dir.to_path_buf()];
            request.libs = vec!["tlsprobe".to_owned()];
            request.rpaths = vec![dir.display().to_string()];
            request
        };
        for (name, source, sentence) in [
            (
                "main",
                MAIN,
                "TLS relocation R_AARCH64_TLSLE_ADD_TPREL_HI12 against undefined symbol `tls_probe_var'"
                    .to_owned(),
            ),
            (
                "main_tls",
                MAIN_WITH_TLS,
                format!(
                    "relocation truncated to fit: R_AARCH64_TLSLE_ADD_TPREL_HI12 against symbol \
                     `tls_probe_var' defined in .tdata section in {}\n",
                    dir.join("libtlsprobe.so").display()
                ),
            ),
        ] {
            let main = dir.join(format!("{name}.o"));
            fs::write(dir.join(format!("{name}.c")), source).unwrap();
            checked(
                Command::new("cc")
                    .args(["-O2", "-c"])
                    .arg(dir.join(format!("{name}.c")))
                    .arg("-o")
                    .arg(&main),
                native_process::codegen_link_timeout(),
            );
            let request = executable(&main, &le_import, &format!("{name}_le"));
            match run_link(&request, "cc") {
                Err(LinkError::Failed(failure)) => {
                    assert_eq!(
                        named(&failure.diagnostics),
                        [(
                            LinkDiagnosticKind::TlsModelMismatch,
                            Some("tls_probe_var"),
                            Some("R_AARCH64_TLSLE_ADD_TPREL_HI12")
                        )],
                        "{name}: {}",
                        failure.stderr
                    );
                    assert!(
                        failure.stderr.contains(&sentence),
                        "{name}: {}",
                        failure.stderr
                    );
                }
                other => panic!("{name}: expected the linker's refusal, got {other:?}"),
            }
            assert!(!request.output.exists(), "{name}");

            // Positive twin: initial-exec reaches the library's thread-local.
            let request = executable(&main, &ie_import, &format!("{name}_ie"));
            if let Err(error) = run_link(&request, "cc") {
                panic!("{name}: {error}");
            }
            let status = checked_status(&request.output);
            assert_eq!(status, Some(42), "{name}");
        }
    }

    /// Exit status of `program`, within the native run timeout.
    fn checked_status(program: &std::path::Path) -> Option<i32> {
        let result = native_process::command_output_with_timeout(
            &mut Command::new(program),
            native_process::codegen_run_timeout(),
        )
        .unwrap_or_else(|error| panic!("{}: {error}", program.display()));
        assert!(!result.timed_out, "{} timed out", program.display());
        result.output.status.code()
    }

    /// A shared object the linker writes for an executable request is
    /// refused when it would carry local-exec TLS, and nothing but the
    /// driver's own staged image is ever read or removed.
    ///
    /// GNU ld 2.42 accepts every unambiguous abbreviation of `-shared` and
    /// `-Bshareable` and reads a bare `-G` as `--shared`. `parse_wl_group`
    /// refuses each of those spellings on Linux, and `run_link` refuses a
    /// request that carries one without the parser, before anything runs.
    /// The read-back behind that is exercised with a C driver that always
    /// links `-shared` (a wrapper around `cc`): through `run_link`, the
    /// local-exec definition of `tls_probe_var` is written at the staging
    /// path as an `ET_DYN` library without `DF_1_PIE`, removed there, and
    /// named by its `R_AARCH64_TLSLE_ADD_TPREL_HI12`; the requested output,
    /// which already holds an executable, keeps its bytes. A successful link
    /// that writes no output (`-Wl,--version`) is refused and leaves the
    /// file at the output path as it was. Positive twins: the initial-exec
    /// definition links through the same driver into a shared object at the
    /// output, and the local-exec definition links as a PIE, a
    /// position-dependent and a static executable that return 42.
    #[test]
    fn local_exec_tls_in_a_linker_steered_shared_object_is_refused() {
        use trust_cg_codegen::link_driver::{
            ElfLinkedKind, LinkDiagnosticKind, LinkError, LinkRequest, PositionIndependence,
            elf_linked_kind, parse_wl_group, run_link,
        };
        use trust_cg_codegen::target::TargetSpec;

        let directory = tempfile::Builder::new()
            .prefix("tcg-linux-tls-steered-")
            .tempdir()
            .unwrap();
        let dir = directory.path();
        let linux = TargetSpec::parse("aarch64-unknown-linux-gnu").unwrap();
        let le_defined = dir.join("le_defined.o");
        fs::write(&le_defined, emit_tls_definition(TlsModel::LocalExec)).unwrap();
        let ie_defined = dir.join("ie_defined.o");
        fs::write(&ie_defined, emit_tls_definition(TlsModel::InitialExec)).unwrap();
        let request = |objects: Vec<std::path::PathBuf>, output: &str| {
            LinkRequest::executable(linux, objects, dir.join(output))
        };
        // Nothing may be left beside the output: no staging directory, no
        // image at another path.
        let listing = || {
            let mut names: Vec<String> = fs::read_dir(dir)
                .unwrap()
                .map(|entry| entry.unwrap().file_name().into_string().unwrap())
                .collect();
            names.sort();
            names
        };

        for spelling in [
            "-shared",
            "--shared",
            "-Bshareable",
            "--Bshareable",
            "--shar",
            "-shar",
            "--Bshare",
            "-Bshar",
            "-sh",
            "-G",
        ] {
            let refusal = parse_wl_group(spelling, linux).unwrap_err();
            assert!(
                refusal
                    .reason
                    .contains("is controlled by the trust-cg option `--shared`"),
                "{spelling}: {refusal}"
            );
            let mut unparsed = request(vec![le_defined.clone()], "libsteered.so");
            unparsed.linker_arg_groups = vec![vec![spelling.to_string()]];
            match run_link(&unparsed, "cc") {
                Err(LinkError::Refused(refusals)) => {
                    assert_eq!(refusals, [refusal], "{spelling}")
                }
                other => panic!("{spelling}: expected Refused, got {other:?}"),
            }
            assert!(!unparsed.output.exists(), "{spelling}");
        }

        // A C driver that links every request as a shared object.
        let shared_cc = dir.join("shared-cc.sh");
        super::write_executable_script(&shared_cc, "#!/bin/sh\nexec cc -shared \"$@\"\n");
        let shared_cc = shared_cc.to_str().unwrap();
        let steered = request(vec![le_defined.clone()], "steered");
        let preexisting = b"\x7fELF preexisting output\n".to_vec();
        fs::write(&steered.output, &preexisting).unwrap();
        let before = listing();
        match run_link(&steered, shared_cc) {
            Err(LinkError::OutputRefused {
                output,
                staged,
                removed,
                diagnostics,
                ..
            }) => {
                assert_eq!(output, steered.output);
                assert_ne!(staged, steered.output);
                assert_eq!(staged.parent().unwrap().parent().unwrap(), dir);
                assert_eq!(staged.file_name().unwrap(), "steered");
                assert!(removed);
                assert!(!staged.exists() && !staged.parent().unwrap().exists());
                assert_eq!(
                    named(&diagnostics),
                    [(
                        LinkDiagnosticKind::TlsModelMismatch,
                        Some("tls_probe_var"),
                        Some("R_AARCH64_TLSLE_ADD_TPREL_HI12")
                    )]
                );
                assert!(
                    diagnostics[0].line.starts_with("[TCG-LINK-TLS-MODEL] ")
                        && diagnostics[0]
                            .line
                            .contains("an ELF shared object (ET_DYN without DF_1_PIE)"),
                    "{}",
                    diagnostics[0].line
                );
            }
            other => panic!("expected OutputRefused, got {other:?}"),
        }
        assert_eq!(fs::read(&steered.output).unwrap(), preexisting);
        assert_eq!(listing(), before);

        // A successful link that writes nothing is refused, and the file at
        // the output path keeps its bytes.
        let mut version = steered.clone();
        version.linker_arg_groups = vec![parse_wl_group("--version", linux).unwrap()];
        match run_link(&version, "cc") {
            Err(error @ LinkError::OutputMissing { .. }) => {
                let LinkError::OutputMissing {
                    output, objects, ..
                } = &error
                else {
                    unreachable!()
                };
                assert_eq!(output, &version.output);
                assert_eq!(objects, std::slice::from_ref(&le_defined));
                assert!(
                    error.to_string().starts_with("[TCG-LINK-NO-OUTPUT] "),
                    "{error}"
                );
            }
            other => panic!("expected OutputMissing, got {other:?}"),
        }
        assert_eq!(fs::read(&version.output).unwrap(), preexisting);
        assert_eq!(listing(), before);
        fs::remove_file(&steered.output).unwrap();

        // Positive twin: the same driver makes a shared object, which
        // initial-exec TLS may be linked into; it is installed at the output.
        let twin = request(vec![ie_defined.clone()], "libsteered_ie.so");
        if let Err(error) = run_link(&twin, shared_cc) {
            panic!("{error}");
        }
        assert_eq!(
            elf_linked_kind(&fs::read(&twin.output).unwrap()),
            Ok(ElfLinkedKind::SharedObject)
        );
        fs::remove_file(&twin.output).unwrap();

        // Positive twins: local-exec is the executable's own model.
        fs::write(
            dir.join("main.c"),
            "extern long *trust_cg_tls_addr(void);\n\
             int main(void) {\n\
                 long *value = trust_cg_tls_addr();\n\
                 if (*value != 19) return 1;\n\
                 *value = 42;\n\
                 return (int)*trust_cg_tls_addr();\n\
             }\n",
        )
        .unwrap();
        checked(
            Command::new("cc")
                .args(["-O2", "-c"])
                .arg(dir.join("main.c"))
                .arg("-o")
                .arg(dir.join("main.o")),
            native_process::codegen_link_timeout(),
        );
        for (name, independence, static_link, kind) in [
            (
                "pie",
                PositionIndependence::DriverDefault,
                false,
                ElfLinkedKind::PositionIndependentExecutable,
            ),
            (
                "no_pie",
                PositionIndependence::NoPie,
                false,
                ElfLinkedKind::Executable,
            ),
            (
                "static",
                PositionIndependence::DriverDefault,
                true,
                ElfLinkedKind::Executable,
            ),
        ] {
            let mut executable = request(vec![dir.join("main.o"), le_defined.clone()], name);
            executable.position_independence = independence;
            executable.static_link = static_link;
            if let Err(error) = run_link(&executable, "cc") {
                panic!("{name}: {error}");
            }
            assert_eq!(
                elf_linked_kind(&fs::read(&executable.output).unwrap()),
                Ok(kind),
                "{name}"
            );
            assert_eq!(checked_status(&executable.output), Some(42), "{name}");
        }
    }

    /// The directory holding `ld.lld` for `cc -fuse-ld=lld -B<dir>`:
    /// `TCG_LLD_DIR`, else `~/.local/bin`, else the first `PATH` entry with
    /// one. `TCG_REQUIRE_LLD` turns a missing LLD into a failure.
    fn lld_dir() -> Option<std::path::PathBuf> {
        let found = std::env::var_os("TCG_LLD_DIR")
            .map(std::path::PathBuf::from)
            .or_else(|| {
                std::env::var_os("HOME").map(|home| std::path::Path::new(&home).join(".local/bin"))
            })
            .filter(|dir| dir.join("ld.lld").is_file())
            .or_else(|| {
                std::env::var_os("PATH").and_then(|paths| {
                    std::env::split_paths(&paths).find(|dir| dir.join("ld.lld").is_file())
                })
            });
        if found.is_none() {
            assert!(
                std::env::var_os("TCG_REQUIRE_LLD").is_none(),
                "TCG_REQUIRE_LLD is set but no ld.lld was found"
            );
            eprintln!(
                "SKIP: no ld.lld (TCG_LLD_DIR, ~/.local/bin, PATH); the LLD legs did not run"
            );
        }
        found
    }

    /// `run_link` reads both linkers' input traces. A `-shared` link takes
    /// trust-cg's local-exec definition of `tls_probe_var` only as an archive
    /// member (`-Wl,--whole-archive,<archive>,--no-whole-archive`), from a
    /// regular and from a thin archive. GNU ld 2.42 writes the library; its
    /// trace names the member as `(archive)member.o` (the thin archive's as
    /// the member's own path), and `run_link` refuses the image with exactly
    /// one `TlsModelMismatch` naming the member and removes it. LLD 22
    /// refuses the link itself, which is classified as the same kind. Twins:
    /// the initial-exec definition in the same archives links through both
    /// linkers into a shared object, so each trace, including LLD's
    /// `archive(member)` lines, was read in full.
    #[test]
    fn traced_archive_members_are_read_from_gnu_ld_and_lld() {
        use trust_cg_codegen::link_driver::{
            ElfLinkedKind, LinkDiagnosticKind, LinkError, LinkOutputKind, LinkRequest,
            elf_linked_kind, parse_wl_group, run_link,
        };
        use trust_cg_codegen::target::TargetSpec;

        let directory = tempfile::Builder::new()
            .prefix("tcg-linux-tls-traced-")
            .tempdir()
            .unwrap();
        let dir = directory.path();
        let linux = TargetSpec::parse("aarch64-unknown-linux-gnu").unwrap();
        fs::write(
            dir.join("carrier.c"),
            "int tcg_carrier(void) { return 0; }\n",
        )
        .unwrap();
        checked(
            Command::new("cc")
                .args(["-O1", "-fPIC", "-c", "-o"])
                .arg(dir.join("carrier.o"))
                .arg(dir.join("carrier.c")),
            native_process::codegen_link_timeout(),
        );
        let mut linkers = vec![("gnu", "cc".to_string())];
        if let Some(lld) = lld_dir() {
            let shim = dir.join("lld-cc.sh");
            super::write_executable_script(
                &shim,
                &format!(
                    "#!/bin/sh\nexec cc -fuse-ld=lld -B'{}' \"$@\"\n",
                    lld.display()
                ),
            );
            linkers.push(("lld", shim.display().to_string()));
        }
        for (model, name) in [(TlsModel::LocalExec, "le"), (TlsModel::InitialExec, "ie")] {
            let members = dir.join(name);
            fs::create_dir(&members).unwrap();
            fs::write(members.join("member.o"), emit_tls_definition(model)).unwrap();
            for (flag, archive) in [("rcs", "libregular.a"), ("rcsT", "libthin.a")] {
                checked(
                    Command::new("ar")
                        .current_dir(&members)
                        .args([flag, archive, "member.o"]),
                    native_process::codegen_link_timeout(),
                );
            }
        }
        for (linker, driver) in &linkers {
            for (name, archive) in [
                ("le", "libregular.a"),
                ("le", "libthin.a"),
                ("ie", "libregular.a"),
                ("ie", "libthin.a"),
            ] {
                let what = format!("{linker} {name} {archive}");
                let archive = dir.join(name).join(archive);
                let mut request = LinkRequest::executable(
                    linux,
                    vec![dir.join("carrier.o")],
                    dir.join(format!("lib{linker}-{name}.so")),
                );
                request.kind = LinkOutputKind::SharedLibrary;
                request.linker_arg_groups = vec![
                    parse_wl_group(
                        &format!("--whole-archive,{},--no-whole-archive", archive.display()),
                        linux,
                    )
                    .unwrap(),
                ];
                let result = run_link(&request, driver);
                if name == "ie" {
                    if let Err(error) = result {
                        panic!("{what}: {error}");
                    }
                    assert_eq!(
                        elf_linked_kind(&fs::read(&request.output).unwrap()),
                        Ok(ElfLinkedKind::SharedObject),
                        "{what}"
                    );
                    continue;
                }
                let diagnostics = match (*linker, result) {
                    (
                        "gnu",
                        Err(LinkError::OutputRefused {
                            removed,
                            diagnostics,
                            ..
                        }),
                    ) => {
                        assert!(removed, "{what}");
                        assert!(
                            diagnostics[0].line.starts_with("[TCG-LINK-TLS-MODEL] ")
                                && diagnostics[0].line.contains("member.o")
                                && diagnostics[0]
                                    .line
                                    .contains("although it is not a positional input"),
                            "{what}: {}",
                            diagnostics[0].line
                        );
                        diagnostics
                    }
                    ("lld", Err(LinkError::Failed(failure))) => failure.diagnostics,
                    (_, other) => panic!("{what}: {other:?}"),
                };
                assert_eq!(
                    named(&diagnostics),
                    [(
                        LinkDiagnosticKind::TlsModelMismatch,
                        Some("tls_probe_var"),
                        Some("R_AARCH64_TLSLE_ADD_TPREL_HI12")
                    )],
                    "{what}"
                );
                assert!(!request.output.exists(), "{what}");
            }
        }
    }

    /// `object` with every `SHT_RELA` section rewritten as `SHT_REL`
    /// (16-byte entries; trust-cg's TLS relocations have zero addends).
    fn as_sht_rel(object: &[u8]) -> Vec<u8> {
        let mut bytes = object.to_vec();
        let read = |bytes: &[u8], at: usize, width: usize| {
            let mut value = [0u8; 8];
            value[..width].copy_from_slice(&bytes[at..at + width]);
            u64::from_le_bytes(value)
        };
        let shoff = read(&bytes, 40, 8) as usize;
        let shentsize = read(&bytes, 58, 2) as usize;
        let shnum = read(&bytes, 60, 2) as usize;
        for index in 0..shnum {
            let header = shoff + index * shentsize;
            if read(&bytes, header + 4, 4) != 4 {
                continue;
            }
            let offset = read(&bytes, header + 24, 8) as usize;
            let size = read(&bytes, header + 32, 8) as usize;
            let entries: Vec<(u64, u64, u64)> = (0..size / 24)
                .map(|entry| {
                    let at = offset + 24 * entry;
                    (
                        read(&bytes, at, 8),
                        read(&bytes, at + 8, 8),
                        read(&bytes, at + 16, 8),
                    )
                })
                .collect();
            assert!(
                entries.iter().all(|(_, _, addend)| *addend == 0),
                "only zero addends survive SHT_REL"
            );
            for (entry, (r_offset, info, _)) in entries.iter().enumerate() {
                let at = offset + 16 * entry;
                bytes[at..at + 8].copy_from_slice(&r_offset.to_le_bytes());
                bytes[at + 8..at + 16].copy_from_slice(&info.to_le_bytes());
            }
            bytes[header + 4..header + 8].copy_from_slice(&9u32.to_le_bytes());
            bytes[header + 32..header + 40]
                .copy_from_slice(&(16 * entries.len() as u64).to_le_bytes());
            bytes[header + 56..header + 64].copy_from_slice(&16u64.to_le_bytes());
        }
        bytes
    }

    /// GNU ld 2.42 applies relocations from an `SHT_REL` section although the
    /// AArch64 psABI uses `SHT_RELA` only. trust-cg's local-exec definition
    /// of `tls_probe_var`, with its relocation sections rewritten as
    /// `SHT_REL`, links into a shared object through `cc -shared` outside
    /// the driver (exit 0). The link driver reads `SHT_REL` records too:
    /// `run_link` refuses the positional object before the linker runs and
    /// the same object named as `-Wl,<object>` after it (the traced
    /// examination), each with exactly one `TlsModelMismatch`, and writes
    /// nothing. Twin: the initial-exec definition rewritten the same way
    /// links through the driver by both routes.
    #[test]
    fn sht_rel_local_exec_is_refused_like_sht_rela() {
        use trust_cg_codegen::link_driver::{
            ElfLinkedKind, LinkDiagnosticKind, LinkError, LinkOutputKind, LinkRequest,
            elf_linked_kind, parse_wl_group, run_link,
        };
        use trust_cg_codegen::target::TargetSpec;

        let directory = tempfile::Builder::new()
            .prefix("tcg-linux-tls-rel-")
            .tempdir()
            .unwrap();
        let dir = directory.path();
        let linux = TargetSpec::parse("aarch64-unknown-linux-gnu").unwrap();
        fs::write(
            dir.join("carrier.c"),
            "int tcg_carrier(void) { return 0; }\n",
        )
        .unwrap();
        checked(
            Command::new("cc")
                .args(["-O1", "-fPIC", "-c", "-o"])
                .arg(dir.join("carrier.o"))
                .arg(dir.join("carrier.c")),
            native_process::codegen_link_timeout(),
        );
        for (model, name) in [(TlsModel::LocalExec, "le"), (TlsModel::InitialExec, "ie")] {
            fs::write(
                dir.join(format!("{name}_rel.o")),
                as_sht_rel(&emit_tls_definition(model)),
            )
            .unwrap();
        }
        // Outside the driver GNU ld links the local-exec object.
        checked(
            Command::new("cc")
                .arg("-shared")
                .arg("-o")
                .arg(dir.join("libraw.so"))
                .arg(dir.join("le_rel.o")),
            native_process::codegen_link_timeout(),
        );
        assert_eq!(
            elf_linked_kind(&fs::read(dir.join("libraw.so")).unwrap()),
            Ok(ElfLinkedKind::SharedObject)
        );

        let shared = |name: &str, route: &str| {
            let object = dir.join(format!("{name}_rel.o"));
            let (objects, groups) = match route {
                "positional" => (vec![object], Vec::new()),
                _ => (
                    vec![dir.join("carrier.o")],
                    vec![parse_wl_group(&object.display().to_string(), linux).unwrap()],
                ),
            };
            let mut request =
                LinkRequest::executable(linux, objects, dir.join(format!("lib{name}-{route}.so")));
            request.kind = LinkOutputKind::SharedLibrary;
            request.linker_arg_groups = groups;
            request
        };
        for route in ["positional", "wl"] {
            let request = shared("le", route);
            let diagnostics = match (route, run_link(&request, "cc")) {
                ("positional", Err(LinkError::InputRefused(diagnostics))) => diagnostics,
                ("wl", Err(LinkError::OutputRefused { diagnostics, .. })) => diagnostics,
                (_, other) => panic!("{route}: {other:?}"),
            };
            assert_eq!(
                named(&diagnostics),
                [(
                    LinkDiagnosticKind::TlsModelMismatch,
                    Some("tls_probe_var"),
                    Some("R_AARCH64_TLSLE_ADD_TPREL_HI12")
                )],
                "{route}"
            );
            assert!(
                diagnostics[0].line.starts_with("[TCG-LINK-TLS-MODEL] "),
                "{route}: {}",
                diagnostics[0].line
            );
            assert!(!request.output.exists(), "{route}");

            let twin = shared("ie", route);
            if let Err(error) = run_link(&twin, "cc") {
                panic!("{route}: {error}");
            }
            assert_eq!(
                elf_linked_kind(&fs::read(&twin.output).unwrap()),
                Ok(ElfLinkedKind::SharedObject),
                "{route}"
            );
        }
    }

    #[test]
    fn tlsie_native_linux_relaxed_provider_preserves_thread_local_identity() {
        link_and_run(false, TlsModel::InitialExec, false);
    }

    #[test]
    fn tlsie_native_linux_shared_provider_preserves_thread_local_identity() {
        link_and_run(true, TlsModel::InitialExec, false);
    }

    #[test]
    fn tlsle_native_linux_cross_object_preserves_thread_local_identity() {
        link_and_run(false, TlsModel::LocalExec, false);
    }

    #[test]
    fn tlsle_native_linux_nonzero_high12_preserves_thread_local_identity() {
        link_and_run(false, TlsModel::LocalExec, true);
    }

    #[test]
    fn cg_defined_tls_templates_native_linux_executable_and_shared_library() {
        let dir = crate::fresh_dir::create("trust-cg-linux-tls-defined-");
        let driver = dir.join("driver.c");
        fs::write(&driver, DEFINED_DRIVER).unwrap();
        let initial: Vec<u8> = [
            0x0123_4567_89ab_cdefu64,
            0xfedc_ba98_7654_3210,
            0x8000_0000_0000_0001,
            0x55aa_55aa_55aa_55aa,
        ]
        .into_iter()
        .flat_map(u64::to_le_bytes)
        .collect();
        let globals: Vec<_> = [
            ("cg_tls_init", initial, 64),
            ("cg_tls_zero", vec![0; 32], 128),
        ]
        .into_iter()
        .map(|(name, data, align)| ObjectGlobal {
            name: name.to_owned(),
            data,
            mutable: true,
            is_external: true,
            symbol_refs: vec![],
            is_thread_local: true,
            is_import: false,
            is_weak: false,
            align,
            visibility: trust_ir::Visibility::Default,
            retained: false,
            section: None,
            comdat: false,
        })
        .collect();
        let mut executions = 0;
        // Local-exec belongs in the main executable. Initial-exec additionally
        // permits a startup-loaded shared image; this does not claim dlopen TLS.
        for (model, shared) in [
            (TlsModel::LocalExec, false),
            (TlsModel::InitialExec, false),
            (TlsModel::InitialExec, true),
        ] {
            for opt in [OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::O3] {
                let pipeline = Pipeline::new(PipelineConfig {
                    target_triple: "aarch64-unknown-linux-gnu".to_owned(),
                    opt_level: opt,
                    ..PipelineConfig::default()
                });
                let functions: Vec<_> = [
                    ("cg_tls_init_addr", "cg_tls_init"),
                    ("cg_tls_zero_addr", "cg_tls_zero"),
                ]
                .into_iter()
                .map(|(name, symbol)| {
                    pipeline
                        .prepare_function(&tls_addr_function(name, symbol, model))
                        .unwrap()
                })
                .collect();
                let bytes = pipeline
                    .compile_module_with_globals(&functions, &globals)
                    .unwrap();
                let object = dir.join(format!("probe-{model:?}-{shared}-{opt:?}.o"));
                let binary = dir.join(format!("probe-{model:?}-{shared}-{opt:?}"));
                fs::write(&object, bytes).unwrap();
                let provider = if shared {
                    let library = dir.join(format!("libprobe-{opt:?}.so"));
                    checked(
                        Command::new("cc")
                            .args(["-shared", "-Wl,-z,defs,-z,text"])
                            .arg(&object)
                            .arg("-o")
                            .arg(&library),
                        native_process::codegen_link_timeout(),
                    );
                    library
                } else {
                    object
                };
                checked(
                    Command::new("cc")
                        .args(["-O2", "-fPIC", "-pthread"])
                        .arg(&driver)
                        .arg(&provider)
                        .arg("-o")
                        .arg(&binary),
                    native_process::codegen_link_timeout(),
                );
                let output = checked(
                    &mut Command::new(&binary),
                    native_process::codegen_run_timeout(),
                );
                assert_eq!(
                    String::from_utf8_lossy(&output.stdout).trim(),
                    "CG initialized and zero TLS templates matched in three independent threads",
                    "{model:?} shared={shared} {opt:?}"
                );
                executions += 1;
            }
        }
        assert_eq!(executions, 12);
        println!("CG TLS template qualification completed {executions} three-thread executions");
        fs::remove_dir_all(&dir).unwrap();
    }
}

#[test]
fn tlsie_sequence_oracle_accepts_a_prologue_but_rejects_wrong_sites_and_dataflow() {
    // Independent gcc words retained above, with a normal frame prefix.
    let words = [
        0xa9bf_7bfd,
        0x9100_03fd,
        0x9000_0000,
        0xf940_0000,
        0xd53b_d041,
        0x8b00_0020,
    ];
    assert_tlsie_sequence(&words[2..], 0);
    assert_tlsie_sequence(&words, 8);
    for bad_offset in [0, 4, 9, 12, 24, u64::MAX - 3] {
        assert!(std::panic::catch_unwind(|| assert_tlsie_sequence(&words, bad_offset)).is_err());
    }
    for (index, flipped_bit) in [
        (2, 29), // ADRP immlo was omitted from the old zero-placeholder mask.
        (2, 30),
        (2, 5),  // ADRP immhi.
        (3, 10), // LDR nonzero offset.
        (3, 5),  // LDR no longer consumes ADRP.
        (3, 0),  // Offset register overwritten by MRS.
        (4, 5),  // Wrong system register.
        (5, 5),  // ADD consumes the wrong thread-pointer register.
        (5, 16), // ADD consumes the wrong TLS-offset register.
        (5, 10), // ADD shifts an input.
    ] {
        let mut corrupt = words;
        corrupt[index] ^= 1 << flipped_bit;
        assert!(
            std::panic::catch_unwind(|| assert_tlsie_sequence(&corrupt, 8)).is_err(),
            "accepted mutation at word {index}, bit {flipped_bit}",
        );
    }
}

/// Writes an executable script from a child shell. A script this process
/// opened for writing can fail to exec with ETXTBSY ("Text file busy"): a
/// test thread that forks while the write descriptor is open hands a copy to
/// its child, which holds it until that child execs. Writing through a child
/// process leaves no writable descriptor to the script in this process.
#[cfg(all(target_arch = "aarch64", target_os = "linux", target_env = "gnu"))]
fn write_executable_script(path: &std::path::Path, contents: &str) {
    use std::io::Write;
    let mut child = std::process::Command::new("/bin/sh")
        .arg("-c")
        .arg("cat > \"$1\" && chmod 755 \"$1\"")
        .arg("sh")
        .arg(path)
        .stdin(std::process::Stdio::piped())
        .spawn()
        .expect("spawn /bin/sh to write the script");
    child
        .stdin
        .take()
        .expect("script writer stdin")
        .write_all(contents.as_bytes())
        .expect("write the script");
    assert!(
        child.wait().expect("wait for the script writer").success(),
        "writing {}",
        path.display()
    );
}
