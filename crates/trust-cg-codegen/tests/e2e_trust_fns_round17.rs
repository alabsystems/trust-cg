//! TRUST-SELF ROUND 30 (thread R30, TRUST BATCH 17): verifying trust-cg's ELF64
//! OBJECT-WRITER byte machinery — the field-packing bit ops + the fixed-layout
//! 24-byte symbol/relocation entries + the 64-byte ELF header — through the full
//! pipeline Rust -> MIR -> trust-ir (stage1 `trust_ir_mir --mir-emit-closure`) ->
//! trust-cg JIT -> machine code, asserting native Rust == JIT over swept real
//! inputs, with the LINKED PRODUCTION functions as a SECOND oracle
//! (`trust_cg_codegen::elf::{constants,symbol,reloc,header}`).
//!
//! WHY THIS SURFACE: a wrong bit in an ELF field-packing (`st_info`, `r_info`) or a
//! wrong byte OFFSET in an `Elf64_Sym`/`Elf64_Rela`/`Elf64_Ehdr` layout produces a
//! MALFORMED `.o` file the system linker mis-links or rejects. These are the pure,
//! scalar-shaped bit-packers + fixed-layout encoders/decoders of the ELF path — the
//! classic ELF field-packing bug sites (the `r_info = (sym<<32)|type` 32-bit boundary
//! especially).
//!
//! THE ROUND'S POWER — up to FOUR independent oracles per value:
//!   (1) native==JIT: the verbatim slice, compiled by native rustc, must equal the JIT.
//!   (2) LINKED PRODUCTION (2nd oracle): the REAL `elf64_st_info`/`Elf64Sym::encode`/
//!       `Elf64Rela::encode`/`Elf64Header::write` etc. run on the same inputs.
//!   (3) ENCODE<->DECODE ROUND-TRIP: `decode(encode(x)) == x` over swept field values;
//!       `extract(pack(a,b)) == (a,b)` for st_info/r_info. An encoder/decoder ASYMMETRY
//!       is a REAL bug (a malformed .o). The r_info 32-bit boundary is swept directly
//!       (sym {0,1,0x7fffffff,0xffffffff} × type {0,1,0x100,0xffffffff}).
//!   (4) ELF-SPEC BYTE LAYOUT: the exact Elf64_Sym / Elf64_Rela / Elf64_Ehdr byte
//!       offsets vs the System-V ELF-64 spec (st_name at [0..4] LE, st_info at [4],
//!       st_value at [8..16] LE, ...; ELF64_SYM_SIZE=24; r_info=(sym<<32)|type; ident
//!       magic 0x7f454c46, EI_CLASS=2, EI_DATA=1) — catches a bug even if encode+decode
//!       share the same mistake.
//!
//! Run tests ONE AT A TIME (`-- --exact <name> --test-threads=1`): the JIT engine is
//! not thread-safe at suite scale (jit-parallel-race-2026-06-29.md). Every JIT
//! execution runs inside a WATCHDOG worker thread; the output POD is 0xDEAD-poisoned
//! before each JIT call so a silent no-op fails loudly.

#![cfg(target_arch = "aarch64")]

use std::collections::HashMap;
use std::sync::mpsc;
use std::time::Duration;

use trust_cg_codegen::Target;
use trust_cg_codegen::compiler::{Compiler, CompilerConfig};

// LINKED PRODUCTION functions/types/constants (the second oracle):
use trust_cg_codegen::elf::constants::{
    ELF64_EHDR_SIZE, ELF64_RELA_SIZE, ELF64_SYM_SIZE, ELFCLASS64, ELFDATA2LSB, ELFMAG0, ELFMAG1,
    ELFMAG2, ELFMAG3, ELFOSABI_NONE, EM_AARCH64, EM_RISCV, EM_X86_64, ET_REL, EV_CURRENT,
    R_AARCH64_ABS64, R_AARCH64_CALL26, SHN_UNDEF, STB_GLOBAL, STB_LOCAL, STB_WEAK, STT_FUNC,
    STT_NOTYPE, STT_OBJECT, STT_SECTION, STV_DEFAULT, elf64_r_info, elf64_r_sym, elf64_r_type,
    elf64_st_bind, elf64_st_info, elf64_st_type,
};
use trust_cg_codegen::elf::header::{Elf64Header, ElfMachine};
use trust_cg_codegen::elf::reloc::Elf64Rela;
use trust_cg_codegen::elf::symbol::Elf64Sym;

// NATIVE ORACLE: the verbatim slice, compiled by native rustc (+ its POD types).
#[path = "slices/trust_elf_writer_slice.rs"]
mod s;

// ── the MIR-emitted trust-ir modules (one per root) ─────────────────────────
const ST_INFO_IR: &str = include_str!("slices/trust_elf_st_info_root.tir");
const R_INFO_IR: &str = include_str!("slices/trust_elf_r_info_root.tir");
const SYM_ENC_IR: &str = include_str!("slices/trust_elf_sym_enc_root.tir");
const SYM_DEC_IR: &str = include_str!("slices/trust_elf_sym_dec_root.tir");
const RELA_ENC_IR: &str = include_str!("slices/trust_elf_rela_enc_root.tir");
const RELA_DEC_IR: &str = include_str!("slices/trust_elf_rela_dec_root.tir");
const HEADER_IR: &str = include_str!("slices/trust_elf_header_root.tir");

// ── shared harness (R24/R28 pattern) ─────────────────────────────────────────

fn jit_module(text: &str, what: &str) -> trust_cg_codegen::jit::ExecutableBuffer {
    let module = trust_ir::parser::parse_module(text)
        .unwrap_or_else(|e| panic!("MIR-emitted `{what}` trust-ir text must parse: {e:?}"));
    let config = CompilerConfig::jit_fast(Target::Aarch64);
    Compiler::new(config)
        .compile_module_to_jit(&module, &HashMap::new())
        .unwrap_or_else(|e| panic!("trust-cg JIT compile of MIR-emitted `{what}` failed: {e:?}"))
        .buffer
}

fn bind_sym(buffer: &trust_cg_codegen::jit::ExecutableBuffer, sym: &str) -> *const u8 {
    buffer
        .get_fn_ptr_bound(sym)
        .unwrap_or_else(|| panic!("JIT symbol `{sym}` not found"))
        .as_ptr()
}

const WATCHDOG_SECS: u64 = 240;

fn run_watchdogged<T: Send + 'static>(
    what: &'static str,
    expected: usize,
    worker: impl FnOnce(mpsc::Sender<T>) + Send + 'static,
) -> Vec<T> {
    let (tx, rx) = mpsc::channel::<T>();
    std::thread::spawn(move || worker(tx));
    let mut rows = Vec::with_capacity(expected);
    for i in 0..expected {
        match rx.recv_timeout(Duration::from_secs(WATCHDOG_SECS)) {
            Ok(row) => rows.push(row),
            Err(_) => panic!(
                "JIT `{what}` HUNG (watchdog {WATCHDOG_SECS}s): no progress at row {i} of {expected}"
            ),
        }
    }
    rows
}

// ── ABI adapters ─────────────────────────────────────────────────────────────
type StInfoFn = unsafe extern "C" fn(u32, u32, *mut s::StInfoOut);
type RInfoFn = unsafe extern "C" fn(u32, u32, *mut s::RInfoOut);
type SymEncFn = unsafe extern "C" fn(u32, u32, u32, u32, u32, u64, u64, *mut s::SymEncOut);
type SymDecFn = unsafe extern "C" fn(u64, u64, u64, *mut s::SymDecOut);
type RelaEncFn = unsafe extern "C" fn(u64, u32, u32, i64, *mut s::RelaEncOut);
type RelaDecFn = unsafe extern "C" fn(u64, u64, u64, *mut s::RelaDecOut);
type HeaderFn = unsafe extern "C" fn(u32, u64, u32, u32, *mut s::HdrOut);

// poison factories
fn poison_st_info() -> s::StInfoOut {
    s::StInfoOut {
        info: 0xDEAD,
        bind_out: 0xDEAD,
        type_out: 0xDEAD,
    }
}
fn poison_r_info() -> s::RInfoOut {
    s::RInfoOut {
        info: 0xDEAD,
        sym_out: 0xDEAD,
        type_out: 0xDEAD,
    }
}
fn poison_sym_enc() -> s::SymEncOut {
    s::SymEncOut {
        w0: 0xDEAD,
        w1: 0xDEAD,
        w2: 0xDEAD,
    }
}
fn poison_sym_dec() -> s::SymDecOut {
    s::SymDecOut {
        st_name: 0xDEAD,
        st_info: 0xDEAD,
        st_other: 0xDEAD,
        st_shndx: 0xDEAD,
        st_value: 0xDEAD,
        st_size: 0xDEAD,
    }
}
fn poison_rela_enc() -> s::RelaEncOut {
    s::RelaEncOut {
        w0: 0xDEAD,
        w1: 0xDEAD,
        w2: 0xDEAD,
    }
}
fn poison_rela_dec() -> s::RelaDecOut {
    s::RelaDecOut {
        r_offset: 0xDEAD,
        r_info: 0xDEAD,
        symbol_index: 0xDEAD,
        reloc_type: 0xDEAD,
        r_addend: 0xDEAD,
    }
}
fn poison_hdr() -> s::HdrOut {
    s::HdrOut {
        w0: 0xDEAD,
        w1: 0xDEAD,
        w2: 0xDEAD,
        w3: 0xDEAD,
        w4: 0xDEAD,
        w5: 0xDEAD,
        w6: 0xDEAD,
        w7: 0xDEAD,
    }
}

// ── little-endian byte<->word packers (match the slice's pack8, LE) ──────────
fn pack_window(b: &[u8], off: usize) -> u64 {
    let mut w = 0u64;
    for i in 0..8 {
        w |= (b[off + i] as u64) << (8 * i);
    }
    w
}
fn pack24(b: &[u8]) -> (u64, u64, u64) {
    (pack_window(b, 0), pack_window(b, 8), pack_window(b, 16))
}
fn pack64(b: &[u8]) -> [u64; 8] {
    let mut w = [0u64; 8];
    for (k, word) in w.iter_mut().enumerate() {
        *word = pack_window(b, 8 * k);
    }
    w
}
/// extract byte `i` from the LE-packed (w0,w1,w2) 24-byte window.
fn byte_of24(w0: u64, w1: u64, w2: u64, i: usize) -> u8 {
    let w = if i < 8 {
        w0
    } else if i < 16 {
        w1
    } else {
        w2
    };
    (w >> (8 * (i % 8))) as u8
}

// ============================================================================
// TEST 1 — st_info PACK/EXTRACT (elf64_st_info / elf64_st_bind / elf64_st_type).
//   native==JIT==production, extract(pack(bind,typ))==(bind,typ) round-trip,
//   EXHAUSTIVE over bind 0..16 × type 0..16.
// ============================================================================
#[test]
fn trust_elf_st_info_pack_extract() {
    // Sweep bind 0..16 × type 0..16 (the round-trip domain) PLUS a few > 15 to
    // exercise the truncating pack (bind<<4 overflows u8 for bind>=16).
    let mut inputs: Vec<(u32, u32)> = Vec::new();
    for bind in 0..16u32 {
        for typ in 0..16u32 {
            inputs.push((bind, typ));
        }
    }
    // a couple of out-of-nibble values (round-trip not expected, just native==JIT).
    for &(b, t) in &[(1u32, 0x1Fu32), (0x11u32, 2u32), (0xFFu32, 0xFFu32)] {
        inputs.push((b, t));
    }
    let expected = inputs.len();
    let sweep = inputs.clone();
    let rows = run_watchdogged::<(u32, u32, u32)>("st_info", expected, move |tx| {
        let b = jit_module(ST_INFO_IR, "st_info");
        let f: StInfoFn = unsafe { std::mem::transmute(bind_sym(&b, "st_info_root")) };
        for &(bind, typ) in &sweep {
            let mut o = poison_st_info();
            unsafe { f(bind, typ, &mut o) };
            if tx.send((o.info, o.bind_out, o.type_out)).is_err() {
                return;
            }
        }
    });

    assert_eq!(rows.len(), expected);
    for (i, &(bind, typ)) in inputs.iter().enumerate() {
        let (info, bo, to) = rows[i];
        assert_ne!(info, 0xDEAD, "row {i} info still poisoned");

        // native oracle
        let mut no = poison_st_info();
        s::st_info_root(bind, typ, &mut no);
        assert_eq!(
            (info, bo, to),
            (no.info, no.bind_out, no.type_out),
            "st_info({bind},{typ}): JIT != native"
        );
        // LINKED production oracle
        let p_info = elf64_st_info(bind as u8, typ as u8);
        let p_bind = elf64_st_bind(p_info);
        let p_type = elf64_st_type(p_info);
        assert_eq!(
            (info, bo, to),
            (p_info as u32, p_bind as u32, p_type as u32),
            "st_info({bind},{typ}): JIT != production"
        );
        // SPEC: info == (bind<<4)|(typ&0xf) (as u8)
        let spec = (((bind as u8) << 4) | ((typ as u8) & 0xf)) as u32;
        assert_eq!(info, spec, "st_info({bind},{typ}) spec pack");
        // ROUND-TRIP on the nibble domain: extract(pack(b,t)) == (b,t).
        if bind < 16 && typ < 16 {
            assert_eq!((bo, to), (bind, typ), "st_info round-trip ({bind},{typ})");
        }
    }

    // Independent named spot-checks (the ELF ABI examples).
    let idx = |b: u32, t: u32| inputs.iter().position(|&x| x == (b, t)).unwrap();
    // STB_GLOBAL(1)|STT_FUNC(2) = 0x12
    assert_eq!(rows[idx(1, 2)].0, 0x12, "GLOBAL|FUNC = 0x12");
    // STB_LOCAL(0)|STT_OBJECT(1) = 0x01
    assert_eq!(rows[idx(0, 1)].0, 0x01, "LOCAL|OBJECT = 0x01");
    // STB_WEAK(2)|STT_SECTION(3) = 0x23
    assert_eq!(rows[idx(2, 3)].0, 0x23, "WEAK|SECTION = 0x23");
    assert_eq!(STB_GLOBAL as u32, 1);
    assert_eq!(STT_FUNC as u32, 2);
    assert_eq!(STB_WEAK as u32, 2);
    assert_eq!(STT_SECTION as u32, 3);
    assert_eq!(STB_LOCAL as u32, 0);
    assert_eq!(STT_OBJECT as u32, 1);
    assert_eq!(STT_NOTYPE as u32, 0);
}

/// ARMED (Test 1): patch the TYPE-field MASK in `elf64_st_info` (`%5 = const u8 15`
/// = 0xf -> 7), dropping bit 3 of the packed symbol TYPE. `st_info(1,15)` then packs
/// 0x17 instead of 0x1F — a malformed symbol whose type reads as 7 not 15. Prove
/// divergence, restore, re-pass.
#[test]
fn trust_elf_st_info_armed_control() {
    const ANCHOR: &str = "%5 = const u8 15";
    assert_eq!(
        ST_INFO_IR.matches(ANCHOR).count(),
        1,
        "corruption anchor must be unique (elf64_st_info type mask 0xf)"
    );
    let corrupted = ST_INFO_IR.replace(ANCHOR, "%5 = const u8 7");
    assert_ne!(corrupted, ST_INFO_IR);

    let (bind, typ) = (1u32, 15u32);
    let corrupt = run_watchdogged::<(u32, u32, u32)>("st_info CORRUPTED", 1, move |tx| {
        let b = jit_module(&corrupted, "st_info CORRUPTED");
        let f: StInfoFn = unsafe { std::mem::transmute(bind_sym(&b, "st_info_root")) };
        let mut o = poison_st_info();
        unsafe { f(bind, typ, &mut o) };
        let _ = tx.send((o.info, o.bind_out, o.type_out));
    })[0];
    let pristine = run_watchdogged::<(u32, u32, u32)>("st_info RESTORED", 1, move |tx| {
        let b = jit_module(ST_INFO_IR, "st_info RESTORED");
        let f: StInfoFn = unsafe { std::mem::transmute(bind_sym(&b, "st_info_root")) };
        let mut o = poison_st_info();
        unsafe { f(bind, typ, &mut o) };
        let _ = tx.send((o.info, o.bind_out, o.type_out));
    })[0];

    let p_info = elf64_st_info(bind as u8, typ as u8) as u32;
    assert_eq!(p_info, 0x1F, "production st_info(1,15) = 0x1F");
    assert_eq!(
        corrupt.0, 0x17,
        "corrupted mask 0x7 drops type bit 3 -> 0x17"
    );
    assert_eq!(corrupt.2, 7, "corrupted type extracts as 7 (not 15)");
    assert_ne!(corrupt.0, p_info, "corrupted JIT DIVERGES from production");
    assert_eq!(
        pristine.0, p_info,
        "pristine module AGREES (restore + re-pass)"
    );
}

// ============================================================================
// TEST 2 — r_info PACK/EXTRACT (elf64_r_info / elf64_r_sym / elf64_r_type).
//   native==JIT==production, extract(pack(sym,typ))==(sym,typ) round-trip, swept at
//   the 32-BIT BOUNDARY (sym {0,1,0x7fffffff,0xffffffff} × type {0,1,0x100,...}).
// ============================================================================
#[test]
fn trust_elf_r_info_pack_extract() {
    let syms: [u32; 6] = [0, 1, 0x7FFF_FFFF, 0x8000_0000, 0xFFFF_FFFF, 0x0012_3456];
    let types: [u32; 8] = [
        0,
        1,
        0x100,
        0xFFFF_FFFF,
        R_AARCH64_ABS64,  // 257
        R_AARCH64_CALL26, // 283
        0x0000_00FF,
        0x8000_0000,
    ];
    let mut inputs: Vec<(u32, u32)> = Vec::new();
    for &sym in &syms {
        for &typ in &types {
            inputs.push((sym, typ));
        }
    }
    let expected = inputs.len();
    let sweep = inputs.clone();
    let rows = run_watchdogged::<(u64, u32, u32)>("r_info", expected, move |tx| {
        let b = jit_module(R_INFO_IR, "r_info");
        let f: RInfoFn = unsafe { std::mem::transmute(bind_sym(&b, "r_info_root")) };
        for &(sym, typ) in &sweep {
            let mut o = poison_r_info();
            unsafe { f(sym, typ, &mut o) };
            if tx.send((o.info, o.sym_out, o.type_out)).is_err() {
                return;
            }
        }
    });

    assert_eq!(rows.len(), expected);
    for (i, &(sym, typ)) in inputs.iter().enumerate() {
        let (info, so, to) = rows[i];
        assert_ne!(so, 0xDEAD, "row {i} sym_out still poisoned");
        // native
        let mut no = poison_r_info();
        s::r_info_root(sym, typ, &mut no);
        assert_eq!(
            (info, so, to),
            (no.info, no.sym_out, no.type_out),
            "r_info({sym:#x},{typ:#x}): JIT != native"
        );
        // production
        let p_info = elf64_r_info(sym, typ);
        assert_eq!(
            (info, so, to),
            (p_info, elf64_r_sym(p_info), elf64_r_type(p_info)),
            "r_info({sym:#x},{typ:#x}): JIT != production"
        );
        // SPEC: info == (sym as u64)<<32 | (typ as u64)
        let spec = ((sym as u64) << 32) | (typ as u64);
        assert_eq!(info, spec, "r_info({sym:#x},{typ:#x}) spec pack");
        // ROUND-TRIP holds for ALL u32 sym,typ (no truncation): extract(pack)==(sym,typ).
        assert_eq!(
            (so, to),
            (sym, typ),
            "r_info round-trip ({sym:#x},{typ:#x}) — 32-bit boundary"
        );
    }

    // Independent boundary spot-checks (the classic (sym<<32)|type packing).
    let idx = |sm: u32, t: u32| inputs.iter().position(|&x| x == (sm, t)).unwrap();
    assert_eq!(
        rows[idx(1, 257)].0,
        0x0000_0001_0000_0101,
        "r_info(1,257) = 0x100000101"
    );
    assert_eq!(
        rows[idx(0xFFFF_FFFF, 0xFFFF_FFFF)].0,
        0xFFFF_FFFF_FFFF_FFFF,
        "r_info(MAX,MAX) all ones"
    );
    // The 32-bit boundary: type in the low half never leaks into sym, and vice versa.
    assert_eq!(
        rows[idx(0x8000_0000, 0x100)].1,
        0x8000_0000,
        "sym recovered across boundary"
    );
    assert_eq!(
        rows[idx(0x8000_0000, 0x100)].2,
        0x100,
        "type recovered across boundary"
    );
}

/// ARMED (Test 2, THE 32-BIT BOUNDARY BUG SITE): patch the symbol-index shift in
/// `elf64_r_info` (`%3 = const i32 32` -> 31), so r_info packs `(sym<<31)|type`
/// instead of `(sym<<32)|type`. The symbol index and relocation type then OVERLAP at
/// bit 31 — the linker resolves the reloc against the WRONG symbol. Prove divergence,
/// restore, re-pass.
#[test]
fn trust_elf_r_info_armed_control() {
    const ANCHOR: &str = "%3 = const i32 32";
    assert_eq!(
        R_INFO_IR.matches(ANCHOR).count(),
        1,
        "corruption anchor must be unique (elf64_r_info sym shift <<32)"
    );
    let corrupted = R_INFO_IR.replace(ANCHOR, "%3 = const i32 31");
    assert_ne!(corrupted, R_INFO_IR);

    let (sym, typ) = (1u32, 257u32);
    let corrupt = run_watchdogged::<(u64, u32, u32)>("r_info CORRUPTED", 1, move |tx| {
        let b = jit_module(&corrupted, "r_info CORRUPTED");
        let f: RInfoFn = unsafe { std::mem::transmute(bind_sym(&b, "r_info_root")) };
        let mut o = poison_r_info();
        unsafe { f(sym, typ, &mut o) };
        let _ = tx.send((o.info, o.sym_out, o.type_out));
    })[0];
    let pristine = run_watchdogged::<(u64, u32, u32)>("r_info RESTORED", 1, move |tx| {
        let b = jit_module(R_INFO_IR, "r_info RESTORED");
        let f: RInfoFn = unsafe { std::mem::transmute(bind_sym(&b, "r_info_root")) };
        let mut o = poison_r_info();
        unsafe { f(sym, typ, &mut o) };
        let _ = tx.send((o.info, o.sym_out, o.type_out));
    })[0];

    let p_info = elf64_r_info(sym, typ);
    assert_eq!(
        p_info, 0x0000_0001_0000_0101,
        "production r_info(1,257) = 0x100000101"
    );
    assert_eq!(
        corrupt.0, 0x0000_0000_8000_0101,
        "corrupted <<31 -> 0x80000101"
    );
    assert_eq!(
        corrupt.1, 0,
        "corrupted sym_out extracts as 0 (bit lost below the boundary)"
    );
    assert_ne!(corrupt.0, p_info, "corrupted JIT DIVERGES from production");
    assert_eq!(
        pristine.0, p_info,
        "pristine module AGREES (restore + re-pass)"
    );
}

// ============================================================================
// TEST 3 — Elf64Sym ENCODE + DECODE round-trip + SPEC layout.
//   native==JIT==production; decode(encode(sym))==sym; the exact Elf64_Sym byte layout.
// ============================================================================

#[derive(Clone, Copy)]
struct SymFields {
    st_name: u32,
    binding: u8,
    sym_type: u8,
    visibility: u8,
    section_index: u16,
    value: u64,
    size: u64,
}

#[allow(clippy::vec_init_then_push)] // Ordered cases document the ELF coverage matrix.
fn sym_inputs() -> Vec<SymFields> {
    let mut v = Vec::new();
    // canonical entries
    v.push(SymFields {
        st_name: 0,
        binding: 0,
        sym_type: 0,
        visibility: 0,
        section_index: 0,
        value: 0,
        size: 0,
    }); // null
    v.push(SymFields {
        st_name: 5,
        binding: STB_GLOBAL,
        sym_type: STT_FUNC,
        visibility: STV_DEFAULT,
        section_index: 1,
        value: 0x1000,
        size: 64,
    });
    v.push(SymFields {
        st_name: 1,
        binding: STB_LOCAL,
        sym_type: STT_OBJECT,
        visibility: STV_DEFAULT,
        section_index: 2,
        value: 0,
        size: 8,
    });
    v.push(SymFields {
        st_name: 1,
        binding: STB_WEAK,
        sym_type: STT_NOTYPE,
        visibility: STV_DEFAULT,
        section_index: SHN_UNDEF,
        value: 0,
        size: 0,
    });
    // field EDGE values (each field at its max / sign-ish boundary)
    v.push(SymFields {
        st_name: 0xFFFF_FFFF,
        binding: 0xF,
        sym_type: 0xF,
        visibility: 0xFF,
        section_index: 0xFFFF,
        value: u64::MAX,
        size: u64::MAX,
    });
    v.push(SymFields {
        st_name: 0x8000_0000,
        binding: 1,
        sym_type: 2,
        visibility: 0,
        section_index: 0x8000,
        value: 0x8000_0000_0000_0000,
        size: 1,
    });
    v.push(SymFields {
        st_name: 0x0102_0304,
        binding: 2,
        sym_type: 1,
        visibility: 2,
        section_index: 0x0506,
        value: 0x0708_090A_0B0C_0D0E,
        size: 0x1122_3344_5566_7788,
    });
    v.push(SymFields {
        st_name: 1,
        binding: 0,
        sym_type: 0,
        visibility: 0,
        section_index: 0xFFF1,
        value: 0xDEAD_BEEF_CAFE_BABE,
        size: 0x00FF_00FF_00FF_00FF,
    });
    v
}

/// Production oracle: build the real Elf64Sym, encode to 24 bytes, pack to (w0,w1,w2).
fn prod_sym_encode(sf: SymFields) -> (u64, u64, u64) {
    let sym = Elf64Sym::new(
        sf.st_name,
        sf.binding,
        sf.sym_type,
        sf.visibility,
        sf.section_index,
        sf.value,
        sf.size,
    );
    let bytes = sym.encode();
    assert_eq!(bytes.len(), ELF64_SYM_SIZE);
    pack24(&bytes)
}

#[test]
fn trust_elf_sym_encode_decode() {
    let inputs = sym_inputs();
    let expected = inputs.len();
    let sweep = inputs.clone();
    // JIT encode, then feed the encoded words back through JIT decode (round-trip).
    let rows = run_watchdogged::<((u64, u64, u64), (u32, u32, u32, u32, u64, u64))>(
        "sym_encdec",
        expected,
        move |tx| {
            let eb = jit_module(SYM_ENC_IR, "sym_enc");
            let db = jit_module(SYM_DEC_IR, "sym_dec");
            let ef: SymEncFn = unsafe { std::mem::transmute(bind_sym(&eb, "sym_enc_root")) };
            let df: SymDecFn = unsafe { std::mem::transmute(bind_sym(&db, "sym_dec_root")) };
            for sf in &sweep {
                let mut eo = poison_sym_enc();
                unsafe {
                    ef(
                        sf.st_name,
                        sf.binding as u32,
                        sf.sym_type as u32,
                        sf.visibility as u32,
                        sf.section_index as u32,
                        sf.value,
                        sf.size,
                        &mut eo,
                    )
                };
                let mut deco = poison_sym_dec();
                unsafe { df(eo.w0, eo.w1, eo.w2, &mut deco) };
                if tx
                    .send((
                        (eo.w0, eo.w1, eo.w2),
                        (
                            deco.st_name,
                            deco.st_info,
                            deco.st_other,
                            deco.st_shndx,
                            deco.st_value,
                            deco.st_size,
                        ),
                    ))
                    .is_err()
                {
                    return;
                }
            }
        },
    );

    assert_eq!(rows.len(), expected);
    for (i, sf) in inputs.iter().enumerate() {
        let ((w0, w1, w2), dec) = rows[i];
        assert_ne!(w0, 0xDEAD, "row {i} w0 still poisoned");

        // native encode oracle
        let mut neo = poison_sym_enc();
        s::sym_enc_root(
            sf.st_name,
            sf.binding as u32,
            sf.sym_type as u32,
            sf.visibility as u32,
            sf.section_index as u32,
            sf.value,
            sf.size,
            &mut neo,
        );
        assert_eq!(
            (w0, w1, w2),
            (neo.w0, neo.w1, neo.w2),
            "sym encode row {i}: JIT != native"
        );
        // LINKED production encode oracle (byte-for-byte)
        assert_eq!(
            (w0, w1, w2),
            prod_sym_encode(*sf),
            "sym encode row {i}: JIT != production"
        );

        // SPEC — the exact Elf64_Sym byte layout (System V ELF-64).
        let st_info = elf64_st_info(sf.binding, sf.sym_type);
        assert_eq!(
            byte_of24(w0, w1, w2, 0),
            sf.st_name as u8,
            "st_name[0] @ byte0"
        );
        assert_eq!(
            byte_of24(w0, w1, w2, 1),
            (sf.st_name >> 8) as u8,
            "st_name[1] @ byte1"
        );
        assert_eq!(
            byte_of24(w0, w1, w2, 2),
            (sf.st_name >> 16) as u8,
            "st_name[2] @ byte2"
        );
        assert_eq!(
            byte_of24(w0, w1, w2, 3),
            (sf.st_name >> 24) as u8,
            "st_name[3] @ byte3"
        );
        assert_eq!(byte_of24(w0, w1, w2, 4), st_info, "st_info @ byte4");
        assert_eq!(byte_of24(w0, w1, w2, 5), sf.visibility, "st_other @ byte5");
        assert_eq!(
            byte_of24(w0, w1, w2, 6),
            sf.section_index as u8,
            "st_shndx[0] @ byte6"
        );
        assert_eq!(
            byte_of24(w0, w1, w2, 7),
            (sf.section_index >> 8) as u8,
            "st_shndx[1] @ byte7"
        );
        // st_value at [8..16] LE == w1
        assert_eq!(w1, sf.value, "st_value @ [8..16] LE");
        // st_size at [16..24] LE == w2
        assert_eq!(w2, sf.size, "st_size @ [16..24] LE");

        // ROUND-TRIP: decode(encode(sym)) == sym (the field values back).
        let (d_name, d_info, d_other, d_shndx, d_value, d_size) = dec;
        assert_eq!(d_name, sf.st_name, "roundtrip st_name row {i}");
        assert_eq!(d_info as u8, st_info, "roundtrip st_info row {i}");
        assert_eq!(d_other as u8, sf.visibility, "roundtrip st_other row {i}");
        assert_eq!(
            d_shndx as u16, sf.section_index,
            "roundtrip st_shndx row {i}"
        );
        assert_eq!(d_value, sf.value, "roundtrip st_value row {i}");
        assert_eq!(d_size, sf.size, "roundtrip st_size row {i}");

        // Cross-check the round-trip against the LINKED production decode too.
        let mut b = [0u8; ELF64_SYM_SIZE];
        for k in 0..8 {
            b[k] = (w0 >> (8 * k)) as u8;
            b[k + 8] = (w1 >> (8 * k)) as u8;
            b[k + 16] = (w2 >> (8 * k)) as u8;
        }
        let p_dec = Elf64Sym::decode(&b);
        assert_eq!(
            p_dec.st_name, sf.st_name,
            "production decode st_name row {i}"
        );
        assert_eq!(p_dec.st_info, st_info, "production decode st_info row {i}");
        assert_eq!(
            p_dec.st_shndx, sf.section_index,
            "production decode st_shndx row {i}"
        );
        assert_eq!(
            p_dec.st_value, sf.value,
            "production decode st_value row {i}"
        );
        assert_eq!(p_dec.st_size, sf.size, "production decode st_size row {i}");
    }
}

/// ARMED (Test 3): patch the TYPE-field MASK inside `Elf64Sym::encode`'s
/// `elf64_st_info` (`%5 = const u8 15` = 0xf -> 7), dropping bit 3 of the symbol TYPE
/// that lands at spec byte 4 (st_info). A symbol with type nibble 0xF then encodes
/// st_info type = 7 at byte 4 — a malformed symbol the linker mis-types. Prove
/// divergence (at the st_info byte), restore, re-pass.
#[test]
fn trust_elf_sym_encode_armed_control() {
    const ANCHOR: &str = "%5 = const u8 15";
    assert_eq!(
        SYM_ENC_IR.matches(ANCHOR).count(),
        1,
        "corruption anchor must be unique (elf64_st_info type mask 0xf in encode closure)"
    );
    let corrupted = SYM_ENC_IR.replace(ANCHOR, "%5 = const u8 7");
    assert_ne!(corrupted, SYM_ENC_IR);

    // binding=GLOBAL(1), type nibble = 0xF -> st_info = 0x1F at byte 4; visibility=0.
    let sf = SymFields {
        st_name: 5,
        binding: STB_GLOBAL,
        sym_type: 0xF,
        visibility: STV_DEFAULT,
        section_index: 1,
        value: 0x1000,
        size: 64,
    };
    let corrupt = run_watchdogged::<(u64, u64, u64)>("sym enc CORRUPTED", 1, move |tx| {
        let b = jit_module(&corrupted, "sym enc CORRUPTED");
        let f: SymEncFn = unsafe { std::mem::transmute(bind_sym(&b, "sym_enc_root")) };
        let mut o = poison_sym_enc();
        unsafe {
            f(
                sf.st_name,
                sf.binding as u32,
                sf.sym_type as u32,
                sf.visibility as u32,
                sf.section_index as u32,
                sf.value,
                sf.size,
                &mut o,
            )
        };
        let _ = tx.send((o.w0, o.w1, o.w2));
    })[0];
    let pristine = run_watchdogged::<(u64, u64, u64)>("sym enc RESTORED", 1, move |tx| {
        let b = jit_module(SYM_ENC_IR, "sym enc RESTORED");
        let f: SymEncFn = unsafe { std::mem::transmute(bind_sym(&b, "sym_enc_root")) };
        let mut o = poison_sym_enc();
        unsafe {
            f(
                sf.st_name,
                sf.binding as u32,
                sf.sym_type as u32,
                sf.visibility as u32,
                sf.section_index as u32,
                sf.value,
                sf.size,
                &mut o,
            )
        };
        let _ = tx.send((o.w0, o.w1, o.w2));
    })[0];

    let prod = prod_sym_encode(sf);
    assert_eq!(
        byte_of24(prod.0, prod.1, prod.2, 4),
        0x1F,
        "production st_info=0x1F @ byte4"
    );
    assert_eq!(
        byte_of24(corrupt.0, corrupt.1, corrupt.2, 4),
        0x17,
        "corrupted st_info type bit dropped -> 0x17 @ byte4"
    );
    assert_ne!(corrupt, prod, "corrupted JIT DIVERGES from production");
    assert_eq!(pristine, prod, "pristine module AGREES (restore + re-pass)");
}

// ============================================================================
// TEST 4 — Elf64Rela ENCODE + DECODE round-trip + SPEC layout.
//   native==JIT==production; decode(encode(rela))==rela; the exact Elf64_Rela layout,
//   incl. the r_info=(sym<<32)|type packing and the SIGNED r_addend edges.
// ============================================================================

#[derive(Clone, Copy)]
struct RelaFields {
    r_offset: u64,
    symbol_index: u32,
    reloc_type: u32,
    r_addend: i64,
}

#[allow(clippy::vec_init_then_push)] // Ordered cases document the ELF coverage matrix.
fn rela_inputs() -> Vec<RelaFields> {
    let mut v = Vec::new();
    v.push(RelaFields {
        r_offset: 0,
        symbol_index: 0,
        reloc_type: 0,
        r_addend: 0,
    });
    v.push(RelaFields {
        r_offset: 0x100,
        symbol_index: 5,
        reloc_type: R_AARCH64_CALL26,
        r_addend: 0,
    });
    v.push(RelaFields {
        r_offset: 0x10,
        symbol_index: 2,
        reloc_type: R_AARCH64_ABS64,
        r_addend: 0x1000,
    });
    // negative addend edges (the SIGNED i64 field)
    v.push(RelaFields {
        r_offset: 0x20,
        symbol_index: 1,
        reloc_type: 2,
        r_addend: -4,
    });
    v.push(RelaFields {
        r_offset: 0x30,
        symbol_index: 7,
        reloc_type: 9,
        r_addend: -1,
    });
    v.push(RelaFields {
        r_offset: 0x40,
        symbol_index: 3,
        reloc_type: 4,
        r_addend: i64::MIN,
    });
    v.push(RelaFields {
        r_offset: 0x50,
        symbol_index: 4,
        reloc_type: 1,
        r_addend: i64::MAX,
    });
    // 32-bit symbol-index boundary in the r_info field
    v.push(RelaFields {
        r_offset: u64::MAX,
        symbol_index: 0xFFFF_FFFF,
        reloc_type: 0xFFFF_FFFF,
        r_addend: -1,
    });
    v.push(RelaFields {
        r_offset: 0x0102_0304_0506_0708,
        symbol_index: 0x8000_0000,
        reloc_type: 0x100,
        r_addend: 0x1122_3344_5566_7788,
    });
    v.push(RelaFields {
        r_offset: 0xDEAD_BEEF,
        symbol_index: 0x7FFF_FFFF,
        reloc_type: 257,
        r_addend: -0x8000_0000,
    });
    v
}

/// Production oracle: build the real Elf64Rela, encode, pack to (w0,w1,w2).
fn prod_rela_encode(rf: RelaFields) -> (u64, u64, u64) {
    let rela = Elf64Rela::new(rf.r_offset, rf.symbol_index, rf.reloc_type, rf.r_addend);
    let bytes = rela.encode();
    assert_eq!(bytes.len(), ELF64_RELA_SIZE);
    pack24(&bytes)
}

#[test]
fn trust_elf_rela_encode_decode() {
    let inputs = rela_inputs();
    let expected = inputs.len();
    let sweep = inputs.clone();
    let rows = run_watchdogged::<((u64, u64, u64), (u64, u64, u32, u32, i64))>(
        "rela_encdec",
        expected,
        move |tx| {
            let eb = jit_module(RELA_ENC_IR, "rela_enc");
            let db = jit_module(RELA_DEC_IR, "rela_dec");
            let ef: RelaEncFn = unsafe { std::mem::transmute(bind_sym(&eb, "rela_enc_root")) };
            let df: RelaDecFn = unsafe { std::mem::transmute(bind_sym(&db, "rela_dec_root")) };
            for rf in &sweep {
                let mut eo = poison_rela_enc();
                unsafe {
                    ef(
                        rf.r_offset,
                        rf.symbol_index,
                        rf.reloc_type,
                        rf.r_addend,
                        &mut eo,
                    )
                };
                let mut deco = poison_rela_dec();
                unsafe { df(eo.w0, eo.w1, eo.w2, &mut deco) };
                if tx
                    .send((
                        (eo.w0, eo.w1, eo.w2),
                        (
                            deco.r_offset,
                            deco.r_info,
                            deco.symbol_index,
                            deco.reloc_type,
                            deco.r_addend,
                        ),
                    ))
                    .is_err()
                {
                    return;
                }
            }
        },
    );

    assert_eq!(rows.len(), expected);
    for (i, rf) in inputs.iter().enumerate() {
        let ((w0, w1, w2), dec) = rows[i];
        assert_ne!(w0, 0xDEAD, "row {i} w0 still poisoned");

        // native encode oracle
        let mut neo = poison_rela_enc();
        s::rela_enc_root(
            rf.r_offset,
            rf.symbol_index,
            rf.reloc_type,
            rf.r_addend,
            &mut neo,
        );
        assert_eq!(
            (w0, w1, w2),
            (neo.w0, neo.w1, neo.w2),
            "rela encode row {i}: JIT != native"
        );
        // LINKED production encode oracle (byte-for-byte)
        assert_eq!(
            (w0, w1, w2),
            prod_rela_encode(*rf),
            "rela encode row {i}: JIT != production"
        );

        // SPEC — the exact Elf64_Rela byte layout.
        assert_eq!(w0, rf.r_offset, "r_offset @ [0..8] LE");
        let r_info = elf64_r_info(rf.symbol_index, rf.reloc_type);
        assert_eq!(w1, r_info, "r_info @ [8..16] LE = (sym<<32)|type");
        assert_eq!(
            w2, rf.r_addend as u64,
            "r_addend @ [16..24] LE (signed bit pattern)"
        );

        // ROUND-TRIP: decode(encode(rela)) == rela.
        let (d_off, d_info, d_sym, d_type, d_add) = dec;
        assert_eq!(d_off, rf.r_offset, "roundtrip r_offset row {i}");
        assert_eq!(d_info, r_info, "roundtrip r_info row {i}");
        assert_eq!(d_sym, rf.symbol_index, "roundtrip symbol_index row {i}");
        assert_eq!(d_type, rf.reloc_type, "roundtrip reloc_type row {i}");
        assert_eq!(d_add, rf.r_addend, "roundtrip r_addend row {i}");

        // Cross-check round-trip against LINKED production decode.
        let mut b = [0u8; ELF64_RELA_SIZE];
        for k in 0..8 {
            b[k] = (w0 >> (8 * k)) as u8;
            b[k + 8] = (w1 >> (8 * k)) as u8;
            b[k + 16] = (w2 >> (8 * k)) as u8;
        }
        let p_dec = Elf64Rela::decode(&b);
        assert_eq!(
            p_dec.r_offset, rf.r_offset,
            "production decode r_offset row {i}"
        );
        assert_eq!(
            p_dec.symbol_index, rf.symbol_index,
            "production decode symbol_index row {i}"
        );
        assert_eq!(
            p_dec.reloc_type, rf.reloc_type,
            "production decode reloc_type row {i}"
        );
        assert_eq!(
            p_dec.r_addend, rf.r_addend,
            "production decode r_addend row {i}"
        );
    }
}

/// ARMED (Test 4, THE 32-BIT BOUNDARY at the reloc's r_info field): patch the
/// symbol-index shift inside `Elf64Rela::encode`'s `elf64_r_info`
/// (`%3 = const i32 32` -> 31), so the r_info packed into spec bytes [8..16] becomes
/// `(sym<<31)|type` — the linker resolves the reloc against the WRONG symbol. Prove
/// divergence (at the r_info word w1), restore, re-pass.
#[test]
fn trust_elf_rela_encode_armed_control() {
    const ANCHOR: &str = "%3 = const i32 32";
    assert_eq!(
        RELA_ENC_IR.matches(ANCHOR).count(),
        1,
        "corruption anchor must be unique (elf64_r_info sym shift <<32 in encode closure)"
    );
    let corrupted = RELA_ENC_IR.replace(ANCHOR, "%3 = const i32 31");
    assert_ne!(corrupted, RELA_ENC_IR);

    let rf = RelaFields {
        r_offset: 0x100,
        symbol_index: 5,
        reloc_type: R_AARCH64_CALL26,
        r_addend: 0x1122_3344_5566_7788,
    };
    let corrupt = run_watchdogged::<(u64, u64, u64)>("rela enc CORRUPTED", 1, move |tx| {
        let b = jit_module(&corrupted, "rela enc CORRUPTED");
        let f: RelaEncFn = unsafe { std::mem::transmute(bind_sym(&b, "rela_enc_root")) };
        let mut o = poison_rela_enc();
        unsafe {
            f(
                rf.r_offset,
                rf.symbol_index,
                rf.reloc_type,
                rf.r_addend,
                &mut o,
            )
        };
        let _ = tx.send((o.w0, o.w1, o.w2));
    })[0];
    let pristine = run_watchdogged::<(u64, u64, u64)>("rela enc RESTORED", 1, move |tx| {
        let b = jit_module(RELA_ENC_IR, "rela enc RESTORED");
        let f: RelaEncFn = unsafe { std::mem::transmute(bind_sym(&b, "rela_enc_root")) };
        let mut o = poison_rela_enc();
        unsafe {
            f(
                rf.r_offset,
                rf.symbol_index,
                rf.reloc_type,
                rf.r_addend,
                &mut o,
            )
        };
        let _ = tx.send((o.w0, o.w1, o.w2));
    })[0];

    let prod = prod_rela_encode(rf);
    let correct_info = elf64_r_info(rf.symbol_index, rf.reloc_type); // (5<<32)|CALL26
    let corrupt_info = ((rf.symbol_index as u64) << 31) | (rf.reloc_type as u64);
    assert_eq!(
        prod.1, correct_info,
        "production r_info @ w1 = (5<<32)|type"
    );
    assert_eq!(
        corrupt.1, corrupt_info,
        "corrupted r_info @ w1 = (5<<31)|type"
    );
    assert_ne!(
        corrupt.1, prod.1,
        "corrupted JIT r_info word DIVERGES from production"
    );
    assert_eq!(pristine, prod, "pristine module AGREES (restore + re-pass)");
}

// ============================================================================
// TEST 5 — Elf64Header (ident/magic + to_e_machine + field layout).
//   native==JIT==production; the exact Elf64_Ehdr byte layout over all 3 machines.
// ============================================================================

fn header_inputs() -> Vec<(u32, u64, u32, u32)> {
    // (machine_tag, sh_offset, sh_num, sh_strndx)
    let mut v = Vec::new();
    for machine in 0..3u32 {
        v.push((machine, 0, 0, 0));
        v.push((machine, 0x1234, 8, 6));
        v.push((machine, 0x0102_0304_0506_0708, 0xABCD, 0x1234));
        v.push((machine, u64::MAX, 0xFFFF, 0xFFFF));
    }
    v
}

fn prod_e_machine(tag: u32) -> u16 {
    let m = match tag {
        0 => ElfMachine::AArch64,
        1 => ElfMachine::X86_64,
        _ => ElfMachine::Riscv64,
    };
    m.to_e_machine()
}

/// Production oracle: build the real Elf64Header, write to a Vec, pack to 8 words.
fn prod_header(tag: u32, sh_offset: u64, sh_num: u32, sh_strndx: u32) -> [u64; 8] {
    let m = match tag {
        0 => ElfMachine::AArch64,
        1 => ElfMachine::X86_64,
        _ => ElfMachine::Riscv64,
    };
    let h = Elf64Header::new(m, sh_offset, sh_num as u16, sh_strndx as u16);
    let mut buf = Vec::new();
    h.write(&mut buf);
    assert_eq!(buf.len(), ELF64_EHDR_SIZE);
    pack64(&buf)
}

#[test]
fn trust_elf_header_write() {
    let inputs = header_inputs();
    let expected = inputs.len();
    let sweep = inputs.clone();
    let rows = run_watchdogged::<[u64; 8]>("header", expected, move |tx| {
        let b = jit_module(HEADER_IR, "header");
        let f: HeaderFn = unsafe { std::mem::transmute(bind_sym(&b, "header_root")) };
        for &(tag, sh_offset, sh_num, sh_strndx) in &sweep {
            let mut o = poison_hdr();
            unsafe { f(tag, sh_offset, sh_num, sh_strndx, &mut o) };
            if tx
                .send([o.w0, o.w1, o.w2, o.w3, o.w4, o.w5, o.w6, o.w7])
                .is_err()
            {
                return;
            }
        }
    });

    assert_eq!(rows.len(), expected);
    for (i, &(tag, sh_offset, sh_num, sh_strndx)) in inputs.iter().enumerate() {
        let w = rows[i];
        assert_ne!(w[0], 0xDEAD, "row {i} w0 still poisoned");

        // native oracle
        let mut no = poison_hdr();
        s::header_root(tag, sh_offset, sh_num, sh_strndx, &mut no);
        assert_eq!(
            w,
            [no.w0, no.w1, no.w2, no.w3, no.w4, no.w5, no.w6, no.w7],
            "header row {i}: JIT != native"
        );
        // LINKED production oracle (byte-for-byte)
        assert_eq!(
            w,
            prod_header(tag, sh_offset, sh_num, sh_strndx),
            "header row {i}: JIT != production"
        );

        // SPEC — the exact Elf64_Ehdr byte layout.
        let byte = |k: usize| -> u8 { (w[k / 8] >> (8 * (k % 8))) as u8 };
        // e_ident magic 0x7f 'E' 'L' 'F'
        assert_eq!(byte(0), 0x7f, "EI_MAG0 = 0x7f");
        assert_eq!(byte(1), b'E', "EI_MAG1 = 'E'");
        assert_eq!(byte(2), b'L', "EI_MAG2 = 'L'");
        assert_eq!(byte(3), b'F', "EI_MAG3 = 'F'");
        assert_eq!(byte(4), 2, "EI_CLASS = ELFCLASS64 (2)");
        assert_eq!(byte(5), 1, "EI_DATA = ELFDATA2LSB (1)");
        assert_eq!(byte(6), 1, "EI_VERSION = EV_CURRENT (1)");
        assert_eq!(byte(7), 0, "EI_OSABI = ELFOSABI_NONE (0)");
        // e_type at [16..18] = ET_REL (1)
        let e_type = (byte(16) as u16) | ((byte(17) as u16) << 8);
        assert_eq!(e_type, ET_REL, "e_type = ET_REL");
        // e_machine at [18..20]
        let e_machine = (byte(18) as u16) | ((byte(19) as u16) << 8);
        assert_eq!(
            e_machine,
            prod_e_machine(tag),
            "e_machine matches to_e_machine"
        );
        // e_version at [20..24] = 1
        let e_version = w[2] >> 32; // bytes [20..24] are the high 4 bytes of w2
        assert_eq!(e_version as u32, 1, "e_version = 1");
        // e_entry [24..32] = 0 ; e_phoff [32..40] = 0
        assert_eq!(w[3], 0, "e_entry = 0");
        assert_eq!(w[4], 0, "e_phoff = 0");
        // e_shoff at [40..48] = sh_offset
        assert_eq!(w[5], sh_offset, "e_shoff = sh_offset");
        // e_flags [48..52] = 0 ; e_ehsize [52..54] = 64
        let e_flags = (w[6] & 0xFFFF_FFFF) as u32;
        assert_eq!(e_flags, 0, "e_flags = 0");
        let e_ehsize = (byte(52) as u16) | ((byte(53) as u16) << 8);
        assert_eq!(e_ehsize as usize, ELF64_EHDR_SIZE, "e_ehsize = 64");
        // e_phentsize [54..56] = 0 ; e_phnum [56..58] = 0
        let e_phnum = (byte(56) as u16) | ((byte(57) as u16) << 8);
        assert_eq!(e_phnum, 0, "e_phnum = 0 (relocatable object)");
        // e_shentsize [58..60] = 64
        let e_shentsize = (byte(58) as u16) | ((byte(59) as u16) << 8);
        assert_eq!(e_shentsize, 64, "e_shentsize = 64");
        // e_shnum [60..62] = sh_num ; e_shstrndx [62..64] = sh_strndx
        let e_shnum = (byte(60) as u16) | ((byte(61) as u16) << 8);
        assert_eq!(e_shnum, sh_num as u16, "e_shnum = sh_num");
        let e_shstrndx = (byte(62) as u16) | ((byte(63) as u16) << 8);
        assert_eq!(e_shstrndx, sh_strndx as u16, "e_shstrndx = sh_strndx");
    }

    // Independent machine spot-checks: to_e_machine values per the ELF ABI.
    assert_eq!(EM_AARCH64, 183);
    assert_eq!(EM_X86_64, 62);
    assert_eq!(EM_RISCV, 243);
    assert_eq!(prod_e_machine(0), 183, "AArch64 -> 183");
    assert_eq!(prod_e_machine(1), 62, "X86_64 -> 62");
    assert_eq!(prod_e_machine(2), 243, "Riscv64 -> 243");
    // sanity: named ELF ident constants
    assert_eq!(ELFMAG0, 0x7f);
    assert_eq!(ELFMAG1, b'E');
    assert_eq!(ELFMAG2, b'L');
    assert_eq!(ELFMAG3, b'F');
    assert_eq!(ELFCLASS64, 2);
    assert_eq!(ELFDATA2LSB, 1);
    assert_eq!(EV_CURRENT, 1);
    assert_eq!(ELFOSABI_NONE, 0);
}

/// ARMED (Test 5): patch the ELF magic byte 0 in `Elf64Header::write`'s ident array
/// (`%106 = const u8 127` = 0x7f -> 126 = 0x7e). The emitted file no longer begins
/// with the ELF magic `0x7f 'E' 'L' 'F'` — every ELF consumer rejects it. Prove
/// divergence, restore, re-pass.
#[test]
fn trust_elf_header_armed_control() {
    const ANCHOR: &str = "%106 = const u8 127";
    assert_eq!(
        HEADER_IR.matches(ANCHOR).count(),
        1,
        "corruption anchor must be unique (ELF magic byte 0 = 0x7f)"
    );
    let corrupted = HEADER_IR.replace(ANCHOR, "%106 = const u8 126");
    assert_ne!(corrupted, HEADER_IR);

    let (tag, sh_offset, sh_num, sh_strndx) = (0u32, 0x1234u64, 8u32, 6u32);
    let corrupt = run_watchdogged::<[u64; 8]>("header CORRUPTED", 1, move |tx| {
        let b = jit_module(&corrupted, "header CORRUPTED");
        let f: HeaderFn = unsafe { std::mem::transmute(bind_sym(&b, "header_root")) };
        let mut o = poison_hdr();
        unsafe { f(tag, sh_offset, sh_num, sh_strndx, &mut o) };
        let _ = tx.send([o.w0, o.w1, o.w2, o.w3, o.w4, o.w5, o.w6, o.w7]);
    })[0];
    let pristine = run_watchdogged::<[u64; 8]>("header RESTORED", 1, move |tx| {
        let b = jit_module(HEADER_IR, "header RESTORED");
        let f: HeaderFn = unsafe { std::mem::transmute(bind_sym(&b, "header_root")) };
        let mut o = poison_hdr();
        unsafe { f(tag, sh_offset, sh_num, sh_strndx, &mut o) };
        let _ = tx.send([o.w0, o.w1, o.w2, o.w3, o.w4, o.w5, o.w6, o.w7]);
    })[0];

    let prod = prod_header(tag, sh_offset, sh_num, sh_strndx);
    assert_eq!(
        (prod[0] & 0xff) as u8,
        0x7f,
        "production magic byte 0 = 0x7f"
    );
    assert_eq!(
        (corrupt[0] & 0xff) as u8,
        0x7e,
        "corrupted magic byte 0 = 0x7e (invalid ELF)"
    );
    assert_ne!(
        corrupt[0], prod[0],
        "corrupted JIT DIVERGES from production"
    );
    assert_eq!(pristine, prod, "pristine module AGREES (restore + re-pass)");
}
