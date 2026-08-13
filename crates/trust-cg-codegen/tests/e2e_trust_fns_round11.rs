//! TRUST-SELF ROUND 24 (thread R24, TRUST BATCH 11): verifying trust-cg's
//! machine-code EMITTER / RELOCATION / FIXUP layer — the place where the final
//! instruction-word and relocation-record BYTES are produced — through the full
//! pipeline Rust -> MIR -> trust-ir (stage1 `trust_ir_mir --mir-emit-closure`)
//! -> trust-cg JIT -> machine code, asserting native Rust == JIT over swept real
//! inputs, with the LINKED PRODUCTION functions as a SECOND oracle (the
//! round-7/16/20/22/23 dual-oracle discipline).
//!
//! WHY THIS IS THE MOST SOUNDNESS-CRITICAL SURFACE: prior rounds verified the
//! instruction-word BUILDERS (1/3/7/16 — opcode+fields -> word), the register
//! files (5/16), the opt/analysis/addressing predicates (20/21), the
//! scheduler/regalloc/ABI deciders (22/23). This round targets the LAST mile:
//!   * the FIXUP byte-PATCH functions (`apply_branch26`/`apply_page21`/
//!     `apply_pageoff12`) that splice a PC-relative displacement into an
//!     already-built instruction word after final layout — a single wrong bit
//!     in the imm26 / ADRP immhi|immlo / pageoff12 field sends the branch or the
//!     load to the WRONG ADDRESS;
//!   * the RELOCATION-RECORD word assembly (`encode_relocation` /
//!     `encode_x86_64_relocation`) — the little-endian r_word1 bitfield the
//!     LINKER consumes; a wrong bit is a wrong link;
//!   * the relocation-kind predicates (`is_pc_relative` / `default_log2_size` /
//!     `needs_addend_reloc`) that decide pc-rel and the field width;
//!   * the branch-range / veneer decider (`branch_range`) — "does this
//!     displacement fit or need relaxation", swept at the EXACT ±128MB/±1MB/
//!     ±32KB encoding boundaries.
//!
//! Bit-exact byte output is the whole point, so the sweeps hit the ENCODING
//! BOUNDARY cases directly: the max in-range offset, the off-by-one out-of-range
//! word, the sign boundary of the signed displacement, the alignment edges, and
//! the exact bit-field mask edges — where encoder bugs hide.
//!
//! DUAL ORACLE: every production fn exercised here is PUBLIC and LINKED into this
//! test binary (`trust_cg_codegen::macho::fixup::apply_*`,
//! `::macho::reloc::{encode_relocation, AArch64RelocKind, ...}`,
//! `::macho::x86_64_reloc::{encode_x86_64_relocation, X86_64RelocKind}`,
//! `::relax::branch_range`). The slice models (scalar-field-in / error-code-out,
//! see each slice header) are cross-checked against the REAL functions run on
//! real inputs at every boundary — so native==JIT proves the JIT machine code
//! reproduces the production byte output.
//!
//! COVERAGE NOTE: gated to aarch64 (the JIT target). Run tests ONE AT A TIME
//! (`-- --exact <name> --test-threads=1`): the JIT engine is not thread-safe at
//! suite scale (jit-parallel-race-2026-06-29.md). Every JIT execution runs
//! inside a WATCHDOG worker thread. The output POD is 0xDEAD-poisoned before
//! each JIT call so a silent no-op fails loudly.

#![cfg(target_arch = "aarch64")]

use std::collections::HashMap;
use std::sync::mpsc;
use std::time::Duration;

use trust_cg_codegen::Target;
use trust_cg_codegen::compiler::{Compiler, CompilerConfig};

// LINKED PRODUCTION functions/types (the second oracle):
use trust_cg_codegen::macho::fixup::{
    Fixup, FixupError, FixupTarget, apply_branch26, apply_page21, apply_pageoff12,
};
use trust_cg_codegen::macho::reloc::{
    AArch64RelocKind, Relocation, decode_relocation, encode_relocation,
};
use trust_cg_codegen::macho::x86_64_reloc::{
    X86_64RelocKind, X86_64Relocation, decode_x86_64_relocation, encode_x86_64_relocation,
};

// ── shared harness (round-9/10/22/23 pattern) ─────────────────────────────────

const FIXUP_PATCH_IR: &str = include_str!("slices/trust_fixup_patch.tir");
const RELOC_WORD_IR: &str = include_str!("slices/trust_reloc_word.tir");

fn jit_module(text: &str, what: &str) -> trust_cg_codegen::jit::ExecutableBuffer {
    let module = trust_ir::parser::parse_module(text)
        .unwrap_or_else(|e| panic!("MIR-emitted `{what}` trust-ir text must parse: {e:?}"));
    let config = CompilerConfig::jit_fast(Target::Aarch64);
    Compiler::new(config)
        .compile_module_to_jit(&module, &HashMap::new())
        .unwrap_or_else(|e| panic!("trust-cg JIT compile of MIR-emitted `{what}` failed: {e:?}"))
        .buffer
}

fn bind(buffer: &trust_cg_codegen::jit::ExecutableBuffer, sym: &str) -> *const u8 {
    buffer
        .get_fn_ptr_bound(sym)
        .unwrap_or_else(|| panic!("JIT symbol `{sym}` not found"))
        .as_ptr()
}

const WATCHDOG_SECS: u64 = 120;

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

// ============================================================================
// SLICE 1 — the AArch64 FIXUP BYTE-PATCH layer (macho/fixup.rs).
//   apply_branch26 / apply_page21 / apply_pageoff12
// ============================================================================

#[repr(C)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct FixupPatchOut {
    patched: u32,
    err: u32,
}

impl FixupPatchOut {
    fn poisoned() -> Self {
        FixupPatchOut {
            patched: 0xDEAD_BEEF,
            err: 0xDEAD,
        }
    }
}

type FixupPatchFn = unsafe extern "C" fn(u32, i64, u32, u32, *mut FixupPatchOut);

/// Native dual-oracle: drive the REAL linked `apply_*` and reduce to the slice's
/// (patched_word, err_code) shape. Production lumps misalign+range into
/// `RelocationOverflow` (different messages, same variant) and `apply_pageoff12`
/// PANICS on out-of-range/misaligned — we classify independently and, for
/// pageoff12, catch the panic. The Ok-path patched WORD is production's byte
/// output (`u32::from_le_bytes(bytes)`), verified byte-for-byte against the JIT.
fn nat_fixup(insn: u32, off: i64, shift: u32, which: u32) -> (u32, u32) {
    match which {
        0 => {
            let mut b = insn.to_le_bytes();
            match apply_branch26(&mut b, off) {
                Ok(()) => (u32::from_le_bytes(b), 0),
                Err(FixupError::RelocationOverflow { .. }) => {
                    (insn, if off & 3 != 0 { 1 } else { 2 })
                }
                Err(e) => panic!("branch26({insn:#x},{off}) unexpected err {e:?}"),
            }
        }
        1 => {
            let mut b = insn.to_le_bytes();
            match apply_page21(&mut b, off) {
                Ok(()) => (u32::from_le_bytes(b), 0),
                Err(FixupError::RelocationOverflow { .. }) => (insn, 2),
                Err(e) => panic!("page21({insn:#x},{off}) unexpected err {e:?}"),
            }
        }
        _ => {
            let po = off as u32;
            let sh = shift as u8;
            let res = std::panic::catch_unwind(|| {
                let mut b = insn.to_le_bytes();
                apply_pageoff12(&mut b, po, sh);
                u32::from_le_bytes(b)
            });
            match res {
                Ok(word) => (word, 0),
                Err(_) => {
                    let code = if po >= 4096 {
                        2
                    } else if sh > 0 && po & ((1u32 << sh) - 1) != 0 {
                        1
                    } else {
                        3
                    };
                    (insn, code)
                }
            }
        }
    }
}

fn fixup_inputs() -> Vec<(u32, i64, u32, u32)> {
    let mut v: Vec<(u32, i64, u32, u32)> = Vec::new();

    // ---- Branch26 (which=0) : imm26 = byte_offset>>2, bits[25:0]. ----
    // Range: word_offset in [-2^25, 2^25) -> byte_offset in [-134217728, 134217724].
    let b_insns = [0x9400_0000u32, 0x1400_0000u32, 0xFFFF_FFFFu32];
    let b_offs: &[i64] = &[
        0,
        4,
        -4,
        8,
        -8,
        12,
        100,
        -100, // small aligned
        1,
        2,
        3,
        5,
        6,
        7,
        -1,
        -6, // MISALIGNED -> err 1
        134_217_724,
        -134_217_728, // max/min IN-RANGE (boundary)
        134_217_728,
        -134_217_732, // off-by-one OUT-OF-RANGE (boundary)
        67_108_864,   // 2^24 words: sets high imm26 bits (mask edge)
    ];
    for &insn in &b_insns {
        for &off in b_offs {
            v.push((insn, off, 0, 0));
        }
    }

    // ---- Page21 (which=1) : ADRP immhi|immlo split. ----
    // Range: page_offset in [-2^20, 2^20) = [-1048576, 1048575].
    let p_insns = [0x9000_0000u32, 0xFFFF_FFFFu32];
    let p_offs: &[i64] = &[
        0, 1, 2, 3, 4, 5, 6, 7, -1, -7, 100, -100, // immlo/immhi coverage
        1_048_575, -1_048_576, // max/min IN-RANGE (sign boundary)
        1_048_576, -1_048_577, // off-by-one OUT-OF-RANGE
        -524_288,   // mid negative
    ];
    for &insn in &p_insns {
        for &off in p_offs {
            v.push((insn, off, 0, 1));
        }
    }

    // ---- Pageoff12 (which=2) : 12-bit offset bits[21:10], scaled by 2^shift. ----
    let o_insns = [0xF940_0000u32, 0xB940_0000u32, 0xFFFF_FFFFu32];
    // (page_offset, shift) tuples spanning aligned/unaligned/limit edges.
    let o_cases: &[(i64, u32)] = &[
        (0, 0),
        (1, 0),
        (8, 0),
        (0x10, 0),
        (0xFFF, 0), // shift 0: 4095 max
        (4096, 0),
        (4097, 0), // shift 0: OUT (>=4096 -> err2)
        (0, 2),
        (4, 2),
        (8, 2),
        (0xFFC, 2),
        (0x10, 2), // shift 2 aligned
        (1, 2),
        (2, 2),
        (5, 2), // shift 2 UNALIGNED -> err1
        (0, 3),
        (8, 3),
        (0x10, 3),
        (0xFF8, 3), // shift 3 aligned
        (1, 3),
        (4, 3),
        (4095, 3), // shift 3 UNALIGNED -> err1
        (4096, 3), // shift 3: >=4096 -> err2
    ];
    for &insn in &o_insns {
        for &(po, sh) in o_cases {
            v.push((insn, po, sh, 2));
        }
    }

    v
}

/// The AArch64 fixup byte-patch layer, native==JIT over an ENCODING-BOUNDARY
/// sweep (max in-range / off-by-one out / sign boundary / alignment / mask
/// edges), JIT vs the LINKED production `apply_branch26`/`apply_page21`/
/// `apply_pageoff12`.
#[test]
fn trust_fixup_patch_production_eq_jit() {
    let tuples = fixup_inputs();
    let expected = tuples.len();
    // Precompute the native dual-oracle rows while a no-op panic hook silences
    // the INTENTIONAL pageoff12 panics we catch (real assert failures later still
    // print, because the default hook is restored before the assertion loop).
    let prev = std::panic::take_hook();
    std::panic::set_hook(Box::new(|_| {}));
    let oracle: Vec<(u32, u32)> = tuples
        .iter()
        .map(|&(insn, off, shift, which)| nat_fixup(insn, off, shift, which))
        .collect();
    std::panic::set_hook(prev);

    let sweep = tuples.clone();
    let rows = run_watchdogged::<FixupPatchOut>("fixup_patch", expected, move |tx| {
        let buffer = jit_module(FIXUP_PATCH_IR, "fixup_patch");
        let f: FixupPatchFn = unsafe { std::mem::transmute(bind(&buffer, "fixup_patch_root")) };
        for &(insn, off, shift, which) in &sweep {
            let mut out = FixupPatchOut::poisoned();
            unsafe { f(insn, off, shift, which, &mut out) };
            if tx.send(out).is_err() {
                return;
            }
        }
    });

    assert_eq!(rows.len(), expected);
    for (i, &(insn, off, shift, which)) in tuples.iter().enumerate() {
        let (patched, err) = oracle[i];
        assert_eq!(
            (rows[i].patched, rows[i].err),
            (patched, err),
            "fixup(insn={insn:#x} off={off} shift={shift} which={which}): \
             JIT (word={:#x},err={}) != oracle (word={patched:#x},err={err})",
            rows[i].patched,
            rows[i].err
        );
        assert_ne!(rows[i].err, 0xDEAD, "row {i} err still poisoned");
        // On the Ok path the word must be a real patch, never the poison.
        if err == 0 {
            assert_ne!(rows[i].patched, 0xDEAD_BEEF, "row {i} word still poisoned");
        }
    }

    // ---- Spot-check the exact BOUNDARY encodings by hand (independent oracle). ----
    let pos = |t: (u32, i64, u32, u32)| tuples.iter().position(|&x| x == t).expect("tuple present");
    let r = |t: (u32, i64, u32, u32)| rows[pos(t)];

    // BL forward 8 bytes = 2 words -> imm26 = 2 (cf. fixup.rs test_apply_branch26_forward).
    assert_eq!(
        r((0x9400_0000, 8, 0, 0)).patched & 0x03FF_FFFF,
        2,
        "BL +8 -> imm26=2"
    );
    assert_eq!(
        r((0x9400_0000, 8, 0, 0)).patched & 0xFC00_0000,
        0x9400_0000,
        "BL opcode preserved"
    );
    // B backward 8 bytes -> imm26 = -2 in 26-bit two's complement = 0x03FF_FFFE.
    assert_eq!(
        r((0x1400_0000, -8, 0, 0)).patched & 0x03FF_FFFF,
        0x03FF_FFFE,
        "B -8 -> imm26=-2"
    );
    // Max in-range branch: imm26 = 2^25-1.
    assert_eq!(
        r((0x9400_0000, 134_217_724, 0, 0)).patched & 0x03FF_FFFF,
        (1u32 << 25) - 1,
        "max in-range branch26 imm26 = 2^25-1"
    );
    assert_eq!(
        r((0x9400_0000, 134_217_724, 0, 0)).err,
        0,
        "max in-range branch is Ok"
    );
    // Off-by-one OUT: 2^25 words -> err 2 (range).
    assert_eq!(
        r((0x9400_0000, 134_217_728, 0, 0)).err,
        2,
        "2^25 words out of range"
    );
    // Misaligned -> err 1.
    assert_eq!(
        r((0x9400_0000, 6, 0, 0)).err,
        1,
        "misaligned branch offset -> err1"
    );

    // ADRP page_offset 5 = 0b101 -> immlo=01, immhi=1; reconstruct value.
    let a5 = r((0x9000_0000, 5, 0, 1)).patched;
    let immlo = (a5 >> 29) & 3;
    let immhi = (a5 >> 5) & 0x7_FFFF;
    assert_eq!((immhi << 2) | immlo, 5, "ADRP page 5 reconstructs to 5");
    // Max/min in-range page21 (sign boundary): Ok; off-by-one -> err2.
    assert_eq!(
        r((0x9000_0000, 1_048_575, 0, 1)).err,
        0,
        "max in-range page21 Ok"
    );
    assert_eq!(
        r((0x9000_0000, -1_048_576, 0, 1)).err,
        0,
        "min in-range page21 Ok"
    );
    assert_eq!(
        r((0x9000_0000, 1_048_576, 0, 1)).err,
        2,
        "page21 +2^20 out of range"
    );
    assert_eq!(
        r((0x9000_0000, -1_048_577, 0, 1)).err,
        2,
        "page21 -2^20-1 out of range"
    );

    // LDR x0 pageoff 0x10 shift 3 -> imm12 = 0x10>>3 = 2.
    assert_eq!(
        (r((0xF940_0000, 0x10, 3, 2)).patched >> 10) & 0xFFF,
        0x10 >> 3,
        "LDR pageoff 0x10 scaled by 8 -> imm12=2"
    );
    assert_eq!(r((0xF940_0000, 0x10, 3, 2)).err, 0, "aligned pageoff Ok");
    // ADD pageoff 0x10 shift 0 -> imm12 = 0x10.
    assert_eq!(
        (r((0xF940_0000, 0x10, 0, 2)).patched >> 10) & 0xFFF,
        0x10,
        "shift-0 pageoff unscaled"
    );
    // 4095 shift 0 OK (max); 4096 shift 0 -> err2.
    assert_eq!(
        r((0xF940_0000, 0xFFF, 0, 2)).err,
        0,
        "pageoff 4095 shift0 Ok"
    );
    assert_eq!(
        r((0xF940_0000, 4096, 0, 2)).err,
        2,
        "pageoff 4096 -> err2 (>=4096)"
    );
    // Unaligned to shift -> err1.
    assert_eq!(
        r((0xF940_0000, 5, 2, 2)).err,
        1,
        "pageoff 5 not aligned to 4 -> err1"
    );
    assert_eq!(
        r((0xF940_0000, 1, 3, 2)).err,
        1,
        "pageoff 1 not aligned to 8 -> err1"
    );
}

/// ARMED negative control (Slice 1): patch the Branch26 imm26 MASK
/// (`const u32 67108863` = 0x03FF_FFFF -> 0x01FF_FFFF = 33554431), dropping the
/// TOP displacement bit. A branch whose imm26 uses bit 24 then encodes the WRONG
/// displacement -> the branch would jump to the wrong address. Prove divergence,
/// restore, re-pass.
#[test]
fn trust_fixup_patch_armed_control() {
    const ANCHOR: &str = "const u32 67108863";
    assert_eq!(
        FIXUP_PATCH_IR.matches(ANCHOR).count(),
        1,
        "corruption anchor must be unique (branch26 imm26 mask 0x03FFFFFF)"
    );
    let corrupted = FIXUP_PATCH_IR.replace(ANCHOR, "const u32 16777215");
    assert_ne!(corrupted, FIXUP_PATCH_IR);

    // 2^24 words forward (byte_offset 67108864): imm26 = 0x0100_0000 (bit 24 set).
    // Correct patch keeps bit 24; the corrupted mask 0x00FFFFFF drops it -> 0.
    let corrupt = run_watchdogged::<u32>("fixup CORRUPTED", 1, move |tx| {
        let buffer = jit_module(&corrupted, "fixup CORRUPTED");
        let f: FixupPatchFn = unsafe { std::mem::transmute(bind(&buffer, "fixup_patch_root")) };
        let mut out = FixupPatchOut::poisoned();
        unsafe { f(0x9400_0000, 67_108_864, 0, 0, &mut out) };
        let _ = tx.send(out.patched & 0x03FF_FFFF);
    })[0];
    let pristine = run_watchdogged::<u32>("fixup RESTORED", 1, move |tx| {
        let buffer = jit_module(FIXUP_PATCH_IR, "fixup RESTORED");
        let f: FixupPatchFn = unsafe { std::mem::transmute(bind(&buffer, "fixup_patch_root")) };
        let mut out = FixupPatchOut::poisoned();
        unsafe { f(0x9400_0000, 67_108_864, 0, 0, &mut out) };
        let _ = tx.send(out.patched & 0x03FF_FFFF);
    })[0];

    let (native_word, native_err) = nat_fixup(0x9400_0000, 67_108_864, 0, 0);
    assert_eq!(native_err, 0, "production: 2^24-word branch is in range");
    assert_eq!(
        native_word & 0x03FF_FFFF,
        0x0100_0000,
        "production imm26 has bit 24 set"
    );
    assert_eq!(
        corrupt, 0x0000_0000,
        "corrupted module DROPS bit 24 -> imm26 = 0"
    );
    assert_ne!(
        corrupt,
        native_word & 0x03FF_FFFF,
        "corrupted JIT DIVERGES from production"
    );
    assert_eq!(
        pristine, 0x0100_0000,
        "pristine module AGREES (restore + re-pass)"
    );
}

// ============================================================================
// SLICE 2 — the Mach-O RELOCATION-RECORD word assembly + kind predicates
//   (macho/reloc.rs + macho/x86_64_reloc.rs + macho/fixup.rs::needs_addend_reloc)
// ============================================================================

#[repr(C)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct RelocWordOut {
    enc_lo: u32,
    enc_hi: u32,
    is_pcrel: u32,
    log2sz: u32,
    needs_addend: u32,
    dec_sym: u32,
    dec_pcrel: u32,
    dec_len: u32,
    dec_ext: u32,
    dec_type: u32,
    dec_valid: u32,
}

impl RelocWordOut {
    fn poisoned() -> Self {
        RelocWordOut {
            enc_lo: 0xDEAD,
            enc_hi: 0xDEAD,
            is_pcrel: 0xDEAD,
            log2sz: 0xDEAD,
            needs_addend: 0xDEAD,
            dec_sym: 0xDEAD,
            dec_pcrel: 0xDEAD,
            dec_len: 0xDEAD,
            dec_ext: 0xDEAD,
            dec_type: 0xDEAD,
            dec_valid: 0xDEAD,
        }
    }
    fn as_row(&self) -> [u32; 11] {
        [
            self.enc_lo,
            self.enc_hi,
            self.is_pcrel,
            self.log2sz,
            self.needs_addend,
            self.dec_sym,
            self.dec_pcrel,
            self.dec_len,
            self.dec_ext,
            self.dec_type,
            self.dec_valid,
        ]
    }
}

type RelocWordFn =
    unsafe extern "C" fn(u32, u32, u32, u32, u32, u32, i64, u32, u32, *mut RelocWordOut);

fn aa_kind(tag: u32) -> AArch64RelocKind {
    match tag {
        0 => AArch64RelocKind::Unsigned,
        1 => AArch64RelocKind::Subtractor,
        2 => AArch64RelocKind::Branch26,
        3 => AArch64RelocKind::Page21,
        4 => AArch64RelocKind::Pageoff12,
        5 => AArch64RelocKind::GotLoadPage21,
        6 => AArch64RelocKind::GotLoadPageoff12,
        7 => AArch64RelocKind::PointerToGot,
        8 => AArch64RelocKind::TlvpLoadPage21,
        9 => AArch64RelocKind::TlvpLoadPageoff12,
        10 => AArch64RelocKind::Addend,
        _ => AArch64RelocKind::AuthenticatedPointer,
    }
}

fn x86_kind(tag: u32) -> X86_64RelocKind {
    match tag {
        0 => X86_64RelocKind::Unsigned,
        1 => X86_64RelocKind::Signed,
        2 => X86_64RelocKind::Branch,
        3 => X86_64RelocKind::GotLoad,
        4 => X86_64RelocKind::Got,
        5 => X86_64RelocKind::Subtractor,
        6 => X86_64RelocKind::Signed1,
        7 => X86_64RelocKind::Signed2,
        8 => X86_64RelocKind::Signed4,
        _ => X86_64RelocKind::Tlv,
    }
}

/// Native dual-oracle: drive the REAL linked encode/decode/predicate functions
/// on real `Relocation`/`X86_64Relocation`/`Fixup` structs.
#[allow(clippy::too_many_arguments)] // Arguments mirror the relocation record fields.
fn native_reloc(
    kind: u32,
    off: u32,
    sym: u32,
    pcrel: u32,
    len: u32,
    ext: u32,
    addend: i64,
    decw: u32,
    arch: u32,
) -> [u32; 11] {
    let mut db = [0u8; 8];
    db[4..8].copy_from_slice(&decw.to_le_bytes());

    if arch == 0 {
        let k = aa_kind(kind);
        let reloc = Relocation {
            offset: off,
            symbol_index: sym,
            kind: k,
            pc_relative: pcrel != 0,
            length: len as u8,
            is_extern: ext != 0,
        };
        let bytes = encode_relocation(&reloc).unwrap(); // LINKED
        let enc_lo = u32::from_le_bytes([bytes[0], bytes[1], bytes[2], bytes[3]]);
        let enc_hi = u32::from_le_bytes([bytes[4], bytes[5], bytes[6], bytes[7]]);
        let is_pcrel = k.is_pc_relative() as u32; // LINKED
        let log2sz = k.default_log2_size() as u32; // LINKED
        let fx = Fixup {
            offset: 0,
            kind: k,
            tls_model: None,
            target: FixupTarget::Symbol(0),
            addend,
        };
        let needs = fx.needs_addend_reloc() as u32; // LINKED
        let (dvalid, dtype, dsym, dpc, dlen, dext) = match decode_relocation(&db) {
            Ok(r) => (
                1u32,
                r.kind as u32,
                r.symbol_index,
                r.pc_relative as u32,
                r.length as u32,
                r.is_extern as u32,
            ),
            Err(e) => (
                0u32,
                e.type_val as u32,
                decw & 0x00FF_FFFF,
                (decw >> 24) & 1,
                (decw >> 25) & 3,
                (decw >> 27) & 1,
            ),
        };
        [
            enc_lo, enc_hi, is_pcrel, log2sz, needs, dsym, dpc, dlen, dext, dtype, dvalid,
        ]
    } else {
        let k = x86_kind(kind);
        let reloc = X86_64Relocation {
            offset: off,
            symbol_index: sym,
            kind: k,
            pc_relative: pcrel != 0,
            length: len as u8,
            is_extern: ext != 0,
        };
        let bytes = encode_x86_64_relocation(&reloc).unwrap(); // LINKED
        let enc_lo = u32::from_le_bytes([bytes[0], bytes[1], bytes[2], bytes[3]]);
        let enc_hi = u32::from_le_bytes([bytes[4], bytes[5], bytes[6], bytes[7]]);
        let is_pcrel = k.is_pc_relative() as u32; // LINKED
        let log2sz = k.default_log2_size() as u32; // LINKED
        let (dvalid, dtype, dsym, dpc, dlen, dext) = match decode_x86_64_relocation(&db) {
            Ok(r) => (
                1u32,
                r.kind as u32,
                r.symbol_index,
                r.pc_relative as u32,
                r.length as u32,
                r.is_extern as u32,
            ),
            Err(e) => (
                0u32,
                e.type_val as u32,
                decw & 0x00FF_FFFF,
                (decw >> 24) & 1,
                (decw >> 25) & 3,
                (decw >> 27) & 1,
            ),
        };
        [
            enc_lo, enc_hi, is_pcrel, log2sz, 0, dsym, dpc, dlen, dext, dtype, dvalid,
        ]
    }
}

type RelocInput = (u32, u32, u32, u32, u32, u32, i64, u32, u32);

fn reloc_inputs() -> Vec<RelocInput> {
    let mut v: Vec<RelocInput> = Vec::new();
    // A benign decode word (type_val=2, sym=0x0ABCDE, pcrel=1, len=2, ext=1).
    let benign_decw: u32 = (2u32 << 28) | (1u32 << 27) | (2u32 << 25) | (1u32 << 24) | 0x0A_BCDE;

    // ---- AArch64: exhaustive kind sweep (encode + predicates). ----
    for tag in 0..=11u32 {
        // Vary the bitfields per kind so each of pcrel/len/ext is exercised.
        let pcrel = tag & 1;
        let len = tag % 4;
        let ext = (tag >> 1) & 1;
        v.push((tag, 0x100, 0x12_3456, pcrel, len, ext, 0, benign_decw, 0));
    }
    // Full-field edges: sym all-24-bits, pcrel=1, len=3, ext=1.
    v.push((2, 0x2000, 0x00FF_FFFF, 1, 3, 1, 0, benign_decw, 0)); // Branch26
    v.push((0, 0, 0, 0, 0, 0, 0, benign_decw, 0)); // all-zero fields
    // ---- AArch64: needs_addend_reloc (addend x kind). ----
    for &tag in &[2u32, 3, 4, 0, 5, 10] {
        for &ad in &[0i64, 4, -4] {
            v.push((tag, 0x40, 0x1000, 0, 2, 1, ad, benign_decw, 0));
        }
    }
    // ---- AArch64: decode validity gate over type_val 0..=15. ----
    for tv in 0..=15u32 {
        let decw = (tv << 28) | (1u32 << 27) | (2u32 << 25) | (1u32 << 24) | 0x0A_BCDE;
        v.push((0, 0x80, 0x2222, 0, 2, 1, 0, decw, 0));
    }

    // ---- x86-64: exhaustive kind sweep. ----
    for tag in 0..=9u32 {
        let pcrel = tag & 1;
        let len = tag % 4;
        let ext = (tag >> 1) & 1;
        v.push((tag, 0x100, 0x12_3456, pcrel, len, ext, 0, benign_decw, 1));
    }
    v.push((2, 0x2000, 0x00FF_FFFF, 1, 3, 1, 0, benign_decw, 1)); // Branch
    // ---- x86-64: decode validity gate over type_val 0..=15. ----
    for tv in 0..=15u32 {
        let decw = (tv << 28) | (1u32 << 27) | (2u32 << 25) | (1u32 << 24) | 0x0A_BCDE;
        v.push((0, 0x80, 0x2222, 0, 2, 1, 0, decw, 1));
    }
    v
}

/// The Mach-O relocation-record word assembly + kind predicates, native==JIT
/// over an exhaustive kind sweep + full-field edges + a type_val 0..=15 decode
/// validity sweep (both arches), JIT vs the LINKED production
/// `encode_relocation`/`decode_relocation`/`is_pc_relative`/`default_log2_size`/
/// `needs_addend_reloc` (and the x86-64 equivalents).
#[test]
fn trust_reloc_word_production_eq_jit() {
    let tuples = reloc_inputs();
    let expected = tuples.len();
    let sweep = tuples.clone();
    let rows = run_watchdogged::<[u32; 11]>("reloc_word", expected, move |tx| {
        let buffer = jit_module(RELOC_WORD_IR, "reloc_word");
        let f: RelocWordFn = unsafe { std::mem::transmute(bind(&buffer, "reloc_word_root")) };
        for &(kind, off, sym, pcrel, len, ext, addend, decw, arch) in &sweep {
            let mut out = RelocWordOut::poisoned();
            unsafe {
                f(
                    kind, off, sym, pcrel, len, ext, addend, decw, arch, &mut out,
                )
            };
            if tx.send(out.as_row()).is_err() {
                return;
            }
        }
    });

    assert_eq!(rows.len(), expected);
    for (i, &(kind, off, sym, pcrel, len, ext, addend, decw, arch)) in tuples.iter().enumerate() {
        let expect = native_reloc(kind, off, sym, pcrel, len, ext, addend, decw, arch);
        assert_eq!(
            rows[i], expect,
            "reloc(kind={kind} off={off:#x} sym={sym:#x} pcrel={pcrel} len={len} ext={ext} \
             addend={addend} decw={decw:#x} arch={arch}): JIT {:?} != oracle {:?}",
            rows[i], expect
        );
        assert!(
            rows[i].iter().all(|&x| x != 0xDEAD),
            "row {i} still poisoned: {:?}",
            rows[i]
        );
    }

    // ---- Independent boundary spot-checks (the bitfield layout by hand). ----
    let pos = |t: (u32, u32, u32, u32, u32, u32, i64, u32, u32)| {
        tuples.iter().position(|&x| x == t).expect("present")
    };
    let benign_decw: u32 = (2u32 << 28) | (1u32 << 27) | (2u32 << 25) | (1u32 << 24) | 0x0A_BCDE;
    let row = |t: (u32, u32, u32, u32, u32, u32, i64, u32, u32)| rows[pos(t)];

    // AArch64 Branch26 (kind=2) is pc-relative, 4-byte (log2=2).
    let br = row((2, 0x100, 0x12_3456, 0, 2, 1, 0, benign_decw, 0));
    assert_eq!((br[2], br[3]), (1, 2), "AArch64 Branch26 pc-rel, log2=2");
    // Unsigned (kind=0) is NOT pc-relative and 8-byte (log2=3).
    let un = row((0, 0x100, 0x12_3456, 0, 0, 0, 0, benign_decw, 0));
    assert_eq!((un[2], un[3]), (0, 3), "AArch64 Unsigned abs, log2=3");
    // Full-field edge: r_word1 packs sym=0xFFFFFF, pcrel=1, len=3, ext=1, type=2.
    let full = row((2, 0x2000, 0x00FF_FFFF, 1, 3, 1, 0, benign_decw, 0));
    let expect_word1 = 0x00FF_FFFFu32 | (1u32 << 24) | (3u32 << 25) | (1u32 << 27) | (2u32 << 28);
    assert_eq!(
        full[1], expect_word1,
        "full-field r_word1 packs every subfield"
    );
    assert_eq!(full[0], 0x2000, "r_word0 = offset");
    // needs_addend: Branch26 + nonzero addend => true; Unsigned + nonzero => false.
    assert_eq!(
        row((2, 0x40, 0x1000, 0, 2, 1, 4, benign_decw, 0))[4],
        1,
        "Branch26+addend needs pair"
    );
    assert_eq!(
        row((2, 0x40, 0x1000, 0, 2, 1, 0, benign_decw, 0))[4],
        0,
        "Branch26+0 addend no pair"
    );
    assert_eq!(
        row((0, 0x40, 0x1000, 0, 2, 1, 4, benign_decw, 0))[4],
        0,
        "Unsigned+addend no pair (kind gate)"
    );
    // decode validity: type_val 11 valid (AuthenticatedPointer), 12 invalid on AArch64.
    let dv11 = row((
        0,
        0x80,
        0x2222,
        0,
        2,
        1,
        0,
        (11u32 << 28) | (1u32 << 27) | (2u32 << 25) | (1u32 << 24) | 0x0A_BCDE,
        0,
    ));
    assert_eq!((dv11[9], dv11[10]), (11, 1), "AArch64 type_val 11 -> valid");
    let dv12 = row((
        0,
        0x80,
        0x2222,
        0,
        2,
        1,
        0,
        (12u32 << 28) | (1u32 << 27) | (2u32 << 25) | (1u32 << 24) | 0x0A_BCDE,
        0,
    ));
    assert_eq!(
        (dv12[9], dv12[10]),
        (12, 0),
        "AArch64 type_val 12 -> INVALID"
    );
    // decode field extraction: sym/pcrel/len/ext from the benign word.
    assert_eq!(
        (dv11[5], dv11[6], dv11[7], dv11[8]),
        (0x0A_BCDE, 1, 2, 1),
        "decode fields extracted"
    );

    // x86-64: Unsigned NOT pc-rel (log2=3); Branch IS pc-rel (log2=2).
    let x_un = row((0, 0x100, 0x12_3456, 0, 0, 0, 0, benign_decw, 1));
    assert_eq!((x_un[2], x_un[3]), (0, 3), "x86 Unsigned abs, log2=3");
    let x_br = row((2, 0x100, 0x12_3456, 0, 2, 1, 0, benign_decw, 1));
    assert_eq!((x_br[2], x_br[3]), (1, 2), "x86 Branch pc-rel, log2=2");
    // x86 Subtractor (kind=5) is NOT pc-relative (the other exception).
    let x_sub = row((5, 0x100, 0x12_3456, 1, 1, 0, 0, benign_decw, 1));
    assert_eq!(x_sub[2], 0, "x86 Subtractor is absolute");
    // x86 decode validity: type_val 9 valid (Tlv), 10 invalid.
    let xv9 = row((
        0,
        0x80,
        0x2222,
        0,
        2,
        1,
        0,
        (9u32 << 28) | (1u32 << 27) | (2u32 << 25) | (1u32 << 24) | 0x0A_BCDE,
        1,
    ));
    assert_eq!((xv9[9], xv9[10]), (9, 1), "x86 type_val 9 -> valid");
    let xv10 = row((
        0,
        0x80,
        0x2222,
        0,
        2,
        1,
        0,
        (10u32 << 28) | (1u32 << 27) | (2u32 << 25) | (1u32 << 24) | 0x0A_BCDE,
        1,
    ));
    assert_eq!((xv10[9], xv10[10]), (10, 0), "x86 type_val 10 -> INVALID");
}

/// ARMED negative control (Slice 2): patch the r_word1 TYPE-field shift in the
/// packer (`%17 = const u32 28` -> 27), moving the reloc type from bits [31:28]
/// to [30:27] (overlapping r_extern). The encoded r_word1 for a nonzero-type
/// reloc then DIVERGES from the linker-correct production encoding. Prove
/// divergence, restore, re-pass.
#[test]
fn trust_reloc_word_armed_control() {
    const ANCHOR: &str = "%17 = const u32 28";
    assert_eq!(
        RELOC_WORD_IR.matches(ANCHOR).count(),
        1,
        "corruption anchor must be unique (pack r_word1 type-field shift 28)"
    );
    let corrupted = RELOC_WORD_IR.replace(ANCHOR, "%17 = const u32 27");
    assert_ne!(corrupted, RELOC_WORD_IR);

    // Branch26 (type=2), ext=1: correct r_word1 has type 2 at bits[31:28].
    let args = (
        2u32,
        0x100u32,
        0x12_3456u32,
        1u32,
        2u32,
        1u32,
        0i64,
        0u32,
        0u32,
    );
    let corrupt = run_watchdogged::<u32>("reloc CORRUPTED", 1, move |tx| {
        let buffer = jit_module(&corrupted, "reloc CORRUPTED");
        let f: RelocWordFn = unsafe { std::mem::transmute(bind(&buffer, "reloc_word_root")) };
        let mut out = RelocWordOut::poisoned();
        unsafe {
            f(
                args.0, args.1, args.2, args.3, args.4, args.5, args.6, args.7, args.8, &mut out,
            )
        };
        let _ = tx.send(out.enc_hi);
    })[0];
    let pristine = run_watchdogged::<u32>("reloc RESTORED", 1, move |tx| {
        let buffer = jit_module(RELOC_WORD_IR, "reloc RESTORED");
        let f: RelocWordFn = unsafe { std::mem::transmute(bind(&buffer, "reloc_word_root")) };
        let mut out = RelocWordOut::poisoned();
        unsafe {
            f(
                args.0, args.1, args.2, args.3, args.4, args.5, args.6, args.7, args.8, &mut out,
            )
        };
        let _ = tx.send(out.enc_hi);
    })[0];

    let native = native_reloc(2, 0x100, 0x12_3456, 1, 2, 1, 0, 0, 0);
    let native_word1 = native[1];
    // Correct: type 2 at bit 28 -> 0x2000_0000. Corrupt (<<27): 2<<27 = 0x1000_0000,
    // so the type field bits[31:28] read as 1 (the reloc TYPE is mis-encoded 2 -> 1).
    assert_eq!(
        native_word1 & 0xF000_0000,
        0x2000_0000,
        "production packs type 2 at bits[31:28]"
    );
    assert_eq!(
        corrupt & 0xF000_0000,
        0x1000_0000,
        "corrupted module mis-encodes the type field (2 -> 1)"
    );
    assert_ne!(
        corrupt, native_word1,
        "corrupted JIT r_word1 DIVERGES from production"
    );
    assert_eq!(
        pristine, native_word1,
        "pristine module AGREES (restore + re-pass)"
    );
}

// ============================================================================
// SLICE 3 — the AArch64 BRANCH-RANGE / VENEER decider (relax.rs).
//   branch_range / in_range
// ============================================================================

use trust_cg_codegen::relax::branch_range as prod_branch_range;
use trust_cg_ir::AArch64Opcode;

const BRANCH_RANGE_IR: &str = include_str!("slices/trust_branch_range.tir");

#[repr(C)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct BrRangeOut {
    min: i64,
    max: i64,
    in_range: u32,
}

impl BrRangeOut {
    fn poisoned() -> Self {
        BrRangeOut {
            min: 0x0DEA_D0DE_AD0D_EAD0u64 as i64,
            max: 0x0DEA_D0DE_AD0D_EAD0u64 as i64,
            in_range: 0xDEAD,
        }
    }
}

type BrRangeFn = unsafe extern "C" fn(u32, i64, *mut BrRangeOut);

/// Map a tag to the REAL production `AArch64Opcode`. Tag 6 (`Other`) maps to a
/// non-branch opcode (Nop); the F5-safety row uses BL (discriminant 201 >= 128).
fn prod_op(tag: u32) -> AArch64Opcode {
    match tag {
        0 => AArch64Opcode::B,
        1 => AArch64Opcode::BCond,
        2 => AArch64Opcode::Cbz,
        3 => AArch64Opcode::Cbnz,
        4 => AArch64Opcode::Tbz,
        5 => AArch64Opcode::Tbnz,
        _ => AArch64Opcode::Nop,
    }
}

/// Native dual-oracle via the LINKED production `branch_range` (`in_range` is a
/// private fn — transcribed and cross-checked against the linked range).
fn native_br(tag: u32, disp: i64) -> (i64, i64, u32) {
    let (min, max) = prod_branch_range(prod_op(tag));
    (min, max, (disp >= min && disp <= max) as u32)
}

fn br_inputs() -> Vec<(u32, i64)> {
    // Boundary displacements spanning ALL three encoding ranges, so each opcode
    // is tested at its own edge AND across the others (cross-range discrimination).
    let disps: [i64; 19] = [
        0,
        4,
        -4, //
        32_764,
        32_768,
        -32_768,
        -32_772, // TBZ imm14 boundaries
        1_048_572,
        1_048_576,
        -1_048_576,
        -1_048_580, // BCOND imm19 boundaries
        134_217_724,
        134_217_728,
        -134_217_728,
        -134_217_732, // B imm26 boundaries
        1_000_000,
        -1_000_000,
        2_000_000_000,
        -2_000_000_000, // misc + huge (Other)
    ];
    let mut v: Vec<(u32, i64)> = Vec::new();
    for tag in 0..=6u32 {
        for &d in &disps {
            v.push((tag, d));
        }
    }
    v
}

/// The AArch64 branch-range / veneer decider, native==JIT over a
/// tag x boundary-displacement sweep hitting the EXACT +/-128MB/+/-1MB/+/-32KB
/// encoding limits (max in-range, off-by-one out, sign boundary), JIT vs the
/// LINKED production `branch_range`.
#[test]
fn trust_branch_range_production_eq_jit() {
    let tuples = br_inputs();
    let expected = tuples.len();
    let sweep = tuples.clone();
    let rows = run_watchdogged::<BrRangeOut>("branch_range", expected, move |tx| {
        let buffer = jit_module(BRANCH_RANGE_IR, "branch_range");
        let f: BrRangeFn = unsafe { std::mem::transmute(bind(&buffer, "branch_range_root")) };
        for &(tag, disp) in &sweep {
            let mut out = BrRangeOut::poisoned();
            unsafe { f(tag, disp, &mut out) };
            if tx.send(out).is_err() {
                return;
            }
        }
    });

    assert_eq!(rows.len(), expected);
    for (i, &(tag, disp)) in tuples.iter().enumerate() {
        let (min, max, inr) = native_br(tag, disp);
        assert_eq!(
            (rows[i].min, rows[i].max, rows[i].in_range),
            (min, max, inr),
            "branch_range(tag={tag} disp={disp}): JIT {:?} != oracle (min={min},max={max},in={inr})",
            rows[i]
        );
        assert_ne!(rows[i].in_range, 0xDEAD, "row {i} still poisoned");
    }

    // ---- Independent boundary spot-checks. ----
    let r = |tag: u32, disp: i64| {
        let i = tuples
            .iter()
            .position(|&t| t == (tag, disp))
            .expect("present");
        rows[i]
    };
    // B (imm26): +/-128 MB range; max in-range vs off-by-one out.
    assert_eq!(
        (r(0, 0).min, r(0, 0).max),
        (-134_217_728, 134_217_724),
        "B range = +/-128MB"
    );
    assert_eq!(r(0, 134_217_724).in_range, 1, "B max in-range");
    assert_eq!(r(0, 134_217_728).in_range, 0, "B max+4 OUT");
    assert_eq!(
        r(0, -134_217_728).in_range,
        1,
        "B min in-range (sign boundary)"
    );
    assert_eq!(r(0, -134_217_732).in_range, 0, "B min-4 OUT");
    // B.cond/CBZ/CBNZ (imm19): +/-1 MB.
    for tag in [1u32, 2, 3] {
        assert_eq!(
            (r(tag, 0).min, r(tag, 0).max),
            (-1_048_576, 1_048_572),
            "BCOND-class range = +/-1MB"
        );
        assert_eq!(r(tag, 1_048_572).in_range, 1, "BCOND max in-range");
        assert_eq!(r(tag, 1_048_576).in_range, 0, "BCOND max+4 OUT");
        // A displacement in range for B is OUT of range for a conditional branch.
        assert_eq!(
            r(tag, 134_217_724).in_range,
            0,
            "B-range disp is OUT for a cond branch"
        );
    }
    // TBZ/TBNZ (imm14): +/-32 KB.
    for tag in [4u32, 5] {
        assert_eq!(
            (r(tag, 0).min, r(tag, 0).max),
            (-32_768, 32_764),
            "TBZ-class range = +/-32KB"
        );
        assert_eq!(r(tag, 32_764).in_range, 1, "TBZ max in-range");
        assert_eq!(r(tag, 32_768).in_range, 0, "TBZ max+4 OUT (must veneer)");
        assert_eq!(r(tag, -32_768).in_range, 1, "TBZ min in-range");
    }
    // Other (non-branch): (i64::MIN, i64::MAX), always in range.
    assert_eq!(
        (r(6, 0).min, r(6, 0).max),
        (i64::MIN, i64::MAX),
        "non-branch range unbounded"
    );
    assert_eq!(
        r(6, 2_000_000_000).in_range,
        1,
        "non-branch always in range"
    );

    // ---- F5-SAFETY: the production branch_range over a >=128 opcode (BL=201) ----
    // returns the unbounded Other range, confirming branch_range is NOT hit by
    // the F5 sext-i8 miscompile (the six matched branch opcodes are all < 128).
    assert_eq!(
        prod_branch_range(AArch64Opcode::BL),
        (i64::MIN, i64::MAX),
        "production branch_range(BL=201) -> Other range (F5-safe: matched opcodes < 128)"
    );
    assert_eq!(
        prod_branch_range(AArch64Opcode::B),
        (-134_217_728, 134_217_724),
        "linked branch_range(B) matches the slice model"
    );
}

/// ARMED negative control (Slice 3): patch TBZ_MAX_RANGE (`const i64 32764` ->
/// 32768), widening the imm14 range by one word. A TBZ with disp = 32768 — which
/// really OVERFLOWS imm14 and MUST be relaxed to a veneer — is then wrongly
/// judged in-range, so the un-relaxed branch would overflow its field at encode:
/// a link-time miscompile. Prove divergence, restore, re-pass.
#[test]
fn trust_branch_range_armed_control() {
    const ANCHOR: &str = "const i64 32764";
    assert_eq!(
        BRANCH_RANGE_IR.matches(ANCHOR).count(),
        1,
        "corruption anchor must be unique (TBZ_MAX_RANGE)"
    );
    let corrupted = BRANCH_RANGE_IR.replace(ANCHOR, "const i64 32768");
    assert_ne!(corrupted, BRANCH_RANGE_IR);

    // Tbz (tag=4), disp = 32768 (= TBZ_MAX+4, genuinely out of range).
    let corrupt = run_watchdogged::<(i64, u32)>("branch CORRUPTED", 1, move |tx| {
        let buffer = jit_module(&corrupted, "branch CORRUPTED");
        let f: BrRangeFn = unsafe { std::mem::transmute(bind(&buffer, "branch_range_root")) };
        let mut out = BrRangeOut::poisoned();
        unsafe { f(4, 32_768, &mut out) };
        let _ = tx.send((out.max, out.in_range));
    })[0];
    let pristine = run_watchdogged::<(i64, u32)>("branch RESTORED", 1, move |tx| {
        let buffer = jit_module(BRANCH_RANGE_IR, "branch RESTORED");
        let f: BrRangeFn = unsafe { std::mem::transmute(bind(&buffer, "branch_range_root")) };
        let mut out = BrRangeOut::poisoned();
        unsafe { f(4, 32_768, &mut out) };
        let _ = tx.send((out.max, out.in_range));
    })[0];

    let (_, native_max, native_in) = native_br(4, 32_768);
    assert_eq!(native_max, 32_764, "production TBZ max = 32764");
    assert_eq!(
        native_in, 0,
        "production: TBZ disp 32768 is OUT of range (must veneer)"
    );
    assert_eq!(
        corrupt.0, 32_768,
        "corrupted module widens TBZ max to 32768"
    );
    assert_eq!(
        corrupt.1, 1,
        "corrupted module WRONGLY judges the overflowing branch in-range"
    );
    assert_ne!(
        corrupt.1, native_in,
        "corrupted JIT DIVERGES from production (unsound: no veneer)"
    );
    assert_eq!(
        pristine,
        (32_764, 0),
        "pristine module AGREES (restore + re-pass)"
    );
}
