//! TRUST-SELF ROUND 5 (thread R7-B): verifying trust-cg's REGISTER-ALLOCATOR
//! PREDICATES — the pure functions whose answers ARE the allocator's
//! correctness — through the full pipeline Rust -> MIR -> trust-ir (stage1
//! `trust_ir_mir --mir-emit-closure`) -> trust-cg JIT -> machine code,
//! asserting native Rust == JIT over swept real inputs, with the linked
//! PRODUCTION crates (`trust_cg_ir`, `trust_cg_regalloc`) as a SECOND
//! oracle wherever the fn is pub (the round-4 dual-oracle discipline).
//!
//! WHY SOUNDNESS-CRITICAL: a register allocator with a wrong interference
//! predicate SILENTLY CORRUPTS every program it compiles. Specifically:
//!   * `regs_overlap` (aarch64_regs.rs:783) is the aarch64 aliasing
//!     predicate behind `allocator_pregs_overlap` (greedy.rs:142-145) — a
//!     false "no overlap" for X0/W0 or V0/D0/S0/H0/B0 assigns two live
//!     values to one physical register;
//!   * `LiveRange::overlaps` / `LiveInterval::overlaps` (liveness.rs:43/108)
//!     gate coalescing (coalesce.rs:132/217/491) and the greedy assignment
//!     audit (greedy.rs:3281);
//!   * `LiveInterval::is_live_at` (liveness.rs:92) gates call-clobber
//!     spilling (call_clobber.rs:143) and eviction (greedy.rs:629);
//!   * `is_callee_saved`/`is_caller_saved` (aarch64_regs.rs:636/654) are the
//!     AAPCS64 clobber constraints; `preg_class`/`hw_encoding`/`reg_number`
//!     decide the 5-bit fields that reach machine code (SP and XZR both
//!     encode 31); the width converters implement the X<->W / V<->D<->S
//!     aliasing model; `merge_vreg_class` (liveness.rs:552) collapses
//!     mixed-width vreg classes; `reg_class_size` (spill.rs:129) sizes
//!     spill slots (too small => a spilled Q-store tramples its neighbour).
//!
//! New verified functions in this file (25; Trust-itself inventory 54 -> 79):
//!   * register-file predicates (trust-cg-ir/src/aarch64_regs.rs):
//!     `preg_class`, `hw_encoding`, `is_callee_saved`, `is_caller_saved`,
//!     `reg_number`, `reg_root`, `regs_overlap`, `gpr64_to_gpr32`,
//!     `gpr32_to_gpr64`, `fpr128_to_fpr64`, `fpr128_to_fpr32`,
//!     `fpr128_to_fpr16`, `fpr128_to_fpr8`, `fpr64_to_fpr128`,
//!     `fpr32_to_fpr128`, `PReg::is_gpr`, `PReg::is_fpr`,
//!     `RegClass::size_bits`, `RegClass::size_bytes`   (19)
//!   * liveness/spill predicates (trust-cg-regalloc):
//!     `LiveRange::contains`, `LiveRange::overlaps`,
//!     `LiveInterval::is_live_at`, `LiveInterval::overlaps`,
//!     `merge_vreg_class`, `reg_class_size`            (6)
//!
//! THIS ROUND'S DOCUMENTED FRONTEND FINDINGS (no frontend changes this
//! round — both documented as next steps, per the thread charter):
//!   (1) f64 PLACES DO NOT LOWER: `compute_spill_weight` (liveness.rs:576,
//!       the spill-cost computation) fails emit-closure with
//!       "place leaf is not a memory scalar: float". The slice + root are
//!       ALREADY WRITTEN AND WAITING (`ra_spill_weight_root` in
//!       tests/slices/trust_regalloc_liveness_slice.rs, [B3] rewrites
//!       documented incl. the powi->multiply-loop bit-exactness argument);
//!       on the day f64 places lower, emit it and add the differential.
//!       This is the FIRST FP-typed target attempted on the Trust-self
//!       effort; the whole f64 surface of trust-cg is gated behind it.
//!   (2) CONST-AGGREGATE ITEMS AS OPERANDS DO NOT LOWER (known owner-item
//!       #6 class, new minimal witness): `Some(WSP)` — a const STRUCT item
//!       used as an aggregate-field operand — fails "aggregate field
//!       operand is not a place (constant aggregate field): struct-adt".
//!       Slice carries the [B3] const-value inlining rewrite
//!       (`Some(PReg(63))` etc.), swept on all four affected arms.
//!
//! Slices (verbatim transcriptions, modeled boundaries documented inline
//! there and summarized at each fixture below):
//!   tests/slices/trust_regfile_slice.rs            (trust-cg-ir @ 00ae28c)
//!   tests/slices/trust_regalloc_liveness_slice.rs  (trust-cg-regalloc @ 00ae28c)
//! Both transcribed from THIS repo's working tree (clean at 00ae28c),
//! re-checked 2026-07-03; the production fns are linked into this very
//! test binary, so transcription drift is caught by the dual oracle.
//!
//! REGEN (per module; trust-ir frontend @ 1eb4b56):
//!   S=$HOME/trust/build/aarch64-apple-darwin/stage1
//!   cd $HOME/trust-ir/frontend && env -u RUSTUP_TOOLCHAIN RUSTC=$S/bin/rustc \
//!     DYLD_LIBRARY_PATH=$S/lib/rustlib/aarch64-apple-darwin/lib \
//!     $S/bin/cargo run --bin trust_ir_mir -- \
//!     <tests/slices/trust_regfile_slice.rs | trust_regalloc_liveness_slice.rs> \
//!     --crate-type=lib -C overflow-checks=off -C debug-assertions=off \
//!     --mir-emit-closure <root> <out.tir>
//!   Every module: validate_module = 0 errors, re-parse OK, EXTERN-FREE
//!   (no host shims anywhere in this file), deterministic re-emit proven
//!   byte-identical on regfile_props_root.
//!
//! MODELED BOUNDARIES (summary; full text in the slices):
//!   regfile [B1] `preg_name` + Debug/Display out of scope (diagnostic-only
//!     &'static str tables); [B2] enum->u32 tags + Option->(present,enc)
//!     out-params at roots, mirrored 1:1 here; [B3] const-item VALUES
//!     inlined in the two GPR converters (finding (2) above).
//!   liveness [B1] Vec<LiveRange> -> (&[LiveRange; 4], len) plumbing
//!     (len<=4 harness invariant; range arithmetic verbatim); [B2]
//!     `binary_search_by(..).is_ok()` -> explicit lo/hi loop with the
//!     production closure's three-way compare VERBATIM (result-equivalent
//!     on sorted non-overlapping lists — the LiveInterval invariant —
//!     and dual-oracled against production `is_live_at` + a naive
//!     any-contains reference over every swept row); [B4] enum<->u32 tag
//!     decoders at roots. Ranges cross the JIT boundary as FLAT u32
//!     buffers (layout-independent — the round-6 Num-decode lesson).
//!
//! COVERAGE NOTE: gated to aarch64 (the JIT target); on any other host this
//! file compiles to ZERO tests. Run tests ONE AT A TIME
//! (`-- --exact <name> --test-threads=1`): the JIT engine is not
//! thread-safe at suite scale (jit-parallel-race-2026-06-29.md). Every JIT
//! execution runs inside a WATCHDOG worker thread.

#![cfg(target_arch = "aarch64")]

use std::collections::HashMap;
use std::sync::mpsc;
use std::time::Duration;

use trust_cg_codegen::Target;
use trust_cg_codegen::compiler::{Compiler, CompilerConfig};

use trust_cg_ir::regs as prod_regs;
use trust_cg_ir::regs::{PReg as ProdPReg, RegClass as ProdRegClass};
use trust_cg_regalloc::machine_types::VReg as ProdVReg;
use trust_cg_regalloc::{LiveInterval as ProdLiveInterval, LiveRange as ProdLiveRange};

// ── shared harness (round-4 pattern) ────────────────────────────────────────

/// Parse + JIT one embedded module; return the buffer (keep it alive while
/// calling fn pointers bound from it). All round-5 modules are EXTERN-FREE.
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

/// Run `worker` (which JITs a module and streams `expected` rows) under the
/// watchdog: the JIT buffer lives entirely inside the worker thread; the
/// main thread bounds every wait. Workers enumerate inputs deterministically
/// and echo them in each row, so a stall at row N identifies its input.
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

// ── oracle plumbing: the [B2]/[B4] tag maps, mirrored 1:1 from the slices ──

fn tag_of_class(c: ProdRegClass) -> u32 {
    match c {
        ProdRegClass::Gpr64 => 0,
        ProdRegClass::Gpr32 => 1,
        ProdRegClass::Fpr128 => 2,
        ProdRegClass::Fpr64 => 3,
        ProdRegClass::Fpr32 => 4,
        ProdRegClass::Fpr16 => 5,
        ProdRegClass::Fpr8 => 6,
        ProdRegClass::System => 7,
    }
}

fn class_of_tag(tag: u32) -> ProdRegClass {
    match tag {
        0 => ProdRegClass::Gpr64,
        1 => ProdRegClass::Gpr32,
        2 => ProdRegClass::Fpr128,
        3 => ProdRegClass::Fpr64,
        4 => ProdRegClass::Fpr32,
        5 => ProdRegClass::Fpr16,
        6 => ProdRegClass::Fpr8,
        _ => ProdRegClass::System,
    }
}

// ── verbatim transcript oracles for the two PRIVATE fns (no linkable
//    production symbol; fidelity is by line-cited verbatim text, and both
//    are additionally invariant-checked against linked production types) ──

/// liveness.rs:552-567 VERBATIM (private `merge_vreg_class`), over the
/// LINKED production RegClass.
fn n_merge_vreg_class(lhs: ProdRegClass, rhs: ProdRegClass) -> ProdRegClass {
    if lhs == rhs {
        return lhs;
    }

    use ProdRegClass::*;
    match (lhs, rhs) {
        (Gpr64, Gpr32 | System) | (Gpr32 | System, Gpr64) => Gpr64,
        (Gpr32, System) | (System, Gpr32) => Gpr32,
        (Fpr128, Fpr64 | Fpr32 | Fpr16 | Fpr8) | (Fpr64 | Fpr32 | Fpr16 | Fpr8, Fpr128) => Fpr128,
        (Fpr64, Fpr32 | Fpr16 | Fpr8) | (Fpr32 | Fpr16 | Fpr8, Fpr64) => Fpr64,
        (Fpr32, Fpr16 | Fpr8) | (Fpr16 | Fpr8, Fpr32) => Fpr32,
        (Fpr16, Fpr8) | (Fpr8, Fpr16) => Fpr16,
        _ => lhs,
    }
}

/// spill.rs:129-139 VERBATIM (private `reg_class_size`), over the LINKED
/// production RegClass.
fn n_reg_class_size(class: ProdRegClass) -> u32 {
    match class {
        ProdRegClass::Gpr32 | ProdRegClass::Fpr32 => 4,
        ProdRegClass::Gpr64 | ProdRegClass::Fpr64 => 8,
        ProdRegClass::Fpr128 => 16,
        // Smaller FPR classes: use their natural size
        ProdRegClass::Fpr16 => 2,
        ProdRegClass::Fpr8 => 1,
        ProdRegClass::System => 4,
    }
}

/// Build a production LiveInterval owning exactly `ranges` (fields are pub;
/// `add_range` would MERGE adjacent ranges, so the canonical menu below is
/// generated non-adjacent and installed directly).
fn prod_interval(ranges: &[(u32, u32)]) -> ProdLiveInterval {
    let mut iv = ProdLiveInterval::new(ProdVReg::new(0, ProdRegClass::Gpr64));
    iv.ranges = ranges
        .iter()
        .map(|&(s, e)| ProdLiveRange { start: s, end: e })
        .collect();
    iv
}

/// Naive semantic reference for is_live_at: ANY range contains idx.
fn naive_live_at(ranges: &[(u32, u32)], idx: u32) -> bool {
    ranges.iter().any(|&(s, e)| s <= idx && idx < e)
}

/// Naive semantic reference for interval overlap: ANY pair of ranges overlaps.
fn naive_overlaps(a: &[(u32, u32)], b: &[(u32, u32)]) -> bool {
    a.iter()
        .any(|&(s1, e1)| b.iter().any(|&(s2, e2)| s1 < e2 && s2 < e1))
}

/// Flatten a range list into the fixed [u32; 8] buffer the roots read
/// (flat[2i]=start_i, flat[2i+1]=end_i; len <= 4 — the liveness [B1] CAP).
fn flatten(ranges: &[(u32, u32)]) -> ([u32; 8], u32) {
    assert!(ranges.len() <= 4, "menu invariant: len <= CAP=4");
    let mut flat = [0u32; 8];
    for (i, &(s, e)) in ranges.iter().enumerate() {
        flat[2 * i] = s;
        flat[2 * i + 1] = e;
    }
    (flat, ranges.len() as u32)
}

/// Deterministic LCG (fixed seed) — the menu generator's randomness source.
struct Lcg(u64);
impl Lcg {
    fn next(&mut self) -> u64 {
        self.0 = self
            .0
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        self.0 >> 33
    }
}

/// The CANONICAL interval menu: sorted, non-overlapping, NON-ADJACENT range
/// lists (the LiveInterval invariant that both `is_live_at`'s binary search
/// and `overlaps`' merge scan assume, liveness.rs:56). Deterministic:
/// hand-picked witnesses first (fixed indices used by the negative
/// controls), then all single ranges over 0..=10, then LCG-generated lists
/// of up to 4 ranges over 0..24.
fn canonical_menu() -> Vec<Vec<(u32, u32)>> {
    let mut menu: Vec<Vec<(u32, u32)>> = vec![
        vec![(0, 2), (10, 12)],               // [0] negative-control witness A (holed)
        vec![(4, 6)],                         // [1] negative-control witness B (in A's hole)
        vec![],                               // [2] empty interval
        vec![(0, 24)],                        // [3] whole-universe range
        vec![(0, 1), (2, 3), (4, 5), (6, 7)], // [4] max-len alternation
        vec![(17, 23)],                       // [5] high range
    ];
    for s in 0..10u32 {
        for e in (s + 1)..=10u32 {
            menu.push(vec![(s, e)]);
        }
    }
    let mut lcg = Lcg(0x5EED_2026_0703);
    while menu.len() < 160 {
        let mut list = Vec::new();
        let mut cursor = (lcg.next() % 4) as u32;
        let n = 1 + (lcg.next() % 4) as u32;
        for _ in 0..n {
            let start = cursor + 1 + (lcg.next() % 4) as u32; // gap >= 1: non-adjacent
            let end = start + 1 + (lcg.next() % 5) as u32;
            if end > 24 {
                break;
            }
            list.push((start, end));
            cursor = end;
        }
        menu.push(list);
    }
    menu
}

// ── the RegProps out-POD mirror (slice `RegProps`, #[repr(C)], 10 x u32) ───

#[repr(C)]
#[derive(Clone, Copy)]
struct RegPropsC {
    class_tag: u32,
    hw_enc: u32,
    callee_saved: u32,
    caller_saved: u32,
    is_gpr: u32,
    is_fpr: u32,
    num_present: u32,
    num: u32,
    size_bits: u32,
    size_bytes: u32,
}

impl RegPropsC {
    fn poisoned() -> Self {
        RegPropsC {
            class_tag: 0xDEAD,
            hw_enc: 0xDEAD,
            callee_saved: 0xDEAD,
            caller_saved: 0xDEAD,
            is_gpr: 0xDEAD,
            is_fpr: 0xDEAD,
            num_present: 0xDEAD,
            num: 0xDEAD,
            size_bits: 0xDEAD,
            size_bytes: 0xDEAD,
        }
    }

    fn as_row(&self) -> [u32; 10] {
        [
            self.class_tag,
            self.hw_enc,
            self.callee_saved,
            self.caller_saved,
            self.is_gpr,
            self.is_fpr,
            self.num_present,
            self.num,
            self.size_bits,
            self.size_bytes,
        ]
    }
}

/// The PRODUCTION property row for one encoding (the oracle for T1/T2).
fn native_props_row(e: u16) -> [u32; 10] {
    let r = ProdPReg::new(e);
    let c = prod_regs::preg_class(r);
    let (num_present, num) = match prod_regs::reg_number(r) {
        Some(n) => (1u32, n as u32),
        None => (0, 0),
    };
    [
        tag_of_class(c),
        prod_regs::hw_encoding(r) as u32,
        prod_regs::is_callee_saved(r) as u32,
        prod_regs::is_caller_saved(r) as u32,
        r.is_gpr() as u32,
        r.is_fpr() as u32,
        num_present,
        num,
        c.size_bits(),
        c.size_bytes(),
    ]
}

/// The PRODUCTION converter dispatch, mirroring the slice's [B2] total
/// `kind` decoder (wildcard -> fpr32_to_fpr128).
fn prod_alias(kind: u32, e: u16) -> Option<ProdPReg> {
    let r = ProdPReg::new(e);
    match kind {
        0 => prod_regs::gpr64_to_gpr32(r),
        1 => prod_regs::gpr32_to_gpr64(r),
        2 => prod_regs::fpr128_to_fpr64(r),
        3 => prod_regs::fpr128_to_fpr32(r),
        4 => prod_regs::fpr128_to_fpr16(r),
        5 => prod_regs::fpr128_to_fpr8(r),
        6 => prod_regs::fpr64_to_fpr128(r),
        _ => prod_regs::fpr32_to_fpr128(r),
    }
}

// ── embedded fixtures (VERBATIM MIR-closure emits; regen per header) ───────

/// VERBATIM MIR-closure emit of `regfile_props_root` — the scalar property vector root (preg_class, hw_encoding, is_callee_saved,
/// is_caller_saved, PReg::is_gpr/is_fpr, reg_number, RegClass::size_bits/bytes).
/// Slice: tests/slices/trust_regfile_slice.rs; regen per the file header.
/// Emit reported: 19427 bytes; 13 closure member(s); validate_module = 0
/// error(s); re-parse OK; EXTERN-FREE.
/// 2026-07-20: `@PReg__is_fpr` hand-updated in the same dialect to track the
/// production fix (special regs 160..=164 — XZR/WZR/NZCV/FPCR/FPSR — are NOT
/// FPRs: `matches!(e, 64..=159 | 165..=228)`); the exhaustive 65536-point
/// production==JIT sweep below is the byte-equivalence oracle. Fold into the
/// next fresh re-emit.
const REGFILE_PROPS_IR: &str = r#"; TrustIr text format v1
module "mir::closure::regfile_props_root"
target "aarch64-apple-darwin" 8 little
file 0 "trust_regfile_slice.rs"

functy.0 = (u16, ptr) -> ()

functy.1 = (ptr, u16) -> ()

functy.2 = (ptr, u16) -> ()

functy.3 = (u8) -> (u32)

functy.4 = (u16) -> (u8)

functy.5 = (u16) -> (bool)

functy.6 = (u16) -> (bool)

functy.7 = (u16) -> (bool)

functy.8 = (u16) -> (bool)

functy.9 = (ptr, u16) -> ()

functy.10 = (u8) -> (u32)

functy.11 = (u8) -> (u32)

functy.12 = (u16) -> (u16)

fn @regfile_props_root(functy.0) {
bb0(%0: u16, %1: ptr):
    %24 = alloca i16, align 2
    %25 = alloca i8, align 1
    %26 = alloca (i8, i8), align 1
    call @func.1(%24, %0)
    br bb1(%1)
bb1(%2: ptr):
    %27 = load u16, ptr %24
    call @func.2(%25, %27)
    br bb2(%2)
bb2(%3: ptr):
    %28 = load u8, ptr %25
    %29 = call @func.3(%28)
    br bb3(%3, %29)
bb3(%4: ptr, %5: u32):
    store u32 %5, ptr %4
    %30 = load u16, ptr %24
    %31 = call @func.4(%30)
    br bb4(%4, %31)
bb4(%6: ptr, %7: u8):
    %32 = zext u8 %7 to u32
    %33 = const i64 4
    %34 = gep i8, ptr %6, %33
    store u32 %32, ptr %34
    %35 = load u16, ptr %24
    %36 = call @func.5(%35)
    br bb5(%6, %36)
bb5(%8: ptr, %9: bool):
    %37 = const u32 1
    %38 = const u32 0
    %39 = select u32 %9, %37, %38
    %40 = const i64 8
    %41 = gep i8, ptr %8, %40
    store u32 %39, ptr %41
    %42 = load u16, ptr %24
    %43 = call @func.6(%42)
    br bb6(%8, %43)
bb6(%10: ptr, %11: bool):
    %44 = const u32 1
    %45 = const u32 0
    %46 = select u32 %11, %44, %45
    %47 = const i64 12
    %48 = gep i8, ptr %10, %47
    store u32 %46, ptr %48
    %49 = load u16, ptr %24
    %50 = call @func.7(%49)
    br bb7(%10, %50)
bb7(%12: ptr, %13: bool):
    %51 = const u32 1
    %52 = const u32 0
    %53 = select u32 %13, %51, %52
    %54 = const i64 16
    %55 = gep i8, ptr %12, %54
    store u32 %53, ptr %55
    %56 = load u16, ptr %24
    %57 = call @func.8(%56)
    br bb8(%12, %57)
bb8(%14: ptr, %15: bool):
    %58 = const u32 1
    %59 = const u32 0
    %60 = select u32 %15, %58, %59
    %61 = const i64 20
    %62 = gep i8, ptr %14, %61
    store u32 %60, ptr %62
    %63 = load u16, ptr %24
    call @func.9(%26, %63)
    br bb9(%14)
bb9(%16: ptr):
    %64 = load i8, ptr %26
    %65 = sext i8 %64 to i64
    switch %65 [ 0: bb11(%16) 1: bb12(%16) default: bb10 ]
bb10:
    unreachable
bb11(%17: ptr):
    %66 = const u32 0
    %67 = const i64 24
    %68 = gep i8, ptr %17, %67
    store u32 %66, ptr %68
    %69 = const u32 0
    %70 = const i64 28
    %71 = gep i8, ptr %17, %70
    store u32 %69, ptr %71
    br bb13(%17)
bb12(%18: ptr):
    %72 = const i64 1
    %73 = gep i8, ptr %26, %72
    %74 = load u8, ptr %73
    %75 = const u32 1
    %76 = const i64 24
    %77 = gep i8, ptr %18, %76
    store u32 %75, ptr %77
    %78 = zext u8 %74 to u32
    %79 = const i64 28
    %80 = gep i8, ptr %18, %79
    store u32 %78, ptr %80
    br bb13(%18)
bb13(%19: ptr):
    %81 = load u8, ptr %25
    %82 = call @func.10(%81)
    br bb14(%19, %82)
bb14(%20: ptr, %21: u32):
    %83 = const i64 32
    %84 = gep i8, ptr %20, %83
    store u32 %21, ptr %84
    %85 = load u8, ptr %25
    %86 = call @func.11(%85)
    br bb15(%20, %86)
bb15(%22: ptr, %23: u32):
    %87 = const i64 36
    %88 = gep i8, ptr %22, %87
    store u32 %23, ptr %88
    ret
}

fn @PReg__new(functy.1) {
bb0(%0: ptr, %1: u16):
    store u16 %1, ptr %0
    ret
}

fn @preg_class(functy.2) {
bb0(%0: ptr, %1: u16):
    %19 = alloca i16, align 2
    store u16 %1, ptr %19
    %20 = load u16, ptr %19
    %21 = call @func.12(%20)
    br bb1(%21)
bb1(%2: u16):
    %22 = const u16 0
    %23 = icmp ule u16 %22, %2
    condbr %23, bb26(%2), bb4(%2)
bb2:
    %24 = const i8 7
    store i8 %24, ptr %0
    br bb29
bb3:
    %25 = const i8 0
    store i8 %25, ptr %0
    br bb29
bb4(%3: u16):
    %26 = const u16 32
    %27 = icmp ule u16 %26, %3
    condbr %27, bb25(%3), bb6(%3)
bb5:
    %28 = const i8 1
    store i8 %28, ptr %0
    br bb29
bb6(%4: u16):
    %29 = const u16 64
    %30 = icmp ule u16 %29, %4
    condbr %30, bb24(%4), bb8(%4)
bb7:
    %31 = const i8 2
    store i8 %31, ptr %0
    br bb29
bb8(%5: u16):
    %32 = const u16 96
    %33 = icmp ule u16 %32, %5
    condbr %33, bb23(%5), bb10(%5)
bb9:
    %34 = const i8 3
    store i8 %34, ptr %0
    br bb29
bb10(%6: u16):
    %35 = const u16 128
    %36 = icmp ule u16 %35, %6
    condbr %36, bb22(%6), bb12(%6)
bb11:
    %37 = const i8 4
    store i8 %37, ptr %0
    br bb29
bb12(%7: u16):
    switch %7 [ 160: bb28 161: bb27 default: bb13(%7) ]
bb13(%8: u16):
    %38 = const u16 162
    %39 = icmp ule u16 %38, %8
    condbr %39, bb21(%8), bb15(%8)
bb14:
    %40 = const i8 7
    store i8 %40, ptr %0
    br bb29
bb15(%9: u16):
    %41 = const u16 165
    %42 = icmp ule u16 %41, %9
    condbr %42, bb20(%9), bb17(%9)
bb16:
    %43 = const i8 5
    store i8 %43, ptr %0
    br bb29
bb17(%10: u16):
    %44 = const u16 197
    %45 = icmp ule u16 %44, %10
    condbr %45, bb19(%10), bb2
bb18:
    %46 = const i8 6
    store i8 %46, ptr %0
    br bb29
bb19(%11: u16):
    %47 = const u16 228
    %48 = icmp ule u16 %11, %47
    condbr %48, bb18, bb2
bb20(%12: u16):
    %49 = const u16 196
    %50 = icmp ule u16 %12, %49
    condbr %50, bb16, bb17(%12)
bb21(%13: u16):
    %51 = const u16 164
    %52 = icmp ule u16 %13, %51
    condbr %52, bb14, bb15(%13)
bb22(%14: u16):
    %53 = const u16 159
    %54 = icmp ule u16 %14, %53
    condbr %54, bb11, bb12(%14)
bb23(%15: u16):
    %55 = const u16 127
    %56 = icmp ule u16 %15, %55
    condbr %56, bb9, bb10(%15)
bb24(%16: u16):
    %57 = const u16 95
    %58 = icmp ule u16 %16, %57
    condbr %58, bb7, bb8(%16)
bb25(%17: u16):
    %59 = const u16 63
    %60 = icmp ule u16 %17, %59
    condbr %60, bb5, bb6(%17)
bb26(%18: u16):
    %61 = const u16 31
    %62 = icmp ule u16 %18, %61
    condbr %62, bb3, bb4(%18)
bb27:
    %63 = const i8 1
    store i8 %63, ptr %0
    br bb29
bb28:
    %64 = const i8 0
    store i8 %64, ptr %0
    br bb29
bb29:
    ret
}

fn @class_tag(functy.3) {
bb0(%0: u8):
    %2 = alloca i8, align 1
    store u8 %0, ptr %2
    %3 = load i8, ptr %2
    %4 = sext i8 %3 to i64
    switch %4 [ 0: bb9 1: bb8 2: bb7 3: bb6 4: bb5 5: bb4 6: bb3 7: bb2 default: bb1 ]
bb1:
    unreachable
bb2:
    %5 = const u32 7
    br bb10(%5)
bb3:
    %6 = const u32 6
    br bb10(%6)
bb4:
    %7 = const u32 5
    br bb10(%7)
bb5:
    %8 = const u32 4
    br bb10(%8)
bb6:
    %9 = const u32 3
    br bb10(%9)
bb7:
    %10 = const u32 2
    br bb10(%10)
bb8:
    %11 = const u32 1
    br bb10(%11)
bb9:
    %12 = const u32 0
    br bb10(%12)
bb10(%1: u32):
    ret %1
}

fn @hw_encoding(functy.4) {
bb0(%0: u16):
    %26 = alloca i16, align 2
    store u16 %0, ptr %26
    %27 = load u16, ptr %26
    %28 = call @func.12(%27)
    br bb1(%28)
bb1(%1: u16):
    %29 = const u16 0
    %30 = icmp ule u16 %29, %1
    condbr %30, bb26(%1), bb4(%1)
bb2:
    %31 = const u8 0
    br bb29(%31)
bb3(%2: u16):
    %32 = trunc u16 %2 to u8
    br bb29(%32)
bb4(%3: u16):
    %33 = const u16 32
    %34 = icmp ule u16 %33, %3
    condbr %34, bb25(%3), bb6(%3)
bb5(%4: u16):
    %35 = const u16 32
    %36 = sub u16 %4, %35
    %37 = trunc u16 %36 to u8
    br bb29(%37)
bb6(%5: u16):
    %38 = const u16 64
    %39 = icmp ule u16 %38, %5
    condbr %39, bb24(%5), bb8(%5)
bb7(%6: u16):
    %40 = const u16 64
    %41 = sub u16 %6, %40
    %42 = trunc u16 %41 to u8
    br bb29(%42)
bb8(%7: u16):
    %43 = const u16 96
    %44 = icmp ule u16 %43, %7
    condbr %44, bb23(%7), bb10(%7)
bb9(%8: u16):
    %45 = const u16 96
    %46 = sub u16 %8, %45
    %47 = trunc u16 %46 to u8
    br bb29(%47)
bb10(%9: u16):
    %48 = const u16 128
    %49 = icmp ule u16 %48, %9
    condbr %49, bb22(%9), bb12(%9)
bb11(%10: u16):
    %50 = const u16 128
    %51 = sub u16 %10, %50
    %52 = trunc u16 %51 to u8
    br bb29(%52)
bb12(%11: u16):
    switch %11 [ 160: bb28 161: bb27 default: bb13(%11) ]
bb13(%12: u16):
    %53 = const u16 162
    %54 = icmp ule u16 %53, %12
    condbr %54, bb21(%12), bb15(%12)
bb14:
    %55 = const u8 0
    br bb29(%55)
bb15(%13: u16):
    %56 = const u16 165
    %57 = icmp ule u16 %56, %13
    condbr %57, bb20(%13), bb17(%13)
bb16(%14: u16):
    %58 = const u16 165
    %59 = sub u16 %14, %58
    %60 = trunc u16 %59 to u8
    br bb29(%60)
bb17(%15: u16):
    %61 = const u16 197
    %62 = icmp ule u16 %61, %15
    condbr %62, bb19(%15), bb2
bb18(%16: u16):
    %63 = const u16 197
    %64 = sub u16 %16, %63
    %65 = trunc u16 %64 to u8
    br bb29(%65)
bb19(%17: u16):
    %66 = const u16 228
    %67 = icmp ule u16 %17, %66
    condbr %67, bb18(%17), bb2
bb20(%18: u16):
    %68 = const u16 196
    %69 = icmp ule u16 %18, %68
    condbr %69, bb16(%18), bb17(%18)
bb21(%19: u16):
    %70 = const u16 164
    %71 = icmp ule u16 %19, %70
    condbr %71, bb14, bb15(%19)
bb22(%20: u16):
    %72 = const u16 159
    %73 = icmp ule u16 %20, %72
    condbr %73, bb11(%20), bb12(%20)
bb23(%21: u16):
    %74 = const u16 127
    %75 = icmp ule u16 %21, %74
    condbr %75, bb9(%21), bb10(%21)
bb24(%22: u16):
    %76 = const u16 95
    %77 = icmp ule u16 %22, %76
    condbr %77, bb7(%22), bb8(%22)
bb25(%23: u16):
    %78 = const u16 63
    %79 = icmp ule u16 %23, %78
    condbr %79, bb5(%23), bb6(%23)
bb26(%24: u16):
    %80 = const u16 31
    %81 = icmp ule u16 %24, %80
    condbr %81, bb3(%24), bb4(%24)
bb27:
    %82 = const u8 31
    br bb29(%82)
bb28:
    %83 = const u8 31
    br bb29(%83)
bb29(%25: u8):
    ret %25
}

fn @is_callee_saved(functy.5) {
bb0(%0: u16):
    %12 = alloca i16, align 2
    store u16 %0, ptr %12
    %13 = load u16, ptr %12
    %14 = call @func.12(%13)
    br bb1(%14)
bb1(%1: u16):
    %15 = const u16 19
    %16 = icmp ule u16 %15, %1
    condbr %16, bb16(%1), bb4(%1)
bb2:
    %17 = const bool false
    br bb17(%17)
bb3:
    %18 = const bool true
    br bb17(%18)
bb4(%2: u16):
    %19 = const u16 51
    %20 = icmp ule u16 %19, %2
    condbr %20, bb15(%2), bb6(%2)
bb5:
    %21 = const bool true
    br bb17(%21)
bb6(%3: u16):
    %22 = const u16 72
    %23 = icmp ule u16 %22, %3
    condbr %23, bb14(%3), bb8(%3)
bb7:
    %24 = const bool true
    br bb17(%24)
bb8(%4: u16):
    %25 = const u16 104
    %26 = icmp ule u16 %25, %4
    condbr %26, bb13(%4), bb10(%4)
bb9:
    %27 = const bool true
    br bb17(%27)
bb10(%5: u16):
    %28 = const u16 136
    %29 = icmp ule u16 %28, %5
    condbr %29, bb12(%5), bb2
bb11:
    %30 = const bool true
    br bb17(%30)
bb12(%6: u16):
    %31 = const u16 143
    %32 = icmp ule u16 %6, %31
    condbr %32, bb11, bb2
bb13(%7: u16):
    %33 = const u16 111
    %34 = icmp ule u16 %7, %33
    condbr %34, bb9, bb10(%7)
bb14(%8: u16):
    %35 = const u16 79
    %36 = icmp ule u16 %8, %35
    condbr %36, bb7, bb8(%8)
bb15(%9: u16):
    %37 = const u16 60
    %38 = icmp ule u16 %9, %37
    condbr %38, bb5, bb6(%9)
bb16(%10: u16):
    %39 = const u16 28
    %40 = icmp ule u16 %10, %39
    condbr %40, bb3, bb4(%10)
bb17(%11: bool):
    ret %11
}

fn @is_caller_saved(functy.6) {
bb0(%0: u16):
    %22 = alloca i16, align 2
    store u16 %0, ptr %22
    %23 = load u16, ptr %22
    %24 = call @func.12(%23)
    br bb1(%24)
bb1(%1: u16):
    %25 = const u16 0
    %26 = icmp ule u16 %25, %1
    condbr %26, bb21(%1), bb3(%1)
bb2:
    %27 = const bool false
    br bb27(%27)
bb3(%2: u16):
    %28 = const u16 9
    %29 = icmp ule u16 %28, %2
    condbr %29, bb20(%2), bb4(%2)
bb4(%3: u16):
    %30 = const u16 32
    %31 = icmp ule u16 %30, %3
    condbr %31, bb19(%3), bb5(%3)
bb5(%4: u16):
    %32 = const u16 41
    %33 = icmp ule u16 %32, %4
    condbr %33, bb18(%4), bb6(%4)
bb6(%5: u16):
    %34 = const u16 64
    %35 = icmp ule u16 %34, %5
    condbr %35, bb17(%5), bb7(%5)
bb7(%6: u16):
    %36 = const u16 80
    %37 = icmp ule u16 %36, %6
    condbr %37, bb16(%6), bb8(%6)
bb8(%7: u16):
    %38 = const u16 96
    %39 = icmp ule u16 %38, %7
    condbr %39, bb15(%7), bb9(%7)
bb9(%8: u16):
    %40 = const u16 112
    %41 = icmp ule u16 %40, %8
    condbr %41, bb14(%8), bb10(%8)
bb10(%9: u16):
    %42 = const u16 128
    %43 = icmp ule u16 %42, %9
    condbr %43, bb13(%9), bb11(%9)
bb11(%10: u16):
    %44 = const u16 144
    %45 = icmp ule u16 %44, %10
    condbr %45, bb12(%10), bb2
bb12(%11: u16):
    %46 = const u16 159
    %47 = icmp ule u16 %11, %46
    condbr %47, bb22, bb2
bb13(%12: u16):
    %48 = const u16 135
    %49 = icmp ule u16 %12, %48
    condbr %49, bb22, bb11(%12)
bb14(%13: u16):
    %50 = const u16 127
    %51 = icmp ule u16 %13, %50
    condbr %51, bb23, bb10(%13)
bb15(%14: u16):
    %52 = const u16 103
    %53 = icmp ule u16 %14, %52
    condbr %53, bb23, bb9(%14)
bb16(%15: u16):
    %54 = const u16 95
    %55 = icmp ule u16 %15, %54
    condbr %55, bb24, bb8(%15)
bb17(%16: u16):
    %56 = const u16 71
    %57 = icmp ule u16 %16, %56
    condbr %57, bb24, bb7(%16)
bb18(%17: u16):
    %58 = const u16 47
    %59 = icmp ule u16 %17, %58
    condbr %59, bb25, bb6(%17)
bb19(%18: u16):
    %60 = const u16 39
    %61 = icmp ule u16 %18, %60
    condbr %61, bb25, bb5(%18)
bb20(%19: u16):
    %62 = const u16 15
    %63 = icmp ule u16 %19, %62
    condbr %63, bb26, bb4(%19)
bb21(%20: u16):
    %64 = const u16 7
    %65 = icmp ule u16 %20, %64
    condbr %65, bb26, bb3(%20)
bb22:
    %66 = const bool true
    br bb27(%66)
bb23:
    %67 = const bool true
    br bb27(%67)
bb24:
    %68 = const bool true
    br bb27(%68)
bb25:
    %69 = const bool true
    br bb27(%69)
bb26:
    %70 = const bool true
    br bb27(%70)
bb27(%21: bool):
    ret %21
}

fn @PReg__is_gpr(functy.7) {
bb0(%0: u16):
    %1 = alloca i16, align 2
    store u16 %0, ptr %1
    %2 = load u16, ptr %1
    %3 = const u16 31
    %4 = icmp ule u16 %2, %3
    ret %4
}

fn @PReg__is_fpr(functy.8) {
bb0(%0: u16):
    %2 = alloca i16, align 2
    store u16 %0, ptr %2
    %3 = load u16, ptr %2
    %4 = const u16 64
    %5 = icmp uge u16 %3, %4
    condbr %5, bb1, bb3
bb1:
    %6 = load u16, ptr %2
    %7 = const u16 159
    %8 = icmp ule u16 %6, %7
    condbr %8, bb2, bb3
bb2:
    %9 = const bool true
    br bb6(%9)
bb3:
    %10 = load u16, ptr %2
    %11 = const u16 165
    %12 = icmp uge u16 %10, %11
    condbr %12, bb4, bb5
bb4:
    %13 = load u16, ptr %2
    %14 = const u16 228
    %15 = icmp ule u16 %13, %14
    br bb6(%15)
bb5:
    %16 = const bool false
    br bb6(%16)
bb6(%1: bool):
    ret %1
}

fn @reg_number(functy.9) {
bb0(%0: ptr, %1: u16):
    %24 = alloca i16, align 2
    store u16 %1, ptr %24
    %25 = load u16, ptr %24
    %26 = call @func.12(%25)
    br bb1(%26)
bb1(%2: u16):
    %27 = const u16 0
    %28 = icmp ule u16 %27, %2
    condbr %28, bb23(%2), bb4(%2)
bb2:
    %29 = const i8 0
    store i8 %29, ptr %0
    br bb28
bb3(%3: u16):
    %30 = trunc u16 %3 to u8
    %31 = const i64 1
    %32 = gep i8, ptr %0, %31
    store u8 %30, ptr %32
    %33 = const i8 1
    store i8 %33, ptr %0
    br bb28
bb4(%4: u16):
    switch %4 [ 31: bb27 63: bb26 160: bb25 161: bb24 default: bb5(%4) ]
bb5(%5: u16):
    %34 = const u16 32
    %35 = icmp ule u16 %34, %5
    condbr %35, bb22(%5), bb7(%5)
bb6(%6: u16):
    %36 = const u16 32
    %37 = sub u16 %6, %36
    %38 = trunc u16 %37 to u8
    %39 = const i64 1
    %40 = gep i8, ptr %0, %39
    store u8 %38, ptr %40
    %41 = const i8 1
    store i8 %41, ptr %0
    br bb28
bb7(%7: u16):
    %42 = const u16 64
    %43 = icmp ule u16 %42, %7
    condbr %43, bb21(%7), bb9(%7)
bb8(%8: u16):
    %44 = const u16 64
    %45 = sub u16 %8, %44
    %46 = trunc u16 %45 to u8
    %47 = const i64 1
    %48 = gep i8, ptr %0, %47
    store u8 %46, ptr %48
    %49 = const i8 1
    store i8 %49, ptr %0
    br bb28
bb9(%9: u16):
    %50 = const u16 96
    %51 = icmp ule u16 %50, %9
    condbr %51, bb20(%9), bb11(%9)
bb10(%10: u16):
    %52 = const u16 96
    %53 = sub u16 %10, %52
    %54 = trunc u16 %53 to u8
    %55 = const i64 1
    %56 = gep i8, ptr %0, %55
    store u8 %54, ptr %56
    %57 = const i8 1
    store i8 %57, ptr %0
    br bb28
bb11(%11: u16):
    %58 = const u16 128
    %59 = icmp ule u16 %58, %11
    condbr %59, bb19(%11), bb13(%11)
bb12(%12: u16):
    %60 = const u16 128
    %61 = sub u16 %12, %60
    %62 = trunc u16 %61 to u8
    %63 = const i64 1
    %64 = gep i8, ptr %0, %63
    store u8 %62, ptr %64
    %65 = const i8 1
    store i8 %65, ptr %0
    br bb28
bb13(%13: u16):
    %66 = const u16 165
    %67 = icmp ule u16 %66, %13
    condbr %67, bb18(%13), bb15(%13)
bb14(%14: u16):
    %68 = const u16 165
    %69 = sub u16 %14, %68
    %70 = trunc u16 %69 to u8
    %71 = const i64 1
    %72 = gep i8, ptr %0, %71
    store u8 %70, ptr %72
    %73 = const i8 1
    store i8 %73, ptr %0
    br bb28
bb15(%15: u16):
    %74 = const u16 197
    %75 = icmp ule u16 %74, %15
    condbr %75, bb17(%15), bb2
bb16(%16: u16):
    %76 = const u16 197
    %77 = sub u16 %16, %76
    %78 = trunc u16 %77 to u8
    %79 = const i64 1
    %80 = gep i8, ptr %0, %79
    store u8 %78, ptr %80
    %81 = const i8 1
    store i8 %81, ptr %0
    br bb28
bb17(%17: u16):
    %82 = const u16 228
    %83 = icmp ule u16 %17, %82
    condbr %83, bb16(%17), bb2
bb18(%18: u16):
    %84 = const u16 196
    %85 = icmp ule u16 %18, %84
    condbr %85, bb14(%18), bb15(%18)
bb19(%19: u16):
    %86 = const u16 159
    %87 = icmp ule u16 %19, %86
    condbr %87, bb12(%19), bb13(%19)
bb20(%20: u16):
    %88 = const u16 127
    %89 = icmp ule u16 %20, %88
    condbr %89, bb10(%20), bb11(%20)
bb21(%21: u16):
    %90 = const u16 95
    %91 = icmp ule u16 %21, %90
    condbr %91, bb8(%21), bb9(%21)
bb22(%22: u16):
    %92 = const u16 62
    %93 = icmp ule u16 %22, %92
    condbr %93, bb6(%22), bb7(%22)
bb23(%23: u16):
    %94 = const u16 30
    %95 = icmp ule u16 %23, %94
    condbr %95, bb3(%23), bb4(%23)
bb24:
    %96 = const u8 31
    %97 = const i64 1
    %98 = gep i8, ptr %0, %97
    store u8 %96, ptr %98
    %99 = const i8 1
    store i8 %99, ptr %0
    br bb28
bb25:
    %100 = const u8 31
    %101 = const i64 1
    %102 = gep i8, ptr %0, %101
    store u8 %100, ptr %102
    %103 = const i8 1
    store i8 %103, ptr %0
    br bb28
bb26:
    %104 = const u8 31
    %105 = const i64 1
    %106 = gep i8, ptr %0, %105
    store u8 %104, ptr %106
    %107 = const i8 1
    store i8 %107, ptr %0
    br bb28
bb27:
    %108 = const u8 31
    %109 = const i64 1
    %110 = gep i8, ptr %0, %109
    store u8 %108, ptr %110
    %111 = const i8 1
    store i8 %111, ptr %0
    br bb28
bb28:
    ret
}

fn @RegClass__size_bits(functy.10) {
bb0(%0: u8):
    %2 = alloca i8, align 1
    store u8 %0, ptr %2
    %3 = load i8, ptr %2
    %4 = sext i8 %3 to i64
    switch %4 [ 0: bb9 1: bb8 2: bb7 3: bb6 4: bb5 5: bb4 6: bb3 7: bb2 default: bb1 ]
bb1:
    unreachable
bb2:
    %5 = const u32 32
    br bb10(%5)
bb3:
    %6 = const u32 8
    br bb10(%6)
bb4:
    %7 = const u32 16
    br bb10(%7)
bb5:
    %8 = const u32 32
    br bb10(%8)
bb6:
    %9 = const u32 64
    br bb10(%9)
bb7:
    %10 = const u32 128
    br bb10(%10)
bb8:
    %11 = const u32 32
    br bb10(%11)
bb9:
    %12 = const u32 64
    br bb10(%12)
bb10(%1: u32):
    ret %1
}

fn @RegClass__size_bytes(functy.11) {
bb0(%0: u8):
    %3 = alloca i8, align 1
    store u8 %0, ptr %3
    %4 = load u8, ptr %3
    %5 = call @func.10(%4)
    br bb1(%5)
bb1(%1: u32):
    %6 = const u32 8
    %7 = const u32 0
    %8 = icmp eq u32 %6, %7
    %9 = const bool false
    %10 = icmp eq bool %8, %9
    condbr %10, bb2(%1), bb3
bb2(%2: u32):
    %11 = const u32 8
    %12 = udiv u32 %2, %11
    ret %12
bb3:
    unreachable
}

fn @PReg__encoding(functy.12) {
bb0(%0: u16):
    %1 = alloca i16, align 2
    store u16 %0, ptr %1
    %2 = load u16, ptr %1
    ret %2
}
"#;

/// VERBATIM MIR-closure emit of `regfile_alias_root` — the width-alias converter family root (all 8 converters via the [B2]
/// total kind decoder; [B3] const-inlined GPR special arms).
/// Slice: tests/slices/trust_regfile_slice.rs; regen per the file header.
/// Emit reported: 9587 bytes; 11 closure member(s); validate_module = 0
/// error(s); re-parse OK; EXTERN-FREE.
const REGFILE_ALIAS_IR: &str = r#"; TrustIr text format v1
module "mir::closure::regfile_alias_root"
target "aarch64-apple-darwin" 8 little
file 0 "trust_regfile_slice.rs"

functy.0 = (u32, u16, ptr, ptr) -> ()

functy.1 = (ptr, u16) -> ()

functy.2 = (ptr, u16) -> ()

functy.3 = (ptr, u16) -> ()

functy.4 = (ptr, u16) -> ()

functy.5 = (ptr, u16) -> ()

functy.6 = (ptr, u16) -> ()

functy.7 = (ptr, u16) -> ()

functy.8 = (ptr, u16) -> ()

functy.9 = (ptr, u16) -> ()

functy.10 = (u16) -> (u16)

fn @regfile_alias_root(functy.0) {
bb0(%0: u32, %1: u16, %2: ptr, %3: ptr):
    %31 = alloca i16, align 2
    %32 = alloca (i16, i16), align 2
    %33 = alloca i16, align 2
    call @func.1(%31, %1)
    br bb1(%0, %2, %3)
bb1(%4: u32, %5: ptr, %6: ptr):
    switch %4 [ 0: bb9(%5, %6) 1: bb8(%5, %6) 2: bb7(%5, %6) 3: bb6(%5, %6) 4: bb5(%5, %6) 5: bb4(%5, %6) 6: bb3(%5, %6) default: bb2(%5, %6) ]
bb2(%7: ptr, %8: ptr):
    %34 = load u16, ptr %31
    call @func.2(%32, %34)
    br bb10(%7, %8)
bb3(%9: ptr, %10: ptr):
    %35 = load u16, ptr %31
    call @func.3(%32, %35)
    br bb10(%9, %10)
bb4(%11: ptr, %12: ptr):
    %36 = load u16, ptr %31
    call @func.4(%32, %36)
    br bb10(%11, %12)
bb5(%13: ptr, %14: ptr):
    %37 = load u16, ptr %31
    call @func.5(%32, %37)
    br bb10(%13, %14)
bb6(%15: ptr, %16: ptr):
    %38 = load u16, ptr %31
    call @func.6(%32, %38)
    br bb10(%15, %16)
bb7(%17: ptr, %18: ptr):
    %39 = load u16, ptr %31
    call @func.7(%32, %39)
    br bb10(%17, %18)
bb8(%19: ptr, %20: ptr):
    %40 = load u16, ptr %31
    call @func.8(%32, %40)
    br bb10(%19, %20)
bb9(%21: ptr, %22: ptr):
    %41 = load u16, ptr %31
    call @func.9(%32, %41)
    br bb10(%21, %22)
bb10(%23: ptr, %24: ptr):
    %42 = load i16, ptr %32
    %43 = sext i16 %42 to i64
    switch %43 [ 0: bb12(%23, %24) 1: bb13(%23, %24) default: bb11 ]
bb11:
    unreachable
bb12(%25: ptr, %26: ptr):
    %44 = const u32 0
    store u32 %44, ptr %25
    %45 = const u32 0
    store u32 %45, ptr %26
    br bb15
bb13(%27: ptr, %28: ptr):
    %46 = const i64 2
    %47 = gep i8, ptr %32, %46
    %48 = load i16, ptr %47
    store i16 %48, ptr %33
    %49 = const u32 1
    store u32 %49, ptr %27
    %50 = load u16, ptr %33
    %51 = call @func.10(%50)
    br bb14(%28, %51)
bb14(%29: ptr, %30: u16):
    %52 = zext u16 %30 to u32
    store u32 %52, ptr %29
    br bb15
bb15:
    ret
}

fn @PReg__new(functy.1) {
bb0(%0: ptr, %1: u16):
    store u16 %1, ptr %0
    ret
}

fn @fpr32_to_fpr128(functy.2) {
bb0(%0: ptr, %1: u16):
    %5 = alloca i16, align 2
    %6 = alloca i16, align 2
    store u16 %1, ptr %5
    %7 = load u16, ptr %5
    %8 = call @func.10(%7)
    br bb1(%8)
bb1(%2: u16):
    %9 = const u16 128
    %10 = icmp ule u16 %9, %2
    condbr %10, bb4(%2), bb2
bb2:
    %11 = const i16 0
    store i16 %11, ptr %0
    br bb5
bb3(%3: u16):
    %12 = const u16 64
    %13 = sub u16 %3, %12
    store u16 %13, ptr %6
    %14 = const i64 2
    %15 = gep i8, ptr %0, %14
    %16 = load i16, ptr %6
    store i16 %16, ptr %15
    %17 = const i16 1
    store i16 %17, ptr %0
    br bb5
bb4(%4: u16):
    %18 = const u16 159
    %19 = icmp ule u16 %4, %18
    condbr %19, bb3(%4), bb2
bb5:
    ret
}

fn @fpr64_to_fpr128(functy.3) {
bb0(%0: ptr, %1: u16):
    %5 = alloca i16, align 2
    %6 = alloca i16, align 2
    store u16 %1, ptr %5
    %7 = load u16, ptr %5
    %8 = call @func.10(%7)
    br bb1(%8)
bb1(%2: u16):
    %9 = const u16 96
    %10 = icmp ule u16 %9, %2
    condbr %10, bb4(%2), bb2
bb2:
    %11 = const i16 0
    store i16 %11, ptr %0
    br bb5
bb3(%3: u16):
    %12 = const u16 32
    %13 = sub u16 %3, %12
    store u16 %13, ptr %6
    %14 = const i64 2
    %15 = gep i8, ptr %0, %14
    %16 = load i16, ptr %6
    store i16 %16, ptr %15
    %17 = const i16 1
    store i16 %17, ptr %0
    br bb5
bb4(%4: u16):
    %18 = const u16 127
    %19 = icmp ule u16 %4, %18
    condbr %19, bb3(%4), bb2
bb5:
    ret
}

fn @fpr128_to_fpr8(functy.4) {
bb0(%0: ptr, %1: u16):
    %5 = alloca i16, align 2
    %6 = alloca i16, align 2
    store u16 %1, ptr %5
    %7 = load u16, ptr %5
    %8 = call @func.10(%7)
    br bb1(%8)
bb1(%2: u16):
    %9 = const u16 64
    %10 = icmp ule u16 %9, %2
    condbr %10, bb4(%2), bb2
bb2:
    %11 = const i16 0
    store i16 %11, ptr %0
    br bb5
bb3(%3: u16):
    %12 = const u16 133
    %13 = add u16 %3, %12
    store u16 %13, ptr %6
    %14 = const i64 2
    %15 = gep i8, ptr %0, %14
    %16 = load i16, ptr %6
    store i16 %16, ptr %15
    %17 = const i16 1
    store i16 %17, ptr %0
    br bb5
bb4(%4: u16):
    %18 = const u16 95
    %19 = icmp ule u16 %4, %18
    condbr %19, bb3(%4), bb2
bb5:
    ret
}

fn @fpr128_to_fpr16(functy.5) {
bb0(%0: ptr, %1: u16):
    %5 = alloca i16, align 2
    %6 = alloca i16, align 2
    store u16 %1, ptr %5
    %7 = load u16, ptr %5
    %8 = call @func.10(%7)
    br bb1(%8)
bb1(%2: u16):
    %9 = const u16 64
    %10 = icmp ule u16 %9, %2
    condbr %10, bb4(%2), bb2
bb2:
    %11 = const i16 0
    store i16 %11, ptr %0
    br bb5
bb3(%3: u16):
    %12 = const u16 101
    %13 = add u16 %3, %12
    store u16 %13, ptr %6
    %14 = const i64 2
    %15 = gep i8, ptr %0, %14
    %16 = load i16, ptr %6
    store i16 %16, ptr %15
    %17 = const i16 1
    store i16 %17, ptr %0
    br bb5
bb4(%4: u16):
    %18 = const u16 95
    %19 = icmp ule u16 %4, %18
    condbr %19, bb3(%4), bb2
bb5:
    ret
}

fn @fpr128_to_fpr32(functy.6) {
bb0(%0: ptr, %1: u16):
    %5 = alloca i16, align 2
    %6 = alloca i16, align 2
    store u16 %1, ptr %5
    %7 = load u16, ptr %5
    %8 = call @func.10(%7)
    br bb1(%8)
bb1(%2: u16):
    %9 = const u16 64
    %10 = icmp ule u16 %9, %2
    condbr %10, bb4(%2), bb2
bb2:
    %11 = const i16 0
    store i16 %11, ptr %0
    br bb5
bb3(%3: u16):
    %12 = const u16 64
    %13 = add u16 %3, %12
    store u16 %13, ptr %6
    %14 = const i64 2
    %15 = gep i8, ptr %0, %14
    %16 = load i16, ptr %6
    store i16 %16, ptr %15
    %17 = const i16 1
    store i16 %17, ptr %0
    br bb5
bb4(%4: u16):
    %18 = const u16 95
    %19 = icmp ule u16 %4, %18
    condbr %19, bb3(%4), bb2
bb5:
    ret
}

fn @fpr128_to_fpr64(functy.7) {
bb0(%0: ptr, %1: u16):
    %5 = alloca i16, align 2
    %6 = alloca i16, align 2
    store u16 %1, ptr %5
    %7 = load u16, ptr %5
    %8 = call @func.10(%7)
    br bb1(%8)
bb1(%2: u16):
    %9 = const u16 64
    %10 = icmp ule u16 %9, %2
    condbr %10, bb4(%2), bb2
bb2:
    %11 = const i16 0
    store i16 %11, ptr %0
    br bb5
bb3(%3: u16):
    %12 = const u16 32
    %13 = add u16 %3, %12
    store u16 %13, ptr %6
    %14 = const i64 2
    %15 = gep i8, ptr %0, %14
    %16 = load i16, ptr %6
    store i16 %16, ptr %15
    %17 = const i16 1
    store i16 %17, ptr %0
    br bb5
bb4(%4: u16):
    %18 = const u16 95
    %19 = icmp ule u16 %4, %18
    condbr %19, bb3(%4), bb2
bb5:
    ret
}

fn @gpr32_to_gpr64(functy.8) {
bb0(%0: ptr, %1: u16):
    %6 = alloca i16, align 2
    %7 = alloca i16, align 2
    %8 = alloca i16, align 2
    %9 = alloca i16, align 2
    store u16 %1, ptr %6
    %10 = load u16, ptr %6
    %11 = call @func.10(%10)
    br bb1(%11)
bb1(%2: u16):
    %12 = const u16 32
    %13 = icmp ule u16 %12, %2
    condbr %13, bb5(%2), bb4(%2)
bb2:
    %14 = const i16 0
    store i16 %14, ptr %0
    br bb8
bb3(%3: u16):
    %15 = const u16 32
    %16 = sub u16 %3, %15
    store u16 %16, ptr %7
    %17 = const i64 2
    %18 = gep i8, ptr %0, %17
    %19 = load i16, ptr %7
    store i16 %19, ptr %18
    %20 = const i16 1
    store i16 %20, ptr %0
    br bb8
bb4(%4: u16):
    switch %4 [ 63: bb7 161: bb6 default: bb2 ]
bb5(%5: u16):
    %21 = const u16 62
    %22 = icmp ule u16 %5, %21
    condbr %22, bb3(%5), bb4(%5)
bb6:
    %23 = const u16 160
    store u16 %23, ptr %9
    %24 = const i64 2
    %25 = gep i8, ptr %0, %24
    %26 = load i16, ptr %9
    store i16 %26, ptr %25
    %27 = const i16 1
    store i16 %27, ptr %0
    br bb8
bb7:
    %28 = const u16 31
    store u16 %28, ptr %8
    %29 = const i64 2
    %30 = gep i8, ptr %0, %29
    %31 = load i16, ptr %8
    store i16 %31, ptr %30
    %32 = const i16 1
    store i16 %32, ptr %0
    br bb8
bb8:
    ret
}

fn @gpr64_to_gpr32(functy.9) {
bb0(%0: ptr, %1: u16):
    %6 = alloca i16, align 2
    %7 = alloca i16, align 2
    %8 = alloca i16, align 2
    %9 = alloca i16, align 2
    store u16 %1, ptr %6
    %10 = load u16, ptr %6
    %11 = call @func.10(%10)
    br bb1(%11)
bb1(%2: u16):
    %12 = const u16 0
    %13 = icmp ule u16 %12, %2
    condbr %13, bb5(%2), bb4(%2)
bb2:
    %14 = const i16 0
    store i16 %14, ptr %0
    br bb8
bb3(%3: u16):
    %15 = const u16 32
    %16 = add u16 %3, %15
    store u16 %16, ptr %7
    %17 = const i64 2
    %18 = gep i8, ptr %0, %17
    %19 = load i16, ptr %7
    store i16 %19, ptr %18
    %20 = const i16 1
    store i16 %20, ptr %0
    br bb8
bb4(%4: u16):
    switch %4 [ 31: bb7 160: bb6 default: bb2 ]
bb5(%5: u16):
    %21 = const u16 30
    %22 = icmp ule u16 %5, %21
    condbr %22, bb3(%5), bb4(%5)
bb6:
    %23 = const u16 161
    store u16 %23, ptr %9
    %24 = const i64 2
    %25 = gep i8, ptr %0, %24
    %26 = load i16, ptr %9
    store i16 %26, ptr %25
    %27 = const i16 1
    store i16 %27, ptr %0
    br bb8
bb7:
    %28 = const u16 63
    store u16 %28, ptr %8
    %29 = const i64 2
    %30 = gep i8, ptr %0, %29
    %31 = load i16, ptr %8
    store i16 %31, ptr %30
    %32 = const i16 1
    store i16 %32, ptr %0
    br bb8
bb8:
    ret
}

fn @PReg__encoding(functy.10) {
bb0(%0: u16):
    %1 = alloca i16, align 2
    store u16 %0, ptr %1
    %2 = load u16, ptr %1
    ret %2
}
"#;

/// VERBATIM MIR-closure emit of `regfile_overlap_root` — the interference-aliasing predicate root (regs_overlap, reg_root, and the
/// derived PReg PartialEq fast path).
/// Slice: tests/slices/trust_regfile_slice.rs; regen per the file header.
/// Emit reported: 10370 bytes; 6 closure member(s); validate_module = 0
/// error(s); re-parse OK; EXTERN-FREE.
const REGFILE_OVERLAP_IR: &str = r#"; TrustIr text format v1
module "mir::closure::regfile_overlap_root"
target "aarch64-apple-darwin" 8 little
file 0 "trust_regfile_slice.rs"

functy.0 = (u16, u16) -> (u32)

functy.1 = (ptr, u16) -> ()

functy.2 = (u16, u16) -> (bool)

functy.3 = (ptr, ptr) -> (bool)

functy.4 = (ptr, u16) -> ()

functy.5 = (u16) -> (u16)

fn @regfile_overlap_root(functy.0) {
bb0(%0: u16, %1: u16):
    %4 = alloca i16, align 2
    %5 = alloca i16, align 2
    call @func.1(%4, %0)
    br bb1(%1)
bb1(%2: u16):
    call @func.1(%5, %2)
    br bb2
bb2:
    %6 = load u16, ptr %4
    %7 = load u16, ptr %5
    %8 = call @func.2(%6, %7)
    br bb3(%8)
bb3(%3: bool):
    %9 = const u32 1
    %10 = const u32 0
    %11 = select u32 %3, %9, %10
    ret %11
}

fn @PReg__new(functy.1) {
bb0(%0: ptr, %1: u16):
    store u16 %1, ptr %0
    ret
}

fn @regs_overlap(functy.2) {
bb0(%0: u16, %1: u16):
    %6 = alloca i16, align 2
    %7 = alloca i16, align 2
    %8 = alloca (i8, i8, i8), align 1
    %9 = alloca (i8, i8, i8), align 1
    %10 = alloca (i8, i8, i8, i8, i8, i8), align 1
    store u16 %0, ptr %6
    store u16 %1, ptr %7
    %11 = call @func.3(%6, %7)
    br bb1(%11)
bb1(%2: bool):
    condbr %2, bb2, bb3
bb2:
    %12 = const bool true
    br bb11(%12)
bb3:
    %13 = load u16, ptr %6
    call @func.4(%8, %13)
    br bb4
bb4:
    %14 = load u16, ptr %7
    call @func.4(%9, %14)
    br bb5
bb5:
    %15 = load i8, ptr %8
    store i8 %15, ptr %10
    %16 = const i64 1
    %17 = gep i8, ptr %8, %16
    %18 = const i64 1
    %19 = gep i8, ptr %10, %18
    %20 = load i8, ptr %17
    store i8 %20, ptr %19
    %21 = const i64 2
    %22 = gep i8, ptr %8, %21
    %23 = const i64 2
    %24 = gep i8, ptr %10, %23
    %25 = load i8, ptr %22
    store i8 %25, ptr %24
    %26 = const i64 3
    %27 = gep i8, ptr %10, %26
    %28 = load i8, ptr %9
    store i8 %28, ptr %27
    %29 = const i64 1
    %30 = gep i8, ptr %9, %29
    %31 = const i64 1
    %32 = gep i8, ptr %27, %31
    %33 = load i8, ptr %30
    store i8 %33, ptr %32
    %34 = const i64 2
    %35 = gep i8, ptr %9, %34
    %36 = const i64 2
    %37 = gep i8, ptr %27, %36
    %38 = load i8, ptr %35
    store i8 %38, ptr %37
    %39 = load i8, ptr %10
    %40 = sext i8 %39 to i64
    switch %40 [ 1: bb7 0: bb6 default: bb12 ]
bb6:
    %41 = const bool false
    br bb11(%41)
bb7:
    %42 = const i64 3
    %43 = gep i8, ptr %10, %42
    %44 = load i8, ptr %43
    %45 = sext i8 %44 to i64
    switch %45 [ 1: bb8 0: bb6 default: bb12 ]
bb8:
    %46 = const i64 1
    %47 = gep i8, ptr %10, %46
    %48 = load u8, ptr %47
    %49 = const i64 2
    %50 = gep i8, ptr %10, %49
    %51 = load u8, ptr %50
    %52 = const i64 4
    %53 = gep i8, ptr %10, %52
    %54 = load u8, ptr %53
    %55 = const i64 5
    %56 = gep i8, ptr %10, %55
    %57 = load u8, ptr %56
    %58 = icmp eq u8 %48, %54
    condbr %58, bb9(%51, %57), bb10
bb9(%3: u8, %4: u8):
    %59 = icmp eq u8 %3, %4
    br bb11(%59)
bb10:
    %60 = const bool false
    br bb11(%60)
bb11(%5: bool):
    ret %5
bb12:
    unreachable
}

fn @_PReg_as_std__cmp__PartialEq___eq(functy.3) {
bb0(%0: ptr, %1: ptr):
    %2 = load u16, ptr %0
    %3 = load u16, ptr %1
    %4 = icmp eq u16 %2, %3
    ret %4
}

fn @reg_root(functy.4) {
bb0(%0: ptr, %1: u16):
    %24 = alloca i16, align 2
    %25 = alloca (i8, i8), align 1
    %26 = alloca (i8, i8), align 1
    %27 = alloca (i8, i8), align 1
    %28 = alloca (i8, i8), align 1
    %29 = alloca (i8, i8), align 1
    %30 = alloca (i8, i8), align 1
    %31 = alloca (i8, i8), align 1
    %32 = alloca (i8, i8), align 1
    %33 = alloca (i8, i8), align 1
    store u16 %1, ptr %24
    %34 = load u16, ptr %24
    %35 = call @func.5(%34)
    br bb1(%35)
bb1(%2: u16):
    %36 = const u16 0
    %37 = icmp ule u16 %36, %2
    condbr %37, bb23(%2), bb4(%2)
bb2:
    %38 = const i8 0
    store i8 %38, ptr %0
    br bb26
bb3(%3: u16):
    %39 = trunc u16 %3 to u8
    store u8 %39, ptr %25
    %40 = const u8 0
    %41 = const i64 1
    %42 = gep i8, ptr %25, %41
    store u8 %40, ptr %42
    %43 = const i64 1
    %44 = gep i8, ptr %0, %43
    %45 = load i8, ptr %25
    store i8 %45, ptr %44
    %46 = const i64 1
    %47 = gep i8, ptr %25, %46
    %48 = const i64 1
    %49 = gep i8, ptr %44, %48
    %50 = load i8, ptr %47
    store i8 %50, ptr %49
    %51 = const i8 1
    store i8 %51, ptr %0
    br bb26
bb4(%4: u16):
    %52 = const u16 32
    %53 = icmp ule u16 %52, %4
    condbr %53, bb22(%4), bb6(%4)
bb5(%5: u16):
    %54 = const u16 32
    %55 = sub u16 %5, %54
    %56 = trunc u16 %55 to u8
    store u8 %56, ptr %26
    %57 = const u8 0
    %58 = const i64 1
    %59 = gep i8, ptr %26, %58
    store u8 %57, ptr %59
    %60 = const i64 1
    %61 = gep i8, ptr %0, %60
    %62 = load i8, ptr %26
    store i8 %62, ptr %61
    %63 = const i64 1
    %64 = gep i8, ptr %26, %63
    %65 = const i64 1
    %66 = gep i8, ptr %61, %65
    %67 = load i8, ptr %64
    store i8 %67, ptr %66
    %68 = const i8 1
    store i8 %68, ptr %0
    br bb26
bb6(%6: u16):
    %69 = const u16 64
    %70 = icmp ule u16 %69, %6
    condbr %70, bb21(%6), bb8(%6)
bb7(%7: u16):
    %71 = const u16 64
    %72 = sub u16 %7, %71
    %73 = trunc u16 %72 to u8
    store u8 %73, ptr %27
    %74 = const u8 1
    %75 = const i64 1
    %76 = gep i8, ptr %27, %75
    store u8 %74, ptr %76
    %77 = const i64 1
    %78 = gep i8, ptr %0, %77
    %79 = load i8, ptr %27
    store i8 %79, ptr %78
    %80 = const i64 1
    %81 = gep i8, ptr %27, %80
    %82 = const i64 1
    %83 = gep i8, ptr %78, %82
    %84 = load i8, ptr %81
    store i8 %84, ptr %83
    %85 = const i8 1
    store i8 %85, ptr %0
    br bb26
bb8(%8: u16):
    %86 = const u16 96
    %87 = icmp ule u16 %86, %8
    condbr %87, bb20(%8), bb10(%8)
bb9(%9: u16):
    %88 = const u16 96
    %89 = sub u16 %9, %88
    %90 = trunc u16 %89 to u8
    store u8 %90, ptr %28
    %91 = const u8 1
    %92 = const i64 1
    %93 = gep i8, ptr %28, %92
    store u8 %91, ptr %93
    %94 = const i64 1
    %95 = gep i8, ptr %0, %94
    %96 = load i8, ptr %28
    store i8 %96, ptr %95
    %97 = const i64 1
    %98 = gep i8, ptr %28, %97
    %99 = const i64 1
    %100 = gep i8, ptr %95, %99
    %101 = load i8, ptr %98
    store i8 %101, ptr %100
    %102 = const i8 1
    store i8 %102, ptr %0
    br bb26
bb10(%10: u16):
    %103 = const u16 128
    %104 = icmp ule u16 %103, %10
    condbr %104, bb19(%10), bb12(%10)
bb11(%11: u16):
    %105 = const u16 128
    %106 = sub u16 %11, %105
    %107 = trunc u16 %106 to u8
    store u8 %107, ptr %29
    %108 = const u8 1
    %109 = const i64 1
    %110 = gep i8, ptr %29, %109
    store u8 %108, ptr %110
    %111 = const i64 1
    %112 = gep i8, ptr %0, %111
    %113 = load i8, ptr %29
    store i8 %113, ptr %112
    %114 = const i64 1
    %115 = gep i8, ptr %29, %114
    %116 = const i64 1
    %117 = gep i8, ptr %112, %116
    %118 = load i8, ptr %115
    store i8 %118, ptr %117
    %119 = const i8 1
    store i8 %119, ptr %0
    br bb26
bb12(%12: u16):
    switch %12 [ 160: bb25 161: bb24 default: bb13(%12) ]
bb13(%13: u16):
    %120 = const u16 165
    %121 = icmp ule u16 %120, %13
    condbr %121, bb18(%13), bb15(%13)
bb14(%14: u16):
    %122 = const u16 165
    %123 = sub u16 %14, %122
    %124 = trunc u16 %123 to u8
    store u8 %124, ptr %32
    %125 = const u8 1
    %126 = const i64 1
    %127 = gep i8, ptr %32, %126
    store u8 %125, ptr %127
    %128 = const i64 1
    %129 = gep i8, ptr %0, %128
    %130 = load i8, ptr %32
    store i8 %130, ptr %129
    %131 = const i64 1
    %132 = gep i8, ptr %32, %131
    %133 = const i64 1
    %134 = gep i8, ptr %129, %133
    %135 = load i8, ptr %132
    store i8 %135, ptr %134
    %136 = const i8 1
    store i8 %136, ptr %0
    br bb26
bb15(%15: u16):
    %137 = const u16 197
    %138 = icmp ule u16 %137, %15
    condbr %138, bb17(%15), bb2
bb16(%16: u16):
    %139 = const u16 197
    %140 = sub u16 %16, %139
    %141 = trunc u16 %140 to u8
    store u8 %141, ptr %33
    %142 = const u8 1
    %143 = const i64 1
    %144 = gep i8, ptr %33, %143
    store u8 %142, ptr %144
    %145 = const i64 1
    %146 = gep i8, ptr %0, %145
    %147 = load i8, ptr %33
    store i8 %147, ptr %146
    %148 = const i64 1
    %149 = gep i8, ptr %33, %148
    %150 = const i64 1
    %151 = gep i8, ptr %146, %150
    %152 = load i8, ptr %149
    store i8 %152, ptr %151
    %153 = const i8 1
    store i8 %153, ptr %0
    br bb26
bb17(%17: u16):
    %154 = const u16 228
    %155 = icmp ule u16 %17, %154
    condbr %155, bb16(%17), bb2
bb18(%18: u16):
    %156 = const u16 196
    %157 = icmp ule u16 %18, %156
    condbr %157, bb14(%18), bb15(%18)
bb19(%19: u16):
    %158 = const u16 159
    %159 = icmp ule u16 %19, %158
    condbr %159, bb11(%19), bb12(%19)
bb20(%20: u16):
    %160 = const u16 127
    %161 = icmp ule u16 %20, %160
    condbr %161, bb9(%20), bb10(%20)
bb21(%21: u16):
    %162 = const u16 95
    %163 = icmp ule u16 %21, %162
    condbr %163, bb7(%21), bb8(%21)
bb22(%22: u16):
    %164 = const u16 63
    %165 = icmp ule u16 %22, %164
    condbr %165, bb5(%22), bb6(%22)
bb23(%23: u16):
    %166 = const u16 31
    %167 = icmp ule u16 %23, %166
    condbr %167, bb3(%23), bb4(%23)
bb24:
    %168 = const u8 31
    store u8 %168, ptr %31
    %169 = const u8 0
    %170 = const i64 1
    %171 = gep i8, ptr %31, %170
    store u8 %169, ptr %171
    %172 = const i64 1
    %173 = gep i8, ptr %0, %172
    %174 = load i8, ptr %31
    store i8 %174, ptr %173
    %175 = const i64 1
    %176 = gep i8, ptr %31, %175
    %177 = const i64 1
    %178 = gep i8, ptr %173, %177
    %179 = load i8, ptr %176
    store i8 %179, ptr %178
    %180 = const i8 1
    store i8 %180, ptr %0
    br bb26
bb25:
    %181 = const u8 31
    store u8 %181, ptr %30
    %182 = const u8 0
    %183 = const i64 1
    %184 = gep i8, ptr %30, %183
    store u8 %182, ptr %184
    %185 = const i64 1
    %186 = gep i8, ptr %0, %185
    %187 = load i8, ptr %30
    store i8 %187, ptr %186
    %188 = const i64 1
    %189 = gep i8, ptr %30, %188
    %190 = const i64 1
    %191 = gep i8, ptr %186, %190
    %192 = load i8, ptr %189
    store i8 %192, ptr %191
    %193 = const i8 1
    store i8 %193, ptr %0
    br bb26
bb26:
    ret
}

fn @PReg__encoding(functy.5) {
bb0(%0: u16):
    %1 = alloca i16, align 2
    store u16 %0, ptr %1
    %2 = load u16, ptr %1
    ret %2
}
"#;

/// VERBATIM MIR-closure emit of `ra_lr_contains_root` — LiveRange::contains (liveness.rs:38-40 VERBATIM).
/// Slice: tests/slices/trust_regalloc_liveness_slice.rs; regen per the file header.
/// Emit reported: 938 bytes; 2 closure member(s); validate_module = 0
/// error(s); re-parse OK; EXTERN-FREE.
const RA_LR_CONTAINS_IR: &str = r#"; TrustIr text format v1
module "mir::closure::ra_lr_contains_root"
target "aarch64-apple-darwin" 8 little
file 0 "trust_regalloc_liveness_slice.rs"

functy.0 = (u32, u32, u32) -> (u32)

functy.1 = (ptr, u32) -> (bool)

fn @ra_lr_contains_root(functy.0) {
bb0(%0: u32, %1: u32, %2: u32):
    %4 = alloca (i32, i32), align 4
    store u32 %0, ptr %4
    %5 = const i64 4
    %6 = gep i8, ptr %4, %5
    store u32 %1, ptr %6
    %7 = call @func.1(%4, %2)
    br bb1(%7)
bb1(%3: bool):
    %8 = const u32 1
    %9 = const u32 0
    %10 = select u32 %3, %8, %9
    ret %10
}

fn @LiveRange__contains(functy.1) {
bb0(%0: ptr, %1: u32):
    %5 = load u32, ptr %0
    %6 = icmp ule u32 %5, %1
    condbr %6, bb1(%0, %1), bb2
bb1(%2: ptr, %3: u32):
    %7 = const i64 4
    %8 = gep i8, ptr %2, %7
    %9 = load u32, ptr %8
    %10 = icmp ult u32 %3, %9
    br bb3(%10)
bb2:
    %11 = const bool false
    br bb3(%11)
bb3(%4: bool):
    ret %4
}
"#;

/// VERBATIM MIR-closure emit of `ra_lr_overlaps_root` — LiveRange::overlaps (liveness.rs:43-45 VERBATIM).
/// Slice: tests/slices/trust_regalloc_liveness_slice.rs; regen per the file header.
/// Emit reported: 1204 bytes; 2 closure member(s); validate_module = 0
/// error(s); re-parse OK; EXTERN-FREE.
const RA_LR_OVERLAPS_IR: &str = r#"; TrustIr text format v1
module "mir::closure::ra_lr_overlaps_root"
target "aarch64-apple-darwin" 8 little
file 0 "trust_regalloc_liveness_slice.rs"

functy.0 = (u32, u32, u32, u32) -> (u32)

functy.1 = (ptr, ptr) -> (bool)

fn @ra_lr_overlaps_root(functy.0) {
bb0(%0: u32, %1: u32, %2: u32, %3: u32):
    %5 = alloca (i32, i32), align 4
    %6 = alloca (i32, i32), align 4
    store u32 %0, ptr %5
    %7 = const i64 4
    %8 = gep i8, ptr %5, %7
    store u32 %1, ptr %8
    store u32 %2, ptr %6
    %9 = const i64 4
    %10 = gep i8, ptr %6, %9
    store u32 %3, ptr %10
    %11 = call @func.1(%5, %6)
    br bb1(%11)
bb1(%4: bool):
    %12 = const u32 1
    %13 = const u32 0
    %14 = select u32 %4, %12, %13
    ret %14
}

fn @LiveRange__overlaps(functy.1) {
bb0(%0: ptr, %1: ptr):
    %5 = load u32, ptr %0
    %6 = const i64 4
    %7 = gep i8, ptr %1, %6
    %8 = load u32, ptr %7
    %9 = icmp ult u32 %5, %8
    condbr %9, bb1(%0, %1), bb2
bb1(%2: ptr, %3: ptr):
    %10 = load u32, ptr %3
    %11 = const i64 4
    %12 = gep i8, ptr %2, %11
    %13 = load u32, ptr %12
    %14 = icmp ult u32 %10, %13
    br bb3(%14)
bb2:
    %15 = const bool false
    br bb3(%15)
bb3(%4: bool):
    ret %4
}
"#;

/// VERBATIM MIR-closure emit of `ra_iv_live_at_root` — LiveInterval::is_live_at ([B2] explicit binary search; flat-buffer unflatten).
/// Slice: tests/slices/trust_regalloc_liveness_slice.rs; regen per the file header.
/// Emit reported: 4885 bytes; 3 closure member(s); validate_module = 0
/// error(s); re-parse OK; EXTERN-FREE.
const RA_IV_LIVE_AT_IR: &str = r#"; TrustIr text format v1
module "mir::closure::ra_iv_live_at_root"
target "aarch64-apple-darwin" 8 little
file 0 "trust_regalloc_liveness_slice.rs"

functy.0 = (ptr, u32, u32) -> (u32)

functy.1 = (ptr, ptr) -> ()

functy.2 = (ptr, u32, u32) -> (bool)

fn @ra_iv_live_at_root(functy.0) {
bb0(%0: ptr, %1: u32, %2: u32):
    %6 = alloca (i32, i32, i32, i32, i32, i32, i32, i32), align 4
    %7 = alloca (i32, i32), align 4
    %8 = const u32 0
    store u32 %8, ptr %7
    %9 = const u32 0
    %10 = const i64 4
    %11 = gep i8, ptr %7, %10
    store u32 %9, ptr %11
    %12 = load i32, ptr %7
    store i32 %12, ptr %6
    %13 = const i64 4
    %14 = gep i8, ptr %7, %13
    %15 = const i64 4
    %16 = gep i8, ptr %6, %15
    %17 = load i32, ptr %14
    store i32 %17, ptr %16
    %18 = const i64 8
    %19 = gep i8, ptr %6, %18
    %20 = load i32, ptr %7
    store i32 %20, ptr %19
    %21 = const i64 4
    %22 = gep i8, ptr %7, %21
    %23 = const i64 4
    %24 = gep i8, ptr %19, %23
    %25 = load i32, ptr %22
    store i32 %25, ptr %24
    %26 = const i64 16
    %27 = gep i8, ptr %6, %26
    %28 = load i32, ptr %7
    store i32 %28, ptr %27
    %29 = const i64 4
    %30 = gep i8, ptr %7, %29
    %31 = const i64 4
    %32 = gep i8, ptr %27, %31
    %33 = load i32, ptr %30
    store i32 %33, ptr %32
    %34 = const i64 24
    %35 = gep i8, ptr %6, %34
    %36 = load i32, ptr %7
    store i32 %36, ptr %35
    %37 = const i64 4
    %38 = gep i8, ptr %7, %37
    %39 = const i64 4
    %40 = gep i8, ptr %35, %39
    %41 = load i32, ptr %38
    store i32 %41, ptr %40
    call @func.1(%0, %6)
    br bb1(%1, %2)
bb1(%3: u32, %4: u32):
    %42 = call @func.2(%6, %3, %4)
    br bb2(%42)
bb2(%5: bool):
    %43 = const u32 1
    %44 = const u32 0
    %45 = select u32 %5, %43, %44
    ret %45
}

fn @unflatten(functy.1) {
bb0(%0: ptr, %1: ptr):
    %21 = alloca (i32, i32), align 4
    %22 = const u64 0
    br bb1(%0, %1, %22)
bb1(%2: ptr, %3: ptr, %4: u64):
    %23 = const u64 4
    %24 = icmp ult u64 %4, %23
    condbr %24, bb2(%2, %3, %4), bb6
bb2(%5: ptr, %6: ptr, %7: u64):
    %25 = const u64 2
    %26 = mul u64 %25, %7
    %27 = const u64 8
    %28 = icmp ult u64 %26, %27
    condbr %28, bb3(%5, %6, %7, %26), bb7
bb3(%8: ptr, %9: ptr, %10: u64, %11: u64):
    %29 = gep u32, ptr %8, %11
    %30 = load u32, ptr %29
    %31 = const u64 2
    %32 = mul u64 %31, %10
    %33 = const u64 1
    %34 = add u64 %32, %33
    %35 = const u64 8
    %36 = icmp ult u64 %34, %35
    condbr %36, bb4(%8, %9, %10, %30, %34), bb7
bb4(%12: ptr, %13: ptr, %14: u64, %15: u32, %16: u64):
    %37 = gep u32, ptr %12, %16
    %38 = load u32, ptr %37
    store u32 %15, ptr %21
    %39 = const i64 4
    %40 = gep i8, ptr %21, %39
    store u32 %38, ptr %40
    %41 = const u64 4
    %42 = icmp ult u64 %14, %41
    condbr %42, bb5(%12, %13, %14, %14), bb7
bb5(%17: ptr, %18: ptr, %19: u64, %20: u64):
    %43 = const u64 8
    %44 = mul u64 %20, %43
    %45 = gep i8, ptr %18, %44
    %46 = load i32, ptr %21
    store i32 %46, ptr %45
    %47 = const i64 4
    %48 = gep i8, ptr %21, %47
    %49 = const i64 4
    %50 = gep i8, ptr %45, %49
    %51 = load i32, ptr %48
    store i32 %51, ptr %50
    %52 = const u64 1
    %53 = add u64 %19, %52
    br bb1(%17, %18, %53)
bb6:
    ret
bb7:
    unreachable
}

fn @interval_is_live_at(functy.2) {
bb0(%0: ptr, %1: u32, %2: u32):
    %30 = alloca i64, align 8
    store ptr %0, ptr %30
    %31 = const u32 0
    br bb1(%2, %31, %1)
bb1(%3: u32, %4: u32, %5: u32):
    %32 = icmp ult u32 %4, %5
    condbr %32, bb2(%3, %4, %5), bb9
bb2(%6: u32, %7: u32, %8: u32):
    %33 = sub u32 %8, %7
    %34 = const u32 2
    %35 = const u32 0
    %36 = icmp eq u32 %34, %35
    %37 = const bool false
    %38 = icmp eq bool %36, %37
    condbr %38, bb3(%6, %7, %8, %7, %33), bb11
bb3(%9: u32, %10: u32, %11: u32, %12: u32, %13: u32):
    %39 = const u32 2
    %40 = udiv u32 %13, %39
    %41 = add u32 %12, %40
    %42 = zext u32 %41 to u64
    %43 = const u64 4
    %44 = icmp ult u64 %42, %43
    condbr %44, bb4(%9, %10, %11, %41, %42), bb11
bb4(%14: u32, %15: u32, %16: u32, %17: u32, %18: u64):
    %45 = load ptr, ptr %30
    %46 = const u64 8
    %47 = mul u64 %18, %46
    %48 = gep i8, ptr %45, %47
    %49 = const i64 4
    %50 = gep i8, ptr %48, %49
    %51 = load u32, ptr %50
    %52 = icmp ule u32 %51, %14
    condbr %52, bb5(%14, %16, %17), bb6(%14, %15, %17, %48)
bb5(%19: u32, %20: u32, %21: u32):
    %53 = const u32 1
    %54 = add u32 %21, %53
    br bb1(%19, %54, %20)
bb6(%22: u32, %23: u32, %24: u32, %25: ptr):
    %55 = load u32, ptr %25
    %56 = icmp ugt u32 %55, %22
    condbr %56, bb7(%22, %23, %24), bb8
bb7(%26: u32, %27: u32, %28: u32):
    br bb1(%26, %27, %28)
bb8:
    %57 = const bool true
    br bb10(%57)
bb9:
    %58 = const bool false
    br bb10(%58)
bb10(%29: bool):
    ret %29
bb11:
    unreachable
}
"#;

/// VERBATIM MIR-closure emit of `ra_iv_overlaps_root` — LiveInterval::overlaps ([B1] bounds fast-reject + merge scan, LiveRange::overlaps inlined in closure).
/// Slice: tests/slices/trust_regalloc_liveness_slice.rs; regen per the file header.
/// Emit reported: 9937 bytes; 4 closure member(s); validate_module = 0
/// error(s); re-parse OK; EXTERN-FREE.
const RA_IV_OVERLAPS_IR: &str = r#"; TrustIr text format v1
module "mir::closure::ra_iv_overlaps_root"
target "aarch64-apple-darwin" 8 little
file 0 "trust_regalloc_liveness_slice.rs"

functy.0 = (ptr, u32, ptr, u32) -> (u32)

functy.1 = (ptr, ptr) -> ()

functy.2 = (ptr, u32, ptr, u32) -> (bool)

functy.3 = (ptr, ptr) -> (bool)

fn @ra_iv_overlaps_root(functy.0) {
bb0(%0: ptr, %1: u32, %2: ptr, %3: u32):
    %10 = alloca (i32, i32, i32, i32, i32, i32, i32, i32), align 4
    %11 = alloca (i32, i32), align 4
    %12 = alloca (i32, i32, i32, i32, i32, i32, i32, i32), align 4
    %13 = alloca (i32, i32), align 4
    %14 = const u32 0
    store u32 %14, ptr %11
    %15 = const u32 0
    %16 = const i64 4
    %17 = gep i8, ptr %11, %16
    store u32 %15, ptr %17
    %18 = load i32, ptr %11
    store i32 %18, ptr %10
    %19 = const i64 4
    %20 = gep i8, ptr %11, %19
    %21 = const i64 4
    %22 = gep i8, ptr %10, %21
    %23 = load i32, ptr %20
    store i32 %23, ptr %22
    %24 = const i64 8
    %25 = gep i8, ptr %10, %24
    %26 = load i32, ptr %11
    store i32 %26, ptr %25
    %27 = const i64 4
    %28 = gep i8, ptr %11, %27
    %29 = const i64 4
    %30 = gep i8, ptr %25, %29
    %31 = load i32, ptr %28
    store i32 %31, ptr %30
    %32 = const i64 16
    %33 = gep i8, ptr %10, %32
    %34 = load i32, ptr %11
    store i32 %34, ptr %33
    %35 = const i64 4
    %36 = gep i8, ptr %11, %35
    %37 = const i64 4
    %38 = gep i8, ptr %33, %37
    %39 = load i32, ptr %36
    store i32 %39, ptr %38
    %40 = const i64 24
    %41 = gep i8, ptr %10, %40
    %42 = load i32, ptr %11
    store i32 %42, ptr %41
    %43 = const i64 4
    %44 = gep i8, ptr %11, %43
    %45 = const i64 4
    %46 = gep i8, ptr %41, %45
    %47 = load i32, ptr %44
    store i32 %47, ptr %46
    %48 = const u32 0
    store u32 %48, ptr %13
    %49 = const u32 0
    %50 = const i64 4
    %51 = gep i8, ptr %13, %50
    store u32 %49, ptr %51
    %52 = load i32, ptr %13
    store i32 %52, ptr %12
    %53 = const i64 4
    %54 = gep i8, ptr %13, %53
    %55 = const i64 4
    %56 = gep i8, ptr %12, %55
    %57 = load i32, ptr %54
    store i32 %57, ptr %56
    %58 = const i64 8
    %59 = gep i8, ptr %12, %58
    %60 = load i32, ptr %13
    store i32 %60, ptr %59
    %61 = const i64 4
    %62 = gep i8, ptr %13, %61
    %63 = const i64 4
    %64 = gep i8, ptr %59, %63
    %65 = load i32, ptr %62
    store i32 %65, ptr %64
    %66 = const i64 16
    %67 = gep i8, ptr %12, %66
    %68 = load i32, ptr %13
    store i32 %68, ptr %67
    %69 = const i64 4
    %70 = gep i8, ptr %13, %69
    %71 = const i64 4
    %72 = gep i8, ptr %67, %71
    %73 = load i32, ptr %70
    store i32 %73, ptr %72
    %74 = const i64 24
    %75 = gep i8, ptr %12, %74
    %76 = load i32, ptr %13
    store i32 %76, ptr %75
    %77 = const i64 4
    %78 = gep i8, ptr %13, %77
    %79 = const i64 4
    %80 = gep i8, ptr %75, %79
    %81 = load i32, ptr %78
    store i32 %81, ptr %80
    call @func.1(%0, %10)
    br bb1(%1, %2, %3)
bb1(%4: u32, %5: ptr, %6: u32):
    call @func.1(%5, %12)
    br bb2(%4, %6)
bb2(%7: u32, %8: u32):
    %82 = call @func.2(%10, %7, %12, %8)
    br bb3(%82)
bb3(%9: bool):
    %83 = const u32 1
    %84 = const u32 0
    %85 = select u32 %9, %83, %84
    ret %85
}

fn @unflatten(functy.1) {
bb0(%0: ptr, %1: ptr):
    %21 = alloca (i32, i32), align 4
    %22 = const u64 0
    br bb1(%0, %1, %22)
bb1(%2: ptr, %3: ptr, %4: u64):
    %23 = const u64 4
    %24 = icmp ult u64 %4, %23
    condbr %24, bb2(%2, %3, %4), bb6
bb2(%5: ptr, %6: ptr, %7: u64):
    %25 = const u64 2
    %26 = mul u64 %25, %7
    %27 = const u64 8
    %28 = icmp ult u64 %26, %27
    condbr %28, bb3(%5, %6, %7, %26), bb7
bb3(%8: ptr, %9: ptr, %10: u64, %11: u64):
    %29 = gep u32, ptr %8, %11
    %30 = load u32, ptr %29
    %31 = const u64 2
    %32 = mul u64 %31, %10
    %33 = const u64 1
    %34 = add u64 %32, %33
    %35 = const u64 8
    %36 = icmp ult u64 %34, %35
    condbr %36, bb4(%8, %9, %10, %30, %34), bb7
bb4(%12: ptr, %13: ptr, %14: u64, %15: u32, %16: u64):
    %37 = gep u32, ptr %12, %16
    %38 = load u32, ptr %37
    store u32 %15, ptr %21
    %39 = const i64 4
    %40 = gep i8, ptr %21, %39
    store u32 %38, ptr %40
    %41 = const u64 4
    %42 = icmp ult u64 %14, %41
    condbr %42, bb5(%12, %13, %14, %14), bb7
bb5(%17: ptr, %18: ptr, %19: u64, %20: u64):
    %43 = const u64 8
    %44 = mul u64 %20, %43
    %45 = gep i8, ptr %18, %44
    %46 = load i32, ptr %21
    store i32 %46, ptr %45
    %47 = const i64 4
    %48 = gep i8, ptr %21, %47
    %49 = const i64 4
    %50 = gep i8, ptr %45, %49
    %51 = load i32, ptr %48
    store i32 %51, ptr %50
    %52 = const u64 1
    %53 = add u64 %19, %52
    br bb1(%17, %18, %53)
bb6:
    ret
bb7:
    unreachable
}

fn @interval_overlaps(functy.2) {
bb0(%0: ptr, %1: u32, %2: ptr, %3: u32):
    %77 = alloca i64, align 8
    %78 = alloca i64, align 8
    %79 = alloca (i32, i32), align 4
    %80 = alloca (i64, i64), align 8
    store ptr %0, ptr %77
    store ptr %2, ptr %78
    %81 = const u32 0
    %82 = icmp eq u32 %1, %81
    condbr %82, bb2, bb1(%1, %3)
bb1(%4: u32, %5: u32):
    %83 = const u32 0
    %84 = icmp eq u32 %5, %83
    condbr %84, bb2, bb3(%4, %5)
bb2:
    %85 = const bool false
    br bb22(%85)
bb3(%6: u32, %7: u32):
    %86 = const u64 0
    %87 = const u64 4
    %88 = icmp ult u64 %86, %87
    condbr %88, bb4(%6, %7, %86), bb23
bb4(%8: u32, %9: u32, %10: u64):
    %89 = load ptr, ptr %77
    %90 = const u64 8
    %91 = mul u64 %10, %90
    %92 = gep i8, ptr %89, %91
    %93 = const u32 1
    %94 = sub u32 %8, %93
    %95 = zext u32 %94 to u64
    %96 = const u64 4
    %97 = icmp ult u64 %95, %96
    condbr %97, bb5(%8, %9, %92, %95), bb23
bb5(%11: u32, %12: u32, %13: ptr, %14: u64):
    %98 = load ptr, ptr %77
    %99 = const u64 8
    %100 = mul u64 %14, %99
    %101 = gep i8, ptr %98, %100
    %102 = const u64 0
    %103 = const u64 4
    %104 = icmp ult u64 %102, %103
    condbr %104, bb6(%11, %12, %13, %101, %102), bb23
bb6(%15: u32, %16: u32, %17: ptr, %18: ptr, %19: u64):
    %105 = load ptr, ptr %78
    %106 = const u64 8
    %107 = mul u64 %19, %106
    %108 = gep i8, ptr %105, %107
    %109 = const u32 1
    %110 = sub u32 %16, %109
    %111 = zext u32 %110 to u64
    %112 = const u64 4
    %113 = icmp ult u64 %111, %112
    condbr %113, bb7(%15, %16, %17, %18, %108, %111), bb23
bb7(%20: u32, %21: u32, %22: ptr, %23: ptr, %24: ptr, %25: u64):
    %114 = load ptr, ptr %78
    %115 = const u64 8
    %116 = mul u64 %25, %115
    %117 = gep i8, ptr %114, %116
    %118 = const i64 4
    %119 = gep i8, ptr %23, %118
    %120 = load u32, ptr %119
    %121 = load u32, ptr %24
    %122 = icmp ule u32 %120, %121
    condbr %122, bb9, bb8(%20, %21, %22, %117)
bb8(%26: u32, %27: u32, %28: ptr, %29: ptr):
    %123 = const i64 4
    %124 = gep i8, ptr %29, %123
    %125 = load u32, ptr %124
    %126 = load u32, ptr %28
    %127 = icmp ule u32 %125, %126
    condbr %127, bb9, bb10(%26, %27)
bb9:
    %128 = const bool false
    br bb22(%128)
bb10(%30: u32, %31: u32):
    %129 = const u32 0
    store u32 %129, ptr %79
    %130 = const u32 0
    %131 = const i64 4
    %132 = gep i8, ptr %79, %131
    store u32 %130, ptr %132
    %133 = load u32, ptr %79
    %134 = const i64 4
    %135 = gep i8, ptr %79, %134
    %136 = load u32, ptr %135
    br bb11(%30, %31, %133, %136)
bb11(%32: u32, %33: u32, %34: u32, %35: u32):
    %137 = icmp ult u32 %34, %32
    condbr %137, bb12(%32, %33, %34, %35), bb21
bb12(%36: u32, %37: u32, %38: u32, %39: u32):
    %138 = icmp ult u32 %39, %37
    condbr %138, bb13(%36, %37, %38, %39), bb21
bb13(%40: u32, %41: u32, %42: u32, %43: u32):
    %139 = zext u32 %42 to u64
    %140 = const u64 4
    %141 = icmp ult u64 %139, %140
    condbr %141, bb14(%40, %41, %42, %43, %139), bb23
bb14(%44: u32, %45: u32, %46: u32, %47: u32, %48: u64):
    %142 = load ptr, ptr %77
    %143 = const u64 8
    %144 = mul u64 %48, %143
    %145 = gep i8, ptr %142, %144
    %146 = zext u32 %47 to u64
    %147 = const u64 4
    %148 = icmp ult u64 %146, %147
    condbr %148, bb15(%44, %45, %46, %47, %145, %146), bb23
bb15(%49: u32, %50: u32, %51: u32, %52: u32, %53: ptr, %54: u64):
    %149 = load ptr, ptr %78
    %150 = const u64 8
    %151 = mul u64 %54, %150
    %152 = gep i8, ptr %149, %151
    store ptr %53, ptr %80
    %153 = const i64 8
    %154 = gep i8, ptr %80, %153
    store ptr %152, ptr %154
    %155 = load ptr, ptr %80
    %156 = const i64 8
    %157 = gep i8, ptr %80, %156
    %158 = load ptr, ptr %157
    %159 = call @func.3(%155, %158)
    br bb16(%49, %50, %51, %52, %155, %158, %159)
bb16(%55: u32, %56: u32, %57: u32, %58: u32, %59: ptr, %60: ptr, %61: bool):
    condbr %61, bb17, bb18(%55, %56, %57, %58, %59, %60)
bb17:
    %160 = const bool true
    br bb22(%160)
bb18(%62: u32, %63: u32, %64: u32, %65: u32, %66: ptr, %67: ptr):
    %161 = const i64 4
    %162 = gep i8, ptr %66, %161
    %163 = load u32, ptr %162
    %164 = load u32, ptr %67
    %165 = icmp ule u32 %163, %164
    condbr %165, bb19(%62, %63, %64, %65), bb20(%62, %63, %64, %65)
bb19(%68: u32, %69: u32, %70: u32, %71: u32):
    %166 = const u32 1
    %167 = add u32 %70, %166
    br bb11(%68, %69, %167, %71)
bb20(%72: u32, %73: u32, %74: u32, %75: u32):
    %168 = const u32 1
    %169 = add u32 %75, %168
    br bb11(%72, %73, %74, %169)
bb21:
    %170 = const bool false
    br bb22(%170)
bb22(%76: bool):
    ret %76
bb23:
    unreachable
}

fn @LiveRange__overlaps(functy.3) {
bb0(%0: ptr, %1: ptr):
    %5 = load u32, ptr %0
    %6 = const i64 4
    %7 = gep i8, ptr %1, %6
    %8 = load u32, ptr %7
    %9 = icmp ult u32 %5, %8
    condbr %9, bb1(%0, %1), bb2
bb1(%2: ptr, %3: ptr):
    %10 = load u32, ptr %3
    %11 = const i64 4
    %12 = gep i8, ptr %2, %11
    %13 = load u32, ptr %12
    %14 = icmp ult u32 %10, %13
    br bb3(%14)
bb2:
    %15 = const bool false
    br bb3(%15)
bb3(%4: bool):
    ret %4
}
"#;

/// VERBATIM MIR-closure emit of `ra_merge_class_root` — merge_vreg_class (liveness.rs:552-567 VERBATIM; [B4] tag decoders in closure).
/// Slice: tests/slices/trust_regalloc_liveness_slice.rs; regen per the file header.
/// Emit reported: 5770 bytes; 5 closure member(s); validate_module = 0
/// error(s); re-parse OK; EXTERN-FREE.
const RA_MERGE_CLASS_IR: &str = r#"; TrustIr text format v1
module "mir::closure::ra_merge_class_root"
target "aarch64-apple-darwin" 8 little
file 0 "trust_regalloc_liveness_slice.rs"

functy.0 = (u32, u32) -> (u32)

functy.1 = (ptr, u32) -> ()

functy.2 = (ptr, u8, u8) -> ()

functy.3 = (u8) -> (u32)

functy.4 = (ptr, ptr) -> (bool)

fn @ra_merge_class_root(functy.0) {
bb0(%0: u32, %1: u32):
    %4 = alloca i8, align 1
    %5 = alloca i8, align 1
    %6 = alloca i8, align 1
    call @func.1(%5, %0)
    br bb1(%1)
bb1(%2: u32):
    call @func.1(%6, %2)
    br bb2
bb2:
    %7 = load u8, ptr %5
    %8 = load u8, ptr %6
    call @func.2(%4, %7, %8)
    br bb3
bb3:
    %9 = load u8, ptr %4
    %10 = call @func.3(%9)
    br bb4(%10)
bb4(%3: u32):
    ret %3
}

fn @class_from_u32(functy.1) {
bb0(%0: ptr, %1: u32):
    switch %1 [ 0: bb8 1: bb7 2: bb6 3: bb5 4: bb4 5: bb3 6: bb2 default: bb1 ]
bb1:
    %2 = const i8 7
    store i8 %2, ptr %0
    br bb9
bb2:
    %3 = const i8 6
    store i8 %3, ptr %0
    br bb9
bb3:
    %4 = const i8 5
    store i8 %4, ptr %0
    br bb9
bb4:
    %5 = const i8 4
    store i8 %5, ptr %0
    br bb9
bb5:
    %6 = const i8 3
    store i8 %6, ptr %0
    br bb9
bb6:
    %7 = const i8 2
    store i8 %7, ptr %0
    br bb9
bb7:
    %8 = const i8 1
    store i8 %8, ptr %0
    br bb9
bb8:
    %9 = const i8 0
    store i8 %9, ptr %0
    br bb9
bb9:
    ret
}

fn @merge_vreg_class(functy.2) {
bb0(%0: ptr, %1: u8, %2: u8):
    %4 = alloca i8, align 1
    %5 = alloca i8, align 1
    %6 = alloca (i8, i8), align 1
    store u8 %1, ptr %4
    store u8 %2, ptr %5
    %7 = call @func.4(%4, %5)
    br bb1(%7)
bb1(%3: bool):
    condbr %3, bb2, bb3
bb2:
    %8 = load i8, ptr %4
    store i8 %8, ptr %0
    br bb30
bb3:
    %9 = load i8, ptr %4
    store i8 %9, ptr %6
    %10 = const i64 1
    %11 = gep i8, ptr %6, %10
    %12 = load i8, ptr %5
    store i8 %12, ptr %11
    %13 = load i8, ptr %6
    %14 = sext i8 %13 to i64
    switch %14 [ 0: bb5 default: bb4 ]
bb4:
    %15 = const i64 1
    %16 = gep i8, ptr %6, %15
    %17 = load i8, ptr %16
    %18 = sext i8 %17 to i64
    switch %18 [ 0: bb7 1: bb9 7: bb8 default: bb6 ]
bb5:
    %19 = const i64 1
    %20 = gep i8, ptr %6, %19
    %21 = load i8, ptr %20
    %22 = sext i8 %21 to i64
    switch %22 [ 1: bb29 7: bb29 default: bb4 ]
bb6:
    %23 = load i8, ptr %6
    %24 = sext i8 %23 to i64
    switch %24 [ 2: bb11 default: bb10 ]
bb7:
    %25 = load i8, ptr %6
    %26 = sext i8 %25 to i64
    switch %26 [ 1: bb29 7: bb29 default: bb6 ]
bb8:
    %27 = load i8, ptr %6
    %28 = sext i8 %27 to i64
    switch %28 [ 1: bb28 default: bb6 ]
bb9:
    %29 = load i8, ptr %6
    %30 = sext i8 %29 to i64
    switch %30 [ 7: bb28 default: bb6 ]
bb10:
    %31 = const i64 1
    %32 = gep i8, ptr %6, %31
    %33 = load i8, ptr %32
    %34 = sext i8 %33 to i64
    switch %34 [ 2: bb13 default: bb12 ]
bb11:
    %35 = const i64 1
    %36 = gep i8, ptr %6, %35
    %37 = load i8, ptr %36
    %38 = sext i8 %37 to i64
    switch %38 [ 3: bb27 4: bb27 5: bb27 6: bb27 default: bb10 ]
bb12:
    %39 = load i8, ptr %6
    %40 = sext i8 %39 to i64
    switch %40 [ 3: bb15 default: bb14 ]
bb13:
    %41 = load i8, ptr %6
    %42 = sext i8 %41 to i64
    switch %42 [ 3: bb27 4: bb27 5: bb27 6: bb27 default: bb12 ]
bb14:
    %43 = const i64 1
    %44 = gep i8, ptr %6, %43
    %45 = load i8, ptr %44
    %46 = sext i8 %45 to i64
    switch %46 [ 3: bb17 default: bb16 ]
bb15:
    %47 = const i64 1
    %48 = gep i8, ptr %6, %47
    %49 = load i8, ptr %48
    %50 = sext i8 %49 to i64
    switch %50 [ 4: bb26 5: bb26 6: bb26 default: bb14 ]
bb16:
    %51 = load i8, ptr %6
    %52 = sext i8 %51 to i64
    switch %52 [ 4: bb19 default: bb18 ]
bb17:
    %53 = load i8, ptr %6
    %54 = sext i8 %53 to i64
    switch %54 [ 4: bb26 5: bb26 6: bb26 default: bb16 ]
bb18:
    %55 = const i64 1
    %56 = gep i8, ptr %6, %55
    %57 = load i8, ptr %56
    %58 = sext i8 %57 to i64
    switch %58 [ 4: bb21 5: bb23 6: bb22 default: bb20 ]
bb19:
    %59 = const i64 1
    %60 = gep i8, ptr %6, %59
    %61 = load i8, ptr %60
    %62 = sext i8 %61 to i64
    switch %62 [ 5: bb25 6: bb25 default: bb18 ]
bb20:
    %63 = load i8, ptr %4
    store i8 %63, ptr %0
    br bb30
bb21:
    %64 = load i8, ptr %6
    %65 = sext i8 %64 to i64
    switch %65 [ 5: bb25 6: bb25 default: bb20 ]
bb22:
    %66 = load i8, ptr %6
    %67 = sext i8 %66 to i64
    switch %67 [ 5: bb24 default: bb20 ]
bb23:
    %68 = load i8, ptr %6
    %69 = sext i8 %68 to i64
    switch %69 [ 6: bb24 default: bb20 ]
bb24:
    %70 = const i8 5
    store i8 %70, ptr %0
    br bb30
bb25:
    %71 = const i8 4
    store i8 %71, ptr %0
    br bb30
bb26:
    %72 = const i8 3
    store i8 %72, ptr %0
    br bb30
bb27:
    %73 = const i8 2
    store i8 %73, ptr %0
    br bb30
bb28:
    %74 = const i8 1
    store i8 %74, ptr %0
    br bb30
bb29:
    %75 = const i8 0
    store i8 %75, ptr %0
    br bb30
bb30:
    ret
}

fn @class_tag(functy.3) {
bb0(%0: u8):
    %2 = alloca i8, align 1
    store u8 %0, ptr %2
    %3 = load i8, ptr %2
    %4 = sext i8 %3 to i64
    switch %4 [ 0: bb9 1: bb8 2: bb7 3: bb6 4: bb5 5: bb4 6: bb3 7: bb2 default: bb1 ]
bb1:
    unreachable
bb2:
    %5 = const u32 7
    br bb10(%5)
bb3:
    %6 = const u32 6
    br bb10(%6)
bb4:
    %7 = const u32 5
    br bb10(%7)
bb5:
    %8 = const u32 4
    br bb10(%8)
bb6:
    %9 = const u32 3
    br bb10(%9)
bb7:
    %10 = const u32 2
    br bb10(%10)
bb8:
    %11 = const u32 1
    br bb10(%11)
bb9:
    %12 = const u32 0
    br bb10(%12)
bb10(%1: u32):
    ret %1
}

fn @_RegClass_as_std__cmp__PartialEq___eq(functy.4) {
bb0(%0: ptr, %1: ptr):
    %2 = load i8, ptr %0
    %3 = sext i8 %2 to i64
    %4 = load i8, ptr %1
    %5 = sext i8 %4 to i64
    %6 = icmp eq i64 %3, %5
    ret %6
}
"#;

/// VERBATIM MIR-closure emit of `ra_slot_size_root` — reg_class_size (spill.rs:129-139 VERBATIM; [B4] tag decoder in closure).
/// Slice: tests/slices/trust_regalloc_liveness_slice.rs; regen per the file header.
/// Emit reported: 1603 bytes; 3 closure member(s); validate_module = 0
/// error(s); re-parse OK; EXTERN-FREE.
const RA_SLOT_SIZE_IR: &str = r#"; TrustIr text format v1
module "mir::closure::ra_slot_size_root"
target "aarch64-apple-darwin" 8 little
file 0 "trust_regalloc_liveness_slice.rs"

functy.0 = (u32) -> (u32)

functy.1 = (ptr, u32) -> ()

functy.2 = (u8) -> (u32)

fn @ra_slot_size_root(functy.0) {
bb0(%0: u32):
    %2 = alloca i8, align 1
    call @func.1(%2, %0)
    br bb1
bb1:
    %3 = load u8, ptr %2
    %4 = call @func.2(%3)
    br bb2(%4)
bb2(%1: u32):
    ret %1
}

fn @class_from_u32(functy.1) {
bb0(%0: ptr, %1: u32):
    switch %1 [ 0: bb8 1: bb7 2: bb6 3: bb5 4: bb4 5: bb3 6: bb2 default: bb1 ]
bb1:
    %2 = const i8 7
    store i8 %2, ptr %0
    br bb9
bb2:
    %3 = const i8 6
    store i8 %3, ptr %0
    br bb9
bb3:
    %4 = const i8 5
    store i8 %4, ptr %0
    br bb9
bb4:
    %5 = const i8 4
    store i8 %5, ptr %0
    br bb9
bb5:
    %6 = const i8 3
    store i8 %6, ptr %0
    br bb9
bb6:
    %7 = const i8 2
    store i8 %7, ptr %0
    br bb9
bb7:
    %8 = const i8 1
    store i8 %8, ptr %0
    br bb9
bb8:
    %9 = const i8 0
    store i8 %9, ptr %0
    br bb9
bb9:
    ret
}

fn @reg_class_size(functy.2) {
bb0(%0: u8):
    %2 = alloca i8, align 1
    store u8 %0, ptr %2
    %3 = load i8, ptr %2
    %4 = sext i8 %3 to i64
    switch %4 [ 0: bb6 1: bb7 2: bb5 3: bb6 4: bb7 5: bb4 6: bb3 7: bb2 default: bb1 ]
bb1:
    unreachable
bb2:
    %5 = const u32 4
    br bb8(%5)
bb3:
    %6 = const u32 1
    br bb8(%6)
bb4:
    %7 = const u32 2
    br bb8(%7)
bb5:
    %8 = const u32 16
    br bb8(%8)
bb6:
    %9 = const u32 8
    br bb8(%9)
bb7:
    %10 = const u32 4
    br bb8(%10)
bb8(%1: u32):
    ret %1
}
"#;

// ARMED-DEMO RECORD (2026-07-03, performed and observed, beyond the
// in-test armed control): with RA_SLOT_SIZE_IR's `    %8 = const u32 16`
// (the Fpr128 spill-slot size) hand-corrupted to `const u32 8` — exactly
// the neighbour-trampling bug class named in the header —
// `trust_ra_slot_size_exhaustive_native_eq_jit` FAILED LOUDLY at the
// transcript-oracle assert; the file was then restored (cmp-verified
// byte-identical) and the test re-passed. The in-repo armed control
// (`trust_regfile_armed_control_corrupted_fixture_caught_then_restored`)
// repeats the same discipline automatically on every run: it corrupts the
// X19 callee-saved lower bound inside the embedded module text, proves the
// divergence is caught at EXACTLY e=19, and re-passes the pristine text.
//
// FRESH-RE-EMIT RECORD (2026-07-03): all 9 embedded fixtures re-emitted
// from their slices and cmp-verified byte-identical (deterministic emits);
// the whnf no-drift gate re-run the same session: 115661-byte gold matched
// (no frontend changes this round).

// ── the tests ───────────────────────────────────────────────────────────────

/// The scalar register-file property vector — `preg_class`, `hw_encoding`,
/// `is_callee_saved`, `is_caller_saved`, `PReg::{is_gpr,is_fpr}`,
/// `reg_number`, `RegClass::{size_bits,size_bytes}` — EXHAUSTIVE over the
/// ENTIRE u16 encoding space (all 65536 values: every defined register,
/// every boundary, the whole wildcard tail), JIT vs the LINKED PRODUCTION
/// `trust_cg_ir::regs`.
#[test]
fn trust_regfile_props_exhaustive_production_eq_jit() {
    let expected = 65536usize;
    let rows = run_watchdogged::<(u32, [u32; 10])>("regfile_props", expected, move |tx| {
        let buffer = jit_module(REGFILE_PROPS_IR, "regfile_props");
        // SAFETY: machine code for functy.0 = (u16, ptr) -> ().
        let f: unsafe extern "C" fn(u16, *mut RegPropsC) =
            unsafe { std::mem::transmute(bind(&buffer, "regfile_props_root")) };
        for e in 0..=0xFFFFu32 {
            let mut out = RegPropsC::poisoned();
            unsafe { f(e as u16, &mut out) };
            if tx.send((e, out.as_row())).is_err() {
                return;
            }
        }
    });
    for &(e, row) in &rows {
        let expect = native_props_row(e as u16);
        assert_eq!(
            row, expect,
            "regfile props({e}): JIT {row:?} != production {expect:?}"
        );
    }
    // Ground truth (independent literals against the ARM/AAPCS64 facts).
    let get = |e: u32| rows[e as usize].1;
    assert_eq!(get(19)[2], 1, "X19 is callee-saved (AAPCS64)");
    assert_eq!(
        get(8)[3],
        0,
        "X8 (indirect-result) is NOT caller-saved here"
    );
    assert_eq!(get(31)[1], 31, "SP hw-encodes as 31");
    assert_eq!(get(160)[1], 31, "XZR hw-encodes as 31");
    assert_eq!(get(160)[0], 0, "XZR classifies as Gpr64");
    assert_eq!(get(162)[0], 7, "NZCV classifies as System");
    assert_eq!(get(228)[0], 6, "encoding 228 is B31 (Fpr8)");
    assert_eq!(get(228)[7], 31, "B31 reg_number is 31");
    assert_eq!(get(229)[6], 0, "encoding 229 has NO reg_number");
    assert_eq!(get(229)[0], 7, "encoding 229 falls to the System wildcard");
    assert_eq!(get(70)[8], 128, "V6 size_bits = 128");
    assert_eq!(get(70)[9], 16, "V6 size_bytes = 16");

    // NEGATIVE CONTROL (armed): a callee-saved oracle shifted by one
    // encoding must DISAGREE with the JIT at the X18/X19 boundary.
    let corrupt = |e: u16| prod_regs::is_callee_saved(ProdPReg::new(e.wrapping_add(1))) as u32;
    assert_ne!(
        corrupt(18),
        get(18)[2],
        "negative control must FAIL: shifted callee-saved oracle at e=18"
    );
}

/// THE ARMED CONTROL for this file (corrupt -> loud failure -> restore
/// byte-identical -> re-pass): patch the SINGLE `const u16 19` in the
/// embedded props module (the X19 lower bound of the callee-saved range,
/// is_callee_saved bb1) to `const u16 20`, JIT the corrupted text, and
/// prove the differential CATCHES the miscompiled constraint at exactly
/// e=19 while the pristine module re-passes the same sweep.
#[test]
fn trust_regfile_armed_control_corrupted_fixture_caught_then_restored() {
    let anchor = "    %15 = const u16 19\n";
    assert_eq!(
        REGFILE_PROPS_IR.matches(anchor).count(),
        1,
        "armed-control anchor must be unique in the fixture"
    );
    let corrupted = REGFILE_PROPS_IR.replace(anchor, "    %15 = const u16 20\n");
    assert_ne!(corrupted, REGFILE_PROPS_IR);

    // Corrupted run: sweep GPR encodings 0..=63.
    let rows = run_watchdogged::<(u32, [u32; 10])>("regfile_props CORRUPTED", 64, move |tx| {
        let buffer = jit_module(&corrupted, "regfile_props CORRUPTED");
        let f: unsafe extern "C" fn(u16, *mut RegPropsC) =
            unsafe { std::mem::transmute(bind(&buffer, "regfile_props_root")) };
        for e in 0..64u32 {
            let mut out = RegPropsC::poisoned();
            unsafe { f(e as u16, &mut out) };
            if tx.send((e, out.as_row())).is_err() {
                return;
            }
        }
    });
    let mut diverged = Vec::new();
    for &(e, row) in &rows {
        if row != native_props_row(e as u16) {
            diverged.push(e);
        }
    }
    assert_eq!(
        diverged,
        vec![19],
        "ARMED: the corrupted lower bound must be caught at exactly e=19 (X19 misreported)"
    );
    let bad19 = rows[19].1;
    assert_eq!(
        bad19[2], 0,
        "ARMED: corrupted module must call X19 NOT callee-saved"
    );
    assert_eq!(
        native_props_row(19)[2],
        1,
        "production says X19 IS callee-saved — the divergence is LOUD"
    );

    // Restore: the pristine const (byte-identical embedded text) re-passes.
    let rows = run_watchdogged::<(u32, [u32; 10])>("regfile_props RESTORED", 64, move |tx| {
        let buffer = jit_module(REGFILE_PROPS_IR, "regfile_props RESTORED");
        let f: unsafe extern "C" fn(u16, *mut RegPropsC) =
            unsafe { std::mem::transmute(bind(&buffer, "regfile_props_root")) };
        for e in 0..64u32 {
            let mut out = RegPropsC::poisoned();
            unsafe { f(e as u16, &mut out) };
            if tx.send((e, out.as_row())).is_err() {
                return;
            }
        }
    });
    for &(e, row) in &rows {
        assert_eq!(
            row,
            native_props_row(e as u16),
            "RESTORED module must re-pass at e={e}"
        );
    }
}

/// The width-alias converter family (8 converters via the [B2] total kind
/// decoder; wildcard proven with kind=8,9) x encodings 0..=1023 (covers
/// every defined range + the None tail) + {1500, 65535}, JIT vs the LINKED
/// PRODUCTION converters. The four [B3] const-inlined arms (SP->WSP,
/// XZR->WZR, WSP->SP, WZR->XZR) are individually ground-truthed.
#[test]
fn trust_regfile_alias_family_production_eq_jit() {
    let kinds: Vec<u32> = (0..=9).collect();
    let encs: Vec<u32> = (0..=1023u32).chain([1500, 65535]).collect();
    let expected = kinds.len() * encs.len();
    let (kw, ew) = (kinds.clone(), encs.clone());
    let rows = run_watchdogged::<(u32, u32, u32, u32)>("regfile_alias", expected, move |tx| {
        let buffer = jit_module(REGFILE_ALIAS_IR, "regfile_alias");
        // SAFETY: machine code for functy.0 = (u32, u16, ptr, ptr) -> ().
        let f: unsafe extern "C" fn(u32, u16, *mut u32, *mut u32) =
            unsafe { std::mem::transmute(bind(&buffer, "regfile_alias_root")) };
        for &kind in &kw {
            for &e in &ew {
                let (mut present, mut enc) = (0xDEADu32, 0xDEADu32);
                unsafe { f(kind, e as u16, &mut present, &mut enc) };
                if tx.send((kind, e, present, enc)).is_err() {
                    return;
                }
            }
        }
    });
    for &(kind, e, present, enc) in &rows {
        let native = prod_alias(kind, e as u16);
        let jit = (present != 0).then_some(enc);
        assert_eq!(
            native.map(|p| p.encoding() as u32),
            jit,
            "alias(kind={kind}, e={e}): production={native:?} jit=({present},{enc})"
        );
    }
    let find = |k: u32, e: u32| {
        rows.iter()
            .find(|r| r.0 == k && r.1 == e)
            .map(|r| (r.2, r.3))
            .unwrap()
    };
    // Ground truth incl. the four [B3] const-inlined arms.
    assert_eq!(find(0, 0), (1, 32), "X0 -> W0");
    assert_eq!(find(0, 31), (1, 63), "SP -> WSP ([B3] arm)");
    assert_eq!(find(0, 160), (1, 161), "XZR -> WZR ([B3] arm)");
    assert_eq!(find(1, 63), (1, 31), "WSP -> SP ([B3] arm)");
    assert_eq!(find(1, 161), (1, 160), "WZR -> XZR ([B3] arm)");
    assert_eq!(find(2, 64), (1, 96), "V0 -> D0");
    assert_eq!(find(3, 95), (1, 159), "V31 -> S31");
    assert_eq!(find(4, 64), (1, 165), "V0 -> H0");
    assert_eq!(find(5, 95), (1, 228), "V31 -> B31");
    assert_eq!(find(6, 96), (1, 64), "D0 -> V0");
    assert_eq!(find(7, 128), (1, 64), "S0 -> V0");
    assert_eq!(
        find(8, 128),
        (1, 64),
        "kind=8 exercises the wildcard decoder arm"
    );
    assert_eq!(find(0, 32), (0, 0), "W0 is not a GPR64: None");
    assert_eq!(find(2, 96), (0, 0), "D0 is not an FPR128: None");

    // NEGATIVE CONTROL: a direction-swapped oracle must disagree.
    let swapped = prod_regs::gpr32_to_gpr64(ProdPReg::new(0));
    assert_ne!(
        swapped.map(|p| p.encoding() as u32),
        Some(find(0, 0).1),
        "negative control must FAIL: swapped converter direction at X0"
    );
}

/// `regs_overlap` — THE aarch64 interference-aliasing predicate — EXHAUSTIVE
/// over all pairs (a,b) in 0..=255 (65536 rows: the entire defined register
/// file, the System regs, the undefined root tail 229..=255) + spot pairs
/// beyond, JIT vs LINKED PRODUCTION, plus the symmetry invariant.
#[test]
fn trust_regfile_overlap_exhaustive_production_eq_jit() {
    let expected = 256 * 256 + 3;
    let rows = run_watchdogged::<(u32, u32, u32)>("regs_overlap", expected, move |tx| {
        let buffer = jit_module(REGFILE_OVERLAP_IR, "regs_overlap");
        // SAFETY: machine code for functy.0 = (u16, u16) -> (u32).
        let f: unsafe extern "C" fn(u16, u16) -> u32 =
            unsafe { std::mem::transmute(bind(&buffer, "regfile_overlap_root")) };
        for a in 0..256u32 {
            for b in 0..256u32 {
                let r = unsafe { f(a as u16, b as u16) };
                if tx.send((a, b, r)).is_err() {
                    return;
                }
            }
        }
        for (a, b) in [(300u32, 0u32), (1000, 31), (65535, 65535)] {
            let r = unsafe { f(a as u16, b as u16) };
            if tx.send((a, b, r)).is_err() {
                return;
            }
        }
    });
    for &(a, b, r) in &rows {
        let native = prod_regs::regs_overlap(ProdPReg::new(a as u16), ProdPReg::new(b as u16));
        assert_eq!(
            native as u32, r,
            "regs_overlap({a},{b}): production={native} jit={r}"
        );
    }
    // Symmetry (on the exhaustive square).
    let at = |a: u32, b: u32| rows[(a * 256 + b) as usize].2;
    for a in 0..256u32 {
        for b in 0..256u32 {
            assert_eq!(at(a, b), at(b, a), "overlap must be symmetric at ({a},{b})");
        }
    }
    // Ground truth: the full V0 alias chain and the GPR aliases.
    assert_eq!(at(0, 32), 1, "X0 overlaps W0");
    assert_eq!(at(64, 96), 1, "V0 overlaps D0");
    assert_eq!(at(64, 128), 1, "V0 overlaps S0");
    assert_eq!(at(64, 165), 1, "V0 overlaps H0");
    assert_eq!(at(64, 197), 1, "V0 overlaps B0");
    assert_eq!(at(96, 197), 1, "D0 overlaps B0 (shared FPR root)");
    assert_eq!(at(0, 64), 0, "X0 does not overlap V0");
    assert_eq!(at(31, 63), 1, "SP overlaps WSP");
    assert_eq!(
        at(160, 161),
        1,
        "XZR overlaps WZR (shared root 31, GPR group)"
    );
    assert_eq!(
        at(31, 160),
        1,
        "SP and XZR share root 31 in the GPR group (production model)"
    );
    assert_eq!(at(162, 162), 1, "NZCV == NZCV (equality fast path)");
    assert_eq!(at(162, 163), 0, "NZCV vs FPCR: no roots, no overlap");
    assert_eq!(
        at(229, 229),
        1,
        "undefined encodings still equal themselves"
    );
    assert_eq!(
        at(229, 230),
        0,
        "distinct undefined encodings never overlap"
    );
    assert_eq!(at(1, 33), 1, "X1 overlaps W1");
    assert_eq!(at(1, 34), 0, "X1 does not overlap W2");

    // NEGATIVE CONTROL: an alias-blind oracle (pure equality) must disagree
    // on the X0/W0 row.
    let blind = |a: u16, b: u16| (a == b) as u32;
    assert_ne!(
        blind(0, 32),
        at(0, 32),
        "negative control must FAIL: alias-blind oracle"
    );
}

/// `LiveRange::contains` — EXHAUSTIVE over (start, end, idx) in 0..=15^3
/// (4096 rows, incl. every degenerate start >= end shape — the method is
/// total), JIT vs LINKED PRODUCTION.
#[test]
fn trust_ra_liverange_contains_exhaustive_production_eq_jit() {
    let expected = 16 * 16 * 16;
    let rows = run_watchdogged::<(u32, u32, u32, u32)>("lr_contains", expected, move |tx| {
        let buffer = jit_module(RA_LR_CONTAINS_IR, "lr_contains");
        // SAFETY: machine code for functy.0 = (u32, u32, u32) -> (u32).
        let f: unsafe extern "C" fn(u32, u32, u32) -> u32 =
            unsafe { std::mem::transmute(bind(&buffer, "ra_lr_contains_root")) };
        for s in 0..16u32 {
            for e in 0..16u32 {
                for i in 0..16u32 {
                    let r = unsafe { f(s, e, i) };
                    if tx.send((s, e, i, r)).is_err() {
                        return;
                    }
                }
            }
        }
    });
    for &(s, e, i, r) in &rows {
        let native = ProdLiveRange { start: s, end: e }.contains(i);
        assert_eq!(native as u32, r, "LiveRange[{s},{e}).contains({i})");
    }
    // Ground truth: half-open semantics.
    let at = |s: u32, e: u32, i: u32| rows[(s * 256 + e * 16 + i) as usize].3;
    assert_eq!(at(2, 5, 2), 1, "start inclusive");
    assert_eq!(at(2, 5, 4), 1, "interior");
    assert_eq!(at(2, 5, 5), 0, "end EXCLUSIVE");
    assert_eq!(at(2, 5, 1), 0, "before");
    assert_eq!(at(7, 7, 7), 0, "degenerate empty range contains nothing");

    // NEGATIVE CONTROL: a closed-interval oracle must disagree at the end.
    let closed = |s: u32, e: u32, i: u32| (s <= i && i <= e) as u32;
    assert_ne!(
        closed(2, 5, 5),
        at(2, 5, 5),
        "negative control must FAIL: closed end"
    );
}

/// `LiveRange::overlaps` — EXHAUSTIVE over two ranges in 0..=12^4
/// (28561 rows), JIT vs LINKED PRODUCTION + symmetry.
#[test]
fn trust_ra_liverange_overlaps_exhaustive_production_eq_jit() {
    let expected = 13 * 13 * 13 * 13;
    let rows = run_watchdogged::<(u32, u32, u32, u32, u32)>("lr_overlaps", expected, move |tx| {
        let buffer = jit_module(RA_LR_OVERLAPS_IR, "lr_overlaps");
        // SAFETY: machine code for functy.0 = (u32, u32, u32, u32) -> (u32).
        let f: unsafe extern "C" fn(u32, u32, u32, u32) -> u32 =
            unsafe { std::mem::transmute(bind(&buffer, "ra_lr_overlaps_root")) };
        for s1 in 0..13u32 {
            for e1 in 0..13u32 {
                for s2 in 0..13u32 {
                    for e2 in 0..13u32 {
                        let r = unsafe { f(s1, e1, s2, e2) };
                        if tx.send((s1, e1, s2, e2, r)).is_err() {
                            return;
                        }
                    }
                }
            }
        }
    });
    let idx = |s1: u32, e1: u32, s2: u32, e2: u32| (((s1 * 13 + e1) * 13 + s2) * 13 + e2) as usize;
    for &(s1, e1, s2, e2, r) in &rows {
        let a = ProdLiveRange { start: s1, end: e1 };
        let b = ProdLiveRange { start: s2, end: e2 };
        assert_eq!(a.overlaps(&b) as u32, r, "[{s1},{e1}) overlaps [{s2},{e2})");
        assert_eq!(
            rows[idx(s2, e2, s1, e1)].4,
            r,
            "overlap symmetry at [{s1},{e1})/[{s2},{e2})"
        );
    }
    let at = |s1: u32, e1: u32, s2: u32, e2: u32| rows[idx(s1, e1, s2, e2)].4;
    assert_eq!(
        at(0, 4, 4, 8),
        0,
        "TOUCHING ranges do NOT overlap (half-open)"
    );
    assert_eq!(at(0, 5, 4, 8), 1, "one-instruction overlap");
    assert_eq!(at(2, 6, 3, 4), 1, "containment overlaps");
    assert_eq!(at(0, 0, 0, 5), 0, "degenerate empty range overlaps nothing");

    // NEGATIVE CONTROL: a closed-interval oracle must disagree on touching.
    let closed = |s1: u32, e1: u32, s2: u32, e2: u32| (s1 <= e2 && s2 <= e1) as u32;
    assert_ne!(
        closed(0, 4, 4, 8),
        at(0, 4, 4, 8),
        "negative control must FAIL"
    );
}

/// `LiveInterval::is_live_at` — the [B2] explicit-binary-search transcription
/// over the canonical menu (160 sorted non-adjacent interval shapes) x idx
/// 0..=23 EXHAUSTIVE, against BOTH the linked PRODUCTION
/// `LiveInterval::is_live_at` (the real `binary_search_by`) AND the naive
/// any-contains semantic reference.
#[test]
fn trust_ra_interval_live_at_production_and_naive_eq_jit() {
    let menu = canonical_menu();
    let expected = menu.len() * 24;
    let menu_w = menu.clone();
    let rows = run_watchdogged::<(usize, u32, u32)>("iv_live_at", expected, move |tx| {
        let buffer = jit_module(RA_IV_LIVE_AT_IR, "iv_live_at");
        // SAFETY: machine code for functy.0 = (ptr, u32, u32) -> (u32).
        let f: unsafe extern "C" fn(*const u32, u32, u32) -> u32 =
            unsafe { std::mem::transmute(bind(&buffer, "ra_iv_live_at_root")) };
        for (mi, list) in menu_w.iter().enumerate() {
            let (flat, len) = flatten(list);
            for idx in 0..24u32 {
                let r = unsafe { f(flat.as_ptr(), len, idx) };
                if tx.send((mi, idx, r)).is_err() {
                    return;
                }
            }
        }
    });
    for &(mi, idx, r) in &rows {
        let list = &menu[mi];
        let iv = prod_interval(list);
        let prod = iv.is_live_at(idx);
        let naive = naive_live_at(list, idx);
        assert_eq!(prod, naive, "menu[{mi}] invariant: production == naive");
        assert_eq!(
            prod as u32, r,
            "is_live_at(menu[{mi}]={list:?}, {idx}): production={prod} jit={r}"
        );
    }
    // Ground truth on the holed witness (menu[0] = [0,2) + [10,12)).
    let at = |mi: usize, idx: u32| rows[mi * 24 + idx as usize].2;
    assert_eq!(at(0, 0), 1);
    assert_eq!(at(0, 1), 1);
    assert_eq!(at(0, 2), 0, "end exclusive");
    assert_eq!(at(0, 5), 0, "dead in the hole");
    assert_eq!(at(0, 10), 1, "second range found by the binary search");
    assert_eq!(at(0, 11), 1);
    assert_eq!(at(0, 12), 0);
    assert_eq!(at(2, 0), 0, "empty interval is never live");

    // NEGATIVE CONTROL: an idx-shifted oracle (probing idx-1) must disagree
    // at the dead/live boundary 9 -> 10 of the holed witness.
    let iv0 = prod_interval(&menu[0]);
    assert_ne!(
        iv0.is_live_at(9) as u32,
        at(0, 10),
        "negative control must FAIL: idx-shifted oracle at the 9/10 boundary"
    );
}

/// `LiveInterval::overlaps` — the [B1] fixed-capacity transcription of the
/// bounds-fast-reject + merge scan, over all pairs of the first 70 menu
/// entries (4900 rows, incl. empty/holed/nested shapes), against BOTH the
/// linked PRODUCTION `LiveInterval::overlaps` AND the naive pairwise
/// reference, plus symmetry.
#[test]
fn trust_ra_interval_overlaps_production_and_naive_eq_jit() {
    let menu = canonical_menu();
    let n = 70usize.min(menu.len());
    let expected = n * n;
    let menu_w = menu.clone();
    let rows = run_watchdogged::<(usize, usize, u32)>("iv_overlaps", expected, move |tx| {
        let buffer = jit_module(RA_IV_OVERLAPS_IR, "iv_overlaps");
        // SAFETY: machine code for functy.0 = (ptr, u32, ptr, u32) -> (u32).
        let f: unsafe extern "C" fn(*const u32, u32, *const u32, u32) -> u32 =
            unsafe { std::mem::transmute(bind(&buffer, "ra_iv_overlaps_root")) };
        for (ai, a) in menu_w.iter().take(n).enumerate() {
            let (a_flat, a_len) = flatten(a);
            for (bi, b) in menu_w.iter().take(n).enumerate() {
                let (b_flat, b_len) = flatten(b);
                let r = unsafe { f(a_flat.as_ptr(), a_len, b_flat.as_ptr(), b_len) };
                if tx.send((ai, bi, r)).is_err() {
                    return;
                }
            }
        }
    });
    for &(ai, bi, r) in &rows {
        let (a, b) = (&menu[ai], &menu[bi]);
        let prod = prod_interval(a).overlaps(&prod_interval(b));
        let naive = naive_overlaps(a, b);
        assert_eq!(
            prod, naive,
            "menu[{ai}]/menu[{bi}] invariant: production == naive"
        );
        assert_eq!(
            prod as u32, r,
            "interval_overlaps(menu[{ai}]={a:?}, menu[{bi}]={b:?}): production={prod} jit={r}"
        );
        assert_eq!(
            rows[bi * n + ai].2,
            r,
            "interval overlap symmetry ({ai},{bi})"
        );
    }
    let at = |ai: usize, bi: usize| rows[ai * n + bi].2;
    // Ground truth: the holed pair the bounds fast-reject CANNOT decide —
    // menu[0]=[0,2)+[10,12) spans menu[1]=[4,6) but they do NOT overlap.
    assert_eq!(at(0, 1), 0, "hole: bounds overlap but ranges do not");
    assert_eq!(at(0, 3), 1, "whole-universe range hits the holed interval");
    assert_eq!(at(2, 0), 0, "empty interval overlaps nothing");
    assert_eq!(at(2, 2), 0, "empty vs empty");
    assert_eq!(at(0, 0), 1, "an interval overlaps itself (non-empty)");

    // NEGATIVE CONTROL: the bounds-only oracle must disagree on the holed
    // witness pair (this is exactly the row where the merge scan matters).
    let bounds_only = |a: &[(u32, u32)], b: &[(u32, u32)]| {
        if a.is_empty() || b.is_empty() {
            return 0u32;
        }
        let (af, al) = (a[0], a[a.len() - 1]);
        let (bf, bl) = (b[0], b[b.len() - 1]);
        (!(al.1 <= bf.0 || bl.1 <= af.0)) as u32
    };
    assert_ne!(
        bounds_only(&menu[0], &menu[1]),
        at(0, 1),
        "negative control must FAIL: bounds-only oracle on the holed pair"
    );
}

/// `merge_vreg_class` — the mixed-width class-merge lattice — EXHAUSTIVE
/// over all 9x9 tag pairs (tags 0..=8; 8 exercises the wildcard decoder),
/// vs the verbatim transcript oracle, with the lattice laws asserted.
#[test]
fn trust_ra_merge_vreg_class_exhaustive_native_eq_jit() {
    let expected = 81;
    let rows = run_watchdogged::<(u32, u32, u32)>("merge_class", expected, move |tx| {
        let buffer = jit_module(RA_MERGE_CLASS_IR, "merge_class");
        // SAFETY: machine code for functy.0 = (u32, u32) -> (u32).
        let f: unsafe extern "C" fn(u32, u32) -> u32 =
            unsafe { std::mem::transmute(bind(&buffer, "ra_merge_class_root")) };
        for l in 0..9u32 {
            for r in 0..9u32 {
                let m = unsafe { f(l, r) };
                if tx.send((l, r, m)).is_err() {
                    return;
                }
            }
        }
    });
    for &(l, r, m) in &rows {
        let native = tag_of_class(n_merge_vreg_class(class_of_tag(l), class_of_tag(r)));
        assert_eq!(native, m, "merge_vreg_class(tag {l}, tag {r})");
    }
    let at = |l: u32, r: u32| rows[(l * 9 + r) as usize].2;
    // Ground truth: widening merges + the asymmetric default arm.
    assert_eq!(at(0, 1), 0, "Gpr64 ⊔ Gpr32 = Gpr64");
    assert_eq!(at(1, 7), 1, "Gpr32 ⊔ System = Gpr32");
    assert_eq!(at(2, 6), 2, "Fpr128 ⊔ Fpr8 = Fpr128");
    assert_eq!(at(5, 6), 5, "Fpr16 ⊔ Fpr8 = Fpr16");
    assert_eq!(at(6, 5), 5, "Fpr8 ⊔ Fpr16 = Fpr16 (commuted)");
    assert_eq!(
        at(0, 2),
        0,
        "Gpr64 vs Fpr128 falls to `_ => lhs` (asymmetric!)"
    );
    assert_eq!(
        at(2, 0),
        2,
        "Fpr128 vs Gpr64 falls to `_ => lhs` (asymmetric!)"
    );
    for t in 0..9u32 {
        let canon = tag_of_class(class_of_tag(t));
        assert_eq!(at(t, t), canon, "idempotence at tag {t}");
    }

    // NEGATIVE CONTROL: a narrowing-corrupt oracle must disagree.
    assert_ne!(
        6,
        at(5, 6),
        "negative control must FAIL: Fpr16⊔Fpr8 is NOT Fpr8"
    );
}

/// `reg_class_size` — the spill-slot size table — EXHAUSTIVE over tags
/// 0..=8, vs the verbatim transcript oracle AND the production
/// `RegClass::size_bytes` equivalence invariant (they agree on every class).
#[test]
fn trust_ra_slot_size_exhaustive_native_eq_jit() {
    let expected = 9;
    let rows = run_watchdogged::<(u32, u32)>("slot_size", expected, move |tx| {
        let buffer = jit_module(RA_SLOT_SIZE_IR, "slot_size");
        // SAFETY: machine code for functy.0 = (u32) -> (u32).
        let f: unsafe extern "C" fn(u32) -> u32 =
            unsafe { std::mem::transmute(bind(&buffer, "ra_slot_size_root")) };
        for t in 0..9u32 {
            let s = unsafe { f(t) };
            if tx.send((t, s)).is_err() {
                return;
            }
        }
    });
    for &(t, s) in &rows {
        let class = class_of_tag(t);
        assert_eq!(n_reg_class_size(class), s, "reg_class_size(tag {t})");
        // Cross-crate invariant: the spill slot size equals the production
        // register width in bytes for EVERY class (checked, not assumed).
        assert_eq!(
            class.size_bytes(),
            s,
            "spill slot size must equal production RegClass::size_bytes for {class:?}"
        );
    }
    let at = |t: u32| rows[t as usize].1;
    assert_eq!(at(2), 16, "Fpr128 spill slot is 16 bytes (Q register)");
    assert_eq!(at(0), 8, "Gpr64 slot");
    assert_eq!(at(5), 2, "Fpr16 slot");
    assert_eq!(at(6), 1, "Fpr8 slot");

    // NEGATIVE CONTROL: a halved-Q-slot oracle must disagree (the exact bug
    // class that tramples the neighbouring spill slot).
    assert_ne!(8, at(2), "negative control must FAIL: halved Fpr128 slot");
}
