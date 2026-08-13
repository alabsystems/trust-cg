//! TRUST-SELF ROUND 22 (thread R22, TRUST BATCH 9): verifying trust-cg's
//! REGALLOC + INSTRUCTION-SCHEDULER DECIDER layer — the pure scalar/enum
//! predicates that gate correctness-affecting allocation and reordering
//! choices — through the full pipeline Rust -> MIR -> trust-ir (stage1
//! `trust_ir_mir --mir-emit-closure`) -> trust-cg JIT -> machine code,
//! asserting native Rust == JIT over swept real inputs, with the LINKED
//! PRODUCTION functions as a SECOND oracle where they are public
//! (the round-7/16/20 dual-oracle discipline).
//!
//! WHY THIS IS NEW: rounds 1/7/16 verified the machine-code ENCODERS, rounds
//! 5/16 the REGISTER FILES (`regs_overlap`), rounds 20/21 the opt/analysis
//! category + addressing-mode predicates. The instruction scheduler's
//! MAY-ALIAS decider (`byte_ranges_overlap` — the gate that lets the scheduler
//! drop a store->load ordering edge) and the register allocator's live-range
//! INTERFERENCE + class-JOIN + spill-slot-SIZE deciders were UNTOUCHED until
//! this round. A wrong answer here is not a slowdown — it is an UNSOUND
//! miscompile: a reordered memory access, two interfering vregs sharing one
//! physical register, or a too-small spill slot.
//!
//! Verified functions in this file — Slice A (this file), 7 across THREE crates:
//!   * trust-cg-opt (scheduler.rs) — the may-alias + port-capacity deciders:
//!     `byte_ranges_overlap` (static memory-disjointness — soundness-crit),
//!     `port_capacity`                                              (2)
//!   * trust-cg-regalloc (liveness.rs, spill.rs) — the interference / class
//!     deciders:
//!     `LiveRange::overlaps` (live-range interference — soundness-crit),
//!     `LiveRange::contains`, `merge_vreg_class` (class-compat JOIN),
//!     `reg_class_size` (spill-slot byte size)                      (4)
//!   * trust-cg-ir (aarch64_regs.rs) — `RegClass::{size_bits, size_bytes}` (1)
//!
//! DUAL ORACLE: the PUBLIC fns (`LiveRange::overlaps`/`contains`,
//! `port_capacity`, `RegClass::size_bits`/`size_bytes`) are LINKED into this
//! very test binary (transcription drift caught by the second oracle). The
//! PRIVATE fns (`byte_ranges_overlap`, `merge_vreg_class`, `reg_class_size`)
//! are cross-checked against a VERBATIM native transcription here;
//! `reg_class_size` is additionally proven identical to production
//! `RegClass::size_bytes` over all 8 classes.
//!
//! Slice (verbatim transcription; boundaries documented inline there):
//!   tests/slices/trust_sched_regalloc_deciders_slice.rs
//!   -> tests/slices/trust_sched_regalloc_deciders.tir (13263 bytes, 13 members,
//!      validate_module = 0, re-parse OK, EXTERN-FREE, deterministic re-emit).
//!      [B4]: production `byte_ranges_overlap` uses `i64::checked_add`, which
//!      lowers to an empty-bodied core-library leaf under --mir-emit-closure
//!      (F4/owner-#6 class); the slice transcribes a RESULT-IDENTICAL pure-i64
//!      high-side overflow check, and the native oracle here runs the REAL
//!      `checked_add` form verbatim so native==JIT proves the equivalence.
//!
//! COVERAGE NOTE: gated to aarch64 (the JIT target). Run tests ONE AT A TIME
//! (`-- --exact <name> --test-threads=1`): the JIT engine is not thread-safe
//! at suite scale (jit-parallel-race-2026-06-29.md). Every JIT execution runs
//! inside a WATCHDOG worker thread.

#![cfg(target_arch = "aarch64")]

use std::collections::HashMap;
use std::sync::mpsc;
use std::time::Duration;

use trust_cg_codegen::Target;
use trust_cg_codegen::compiler::{Compiler, CompilerConfig};

// LINKED PRODUCTION functions/types (the second oracle):
use trust_cg_ir::regs::RegClass as PRc;
use trust_cg_opt::scheduler::{ExecutionPort as PPort, port_capacity as prod_port_capacity};
use trust_cg_regalloc::LiveRange as PLr;

// ── shared harness (round-7/16/20 pattern) ───────────────────────────────────

const DECIDERS_IR: &str = include_str!("slices/trust_sched_regalloc_deciders.tir");

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

// ── POD mirror of the slice's DecidersOut (repr C, 8 x u32, same order) ───────

#[repr(C)]
#[derive(Clone, Copy)]
struct DecidersOutC {
    byte_overlap: u32,
    lr_overlap: u32,
    lr_contains: u32,
    merged_class_tag: u32,
    reg_class_size: u32,
    size_bits: u32,
    size_bytes: u32,
    port_capacity: u32,
}

impl DecidersOutC {
    fn poisoned() -> Self {
        DecidersOutC {
            byte_overlap: 0xDEAD,
            lr_overlap: 0xDEAD,
            lr_contains: 0xDEAD,
            merged_class_tag: 0xDEAD,
            reg_class_size: 0xDEAD,
            size_bits: 0xDEAD,
            size_bytes: 0xDEAD,
            port_capacity: 0xDEAD,
        }
    }
    fn as_row(&self) -> [u32; 8] {
        [
            self.byte_overlap,
            self.lr_overlap,
            self.lr_contains,
            self.merged_class_tag,
            self.reg_class_size,
            self.size_bits,
            self.size_bytes,
            self.port_capacity,
        ]
    }
}

type DecidersFn = unsafe extern "C" fn(i64, i64, i64, i64, u32, u32, u32, *mut DecidersOutC);

// ── NATIVE oracle (private fns transcribed VERBATIM; public fns LINKED) ───────

fn prc_from_tag(tag: u32) -> PRc {
    use PRc::*;
    match tag {
        0 => Gpr64,
        1 => Gpr32,
        2 => Fpr128,
        3 => Fpr64,
        4 => Fpr32,
        5 => Fpr16,
        6 => Fpr8,
        _ => System,
    }
}

fn prc_tag(rc: PRc) -> u32 {
    match rc {
        PRc::Gpr64 => 0,
        PRc::Gpr32 => 1,
        PRc::Fpr128 => 2,
        PRc::Fpr64 => 3,
        PRc::Fpr32 => 4,
        PRc::Fpr16 => 5,
        PRc::Fpr8 => 6,
        PRc::System => 7,
    }
}

fn pport_from_tag(tag: u32) -> PPort {
    use PPort::*;
    match tag {
        0 => IntAlu,
        1 => IntMul,
        2 => IntDiv,
        3 => LoadStore,
        4 => Branch,
        _ => FpAlu,
    }
}

/// VERBATIM native transcription of scheduler.rs:403-421 (private fn).
fn nat_byte_ranges_overlap(
    left_offset: i64,
    left_size: i64,
    right_offset: i64,
    right_size: i64,
) -> bool {
    if left_size <= 0 || right_size <= 0 {
        return true;
    }
    let Some(left_end) = left_offset.checked_add(left_size) else {
        return true;
    };
    let Some(right_end) = right_offset.checked_add(right_size) else {
        return true;
    };
    left_offset < right_end && right_offset < left_end
}

/// VERBATIM native transcription of liveness.rs:552-567 (private fn), over the
/// PRODUCTION `RegClass`.
fn nat_merge_vreg_class(lhs: PRc, rhs: PRc) -> PRc {
    if lhs == rhs {
        return lhs;
    }
    use PRc::*;
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

/// VERBATIM native transcription of spill.rs:128-139 (private fn).
fn nat_reg_class_size(class: PRc) -> u32 {
    match class {
        PRc::Gpr32 | PRc::Fpr32 => 4,
        PRc::Gpr64 | PRc::Fpr64 => 8,
        PRc::Fpr128 => 16,
        PRc::Fpr16 => 2,
        PRc::Fpr8 => 1,
        PRc::System => 4,
    }
}

fn native_row(a: i64, b: i64, c: i64, d: i64, rc1: u32, rc2: u32, port: u32) -> [u32; 8] {
    let ua = a as u32;
    let ub = b as u32;
    let uc = c as u32;
    let ud = d as u32;
    let r1 = prc_from_tag(rc1);
    let r2 = prc_from_tag(rc2);
    [
        nat_byte_ranges_overlap(a, b, c, d) as u32,
        // LINKED production LiveRange::overlaps (struct literal, [B2]).
        (PLr { start: ua, end: ub }).overlaps(&PLr { start: uc, end: ud }) as u32,
        // LINKED production LiveRange::contains.
        (PLr { start: ua, end: ub }).contains(uc) as u32,
        prc_tag(nat_merge_vreg_class(r1, r2)),
        nat_reg_class_size(r1),
        r1.size_bits(),                           // LINKED
        r1.size_bytes(),                          // LINKED
        prod_port_capacity(pport_from_tag(port)), // LINKED
    ]
}

// ── the sweep ────────────────────────────────────────────────────────────────

fn input_tuples() -> Vec<(i64, i64, i64, i64, u32, u32, u32)> {
    let mut t: Vec<(i64, i64, i64, i64, u32, u32, u32)> = Vec::new();

    // Group 1: EXHAUSTIVE class families. All 64 (rc1,rc2) pairs cover
    // merge_vreg_class; rc1 in 0..8 covers reg_class_size/size_bits/size_bytes;
    // port cycles through all 6 execution ports.
    for rc1 in 0..8u32 {
        for rc2 in 0..8u32 {
            let port = (rc1 * 8 + rc2) % 6;
            t.push((0, 8, 4, 8, rc1, rc2, port));
        }
    }

    // Group 2: byte_ranges_overlap edge grid (offsets straddling endpoints,
    // positive sizes) + degenerate/overflow specials (must all return `true`
    // = conservative "assume overlap").
    let offs = [-4i64, -1, 0, 1, 4];
    let szs = [1i64, 2, 4];
    for &lo in &offs {
        for &ls in &szs {
            for &ro in &offs {
                for &rs in &szs {
                    t.push((lo, ls, ro, rs, 0, 0, 0));
                }
            }
        }
    }
    let specials: [(i64, i64, i64, i64); 12] = [
        (0, 0, 0, 4),                       // left size 0 -> true
        (0, -1, 0, 4),                      // left size negative -> true
        (0, 4, 0, 0),                       // right size 0 -> true
        (0, 4, 0, -1),                      // right size negative -> true
        (i64::MAX, 4, 0, 4),                // left_offset+size overflow -> true
        (0, 4, i64::MAX, 4),                // right overflow -> true
        (i64::MAX - 3, 4, 0, 1000),         // left_end overflow boundary -> true
        (i64::MIN, 4, i64::MIN, 4),         // both at min
        (i64::MAX - 4, 4, i64::MAX - 2, 4), // near-max, no overflow, exact overlap
        (-8, 8, 0, 8),                      // adjacent on the negative side -> false
        (-1, 1, 0, 1),                      // adjacent [-1,0)/[0,1) -> false
        (-1, 2, 0, 1),                      // [-1,1) vs [0,1) -> overlap true
    ];
    for &(lo, ls, ro, rs) in &specials {
        t.push((lo, ls, ro, rs, 0, 0, 0));
    }

    // Group 3: live-range interference endpoints. overlaps uses (s1,e1,x,e2);
    // contains uses (s1,e1,x). Half-open: adjacent ranges must NOT overlap.
    let lr_cases: [(i64, i64, i64, i64); 11] = [
        (0, 5, 5, 10), // adjacent -> overlap false; contains(5) on [0,5) false
        (0, 5, 4, 10), // overlap true; contains(4) true
        (0, 10, 3, 7), // containment; contains(3) true
        (0, 3, 7, 10), // disjoint; contains(7) false
        (5, 5, 0, 10), // empty range1: overlap 5<10 && 0<5 -> true; contains(0) false
        (0, 5, 0, 5),  // identical; contains(0) true
        (0, 5, 5, 5),  // range2 empty at 5: overlap 0<5 && 5<5 -> false; contains(5) false
        (3, 7, 2, 4),  // partial; contains(2) false
        (3, 7, 6, 7),  // contains(6) true (end-1)
        (0, 1, 0, 1),  // single point [0,1): contains(0) true
        (0, 0, 0, 0),  // both empty: overlap false; contains(0) false
    ];
    for &(s1, e1, x, e2) in &lr_cases {
        t.push((s1, e1, x, e2, 0, 0, 0));
    }

    t
}

// ── the tests ────────────────────────────────────────────────────────────────

/// The scheduler may-alias + regalloc scalar decider layer, native==JIT over a
/// class-exhaustive + endpoint/overflow sweep, JIT vs the LINKED production
/// deciders (public) + verbatim native transcription (private).
#[test]
fn trust_sched_regalloc_deciders_production_eq_jit() {
    let tuples = input_tuples();
    let expected = tuples.len();
    let sweep = tuples.clone();
    let rows = run_watchdogged::<[u32; 8]>("deciders", expected, move |tx| {
        let buffer = jit_module(DECIDERS_IR, "deciders");
        let f: DecidersFn = unsafe { std::mem::transmute(bind(&buffer, "deciders_root")) };
        for &(a, b, c, d, rc1, rc2, port) in &sweep {
            let mut out = DecidersOutC::poisoned();
            unsafe { f(a, b, c, d, rc1, rc2, port, &mut out) };
            if tx.send(out.as_row()).is_err() {
                return;
            }
        }
    });

    assert_eq!(rows.len(), expected);
    for (i, &(a, b, c, d, rc1, rc2, port)) in tuples.iter().enumerate() {
        let expect = native_row(a, b, c, d, rc1, rc2, port);
        assert_eq!(
            rows[i], expect,
            "deciders(a={a} b={b} c={c} d={d} rc1={rc1} rc2={rc2} port={port}): JIT {:?} != oracle {:?}",
            rows[i], expect
        );
        // 0xDEAD poison must be gone (the JIT genuinely wrote every field).
        assert!(
            rows[i].iter().all(|&v| v != 0xDEAD),
            "row {i} still poisoned: {:?}",
            rows[i]
        );
    }

    // Field-level attribution asserts (readable, decoupled from the oracle):
    let idx = |a: i64, b: i64, c: i64, d: i64, rc1: u32, rc2: u32, port: u32| -> usize {
        tuples
            .iter()
            .position(|&t| t == (a, b, c, d, rc1, rc2, port))
            .expect("tuple present")
    };
    let byte_overlap = |i: usize| rows[i][0];
    let lr_overlap = |i: usize| rows[i][1];
    let lr_contains = |i: usize| rows[i][2];
    let merged = |i: usize| rows[i][3];
    let sz = |i: usize| rows[i][4];
    let bits = |i: usize| rows[i][5];
    let bytes = |i: usize| rows[i][6];
    let cap = |i: usize| rows[i][7];

    // MAY-ALIAS: half-open adjacency is DISJOINT (soundness of the store->load
    // edge drop). [-8,0)+[0,8) touch, must NOT overlap.
    assert_eq!(
        byte_overlap(idx(-8, 8, 0, 8, 0, 0, 0)),
        0,
        "adjacent byte ranges must be disjoint"
    );
    // overflow / degenerate size -> conservative overlap==true.
    assert_eq!(
        byte_overlap(idx(0, 0, 0, 4, 0, 0, 0)),
        1,
        "zero size -> conservative overlap"
    );
    assert_eq!(
        byte_overlap(idx(i64::MAX, 4, 0, 4, 0, 0, 0)),
        1,
        "left overflow -> conservative overlap"
    );

    // LIVE-RANGE INTERFERENCE: adjacent [0,5)+[5,10) must NOT interfere.
    assert_eq!(
        lr_overlap(idx(0, 5, 5, 10, 0, 0, 0)),
        0,
        "adjacent live ranges do not interfere"
    );
    assert_eq!(
        lr_overlap(idx(0, 5, 4, 10, 0, 0, 0)),
        1,
        "overlapping live ranges interfere"
    );
    // contains is half-open: end is exclusive.
    assert_eq!(
        lr_contains(idx(0, 5, 5, 5, 0, 0, 0)),
        0,
        "idx==end is NOT contained (half-open)"
    );
    assert_eq!(
        lr_contains(idx(3, 7, 6, 7, 0, 0, 0)),
        1,
        "idx==end-1 IS contained"
    );

    // CLASS JOIN + SIZE (tags: Gpr64=0 Gpr32=1 Fpr128=2 Fpr64=3 Fpr32=4 Fpr16=5 Fpr8=6 System=7).
    // Group-1 tuples carry port = (rc1*8+rc2)%6; look them up accordingly.
    let cls = |rc1: u32, rc2: u32| idx(0, 8, 4, 8, rc1, rc2, (rc1 * 8 + rc2) % 6);
    assert_eq!(merged(cls(0, 1)), 0, "merge(Gpr64,Gpr32)=Gpr64");
    assert_eq!(merged(cls(4, 3)), 3, "merge(Fpr32,Fpr64)=Fpr64");
    assert_eq!(merged(cls(2, 6)), 2, "merge(Fpr128,Fpr8)=Fpr128");
    assert_eq!(merged(cls(1, 7)), 1, "merge(Gpr32,System)=Gpr32");
    assert_eq!(sz(cls(2, 0)), 16, "reg_class_size(Fpr128)=16");
    assert_eq!(sz(cls(6, 0)), 1, "reg_class_size(Fpr8)=1");
    assert_eq!(bits(cls(2, 0)), 128, "size_bits(Fpr128)=128");
    assert_eq!(bytes(cls(2, 0)), 16, "size_bytes(Fpr128)=16");

    // reg_class_size == RegClass::size_bytes over ALL 8 classes (the identity
    // the two independent tables encode).
    for rc in 0..8u32 {
        let i = cls(rc, 0);
        assert_eq!(
            sz(i),
            bytes(i),
            "reg_class_size(class {rc}) must equal size_bytes"
        );
    }

    // PORT CAPACITY (ports: IntAlu=0 IntMul=1 IntDiv=2 LoadStore=3 Branch=4 FpAlu=5).
    let find_port = |p: u32| tuples.iter().position(|&t| t.6 == p).expect("port present");
    assert_eq!(cap(find_port(0)), 6, "IntAlu capacity = 6");
    assert_eq!(cap(find_port(2)), 1, "IntDiv capacity = 1");
    assert_eq!(cap(find_port(5)), 4, "FpAlu capacity = 4");
}

/// ARMED negative control: patch the `port_capacity(IntAlu) = 6` constant in
/// the emitted module TEXT to 5, re-JIT, and prove the port-capacity field
/// diverges from the native oracle exactly for IntAlu — then re-JIT the
/// pristine module and prove it agrees (restore + re-pass). This proves the
/// .tir genuinely compiled and executed (a silent no-op could not diverge).
#[test]
fn trust_sched_regalloc_deciders_armed_control() {
    const ANCHOR: &str = "%10 = const u32 6";
    assert_eq!(
        DECIDERS_IR.matches(ANCHOR).count(),
        1,
        "corruption anchor must be unique (port_capacity IntAlu arm)"
    );
    let corrupted = DECIDERS_IR.replace(ANCHOR, "%10 = const u32 5");
    assert_ne!(
        corrupted, DECIDERS_IR,
        "corruption must change the module text"
    );

    // Run IntAlu (port=0) through BOTH the corrupted and the pristine module.
    let corrupt_cap = run_watchdogged::<u32>("deciders CORRUPTED", 1, move |tx| {
        let buffer = jit_module(&corrupted, "deciders CORRUPTED");
        let f: DecidersFn = unsafe { std::mem::transmute(bind(&buffer, "deciders_root")) };
        let mut out = DecidersOutC::poisoned();
        unsafe { f(0, 8, 4, 8, 0, 0, 0, &mut out) };
        let _ = tx.send(out.port_capacity);
    })[0];

    let pristine_cap = run_watchdogged::<u32>("deciders RESTORED", 1, move |tx| {
        let buffer = jit_module(DECIDERS_IR, "deciders RESTORED");
        let f: DecidersFn = unsafe { std::mem::transmute(bind(&buffer, "deciders_root")) };
        let mut out = DecidersOutC::poisoned();
        unsafe { f(0, 8, 4, 8, 0, 0, 0, &mut out) };
        let _ = tx.send(out.port_capacity);
    })[0];

    let native_cap = prod_port_capacity(PPort::IntAlu);
    assert_eq!(native_cap, 6, "production IntAlu capacity is 6");
    assert_eq!(
        corrupt_cap, 5,
        "corrupted module must return the patched 5 (JIT really executed the text)"
    );
    assert_ne!(
        corrupt_cap, native_cap,
        "corrupted JIT must DIVERGE from the production oracle"
    );
    assert_eq!(
        pristine_cap, native_cap,
        "pristine module must AGREE with the production oracle (restore + re-pass)"
    );
}

// ============================================================================
// SLICE B — the instruction-scheduler AArch64Opcode CLASSIFIER layer
// (opcode_latency + call-clobber + the three reorder-legality gates), verified
// EXHAUSTIVELY over all 260 production opcodes with the [B3] repr(u16)
// declared-tag workaround (260 variants no longer fit repr(u8); rustc gives
// the no-repr enum a u16 tag). opcode_latency is LINKED (dual oracle); the
// three private reorder gates + call_clobbers are cross-checked against a
// VERBATIM native transcription over the production AArch64Opcode +
// production InstFlags.
// ============================================================================

use trust_cg_ir::{AArch64Opcode as P, InstFlags as PFlags};
use trust_cg_opt::scheduler::opcode_latency as prod_opcode_latency;

const OPCODE_CLASS_IR: &str = include_str!("slices/trust_opcode_sched_class.tir");
const F5_NOREPR_IR: &str = include_str!("slices/trust_f5_norepr_clobbers.tir");

const OPCODE_COUNT: u32 = 260;

/// Production AArch64Opcode by declaration-order index — the ordered array the
/// slice's `opcode_from_index` mirrors 1:1 (so JIT index i and native P index i
/// are the same variant).
fn prod_opcode(idx: u32) -> P {
    match idx {
        0 => P::AddRR,
        1 => P::AddRI,
        2 => P::AddRIShift12,
        3 => P::SubRR,
        4 => P::SubRI,
        5 => P::MulRR,
        6 => P::Msub,
        7 => P::Smull,
        8 => P::Umull,
        9 => P::SDiv,
        10 => P::UDiv,
        11 => P::Neg,
        12 => P::AndRR,
        13 => P::AndRI,
        14 => P::OrrRR,
        15 => P::OrrRI,
        16 => P::EorRR,
        17 => P::EorRI,
        18 => P::OrnRR,
        19 => P::BicRR,
        20 => P::LslRR,
        21 => P::LsrRR,
        22 => P::AsrRR,
        23 => P::LslRI,
        24 => P::LsrRI,
        25 => P::AsrRI,
        26 => P::RorRI,
        27 => P::Rbit,
        28 => P::CmpRR,
        29 => P::CmpRI,
        30 => P::Tst,
        31 => P::Csel,
        32 => P::Csinc,
        33 => P::Csinv,
        34 => P::Csneg,
        35 => P::MovR,
        36 => P::MovI,
        37 => P::Movz,
        38 => P::Movn,
        39 => P::Movk,
        40 => P::FmovImm,
        41 => P::LdrRI,
        42 => P::StrRI,
        43 => P::LdrPreIndex,
        44 => P::StrPreIndex,
        45 => P::LdrPostIndex,
        46 => P::StrPostIndex,
        47 => P::LdrbRI,
        48 => P::LdrhRI,
        49 => P::LdrsbRI,
        50 => P::LdrshRI,
        51 => P::StrbRI,
        52 => P::StrhRI,
        53 => P::LdrLiteral,
        54 => P::LdpRI,
        55 => P::StpRI,
        56 => P::StpPreIndex,
        57 => P::LdpPostIndex,
        58 => P::LdrRO,
        59 => P::StrRO,
        60 => P::LdrbRO,
        61 => P::LdrhRO,
        62 => P::LdrGot,
        63 => P::LdrTlvp,
        64 => P::B,
        65 => P::BCond,
        66 => P::Cbz,
        67 => P::Cbnz,
        68 => P::Tbz,
        69 => P::Tbnz,
        70 => P::Br,
        71 => P::Bl,
        72 => P::Blr,
        73 => P::Ret,
        74 => P::CSet,
        75 => P::Sxtw,
        76 => P::Uxtw,
        77 => P::Sxtb,
        78 => P::Sxth,
        79 => P::Uxtb,
        80 => P::Uxth,
        81 => P::Ubfm,
        82 => P::Sbfm,
        83 => P::Bfm,
        84 => P::FaddRR,
        85 => P::FsubRR,
        86 => P::FmulRR,
        87 => P::FdivRR,
        88 => P::FmaddRR,
        89 => P::FminnmRR,
        90 => P::FmaxnmRR,
        91 => P::FnegRR,
        92 => P::FabsRR,
        93 => P::FsqrtRR,
        94 => P::FrintmRR,
        95 => P::FrintpRR,
        96 => P::FrintzRR,
        97 => P::Fcmp,
        98 => P::FcvtzsRR,
        99 => P::FcvtzuRR,
        100 => P::ScvtfRR,
        101 => P::UcvtfRR,
        102 => P::FcvtSD,
        103 => P::FcvtDS,
        104 => P::FcvtHS,
        105 => P::FcvtHD,
        106 => P::FcvtSH,
        107 => P::FcvtDH,
        108 => P::FmovGprFpr,
        109 => P::FmovFprGpr,
        110 => P::FmovFprFpr,
        111 => P::NeonAddV,
        112 => P::NeonSubV,
        113 => P::NeonMulV,
        114 => P::NeonSmaxV,
        115 => P::NeonSminV,
        116 => P::NeonUmaxV,
        117 => P::NeonUminV,
        118 => P::NeonFaddV,
        119 => P::NeonFsubV,
        120 => P::NeonFmulV,
        121 => P::NeonFdivV,
        122 => P::NeonFcmgtV,
        123 => P::NeonAndV,
        124 => P::NeonOrrV,
        125 => P::NeonEorV,
        126 => P::NeonBicV,
        127 => P::NeonNotV,
        128 => P::NeonRbitV,
        129 => P::NeonRev32V,
        130 => P::NeonRev64V,
        131 => P::NeonCmeqV,
        132 => P::NeonCmgtV,
        133 => P::NeonCmgeV,
        134 => P::NeonCmhiV,
        135 => P::NeonCmhsV,
        136 => P::NeonUmaxv,
        137 => P::NeonAddpScalar,
        138 => P::NeonDupElem,
        139 => P::NeonDupGen,
        140 => P::NeonInsGen,
        141 => P::NeonUmovGen,
        142 => P::NeonMovi,
        143 => P::NeonLd1Post,
        144 => P::NeonLdpQPost,
        145 => P::NeonSt1Post,
        146 => P::NeonStpQPost,
        147 => P::NeonCntV,
        148 => P::NeonUaddlpV,
        149 => P::NeonSaddlpV,
        150 => P::NeonAbsV,
        151 => P::NeonBitV,
        152 => P::NeonUdotV,
        153 => P::NeonExtV,
        154 => P::NeonFmlaV,
        155 => P::NeonFmlsV,
        156 => P::NeonUcvtfV,
        157 => P::NeonScvtfV,
        158 => P::NeonDupScalarD,
        159 => P::Ldar,
        160 => P::Ldarb,
        161 => P::Ldarh,
        162 => P::Stlr,
        163 => P::Stlrb,
        164 => P::Stlrh,
        165 => P::Ldadd,
        166 => P::Ldadda,
        167 => P::Ldaddal,
        168 => P::Ldaddl,
        169 => P::Ldclr,
        170 => P::Ldclra,
        171 => P::Ldclral,
        172 => P::Ldclrl,
        173 => P::Ldeor,
        174 => P::Ldeora,
        175 => P::Ldeoral,
        176 => P::Ldeorl,
        177 => P::Ldset,
        178 => P::Ldseta,
        179 => P::Ldsetal,
        180 => P::Ldsetl,
        181 => P::Ldsmax,
        182 => P::Ldsmaxa,
        183 => P::Ldsmaxal,
        184 => P::Ldsmaxl,
        185 => P::Ldsmin,
        186 => P::Ldsmina,
        187 => P::Ldsminal,
        188 => P::Ldsminl,
        189 => P::Ldumax,
        190 => P::Ldumaxa,
        191 => P::Ldumaxal,
        192 => P::Ldumaxl,
        193 => P::Ldumin,
        194 => P::Ldumina,
        195 => P::Lduminal,
        196 => P::Lduminl,
        197 => P::Swp,
        198 => P::Swpa,
        199 => P::Swpal,
        200 => P::Swpl,
        201 => P::Cas,
        202 => P::Casa,
        203 => P::Casal,
        204 => P::Casl,
        205 => P::Ldaxr,
        206 => P::Stlxr,
        207 => P::Dmb,
        208 => P::Dsb,
        209 => P::Isb,
        210 => P::Adrp,
        211 => P::Adr,
        212 => P::AddPCRel,
        213 => P::LdrswRO,
        214 => P::AddsRR,
        215 => P::AddsRI,
        216 => P::SubsRR,
        217 => P::SubsRI,
        218 => P::Adc,
        219 => P::Sbc,
        220 => P::Umulh,
        221 => P::Smulh,
        222 => P::Madd,
        223 => P::Brk,
        224 => P::TrapOverflow,
        225 => P::TrapBoundsCheck,
        226 => P::TrapBoundsCheckExact,
        227 => P::TrapNull,
        228 => P::TrapNullIfZero,
        229 => P::TrapDivZero,
        230 => P::TrapDivZeroIfZero,
        231 => P::TrapShiftRange,
        232 => P::TrapShiftRangeIfOOB,
        233 => P::Retain,
        234 => P::Release,
        235 => P::MOVWrr,
        236 => P::MOVXrr,
        237 => P::STRWui,
        238 => P::STRXui,
        239 => P::STRSui,
        240 => P::STRDui,
        241 => P::BL,
        242 => P::BLR,
        243 => P::CMPWrr,
        244 => P::CMPXrr,
        245 => P::CMPWri,
        246 => P::CMPXri,
        247 => P::MOVZWi,
        248 => P::MOVZXi,
        249 => P::Bcc,
        250 => P::Mrs,
        251 => P::Phi,
        252 => P::StackAlloc,
        253 => P::Copy,
        254 => P::Nop,
        255 => P::NeonShlVImm,
        256 => P::NeonUshrVImm,
        257 => P::NeonSshrVImm,
        258 => P::TrapOverflowExact,
        259 => P::TailCall,
        _ => P::Nop,
    }
}

fn pport_tag(p: PPort) -> u32 {
    match p {
        PPort::IntAlu => 0,
        PPort::IntMul => 1,
        PPort::IntDiv => 2,
        PPort::LoadStore => 3,
        PPort::Branch => 4,
        PPort::FpAlu => 5,
    }
}

// Native transcriptions of the PRIVATE scheduler predicates (real `==` form).
fn nat_call_clobbers(op: P) -> bool {
    matches!(op, P::Bl | P::Blr | P::BL | P::BLR)
}
fn nat_reorder_load(op: P, flags: PFlags) -> bool {
    use P::*;
    let disq = PFlags::WRITES_MEMORY | PFlags::HAS_SIDE_EFFECTS | PFlags::IS_CALL;
    flags.contains(PFlags::PROOF_REORDERABLE)
        && flags.intersection(disq).is_empty()
        && matches!(
            op,
            LdrRI | LdrbRI | LdrhRI | LdrsbRI | LdrshRI | LdrRO | LdrswRO | LdrLiteral | LdpRI
        )
}
fn nat_reorder_ldr_ri(op: P, flags: PFlags) -> bool {
    let disq = PFlags::WRITES_MEMORY | PFlags::HAS_SIDE_EFFECTS | PFlags::IS_CALL;
    flags.contains(PFlags::PROOF_REORDERABLE)
        && flags.intersection(disq).is_empty()
        && op == P::LdrRI
}
fn nat_reorder_str_ri(op: P, flags: PFlags) -> bool {
    let disq = PFlags::READS_MEMORY | PFlags::IS_CALL | PFlags::IS_PSEUDO;
    flags.contains(PFlags::PROOF_REORDERABLE)
        && flags.contains(PFlags::WRITES_MEMORY)
        && flags.intersection(disq).is_empty()
        && op == P::StrRI
}

fn native_opcode_row(idx: u32, flags_bits: u32) -> [u32; 6] {
    let op = prod_opcode(idx);
    let (lat, port) = prod_opcode_latency(op); // LINKED dual oracle
    let flags = PFlags::from_bits(flags_bits as u16);
    [
        lat,
        pport_tag(port),
        nat_call_clobbers(op) as u32,
        nat_reorder_load(op, flags) as u32,
        nat_reorder_ldr_ri(op, flags) as u32,
        nat_reorder_str_ri(op, flags) as u32,
    ]
}

#[repr(C)]
#[derive(Clone, Copy)]
struct OpcodeOutC {
    latency: u32,
    port_tag: u32,
    call_clobbers: u32,
    reorder_load: u32,
    reorder_ldr_ri: u32,
    reorder_str_ri: u32,
}
impl OpcodeOutC {
    fn poisoned() -> Self {
        OpcodeOutC {
            latency: 0xDEAD,
            port_tag: 0xDEAD,
            call_clobbers: 0xDEAD,
            reorder_load: 0xDEAD,
            reorder_ldr_ri: 0xDEAD,
            reorder_str_ri: 0xDEAD,
        }
    }
    fn as_row(&self) -> [u32; 6] {
        [
            self.latency,
            self.port_tag,
            self.call_clobbers,
            self.reorder_load,
            self.reorder_ldr_ri,
            self.reorder_str_ri,
        ]
    }
}
type OpcodeFn = unsafe extern "C" fn(u32, u32, *mut OpcodeOutC);

// InstFlags bit values (trust-cg-ir inst.rs).
const PR: u32 = 0x200; // PROOF_REORDERABLE
const WM: u32 = 0x80; // WRITES_MEMORY
const RM: u32 = 0x40; // READS_MEMORY
const HSE: u32 = 0x10; // HAS_SIDE_EFFECTS
const CALLF: u32 = 0x01; // IS_CALL
const PSEUDO: u32 = 0x20; // IS_PSEUDO

fn flag_combos() -> [u32; 10] {
    [
        0,
        PR,
        PR | WM,
        PR | RM,
        PR | HSE,
        PR | CALLF,
        PR | PSEUDO,
        PR | WM | RM,
        WM,
        0xFFFF,
    ]
}

/// EXHAUSTIVE over all production AArch64 opcodes x 10 flag combos: opcode
/// latency + port (LINKED oracle) and the call-clobber + three reorder-legality
/// gates (native oracle) agree native==JIT — the repr(u16) [B3] declared-tag
/// form is proven correct across all 132 variants >=128 (the formerly
/// F5-prone range).
#[test]
fn trust_opcode_sched_class_all260_production_eq_jit() {
    let combos = flag_combos();
    let mut inputs: Vec<(u32, u32)> = Vec::new();
    for idx in 0..OPCODE_COUNT {
        for &f in &combos {
            inputs.push((idx, f));
        }
    }
    let expected = inputs.len();
    let sweep = inputs.clone();
    let rows = run_watchdogged::<[u32; 6]>("opcode_class", expected, move |tx| {
        let buffer = jit_module(OPCODE_CLASS_IR, "opcode_class");
        let f: OpcodeFn = unsafe { std::mem::transmute(bind(&buffer, "opcode_root")) };
        for &(idx, flags) in &sweep {
            let mut out = OpcodeOutC::poisoned();
            unsafe { f(idx, flags, &mut out) };
            if tx.send(out.as_row()).is_err() {
                return;
            }
        }
    });

    assert_eq!(rows.len(), expected);
    let mut ge128_checked = 0u32;
    for (i, &(idx, flags)) in inputs.iter().enumerate() {
        let expect = native_opcode_row(idx, flags);
        assert_eq!(
            rows[i],
            expect,
            "opcode_class(idx={idx} flags={flags:#x}) [{:?}]: JIT {:?} != oracle {:?}",
            prod_opcode(idx),
            rows[i],
            expect
        );
        assert!(rows[i].iter().all(|&v| v != 0xDEAD), "row {i} poisoned");
        if idx >= 128 {
            ge128_checked += 1;
        }
    }
    // Prove the >=128 (formerly F5-affected) range was genuinely exercised and
    // correct: exactly 260 - 128 = 132 variants live there.
    assert!(
        ge128_checked == 132 * combos.len() as u32,
        "must exhaustively cover the >=128 variants"
    );

    // Attribution spot-checks (idx: LdrRI=41 StrRI=42 Bl=71 Blr=72 BL=241 BLR=242
    //  SDiv=9). Latency/port table:
    let row = |idx: u32, flags: u32| rows[inputs.iter().position(|&t| t == (idx, flags)).unwrap()];
    // opcode_latency: SDiv (idx 9) = (10, IntDiv=2).
    assert_eq!(row(9, 0)[0], 10, "SDiv latency 10");
    assert_eq!(row(9, 0)[1], 2, "SDiv port IntDiv");
    // AddRR (idx 0) = (1, IntAlu=0).
    assert_eq!(row(0, 0)[0], 1, "AddRR latency 1");
    assert_eq!(row(0, 0)[1], 0, "AddRR port IntAlu");
    // call_clobbers: BL(241)/BLR(242) — the >=128 variants — TRUE (the formerly
    // F5-prone ones; proven correct here under repr(u16)).
    assert_eq!(
        row(241, 0)[2],
        1,
        "BL clobbers registers (variant 241 >= 128)"
    );
    assert_eq!(
        row(242, 0)[2],
        1,
        "BLR clobbers registers (variant 242 >= 128)"
    );
    assert_eq!(row(0, 0)[2], 0, "AddRR does not clobber");
    // reorder gates: LdrRI(41) load-load edge droppable iff PROOF_REORDERABLE
    // set and no disqualifying flag.
    assert_eq!(
        row(41, PR)[3],
        1,
        "LdrRI reorderable-load under PROOF_REORDERABLE"
    );
    assert_eq!(
        row(41, PR)[4],
        1,
        "LdrRI reorderable-ldr_ri under PROOF_REORDERABLE"
    );
    assert_eq!(
        row(41, PR | WM)[3],
        0,
        "WRITES_MEMORY disqualifies load reorder"
    );
    assert_eq!(row(41, 0)[3], 0, "no PROOF_REORDERABLE -> not reorderable");
    // StrRI(42) store->load edge droppable iff PROOF_REORDERABLE && WRITES_MEMORY
    // && no READS_MEMORY/IS_CALL/IS_PSEUDO.
    assert_eq!(
        row(42, PR | WM)[5],
        1,
        "StrRI reorderable-str_ri under PR|WRITES_MEMORY"
    );
    assert_eq!(row(42, PR)[5], 0, "StrRI needs WRITES_MEMORY set");
    assert_eq!(
        row(42, PR | WM | RM)[5],
        0,
        "READS_MEMORY disqualifies str reorder"
    );
    // A non-load/store opcode is never reorderable regardless of flags.
    assert_eq!(row(0, PR)[3], 0, "AddRR never a reorderable load");
    assert_eq!(row(0, PR | WM)[5], 0, "AddRR never a reorderable store");
}

/// ARMED CONTROL #1 (Slice B): patch the `call_clobbers` switch so BL(241) maps
/// to the false-default arm; prove call_clobbers(BL) diverges from the native
/// oracle, then restore + re-pass.
#[test]
fn trust_opcode_sched_class_armed_control() {
    const ANCHOR: &str = "[ 71: bb2 72: bb2 241: bb2 242: bb2 default: bb1 ]";
    assert_eq!(
        OPCODE_CLASS_IR.matches(ANCHOR).count(),
        1,
        "call_clobbers switch anchor unique"
    );
    let corrupted =
        OPCODE_CLASS_IR.replace(ANCHOR, "[ 71: bb2 72: bb2 241: bb1 242: bb2 default: bb1 ]");
    assert_ne!(corrupted, OPCODE_CLASS_IR);

    let corrupt_bl = run_watchdogged::<u32>("opcode CORRUPTED", 1, move |tx| {
        let buffer = jit_module(&corrupted, "opcode CORRUPTED");
        let f: OpcodeFn = unsafe { std::mem::transmute(bind(&buffer, "opcode_root")) };
        let mut out = OpcodeOutC::poisoned();
        unsafe { f(241, 0, &mut out) }; // BL
        let _ = tx.send(out.call_clobbers);
    })[0];
    let pristine_bl = run_watchdogged::<u32>("opcode RESTORED", 1, move |tx| {
        let buffer = jit_module(OPCODE_CLASS_IR, "opcode RESTORED");
        let f: OpcodeFn = unsafe { std::mem::transmute(bind(&buffer, "opcode_root")) };
        let mut out = OpcodeOutC::poisoned();
        unsafe { f(241, 0, &mut out) };
        let _ = tx.send(out.call_clobbers);
    })[0];

    assert!(nat_call_clobbers(P::BL), "production: BL clobbers");
    assert_eq!(corrupt_bl, 0, "corrupted module routes BL to the false arm");
    assert_ne!(corrupt_bl, 1, "corrupted JIT DIVERGES from the oracle");
    assert_eq!(
        pristine_bl, 1,
        "pristine module AGREES with the oracle (restore + re-pass)"
    );
}

/// ARMED CONTROL #2 (Slice B) — the [F5]-in-PRODUCTION demonstration: the SAME
/// `call_opcode_clobbers_registers` predicate over the production AArch64Opcode
/// with NO `#[repr]` (as production declares it). [F5] FIXED: the discriminant read
/// now ZERO-extends the unsigned tag (mir_lower.rs), so BL=241/BLR=242 (both >=128)
/// read back as their positive values and match their unsigned SwitchInt keys —
/// clobbers=true, == native Rust. Bl=71/Blr=72 (<128) were always correct. With
/// 260 variants the no-repr enum's tag is u16 (rustc layout), so this now ALSO
/// pins the u16 no-repr tag read. This proves the F5 fix works on the compiler's
/// OWN no-repr enum (the case the explicit repr of Slice B used to work around).
#[test]
fn trust_f5_norepr_call_clobbers_fixed_bl_blr() {
    let idxs = [71u32, 72, 241, 242]; // Bl, Blr, BL, BLR
    let sweep = idxs;
    let jit: Vec<u32> = run_watchdogged::<(u32, u32)>("f5_norepr", idxs.len(), move |tx| {
        let buffer = jit_module(F5_NOREPR_IR, "f5_norepr");
        let f: unsafe extern "C" fn(u32) -> u32 =
            unsafe { std::mem::transmute(bind(&buffer, "clobbers_root")) };
        for &idx in &sweep {
            let v = unsafe { f(idx) };
            if tx.send((idx, v)).is_err() {
                return;
            }
        }
    })
    .into_iter()
    .map(|(_, v)| v)
    .collect();

    // Native Rust: ALL FOUR clobber (this is the correct answer).
    for &idx in &idxs {
        assert!(
            nat_call_clobbers(prod_opcode(idx)),
            "native: idx {idx} clobbers"
        );
    }
    // [F5] FIXED: the no-repr JIT now agrees with native for ALL FOUR — the >=128
    // variants read back correctly (zero-extended tag) and clobber=true.
    assert_eq!(jit[0], 1, "Bl(71<128): no-repr JIT correct");
    assert_eq!(jit[1], 1, "Blr(72<128): no-repr JIT correct");
    assert_eq!(
        jit[2], 1,
        "BL(241>=128): [F5] FIXED — no-repr JIT clobbers correctly (was false)"
    );
    assert_eq!(
        jit[3], 1,
        "BLR(242>=128): [F5] FIXED — no-repr JIT clobbers correctly (was false)"
    );
    // The repr(u8) Slice B workaround is no longer needed for correctness (the no-repr
    // enum now lowers correctly too).
}
