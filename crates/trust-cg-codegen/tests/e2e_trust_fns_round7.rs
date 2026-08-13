//! TRUST-SELF ROUND 20 (thread R20, TRUST BATCH 7): verifying trust-cg's
//! OPTIMIZATION / ANALYSIS PREDICATE layer — the pure scalar/enum deciders
//! that determine WHEN a machine-level transformation is legal/sound — through
//! the full pipeline Rust -> MIR -> trust-ir (stage1 `trust_ir_mir
//! --mir-emit-closure`) -> trust-cg JIT -> machine code, asserting native Rust
//! == JIT over swept real inputs, with the LINKED PRODUCTION functions as a
//! SECOND oracle (the round-7/16 dual-oracle discipline).
//!
//! WHY THIS IS NEW: rounds 1/7/16 verified the machine-code ENCODERS, rounds
//! 5/16 the REGISTER FILES, round 4 the interpreter INT CORE. The
//! optimization/analysis PREDICATE layer (effects model, opcode categories,
//! addressing-mode legality) was UNTOUCHED until this round. These predicates
//! are the gate every generic pass (DCE, CSE, LICM, strength-reduction,
//! addr-mode formation) consults; a wrong answer lets an UNSOUND optimization
//! through — a deleted live instruction, a reordered memory access, a folded
//! unencodable offset.
//!
//! New verified functions in this file — 15 across TWO crates:
//!   * trust-cg-ir (target_info.rs) — the OpcodeCategory algebraic/strength-
//!     reduction MATCH predicates:
//!     `OpcodeCategory::{is_arithmetic, is_logical, is_shift, is_move,
//!        is_reg_imm, is_reg_reg_binary}`                              (6)
//!   * trust-cg-opt (effects.rs) — the effects-model classifiers +
//!     MemoryEffect queries:
//!     `category_memory_effect`, `category_is_removable`,
//!     `category_reads_flags`, `category_writes_flags`,
//!     `MemoryEffect::{is_pure, reads_memory, writes_memory, is_barrier}` (8)
//!   * trust-cg-opt (addr_mode.rs) — the addressing-mode offset legality
//!     deciders:
//!     `is_encodable_offset`, `is_encodable_pre_post_offset`,
//!     `is_encodable_store_pair_offset`, `is_encodable_generic64_offset`,
//!     `is_foldable_offset` (+ OffsetEncoding)                       (5)
//!     (14 named + MemoryEffect's 4 queries counted as one block = 15 headline.)
//!
//! Slices (verbatim transcriptions; boundaries documented inline there):
//!   tests/slices/trust_opcode_category_slice.rs   (trust-cg-ir + -opt @ 8e48d2e)
//!   tests/slices/trust_addrmode_offset_slice.rs   (trust-cg-opt @ 8e48d2e)
//! The production fns are LINKED into this very test binary, so any
//! transcription drift is caught by the dual oracle.
//!
//! REGEN (per module; trust-ir frontend @ 26379f8):
//!   S=$HOME/trust/build/aarch64-apple-darwin/stage1
//!   cd $HOME/trust-ir/frontend && env -u RUSTUP_TOOLCHAIN RUSTC=$S/bin/rustc \
//!     DYLD_LIBRARY_PATH=$S/lib/rustlib/aarch64-apple-darwin/lib \
//!     $S/bin/cargo run --bin trust_ir_mir -- <slice.rs> \
//!     --crate-type=lib -C overflow-checks=off -C debug-assertions=off \
//!     --mir-emit-closure <root> <out.tir>
//!   opcode_category: 13631 bytes, 17 members, validate_module = 0, re-parse OK
//!   addrmode_offset:  7617 bytes,  6 members, validate_module = 0, re-parse OK
//!   Both EXTERN-FREE (no host shims), deterministic re-emit byte-identical.
//!   No-drift whnf gate re-checked green (115661) — no frontend changes.
//!
//! FRONTEND FINDINGS (this round; owner-reported):
//!   [F1] NEW: the MIR frontend cannot lower `x == Enum::Variant` for a
//!        fieldless enum (derived PartialEq) — the variant-constant lowers to
//!        an aggregate `Const` and the Eq-binop operand asserts a single
//!        scalar ("constant value not a single scalar"). Isolated in a 2-line
//!        repro; the `matches!` form lowers cleanly. `MemoryEffect::is_pure`
//!        (production `self == Self::Pure`) is transcribed as the RESULT-
//!        IDENTICAL `matches!(self, Self::Pure)` (slice [B4]); the linked
//!        production `is_pure` (real `==`) is the dual oracle.
//!   [F2] RE-CONFIRMED (owner item #6, known-open): `RangeInclusive::contains`
//!        does not lower (same const-aggregate assertion). The addr_mode
//!        `(-256..=255).contains(&x)` predicates are transcribed as the
//!        RESULT-IDENTICAL `x >= lo && x <= hi` (slice [B1]); the linked
//!        production `is_encodable_pre_post_offset` (real `.contains`) is the
//!        dual oracle, and the store-pair naive reference uses `.contains`.
//!
//! COVERAGE NOTE: gated to aarch64 (the JIT target); on any other host this
//! file compiles to ZERO tests. Run tests ONE AT A TIME
//! (`-- --exact <name> --test-threads=1`): the JIT engine is not thread-safe
//! at suite scale (jit-parallel-race-2026-06-29.md). Every JIT execution runs
//! inside a WATCHDOG worker thread.

#![cfg(target_arch = "aarch64")]

use std::collections::HashMap;
use std::sync::mpsc;
use std::time::Duration;

use trust_cg_codegen::Target;
use trust_cg_codegen::compiler::{Compiler, CompilerConfig};

// LINKED PRODUCTION functions (the second oracle):
use trust_cg_ir::OpcodeCategory as ProdCat;
use trust_cg_opt::addr_mode::{
    is_encodable_offset as prod_is_encodable_offset, is_encodable_pre_post_offset as prod_pre_post,
};
use trust_cg_opt::effects::{
    MemoryEffect as ProdEffect, category_is_removable as prod_is_removable,
    category_memory_effect as prod_mem_effect, category_reads_flags as prod_reads_flags,
    category_writes_flags as prod_writes_flags,
};

// ── shared harness (round-16 pattern) ────────────────────────────────────────

/// Parse + JIT one embedded module; return the buffer. All round-20 modules
/// are EXTERN-FREE.
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

// ── OpcodeCategory oracle plumbing (mirrored 1:1 from the slice) ──────────────

/// Total reconstruction of the PRODUCTION OpcodeCategory from its
/// declaration-order tag — mirrors the slice's `cat_from_tag` EXACTLY.
fn prod_cat_from_tag(tag: u32) -> ProdCat {
    use ProdCat::*;
    match tag {
        0 => AddRR,
        1 => AddRI,
        2 => SubRR,
        3 => SubRI,
        4 => MulRR,
        5 => Neg,
        6 => AndRR,
        7 => AndRI,
        8 => OrRR,
        9 => OrRI,
        10 => XorRR,
        11 => XorRI,
        12 => ShlRR,
        13 => ShlRI,
        14 => ShrRR,
        15 => ShrRI,
        16 => SarRR,
        17 => SarRI,
        18 => MovRR,
        19 => MovRI,
        20 => CmpRR,
        21 => CmpRI,
        22 => Nop,
        23 => Ret,
        24 => Call,
        25 => Branch,
        26 => CondBranch,
        27 => Load,
        28 => Store,
        29 => Phi,
        _ => Other,
    }
}

fn prod_effect_tag(e: ProdEffect) -> u32 {
    match e {
        ProdEffect::Pure => 0,
        ProdEffect::Load => 1,
        ProdEffect::Store => 2,
        ProdEffect::Call => 3,
    }
}

/// The 31 declared OpcodeCategory variants (a fixed-point cross-check that the
/// tag<->variant map is total and injective on the defined range).
const CAT_COUNT: u32 = 31;

/// POD mirror of the slice's `CatProps` (repr C, 15 x u32, same field order).
#[repr(C)]
#[derive(Clone, Copy)]
struct CatPropsC {
    is_arithmetic: u32,
    is_logical: u32,
    is_shift: u32,
    is_move: u32,
    is_reg_imm: u32,
    is_reg_reg_binary: u32,
    mem_effect_tag: u32,
    eff_is_pure: u32,
    eff_reads_mem: u32,
    eff_writes_mem: u32,
    eff_is_barrier: u32,
    is_removable_wf0: u32,
    is_removable_wf1: u32,
    reads_flags: u32,
    writes_flags: u32,
}

impl CatPropsC {
    fn poisoned() -> Self {
        CatPropsC {
            is_arithmetic: 0xDEAD,
            is_logical: 0xDEAD,
            is_shift: 0xDEAD,
            is_move: 0xDEAD,
            is_reg_imm: 0xDEAD,
            is_reg_reg_binary: 0xDEAD,
            mem_effect_tag: 0xDEAD,
            eff_is_pure: 0xDEAD,
            eff_reads_mem: 0xDEAD,
            eff_writes_mem: 0xDEAD,
            eff_is_barrier: 0xDEAD,
            is_removable_wf0: 0xDEAD,
            is_removable_wf1: 0xDEAD,
            reads_flags: 0xDEAD,
            writes_flags: 0xDEAD,
        }
    }
    fn as_row(&self) -> [u32; 15] {
        [
            self.is_arithmetic,
            self.is_logical,
            self.is_shift,
            self.is_move,
            self.is_reg_imm,
            self.is_reg_reg_binary,
            self.mem_effect_tag,
            self.eff_is_pure,
            self.eff_reads_mem,
            self.eff_writes_mem,
            self.eff_is_barrier,
            self.is_removable_wf0,
            self.is_removable_wf1,
            self.reads_flags,
            self.writes_flags,
        ]
    }
}

/// The PRODUCTION opcode-category property row (oracle for the category test),
/// computed entirely from the LINKED production functions.
fn native_cat_row(tag: u32) -> [u32; 15] {
    let c = prod_cat_from_tag(tag);
    let eff = prod_mem_effect(c);
    [
        c.is_arithmetic() as u32,
        c.is_logical() as u32,
        c.is_shift() as u32,
        c.is_move() as u32,
        c.is_reg_imm() as u32,
        c.is_reg_reg_binary() as u32,
        prod_effect_tag(eff),
        eff.is_pure() as u32,
        eff.reads_memory() as u32,
        eff.writes_memory() as u32,
        eff.is_barrier() as u32,
        prod_is_removable(c, false) as u32,
        prod_is_removable(c, true) as u32,
        prod_reads_flags(c) as u32,
        prod_writes_flags(c) as u32,
    ]
}

// ── addr-mode oracle plumbing ─────────────────────────────────────────────────

/// Naive reference for `is_encodable_store_pair_offset` (private fn; no linked
/// oracle). Uses the PRODUCTION `.contains` form to cross-check the slice's
/// `>= / <=` rewrite ([B1]).
fn naive_store_pair(offset: i64) -> u32 {
    (offset % 8 == 0 && (-64..=63).contains(&(offset / 8))) as u32
}

/// POD mirror of the slice's `OffsetProps` (repr C, 10 x u32, same order).
#[repr(C)]
#[derive(Clone, Copy)]
struct OffsetPropsC {
    enc_offset_1: u32,
    enc_offset_2: u32,
    enc_offset_4: u32,
    enc_offset_8: u32,
    enc_offset_as: u32,
    pre_post: u32,
    store_pair: u32,
    generic64: u32,
    foldable_generic64: u32,
    foldable_scaled_as: u32,
}

impl OffsetPropsC {
    fn poisoned() -> Self {
        OffsetPropsC {
            enc_offset_1: 0xDEAD,
            enc_offset_2: 0xDEAD,
            enc_offset_4: 0xDEAD,
            enc_offset_8: 0xDEAD,
            enc_offset_as: 0xDEAD,
            pre_post: 0xDEAD,
            store_pair: 0xDEAD,
            generic64: 0xDEAD,
            foldable_generic64: 0xDEAD,
            foldable_scaled_as: 0xDEAD,
        }
    }
    fn as_row(&self) -> [u32; 10] {
        [
            self.enc_offset_1,
            self.enc_offset_2,
            self.enc_offset_4,
            self.enc_offset_8,
            self.enc_offset_as,
            self.pre_post,
            self.store_pair,
            self.generic64,
            self.foldable_generic64,
            self.foldable_scaled_as,
        ]
    }
}

/// The PRODUCTION offset-legality property row. The two PUBLIC deciders
/// (`is_encodable_offset`, `is_encodable_pre_post_offset`) are LINKED
/// (dual oracle); the private `generic64`/`foldable` compose from them exactly
/// as the production source does; `store_pair` uses the naive `.contains`
/// reference.
fn native_offset_row(offset: i64, access_size: u32) -> [u32; 10] {
    let asz = access_size as u8;
    let generic64 = (prod_is_encodable_offset(offset, 8) || prod_pre_post(offset)) as u32;
    [
        prod_is_encodable_offset(offset, 1) as u32,
        prod_is_encodable_offset(offset, 2) as u32,
        prod_is_encodable_offset(offset, 4) as u32,
        prod_is_encodable_offset(offset, 8) as u32,
        prod_is_encodable_offset(offset, asz) as u32,
        prod_pre_post(offset) as u32,
        naive_store_pair(offset),
        generic64,
        // foldable(Generic64) == generic64
        generic64,
        // foldable(ScaledUnsigned(asz)) == is_encodable_offset(offset, asz)
        prod_is_encodable_offset(offset, asz) as u32,
    ]
}

// ── the tests ────────────────────────────────────────────────────────────────

/// The OpcodeCategory predicate layer — EXHAUSTIVE over all 31 declared
/// categories, JIT vs the LINKED PRODUCTION `OpcodeCategory` methods +
/// `trust_cg_opt::effects` classifiers.
#[test]
fn trust_opcode_category_all31_production_eq_jit() {
    let expected = CAT_COUNT as usize;
    let rows = run_watchdogged::<(u32, [u32; 15])>("opcode_category", expected, move |tx| {
        let buffer = jit_module(OPCODE_CATEGORY_IR, "opcode_category");
        // SAFETY: machine code for functy.0 = (u32, ptr) -> ().
        let f: unsafe extern "C" fn(u32, *mut CatPropsC) =
            unsafe { std::mem::transmute(bind(&buffer, "cat_props_root")) };
        for tag in 0..CAT_COUNT {
            let mut out = CatPropsC::poisoned();
            unsafe { f(tag, &mut out) };
            if tx.send((tag, out.as_row())).is_err() {
                return;
            }
        }
    });
    for &(tag, row) in &rows {
        let expect = native_cat_row(tag);
        assert_eq!(
            row, expect,
            "opcode_category(tag={tag}): JIT {row:?} != production {expect:?}"
        );
    }
    // field indices into the row (mirror CatPropsC order)
    let get = |tag: u32| rows[tag as usize].1;
    let is_arith = |t: u32| get(t)[0];
    let is_logical = |t: u32| get(t)[1];
    let is_shift = |t: u32| get(t)[2];
    let is_move = |t: u32| get(t)[3];
    let is_reg_imm = |t: u32| get(t)[4];
    let is_rrb = |t: u32| get(t)[5];
    let meff = |t: u32| get(t)[6];
    let eff_pure = |t: u32| get(t)[7];
    let eff_rd = |t: u32| get(t)[8];
    let eff_wr = |t: u32| get(t)[9];
    let eff_barrier = |t: u32| get(t)[10];
    let rm0 = |t: u32| get(t)[11];
    let rm1 = |t: u32| get(t)[12];
    let rdf = |t: u32| get(t)[13];
    let wrf = |t: u32| get(t)[14];

    // Tags (declaration order): AddRR=0 AddRI=1 SubRR=2 MulRR=4 Neg=5
    // AndRR=6 AndRI=7 ShlRR=12 ShlRI=13 MovRR=18 MovRI=19 CmpRR=20 CmpRI=21
    // Nop=22 Ret=23 Call=24 Branch=25 CondBranch=26 Load=27 Store=28 Phi=29
    // Other=30.

    // Arithmetic / logical / shift / move classification.
    assert_eq!(is_arith(0), 1, "AddRR is arithmetic");
    assert_eq!(is_arith(4), 1, "MulRR is arithmetic");
    assert_eq!(is_arith(5), 1, "Neg is arithmetic");
    assert_eq!(is_arith(6), 0, "AndRR is NOT arithmetic");
    assert_eq!(is_logical(6), 1, "AndRR is logical");
    assert_eq!(is_logical(0), 0, "AddRR is NOT logical");
    assert_eq!(is_shift(12), 1, "ShlRR is shift");
    assert_eq!(is_shift(0), 0, "AddRR is NOT shift");
    assert_eq!(is_move(18), 1, "MovRR is move");
    assert_eq!(is_move(19), 1, "MovRI is move");

    // reg-imm / reg-reg-binary — the operand-shape simplification predicates.
    assert_eq!(is_reg_imm(1), 1, "AddRI is reg-imm");
    assert_eq!(is_reg_imm(0), 0, "AddRR is NOT reg-imm");
    assert_eq!(is_reg_imm(19), 1, "MovRI is reg-imm");
    assert_eq!(is_reg_imm(21), 1, "CmpRI is reg-imm");
    assert_eq!(is_rrb(0), 1, "AddRR: op x,x has an identity");
    assert_eq!(is_rrb(2), 1, "SubRR: sub x,x = 0");
    assert_eq!(is_rrb(10), 1, "XorRR: xor x,x = 0 (tag 10)");
    assert_eq!(is_rrb(5), 0, "Neg is unary, NOT reg-reg-binary");
    assert_eq!(is_rrb(1), 0, "AddRI is NOT reg-reg-binary");

    // Memory effect + MemoryEffect queries — the DCE/CSE/LICM gate.
    assert_eq!(meff(0), 0, "AddRR is Pure");
    assert_eq!(eff_pure(0), 1, "AddRR effect is_pure");
    assert_eq!(meff(27), 1, "Load classifies Load");
    assert_eq!(eff_pure(27), 0, "Load is NOT pure");
    assert_eq!(eff_rd(27), 1, "Load reads memory");
    assert_eq!(eff_wr(27), 0, "Load does NOT write memory");
    assert_eq!(eff_barrier(27), 0, "Load is not a barrier");
    assert_eq!(meff(28), 2, "Store classifies Store");
    assert_eq!(eff_rd(28), 0, "Store does not read memory");
    assert_eq!(eff_wr(28), 1, "Store writes memory");
    assert_eq!(meff(24), 3, "Call classifies Call");
    assert_eq!(eff_rd(24), 1, "Call reads (conservative)");
    assert_eq!(eff_wr(24), 1, "Call writes (conservative)");
    assert_eq!(eff_barrier(24), 1, "Call is a barrier");

    // Removability (the DCE decision) at both target_writes_flags polarities.
    assert_eq!(rm0(0), 1, "AddRR removable when target says no flags");
    assert_eq!(rm1(0), 0, "AddRR NOT removable when target writes flags");
    assert_eq!(rm0(20), 0, "CmpRR never removable (always sets flags)");
    assert_eq!(rm0(27), 0, "Load not removable (memory effect)");
    assert_eq!(rm0(28), 0, "Store not removable");
    assert_eq!(rm0(24), 0, "Call not removable");
    assert_eq!(rm0(25), 0, "Branch not removable (control flow)");
    assert_eq!(rm0(26), 0, "CondBranch not removable (control flow)");
    assert_eq!(rm0(23), 0, "Ret not removable (control flow)");
    assert_eq!(rm0(22), 1, "Nop IS removable");
    assert_eq!(rm0(29), 1, "Phi IS removable (pure, non-control)");

    // Flag read/write classification.
    assert_eq!(rdf(26), 1, "CondBranch reads flags");
    assert_eq!(rdf(25), 0, "unconditional Branch does NOT read flags");
    assert_eq!(rdf(0), 0, "AddRR does not read flags (category level)");
    assert_eq!(wrf(20), 1, "CmpRR writes flags");
    assert_eq!(wrf(21), 1, "CmpRI writes flags");
    assert_eq!(wrf(0), 0, "AddRR does not write flags (category level)");

    // Cross-invariant: every removable category is pure (removable => pure).
    for t in 0..CAT_COUNT {
        if rm0(t) == 1 {
            assert_eq!(eff_pure(t), 1, "removable tag {t} must be pure");
        }
    }

    // NEGATIVE CONTROL (armed): an is_removable that DROPS the compare guard
    // (a plausible bug) would call CmpRR removable — production must not.
    let blind_removable = |t: u32| {
        let c = prod_cat_from_tag(t);
        // pure && !target_writes_flags && !control, but WITHOUT the CmpRR/CmpRI guard
        let eff = prod_mem_effect(c);
        let control = matches!(t, 23..=26);
        (eff.is_pure() && !control) as u32
    };
    assert_ne!(
        blind_removable(20),
        rm0(20),
        "negative control must FAIL: CmpRR removable if compare-guard dropped"
    );
    assert_eq!(
        blind_removable(20),
        1,
        "the blind (buggy) oracle wrongly calls CmpRR removable"
    );
}

/// The addressing-mode offset legality deciders — swept over the immediate
/// boundary edges x the access-size menu, JIT vs the LINKED PRODUCTION
/// `is_encodable_offset` / `is_encodable_pre_post_offset` (+ composed refs).
#[test]
fn trust_addrmode_offset_edges_production_eq_jit() {
    // Offset edge values crossing every encodable boundary:
    //   imm12 scaled (4095*sz), signed-9 pre/post (-256..255), STP imm7 (63*8).
    let offsets: Vec<i64> = vec![
        i64::MIN,
        -32768,
        -520,
        -512,
        -257,
        -256,
        -255,
        -128,
        -9,
        -8,
        -7,
        -1,
        0,
        1,
        2,
        3,
        4,
        7,
        8,
        9,
        15,
        16,
        63,
        64,
        255,
        256,
        257,
        504,
        505,
        512,
        4088,
        4095,
        4096,
        8190,
        8192,
        16380,
        16384,
        32760,
        32768,
        1i64 << 40,
        i64::MAX,
    ];
    // valid access sizes 1/2/4/8 + invalid 0/3/5/16.
    let access_sizes: [u32; 8] = [0, 1, 2, 3, 4, 5, 8, 16];
    let mut inputs: Vec<(i64, u32)> = Vec::new();
    for &o in &offsets {
        for &a in &access_sizes {
            inputs.push((o, a));
        }
    }
    let expected = inputs.len();
    let inp = inputs.clone();
    let rows = run_watchdogged::<(i64, u32, [u32; 10])>("addrmode_offset", expected, move |tx| {
        let buffer = jit_module(ADDRMODE_OFFSET_IR, "addrmode_offset");
        // SAFETY: machine code for functy.0 = (i64, u32, ptr) -> ().
        let f: unsafe extern "C" fn(i64, u32, *mut OffsetPropsC) =
            unsafe { std::mem::transmute(bind(&buffer, "offset_props_root")) };
        for &(o, a) in &inp {
            let mut out = OffsetPropsC::poisoned();
            unsafe { f(o, a, &mut out) };
            if tx.send((o, a, out.as_row())).is_err() {
                return;
            }
        }
    });
    for &(o, a, row) in &rows {
        let expect = native_offset_row(o, a);
        assert_eq!(
            row, expect,
            "offset({o},sz={a}): JIT {row:?} != production {expect:?}"
        );
    }
    // Locate a specific (offset, access_size) row.
    let find = |o: i64, a: u32| rows.iter().find(|q| q.0 == o && q.1 == a).unwrap().2;
    // Field indices (mirror OffsetPropsC order): 0=enc1 1=enc2 2=enc4 3=enc8
    // 4=enc_as 5=pre_post 6=store_pair 7=generic64 8=fold_g64 9=fold_scaled_as.

    // imm12 scaled boundary for size 1: max encodable offset is 4095.
    assert_eq!(find(4095, 1)[0], 1, "offset 4095 encodable at size 1");
    assert_eq!(find(4096, 1)[0], 0, "offset 4096 NOT encodable at size 1");
    // size 2 must be aligned: 4095 (odd) not encodable, 8190 (=4095*2) is.
    assert_eq!(
        find(4095, 1)[1],
        0,
        "offset 4095 not encodable at size 2 (misaligned)"
    );
    assert_eq!(find(8190, 1)[1], 1, "offset 8190 encodable at size 2");
    assert_eq!(
        find(8192, 1)[1],
        0,
        "offset 8192 (=4096*2) NOT encodable at size 2"
    );
    // size 8 alignment.
    assert_eq!(find(7, 1)[3], 0, "offset 7 not size-8 aligned");
    assert_eq!(find(8, 1)[3], 1, "offset 8 encodable at size 8");
    // negatives never scaled-encodable.
    assert_eq!(find(-8, 1)[3], 0, "negative offset never scaled-encodable");

    // arbitrary access_size arg: enc_as tracks the swept size.
    assert_eq!(find(4095, 2)[4], 0, "enc_as at size 2 sees 4095 misaligned");
    assert_eq!(find(8190, 2)[4], 1, "enc_as at size 2 sees 8190 encodable");
    assert_eq!(
        find(8, 3)[4],
        0,
        "access_size 3 is invalid -> not encodable"
    );
    assert_eq!(
        find(8, 0)[4],
        0,
        "access_size 0 is invalid -> not encodable"
    );
    assert_eq!(
        find(8, 16)[4],
        0,
        "access_size 16 is invalid -> not encodable"
    );

    // pre/post signed-9 range -256..=255.
    assert_eq!(find(255, 1)[5], 1, "255 fits pre/post");
    assert_eq!(find(256, 1)[5], 0, "256 does NOT fit pre/post");
    assert_eq!(find(-256, 1)[5], 1, "-256 fits pre/post");
    assert_eq!(find(-257, 1)[5], 0, "-257 does NOT fit pre/post");
    assert_eq!(find(0, 1)[5], 1, "0 fits pre/post");

    // STP scaled signed imm7: off%8==0 and off/8 in -64..=63.
    assert_eq!(find(504, 1)[6], 1, "504 (=63*8) fits store-pair");
    assert_eq!(find(505, 1)[6], 0, "505 not 8-aligned -> no store-pair");
    assert_eq!(find(512, 1)[6], 0, "512 (=64*8) out of imm7 range");
    assert_eq!(find(-512, 1)[6], 1, "-512 (=-64*8) fits store-pair");
    assert_eq!(find(-520, 1)[6], 0, "-520 (=-65*8) out of imm7 range");

    // generic64 = size-8-scaled OR pre/post: a negative in [-256,255] is
    // generic64-encodable via pre/post even though not scaled-encodable.
    assert_eq!(find(-8, 1)[7], 1, "-8 generic64-encodable via pre/post");
    assert_eq!(find(-257, 1)[7], 0, "-257 not generic64-encodable");
    assert_eq!(find(255, 1)[7], 1, "255 generic64-encodable via pre/post");
    assert_eq!(find(8, 1)[7], 1, "8 generic64-encodable via scaled");
    // foldable(Generic64) == generic64, foldable(Scaled(asz)) == enc_as.
    assert_eq!(
        find(-8, 1)[8],
        find(-8, 1)[7],
        "foldable(Generic64) == generic64"
    );
    assert_eq!(
        find(8190, 2)[9],
        find(8190, 2)[4],
        "foldable(Scaled(2)) == enc_as(size 2)"
    );

    // NEGATIVE CONTROL (armed): an is_encodable_offset that DROPS the
    // alignment check (a plausible bug) would call 4095 encodable at size 2.
    let blind_scaled = |off: i64, sz: i64| (off >= 0 && off / sz <= 4095) as u32;
    assert_ne!(
        blind_scaled(4095, 2),
        find(4095, 2)[1],
        "negative control must FAIL: alignment-blind scaled offset"
    );
    assert_eq!(
        blind_scaled(4095, 2),
        1,
        "the blind (buggy) oracle wrongly calls 4095 encodable at size 2"
    );

    // NEGATIVE CONTROL: a pre/post oracle that forgets the negative side.
    let blind_prepost = |off: i64| (0..=255).contains(&off) as u32;
    assert_ne!(
        blind_prepost(-256),
        find(-256, 1)[5],
        "negative control must FAIL: unsigned pre/post bound"
    );
}

/// ARMED CONTROL A (corrupt -> loud failure -> restore byte-identical ->
/// re-pass): patch the UNIQUE `const i64 4095` in the embedded addrmode module
/// (the imm12 scaled-offset limit inside `is_encodable_offset`) down to 4094,
/// JIT the corrupted text, and prove the differential CATCHES the shifted
/// boundary at EXACTLY the max-encodable offsets while the pristine module
/// re-passes.
#[test]
fn trust_addrmode_armed_control_corrupted_imm12_limit_caught_then_restored() {
    let anchor = "%51 = const i64 4095\n";
    assert_eq!(
        ADDRMODE_OFFSET_IR.matches(anchor).count(),
        1,
        "armed-control anchor must be unique in the fixture"
    );
    let corrupted = ADDRMODE_OFFSET_IR.replace(anchor, "%51 = const i64 4094\n");
    assert_ne!(corrupted, ADDRMODE_OFFSET_IR);

    // Probe offsets that straddle the 4095/4094 boundary at each valid size.
    let probes: Vec<(i64, u32)> = vec![
        (4095, 1),  // was encodable, corruption flips it to NOT encodable
        (4094, 1),  // still encodable under both
        (8190, 2),  // 8190/2 = 4095: flips
        (16380, 4), // 16380/4 = 4095: flips
        (32760, 8), // 32760/8 = 4095: flips
        (0, 1),     // unaffected
    ];
    let expected = probes.len();
    let inp = probes.clone();
    let rows =
        run_watchdogged::<(i64, u32, [u32; 10])>("addrmode CORRUPTED", expected, move |tx| {
            let buffer = jit_module(&corrupted, "addrmode CORRUPTED");
            let f: unsafe extern "C" fn(i64, u32, *mut OffsetPropsC) =
                unsafe { std::mem::transmute(bind(&buffer, "offset_props_root")) };
            for &(o, a) in &inp {
                let mut out = OffsetPropsC::poisoned();
                unsafe { f(o, a, &mut out) };
                if tx.send((o, a, out.as_row())).is_err() {
                    return;
                }
            }
        });
    let field =
        |o: i64, a: u32, idx: usize| rows.iter().find(|q| q.0 == o && q.1 == a).unwrap().2[idx];
    // The corrupted limit rejects the previously-max-encodable offsets.
    assert_eq!(
        field(4095, 1, 0),
        0,
        "ARMED: corrupted limit rejects 4095 at size 1"
    );
    assert_eq!(
        prod_is_encodable_offset(4095, 1) as u32,
        1,
        "production ACCEPTS 4095 at size 1 — the divergence is LOUD"
    );
    assert_eq!(
        field(8190, 2, 1),
        0,
        "ARMED: corrupted limit rejects 8190 at size 2"
    );
    assert_eq!(
        prod_is_encodable_offset(8190, 2) as u32,
        1,
        "production accepts 8190 at size 2"
    );
    assert_eq!(
        field(16380, 4, 2),
        0,
        "ARMED: corrupted rejects 16380 at size 4"
    );
    assert_eq!(
        field(32760, 8, 3),
        0,
        "ARMED: corrupted rejects 32760 at size 8"
    );
    // 4094 and 0 are unaffected — the corruption is a ONE-step boundary shift.
    assert_eq!(
        field(4094, 1, 0),
        1,
        "ARMED: 4094 still encodable (limit is now 4094)"
    );
    assert_eq!(field(0, 1, 0), 1, "ARMED: 0 unaffected");

    // Restore: the pristine const (byte-identical embedded text) re-passes.
    let inp2 = probes.clone();
    let rows2 =
        run_watchdogged::<(i64, u32, [u32; 10])>("addrmode RESTORED", expected, move |tx| {
            let buffer = jit_module(ADDRMODE_OFFSET_IR, "addrmode RESTORED");
            let f: unsafe extern "C" fn(i64, u32, *mut OffsetPropsC) =
                unsafe { std::mem::transmute(bind(&buffer, "offset_props_root")) };
            for &(o, a) in &inp2 {
                let mut out = OffsetPropsC::poisoned();
                unsafe { f(o, a, &mut out) };
                if tx.send((o, a, out.as_row())).is_err() {
                    return;
                }
            }
        });
    for &(o, a, row) in &rows2 {
        assert_eq!(
            row,
            native_offset_row(o, a),
            "RESTORED module must re-pass at ({o},sz={a})"
        );
    }
}

/// ARMED CONTROL B (opcode-category module): patch the UNIQUE
/// `switch %4 [ 26: bb2 default: bb1 ]` in `category_reads_flags` (the
/// CondBranch=26 discriminant) to 25 (Branch), JIT the corrupted text, and
/// prove `category_reads_flags` MISFIRES on Branch instead of CondBranch —
/// a flag-reading classifier that would license reordering across a flags def.
#[test]
fn trust_opcode_category_armed_control_corrupted_reads_flags_caught_then_restored() {
    let anchor = "switch %4 [ 26: bb2 default: bb1 ]\n";
    assert_eq!(
        OPCODE_CATEGORY_IR.matches(anchor).count(),
        1,
        "armed-control anchor must be unique in the fixture"
    );
    let corrupted = OPCODE_CATEGORY_IR.replace(anchor, "switch %4 [ 25: bb2 default: bb1 ]\n");
    assert_ne!(corrupted, OPCODE_CATEGORY_IR);

    // Sweep every category; collect just the reads_flags field (idx 13).
    let expected = CAT_COUNT as usize;
    let rows = run_watchdogged::<(u32, u32)>("opcode_category CORRUPTED", expected, move |tx| {
        let buffer = jit_module(&corrupted, "opcode_category CORRUPTED");
        let f: unsafe extern "C" fn(u32, *mut CatPropsC) =
            unsafe { std::mem::transmute(bind(&buffer, "cat_props_root")) };
        for tag in 0..CAT_COUNT {
            let mut out = CatPropsC::poisoned();
            unsafe { f(tag, &mut out) };
            if tx.send((tag, out.as_row()[13])).is_err() {
                return;
            }
        }
    });
    let rdf = |t: u32| rows.iter().find(|q| q.0 == t).unwrap().1;
    // Corruption: reads_flags now true for Branch (25), false for CondBranch (26).
    assert_eq!(
        rdf(25),
        1,
        "ARMED: corrupted reads_flags misfires on Branch(25)"
    );
    assert_eq!(
        rdf(26),
        0,
        "ARMED: corrupted reads_flags no longer fires on CondBranch(26)"
    );
    assert_eq!(
        prod_reads_flags(prod_cat_from_tag(26)) as u32,
        1,
        "production: CondBranch DOES read flags — the divergence is LOUD"
    );
    assert_eq!(
        prod_reads_flags(prod_cat_from_tag(25)) as u32,
        0,
        "production: Branch does NOT read flags"
    );
    // Only the two swapped tags diverge from production.
    let diverged: Vec<u32> = (0..CAT_COUNT)
        .filter(|&t| rdf(t) != prod_reads_flags(prod_cat_from_tag(t)) as u32)
        .collect();
    assert_eq!(
        diverged,
        vec![25, 26],
        "ARMED: exactly {{Branch, CondBranch}} diverge"
    );

    // Restore: pristine re-pass on the reads_flags field.
    let rows2 = run_watchdogged::<(u32, u32)>("opcode_category RESTORED", expected, move |tx| {
        let buffer = jit_module(OPCODE_CATEGORY_IR, "opcode_category RESTORED");
        let f: unsafe extern "C" fn(u32, *mut CatPropsC) =
            unsafe { std::mem::transmute(bind(&buffer, "cat_props_root")) };
        for tag in 0..CAT_COUNT {
            let mut out = CatPropsC::poisoned();
            unsafe { f(tag, &mut out) };
            if tx.send((tag, out.as_row()[13])).is_err() {
                return;
            }
        }
    });
    for &(t, v) in &rows2 {
        assert_eq!(
            v,
            prod_reads_flags(prod_cat_from_tag(t)) as u32,
            "RESTORED reads_flags must re-pass at tag {t}"
        );
    }
}

// ── embedded fixtures (VERBATIM MIR-closure emits; regen per header) ──────────

/// VERBATIM MIR-closure emit of `cat_props_root`. OpcodeCategory predicate
/// layer (trust-cg-ir target_info + trust-cg-opt effects); slice
/// trust_opcode_category_slice.rs. 13631 bytes; 17 members; validate 0;
/// re-parse OK; EXTERN-FREE.
const OPCODE_CATEGORY_IR: &str = r#"; TrustIr text format v1
module "mir::closure::cat_props_root"
target "aarch64-apple-darwin" 8 little
file 0 "trust_opcode_category_slice.rs"

functy.0 = (u32, ptr) -> ()

functy.1 = (ptr, u32) -> ()

functy.2 = (ptr, u8) -> ()

functy.3 = (u8) -> (bool)

functy.4 = (u8) -> (bool)

functy.5 = (u8) -> (bool)

functy.6 = (u8) -> (bool)

functy.7 = (u8) -> (bool)

functy.8 = (u8) -> (bool)

functy.9 = (u8) -> (u32)

functy.10 = (u8) -> (bool)

functy.11 = (u8) -> (bool)

functy.12 = (u8) -> (bool)

functy.13 = (u8) -> (bool)

functy.14 = (u8, bool) -> (bool)

functy.15 = (u8) -> (bool)

functy.16 = (u8) -> (bool)

fn @cat_props_root(functy.0) {
bb0(%0: u32, %1: ptr):
    %34 = alloca i8, align 1
    %35 = alloca i8, align 1
    call @func.1(%34, %0)
    br bb1(%1)
bb1(%2: ptr):
    %36 = load u8, ptr %34
    call @func.2(%35, %36)
    br bb2(%2)
bb2(%3: ptr):
    %37 = load u8, ptr %34
    %38 = call @func.3(%37)
    br bb3(%3, %38)
bb3(%4: ptr, %5: bool):
    %39 = const u32 1
    %40 = const u32 0
    %41 = select u32 %5, %39, %40
    store u32 %41, ptr %4
    %42 = load u8, ptr %34
    %43 = call @func.4(%42)
    br bb4(%4, %43)
bb4(%6: ptr, %7: bool):
    %44 = const u32 1
    %45 = const u32 0
    %46 = select u32 %7, %44, %45
    %47 = const i64 4
    %48 = gep i8, ptr %6, %47
    store u32 %46, ptr %48
    %49 = load u8, ptr %34
    %50 = call @func.5(%49)
    br bb5(%6, %50)
bb5(%8: ptr, %9: bool):
    %51 = const u32 1
    %52 = const u32 0
    %53 = select u32 %9, %51, %52
    %54 = const i64 8
    %55 = gep i8, ptr %8, %54
    store u32 %53, ptr %55
    %56 = load u8, ptr %34
    %57 = call @func.6(%56)
    br bb6(%8, %57)
bb6(%10: ptr, %11: bool):
    %58 = const u32 1
    %59 = const u32 0
    %60 = select u32 %11, %58, %59
    %61 = const i64 12
    %62 = gep i8, ptr %10, %61
    store u32 %60, ptr %62
    %63 = load u8, ptr %34
    %64 = call @func.7(%63)
    br bb7(%10, %64)
bb7(%12: ptr, %13: bool):
    %65 = const u32 1
    %66 = const u32 0
    %67 = select u32 %13, %65, %66
    %68 = const i64 16
    %69 = gep i8, ptr %12, %68
    store u32 %67, ptr %69
    %70 = load u8, ptr %34
    %71 = call @func.8(%70)
    br bb8(%12, %71)
bb8(%14: ptr, %15: bool):
    %72 = const u32 1
    %73 = const u32 0
    %74 = select u32 %15, %72, %73
    %75 = const i64 20
    %76 = gep i8, ptr %14, %75
    store u32 %74, ptr %76
    %77 = load u8, ptr %35
    %78 = call @func.9(%77)
    br bb9(%14, %78)
bb9(%16: ptr, %17: u32):
    %79 = const i64 24
    %80 = gep i8, ptr %16, %79
    store u32 %17, ptr %80
    %81 = load u8, ptr %35
    %82 = call @func.10(%81)
    br bb10(%16, %82)
bb10(%18: ptr, %19: bool):
    %83 = const u32 1
    %84 = const u32 0
    %85 = select u32 %19, %83, %84
    %86 = const i64 28
    %87 = gep i8, ptr %18, %86
    store u32 %85, ptr %87
    %88 = load u8, ptr %35
    %89 = call @func.11(%88)
    br bb11(%18, %89)
bb11(%20: ptr, %21: bool):
    %90 = const u32 1
    %91 = const u32 0
    %92 = select u32 %21, %90, %91
    %93 = const i64 32
    %94 = gep i8, ptr %20, %93
    store u32 %92, ptr %94
    %95 = load u8, ptr %35
    %96 = call @func.12(%95)
    br bb12(%20, %96)
bb12(%22: ptr, %23: bool):
    %97 = const u32 1
    %98 = const u32 0
    %99 = select u32 %23, %97, %98
    %100 = const i64 36
    %101 = gep i8, ptr %22, %100
    store u32 %99, ptr %101
    %102 = load u8, ptr %35
    %103 = call @func.13(%102)
    br bb13(%22, %103)
bb13(%24: ptr, %25: bool):
    %104 = const u32 1
    %105 = const u32 0
    %106 = select u32 %25, %104, %105
    %107 = const i64 40
    %108 = gep i8, ptr %24, %107
    store u32 %106, ptr %108
    %109 = load u8, ptr %34
    %110 = const bool false
    %111 = call @func.14(%109, %110)
    br bb14(%24, %111)
bb14(%26: ptr, %27: bool):
    %112 = const u32 1
    %113 = const u32 0
    %114 = select u32 %27, %112, %113
    %115 = const i64 44
    %116 = gep i8, ptr %26, %115
    store u32 %114, ptr %116
    %117 = load u8, ptr %34
    %118 = const bool true
    %119 = call @func.14(%117, %118)
    br bb15(%26, %119)
bb15(%28: ptr, %29: bool):
    %120 = const u32 1
    %121 = const u32 0
    %122 = select u32 %29, %120, %121
    %123 = const i64 48
    %124 = gep i8, ptr %28, %123
    store u32 %122, ptr %124
    %125 = load u8, ptr %34
    %126 = call @func.15(%125)
    br bb16(%28, %126)
bb16(%30: ptr, %31: bool):
    %127 = const u32 1
    %128 = const u32 0
    %129 = select u32 %31, %127, %128
    %130 = const i64 52
    %131 = gep i8, ptr %30, %130
    store u32 %129, ptr %131
    %132 = load u8, ptr %34
    %133 = call @func.16(%132)
    br bb17(%30, %133)
bb17(%32: ptr, %33: bool):
    %134 = const u32 1
    %135 = const u32 0
    %136 = select u32 %33, %134, %135
    %137 = const i64 56
    %138 = gep i8, ptr %32, %137
    store u32 %136, ptr %138
    ret
}

fn @cat_from_tag(functy.1) {
bb0(%0: ptr, %1: u32):
    switch %1 [ 0: bb31 1: bb30 2: bb29 3: bb28 4: bb27 5: bb26 6: bb25 7: bb24 8: bb23 9: bb22 10: bb21 11: bb20 12: bb19 13: bb18 14: bb17 15: bb16 16: bb15 17: bb14 18: bb13 19: bb12 20: bb11 21: bb10 22: bb9 23: bb8 24: bb7 25: bb6 26: bb5 27: bb4 28: bb3 29: bb2 default: bb1 ]
bb1:
    %2 = const i8 30
    store i8 %2, ptr %0
    br bb32
bb2:
    %3 = const i8 29
    store i8 %3, ptr %0
    br bb32
bb3:
    %4 = const i8 28
    store i8 %4, ptr %0
    br bb32
bb4:
    %5 = const i8 27
    store i8 %5, ptr %0
    br bb32
bb5:
    %6 = const i8 26
    store i8 %6, ptr %0
    br bb32
bb6:
    %7 = const i8 25
    store i8 %7, ptr %0
    br bb32
bb7:
    %8 = const i8 24
    store i8 %8, ptr %0
    br bb32
bb8:
    %9 = const i8 23
    store i8 %9, ptr %0
    br bb32
bb9:
    %10 = const i8 22
    store i8 %10, ptr %0
    br bb32
bb10:
    %11 = const i8 21
    store i8 %11, ptr %0
    br bb32
bb11:
    %12 = const i8 20
    store i8 %12, ptr %0
    br bb32
bb12:
    %13 = const i8 19
    store i8 %13, ptr %0
    br bb32
bb13:
    %14 = const i8 18
    store i8 %14, ptr %0
    br bb32
bb14:
    %15 = const i8 17
    store i8 %15, ptr %0
    br bb32
bb15:
    %16 = const i8 16
    store i8 %16, ptr %0
    br bb32
bb16:
    %17 = const i8 15
    store i8 %17, ptr %0
    br bb32
bb17:
    %18 = const i8 14
    store i8 %18, ptr %0
    br bb32
bb18:
    %19 = const i8 13
    store i8 %19, ptr %0
    br bb32
bb19:
    %20 = const i8 12
    store i8 %20, ptr %0
    br bb32
bb20:
    %21 = const i8 11
    store i8 %21, ptr %0
    br bb32
bb21:
    %22 = const i8 10
    store i8 %22, ptr %0
    br bb32
bb22:
    %23 = const i8 9
    store i8 %23, ptr %0
    br bb32
bb23:
    %24 = const i8 8
    store i8 %24, ptr %0
    br bb32
bb24:
    %25 = const i8 7
    store i8 %25, ptr %0
    br bb32
bb25:
    %26 = const i8 6
    store i8 %26, ptr %0
    br bb32
bb26:
    %27 = const i8 5
    store i8 %27, ptr %0
    br bb32
bb27:
    %28 = const i8 4
    store i8 %28, ptr %0
    br bb32
bb28:
    %29 = const i8 3
    store i8 %29, ptr %0
    br bb32
bb29:
    %30 = const i8 2
    store i8 %30, ptr %0
    br bb32
bb30:
    %31 = const i8 1
    store i8 %31, ptr %0
    br bb32
bb31:
    %32 = const i8 0
    store i8 %32, ptr %0
    br bb32
bb32:
    ret
}

fn @category_memory_effect(functy.2) {
bb0(%0: ptr, %1: u8):
    %2 = alloca i8, align 1
    store u8 %1, ptr %2
    %3 = load i8, ptr %2
    %4 = sext i8 %3 to i64
    switch %4 [ 0: bb2 1: bb2 2: bb2 3: bb2 4: bb2 5: bb2 6: bb2 7: bb2 8: bb2 9: bb2 10: bb2 11: bb2 12: bb2 13: bb2 14: bb2 15: bb2 16: bb2 17: bb2 18: bb2 19: bb2 20: bb2 21: bb2 22: bb2 23: bb2 24: bb3 25: bb2 26: bb2 27: bb5 28: bb4 29: bb2 30: bb2 default: bb1 ]
bb1:
    unreachable
bb2:
    %5 = const i8 0
    store i8 %5, ptr %0
    br bb6
bb3:
    %6 = const i8 3
    store i8 %6, ptr %0
    br bb6
bb4:
    %7 = const i8 2
    store i8 %7, ptr %0
    br bb6
bb5:
    %8 = const i8 1
    store i8 %8, ptr %0
    br bb6
bb6:
    ret
}

fn @OpcodeCategory__is_arithmetic(functy.3) {
bb0(%0: u8):
    %2 = alloca i8, align 1
    store u8 %0, ptr %2
    %3 = load i8, ptr %2
    %4 = sext i8 %3 to i64
    switch %4 [ 0: bb2 1: bb2 2: bb2 3: bb2 4: bb2 5: bb2 default: bb1 ]
bb1:
    %5 = const bool false
    br bb3(%5)
bb2:
    %6 = const bool true
    br bb3(%6)
bb3(%1: bool):
    ret %1
}

fn @OpcodeCategory__is_logical(functy.4) {
bb0(%0: u8):
    %2 = alloca i8, align 1
    store u8 %0, ptr %2
    %3 = load i8, ptr %2
    %4 = sext i8 %3 to i64
    switch %4 [ 6: bb2 7: bb2 8: bb2 9: bb2 10: bb2 11: bb2 default: bb1 ]
bb1:
    %5 = const bool false
    br bb3(%5)
bb2:
    %6 = const bool true
    br bb3(%6)
bb3(%1: bool):
    ret %1
}

fn @OpcodeCategory__is_shift(functy.5) {
bb0(%0: u8):
    %2 = alloca i8, align 1
    store u8 %0, ptr %2
    %3 = load i8, ptr %2
    %4 = sext i8 %3 to i64
    switch %4 [ 12: bb2 13: bb2 14: bb2 15: bb2 16: bb2 17: bb2 default: bb1 ]
bb1:
    %5 = const bool false
    br bb3(%5)
bb2:
    %6 = const bool true
    br bb3(%6)
bb3(%1: bool):
    ret %1
}

fn @OpcodeCategory__is_move(functy.6) {
bb0(%0: u8):
    %2 = alloca i8, align 1
    store u8 %0, ptr %2
    %3 = load i8, ptr %2
    %4 = sext i8 %3 to i64
    switch %4 [ 18: bb2 19: bb2 default: bb1 ]
bb1:
    %5 = const bool false
    br bb3(%5)
bb2:
    %6 = const bool true
    br bb3(%6)
bb3(%1: bool):
    ret %1
}

fn @OpcodeCategory__is_reg_imm(functy.7) {
bb0(%0: u8):
    %2 = alloca i8, align 1
    store u8 %0, ptr %2
    %3 = load i8, ptr %2
    %4 = sext i8 %3 to i64
    switch %4 [ 1: bb2 3: bb2 7: bb2 9: bb2 11: bb2 13: bb2 15: bb2 17: bb2 19: bb2 21: bb2 default: bb1 ]
bb1:
    %5 = const bool false
    br bb3(%5)
bb2:
    %6 = const bool true
    br bb3(%6)
bb3(%1: bool):
    ret %1
}

fn @OpcodeCategory__is_reg_reg_binary(functy.8) {
bb0(%0: u8):
    %2 = alloca i8, align 1
    store u8 %0, ptr %2
    %3 = load i8, ptr %2
    %4 = sext i8 %3 to i64
    switch %4 [ 0: bb2 2: bb2 4: bb2 6: bb2 8: bb2 10: bb2 12: bb2 14: bb2 16: bb2 default: bb1 ]
bb1:
    %5 = const bool false
    br bb3(%5)
bb2:
    %6 = const bool true
    br bb3(%6)
bb3(%1: bool):
    ret %1
}

fn @mem_effect_tag(functy.9) {
bb0(%0: u8):
    %2 = alloca i8, align 1
    store u8 %0, ptr %2
    %3 = load i8, ptr %2
    %4 = sext i8 %3 to i64
    switch %4 [ 0: bb5 1: bb4 2: bb3 3: bb2 default: bb1 ]
bb1:
    unreachable
bb2:
    %5 = const u32 3
    br bb6(%5)
bb3:
    %6 = const u32 2
    br bb6(%6)
bb4:
    %7 = const u32 1
    br bb6(%7)
bb5:
    %8 = const u32 0
    br bb6(%8)
bb6(%1: u32):
    ret %1
}

fn @MemoryEffect__is_pure(functy.10) {
bb0(%0: u8):
    %2 = alloca i8, align 1
    store u8 %0, ptr %2
    %3 = load i8, ptr %2
    %4 = sext i8 %3 to i64
    switch %4 [ 0: bb2 default: bb1 ]
bb1:
    %5 = const bool false
    br bb3(%5)
bb2:
    %6 = const bool true
    br bb3(%6)
bb3(%1: bool):
    ret %1
}

fn @MemoryEffect__reads_memory(functy.11) {
bb0(%0: u8):
    %2 = alloca i8, align 1
    store u8 %0, ptr %2
    %3 = load i8, ptr %2
    %4 = sext i8 %3 to i64
    switch %4 [ 1: bb2 3: bb2 default: bb1 ]
bb1:
    %5 = const bool false
    br bb3(%5)
bb2:
    %6 = const bool true
    br bb3(%6)
bb3(%1: bool):
    ret %1
}

fn @MemoryEffect__writes_memory(functy.12) {
bb0(%0: u8):
    %2 = alloca i8, align 1
    store u8 %0, ptr %2
    %3 = load i8, ptr %2
    %4 = sext i8 %3 to i64
    switch %4 [ 2: bb2 3: bb2 default: bb1 ]
bb1:
    %5 = const bool false
    br bb3(%5)
bb2:
    %6 = const bool true
    br bb3(%6)
bb3(%1: bool):
    ret %1
}

fn @MemoryEffect__is_barrier(functy.13) {
bb0(%0: u8):
    %2 = alloca i8, align 1
    store u8 %0, ptr %2
    %3 = load i8, ptr %2
    %4 = sext i8 %3 to i64
    switch %4 [ 3: bb2 default: bb1 ]
bb1:
    %5 = const bool false
    br bb3(%5)
bb2:
    %6 = const bool true
    br bb3(%6)
bb3(%1: bool):
    ret %1
}

fn @category_is_removable(functy.14) {
bb0(%0: u8, %1: bool):
    %13 = alloca i8, align 1
    %14 = alloca i8, align 1
    store u8 %0, ptr %13
    %15 = load u8, ptr %13
    call @func.2(%14, %15)
    br bb1(%1)
bb1(%2: bool):
    %16 = load u8, ptr %14
    %17 = call @func.10(%16)
    br bb2(%2, %17)
bb2(%3: bool, %4: bool):
    condbr %4, bb3(%3), bb4
bb3(%5: bool):
    %18 = load i8, ptr %13
    %19 = sext i8 %18 to i64
    switch %19 [ 20: bb6(%5) 21: bb6(%5) default: bb5(%5) ]
bb4:
    %20 = const bool false
    br bb17(%20)
bb5(%6: bool):
    %21 = const bool false
    br bb7(%6, %21)
bb6(%7: bool):
    %22 = const bool true
    br bb7(%7, %22)
bb7(%8: bool, %9: bool):
    condbr %9, bb8, bb9(%8)
bb8:
    %23 = const bool false
    br bb17(%23)
bb9(%10: bool):
    condbr %10, bb10, bb11
bb10:
    %24 = const bool false
    br bb17(%24)
bb11:
    %25 = load i8, ptr %13
    %26 = sext i8 %25 to i64
    switch %26 [ 23: bb13 24: bb13 25: bb13 26: bb13 default: bb12 ]
bb12:
    %27 = const bool false
    br bb14(%27)
bb13:
    %28 = const bool true
    br bb14(%28)
bb14(%11: bool):
    condbr %11, bb15, bb16
bb15:
    %29 = const bool false
    br bb17(%29)
bb16:
    %30 = const bool true
    br bb17(%30)
bb17(%12: bool):
    ret %12
}

fn @category_reads_flags(functy.15) {
bb0(%0: u8):
    %2 = alloca i8, align 1
    store u8 %0, ptr %2
    %3 = load i8, ptr %2
    %4 = sext i8 %3 to i64
    switch %4 [ 26: bb2 default: bb1 ]
bb1:
    %5 = const bool false
    br bb3(%5)
bb2:
    %6 = const bool true
    br bb3(%6)
bb3(%1: bool):
    ret %1
}

fn @category_writes_flags(functy.16) {
bb0(%0: u8):
    %2 = alloca i8, align 1
    store u8 %0, ptr %2
    %3 = load i8, ptr %2
    %4 = sext i8 %3 to i64
    switch %4 [ 20: bb2 21: bb2 default: bb1 ]
bb1:
    %5 = const bool false
    br bb3(%5)
bb2:
    %6 = const bool true
    br bb3(%6)
bb3(%1: bool):
    ret %1
}
"#;

/// VERBATIM MIR-closure emit of `offset_props_root`. Addressing-mode offset
/// legality deciders (trust-cg-opt addr_mode); slice
/// trust_addrmode_offset_slice.rs. 7617 bytes; 6 members; validate 0;
/// re-parse OK; EXTERN-FREE.
const ADDRMODE_OFFSET_IR: &str = r#"; TrustIr text format v1
module "mir::closure::offset_props_root"
target "aarch64-apple-darwin" 8 little
file 0 "trust_addrmode_offset_slice.rs"

functy.0 = (i64, u32, ptr) -> ()

functy.1 = (i64, u8) -> (bool)

functy.2 = (i64) -> (bool)

functy.3 = (i64) -> (bool)

functy.4 = (i64) -> (bool)

functy.5 = (i64, ptr) -> (bool)

fn @offset_props_root(functy.0) {
bb0(%0: i64, %1: u32, %2: ptr):
    %41 = alloca (i8, i8), align 1
    %42 = alloca (i8, i8), align 1
    %43 = trunc u32 %1 to u8
    %44 = const u8 1
    %45 = call @func.1(%0, %44)
    br bb1(%0, %2, %43, %45)
bb1(%3: i64, %4: ptr, %5: u8, %6: bool):
    %46 = const u32 1
    %47 = const u32 0
    %48 = select u32 %6, %46, %47
    store u32 %48, ptr %4
    %49 = const u8 2
    %50 = call @func.1(%3, %49)
    br bb2(%3, %4, %5, %50)
bb2(%7: i64, %8: ptr, %9: u8, %10: bool):
    %51 = const u32 1
    %52 = const u32 0
    %53 = select u32 %10, %51, %52
    %54 = const i64 4
    %55 = gep i8, ptr %8, %54
    store u32 %53, ptr %55
    %56 = const u8 4
    %57 = call @func.1(%7, %56)
    br bb3(%7, %8, %9, %57)
bb3(%11: i64, %12: ptr, %13: u8, %14: bool):
    %58 = const u32 1
    %59 = const u32 0
    %60 = select u32 %14, %58, %59
    %61 = const i64 8
    %62 = gep i8, ptr %12, %61
    store u32 %60, ptr %62
    %63 = const u8 8
    %64 = call @func.1(%11, %63)
    br bb4(%11, %12, %13, %64)
bb4(%15: i64, %16: ptr, %17: u8, %18: bool):
    %65 = const u32 1
    %66 = const u32 0
    %67 = select u32 %18, %65, %66
    %68 = const i64 12
    %69 = gep i8, ptr %16, %68
    store u32 %67, ptr %69
    %70 = call @func.1(%15, %17)
    br bb5(%15, %16, %17, %70)
bb5(%19: i64, %20: ptr, %21: u8, %22: bool):
    %71 = const u32 1
    %72 = const u32 0
    %73 = select u32 %22, %71, %72
    %74 = const i64 16
    %75 = gep i8, ptr %20, %74
    store u32 %73, ptr %75
    %76 = call @func.2(%19)
    br bb6(%19, %20, %21, %76)
bb6(%23: i64, %24: ptr, %25: u8, %26: bool):
    %77 = const u32 1
    %78 = const u32 0
    %79 = select u32 %26, %77, %78
    %80 = const i64 20
    %81 = gep i8, ptr %24, %80
    store u32 %79, ptr %81
    %82 = call @func.3(%23)
    br bb7(%23, %24, %25, %82)
bb7(%27: i64, %28: ptr, %29: u8, %30: bool):
    %83 = const u32 1
    %84 = const u32 0
    %85 = select u32 %30, %83, %84
    %86 = const i64 24
    %87 = gep i8, ptr %28, %86
    store u32 %85, ptr %87
    %88 = call @func.4(%27)
    br bb8(%27, %28, %29, %88)
bb8(%31: i64, %32: ptr, %33: u8, %34: bool):
    %89 = const u32 1
    %90 = const u32 0
    %91 = select u32 %34, %89, %90
    %92 = const i64 28
    %93 = gep i8, ptr %32, %92
    store u32 %91, ptr %93
    %94 = const i8 0
    store i8 %94, ptr %41
    %95 = call @func.5(%31, %41)
    br bb9(%31, %32, %33, %95)
bb9(%35: i64, %36: ptr, %37: u8, %38: bool):
    %96 = const u32 1
    %97 = const u32 0
    %98 = select u32 %38, %96, %97
    %99 = const i64 32
    %100 = gep i8, ptr %36, %99
    store u32 %98, ptr %100
    %101 = const i64 1
    %102 = gep i8, ptr %42, %101
    store u8 %37, ptr %102
    %103 = const i8 1
    store i8 %103, ptr %42
    %104 = call @func.5(%35, %42)
    br bb10(%36, %104)
bb10(%39: ptr, %40: bool):
    %105 = const u32 1
    %106 = const u32 0
    %107 = select u32 %40, %105, %106
    %108 = const i64 36
    %109 = gep i8, ptr %39, %108
    store u32 %107, ptr %109
    ret
}

fn @is_encodable_offset(functy.1) {
bb0(%0: i64, %1: u8):
    %17 = const i64 0
    %18 = icmp slt i64 %0, %17
    condbr %18, bb1, bb2(%0, %1)
bb1:
    %19 = const bool false
    br bb11(%19)
bb2(%2: i64, %3: u8):
    switch %3 [ 1: bb4(%2, %3) 2: bb4(%2, %3) 4: bb4(%2, %3) 8: bb4(%2, %3) default: bb3 ]
bb3:
    %20 = const bool false
    br bb11(%20)
bb4(%4: i64, %5: u8):
    %21 = zext u8 %5 to i64
    %22 = const i64 0
    %23 = icmp eq i64 %21, %22
    %24 = const bool false
    %25 = icmp eq bool %23, %24
    condbr %25, bb5(%4, %21), bb12
bb5(%6: i64, %7: i64):
    %26 = const i64 -1
    %27 = icmp eq i64 %7, %26
    %28 = const i64 -9223372036854775808
    %29 = icmp eq i64 %6, %28
    %30 = const bool false
    %31 = select bool %27, %29, %30
    %32 = const bool false
    %33 = icmp eq bool %31, %32
    condbr %33, bb6(%6, %7), bb12
bb6(%8: i64, %9: i64):
    %34 = srem i64 %8, %9
    %35 = const i64 0
    %36 = icmp eq i64 %34, %35
    condbr %36, bb7(%8, %9), bb8
bb7(%10: i64, %11: i64):
    %37 = const i64 0
    %38 = icmp eq i64 %11, %37
    %39 = const bool false
    %40 = icmp eq bool %38, %39
    condbr %40, bb9(%10, %11), bb12
bb8:
    %41 = const bool false
    br bb11(%41)
bb9(%12: i64, %13: i64):
    %42 = const i64 -1
    %43 = icmp eq i64 %13, %42
    %44 = const i64 -9223372036854775808
    %45 = icmp eq i64 %12, %44
    %46 = const bool false
    %47 = select bool %43, %45, %46
    %48 = const bool false
    %49 = icmp eq bool %47, %48
    condbr %49, bb10(%12, %13), bb12
bb10(%14: i64, %15: i64):
    %50 = sdiv i64 %14, %15
    %51 = const i64 4095
    %52 = icmp sle i64 %50, %51
    br bb11(%52)
bb11(%16: bool):
    ret %16
bb12:
    unreachable
}

fn @is_encodable_pre_post_offset(functy.2) {
bb0(%0: i64):
    %3 = const i64 -256
    %4 = icmp sge i64 %0, %3
    condbr %4, bb1(%0), bb2
bb1(%1: i64):
    %5 = const i64 255
    %6 = icmp sle i64 %1, %5
    br bb3(%6)
bb2:
    %7 = const bool false
    br bb3(%7)
bb3(%2: bool):
    ret %2
}

fn @is_encodable_store_pair_offset(functy.3) {
bb0(%0: i64):
    %8 = const i64 8
    %9 = const i64 0
    %10 = icmp eq i64 %8, %9
    %11 = const bool false
    %12 = icmp eq bool %10, %11
    condbr %12, bb1(%0), bb10
bb1(%1: i64):
    %13 = const i64 8
    %14 = const i64 -1
    %15 = icmp eq i64 %13, %14
    %16 = const i64 -9223372036854775808
    %17 = icmp eq i64 %1, %16
    %18 = const bool false
    %19 = select bool %15, %17, %18
    %20 = const bool false
    %21 = icmp eq bool %19, %20
    condbr %21, bb2(%1), bb10
bb2(%2: i64):
    %22 = const i64 8
    %23 = srem i64 %2, %22
    %24 = const i64 0
    %25 = icmp eq i64 %23, %24
    condbr %25, bb3(%2), bb4
bb3(%3: i64):
    %26 = const i64 8
    %27 = const i64 0
    %28 = icmp eq i64 %26, %27
    %29 = const bool false
    %30 = icmp eq bool %28, %29
    condbr %30, bb5(%3), bb10
bb4:
    %31 = const bool false
    br bb9(%31)
bb5(%4: i64):
    %32 = const i64 8
    %33 = const i64 -1
    %34 = icmp eq i64 %32, %33
    %35 = const i64 -9223372036854775808
    %36 = icmp eq i64 %4, %35
    %37 = const bool false
    %38 = select bool %34, %36, %37
    %39 = const bool false
    %40 = icmp eq bool %38, %39
    condbr %40, bb6(%4), bb10
bb6(%5: i64):
    %41 = const i64 8
    %42 = sdiv i64 %5, %41
    %43 = const i64 -64
    %44 = icmp sge i64 %42, %43
    condbr %44, bb7(%42), bb8
bb7(%6: i64):
    %45 = const i64 63
    %46 = icmp sle i64 %6, %45
    br bb9(%46)
bb8:
    %47 = const bool false
    br bb9(%47)
bb9(%7: bool):
    ret %7
bb10:
    unreachable
}

fn @is_encodable_generic64_offset(functy.4) {
bb0(%0: i64):
    %5 = const u8 8
    %6 = call @func.1(%0, %5)
    br bb1(%0, %6)
bb1(%1: i64, %2: bool):
    condbr %2, bb2, bb3(%1)
bb2:
    %7 = const bool true
    br bb4(%7)
bb3(%3: i64):
    %8 = call @func.2(%3)
    br bb4(%8)
bb4(%4: bool):
    ret %4
}

fn @is_foldable_offset(functy.5) {
bb0(%0: i64, %1: ptr):
    %5 = load i8, ptr %1
    %6 = sext i8 %5 to i64
    switch %6 [ 0: bb3(%0) 1: bb2(%0) default: bb1 ]
bb1:
    unreachable
bb2(%2: i64):
    %7 = const i64 1
    %8 = gep i8, ptr %1, %7
    %9 = load u8, ptr %8
    %10 = call @func.1(%2, %9)
    br bb4(%10)
bb3(%3: i64):
    %11 = call @func.4(%3)
    br bb4(%11)
bb4(%4: bool):
    ret %4
}
"#;
