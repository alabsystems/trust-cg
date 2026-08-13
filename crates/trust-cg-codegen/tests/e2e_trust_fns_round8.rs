//! TRUST-SELF ROUND 21 (thread R21, TRUST BATCH 8): verifying trust-cg's
//! x86-64 OPCODE CLASSIFIER layer and the AArch64 STRENGTH-REDUCTION /
//! ALGEBRAIC-SIMPLIFICATION legality gates — the pure scalar/enum predicates
//! that decide WHEN a machine-level transformation is legal/sound — through the
//! full pipeline Rust -> MIR -> trust-ir (stage1 `trust_ir_mir
//! --mir-emit-closure`) -> trust-cg JIT -> machine code, asserting native Rust
//! == JIT over swept real inputs.
//!
//! WHY THIS IS NEW: R20 (batch 7) verified the target-INDEPENDENT OpcodeCategory
//! classifiers; this round adds the per-ISA x86-64 LEAF classifiers (the x86
//! COMPANION R20 explicitly scoped out) PLUS the strength-reduce / algebraic
//! gates named by the R20 next_steps.
//!
//! New verified functions in this file — 8 across THREE crates, 2 areas:
//!   * trust-cg-opt (effects.rs) — the x86-64 opcode classifiers, EXHAUSTIVE
//!     over all 193 X86Opcode variants, DUAL-ORACLE (linked production):
//!     `x86_opcode_effect`, `x86_is_removable`, `x86_writes_flags`,
//!     `x86_reads_flags`, `x86_produces_value`                        (5)
//!   * trust-cg-opt (cmp_branch_fusion.rs) — `is_power_of_two` (u64)      (1)
//!   * trust-cg-opt (rewrite/patterns.rs)  — `shift_amount_in_width`      (1)
//!   * trust-cg-opt (x86_const_fold.rs)    — `shift_amount`               (1)
//!
//! The five x86 classifiers are `pub` and LINKED into this test binary as the
//! SECOND oracle (dual-oracle). The three strength-reduce gates are PRIVATE in
//! production (verbatim transcription + an independent naive semantic reference,
//! the R16 `require_disp32` / R20 `store_pair` discipline).
//!
//! Slices (pinned round-21 transcriptions; boundaries documented inline there):
//!   tests/slices/trust_x86_opcode_class_slice.rs   (trust-cg-ir + -opt @ b2c58eb)
//!   tests/slices/trust_strength_reduce_slice.rs    (trust-cg-opt @ b2c58eb)
//!   tests/slices/trust_const_materialize_slice.rs  (historical F4 fixture;
//!                                                    not current const-mat coverage)
//!
//! REGEN (per root; trust-ir frontend @ HEAD):
//!   S=$HOME/trust/build/aarch64-apple-darwin/stage1
//!   cd $HOME/trust-ir/frontend && env -u RUSTUP_TOOLCHAIN RUSTC=$S/bin/rustc \
//!     DYLD_LIBRARY_PATH=$S/lib/rustlib/aarch64-apple-darwin/lib \
//!     $S/bin/cargo run --bin trust_ir_mir -- <slice.rs> \
//!     --crate-type=lib -C overflow-checks=off -C debug-assertions=off \
//!     --mir-emit-closure <root> <out.tir>
//!   x86_class_props_root: 26320 bytes, 12 members, validate 0, re-parse OK, EXTERN-FREE
//!   sr_props_root:         2725 bytes,  4 members, validate 0, re-parse OK, EXTERN-FREE
//!   (F4-pinned, validate 0 but UnresolvedSymbol at JIT link:)
//!   movn_props_root:       4316 bytes,  2 members ; chunks_root: 5685 bytes, 2 members
//!   pow2_props_root:       1576 bytes,  2 members
//!   No-drift whnf gate re-checked green (115661) — no frontend changes.
//!
//! FRONTEND FINDINGS (this round; owner-reported):
//!   [F3] NEW: the MIR frontend normalizes a shift-amount const to the LHS type
//!        for 64-bit shifts (`zext i32->u64`) but NOT for 32-bit shifts: a
//!        `u32 >> <i32 literal>` (Rust's default shift-amount type) emits
//!        `lshr/shl u32 by i32`, which trust-ir's validator rejects
//!        (BinOpTypeMismatch). 2-line repro: `fn f(x:u32)->u32 { x >> 2 }` fails
//!        (validate=2), `x >> 2u32` validates. Distinct from owner #6/F1
//!        (non-scalar const operands) and F2 (RangeInclusive::contains).
//!   [F4] NEW: `[T;N]::into_iter`, slice `iter_mut`, `Iterator::{enumerate,take,
//!        next}`, and the numeric intrinsics `trailing_zeros` / `wrapping_shl` /
//!        `wrapping_neg` / `f64::to_bits` all lower to EMPTY-BODIED external leaf
//!        symbols (the owner-#6 "Box::new lowers to an empty body" class); the
//!        trust-cg JIT cannot resolve them -> `Jit(UnresolvedSymbol)` at compile.
//!        This BLOCKS `single_movn_materialization` (array `into_iter`),
//!        `move_wide_chunks` (slice `iter_mut`), `is_power_of_two`/`pow2_log2`
//!        (historical peephole fixture; `trailing_zeros`),
//!        `effective_register_immediate`
//!        (`wrapping_shl`), and the fmov encoders (`to_bits`). PINNED fail-loud
//!        below (the pin auto-fires when the frontend host-links these leaves).
//!   [F5] NEW — A MISCOMPILE: a fieldless enum with >128 variants gets an 8-bit
//!        tag, but the default (no-repr) lowering reads it with `sext i8` while
//!        emitting the SwitchInt keys as the UNSIGNED discriminants 0..192 — so
//!        variants 128..192 never match their arm, fall through to the
//!        exhaustive-match `unreachable`, and the JIT machine code `abort()`s at
//!        runtime. Confirmed on the 193-variant X86Opcode. `#[repr(u8)]` forces
//!        the correct UNSIGNED treatment (`bitcast i8->u8`) and is used by the
//!        x86 slice ([B4] there); F5 is the FRONTEND-lowering bug to fix at root.
//!
//! COVERAGE NOTE: gated to aarch64 (the JIT target). Run ONE AT A TIME
//! (`-- --exact <name> --test-threads=1`): the JIT engine is not thread-safe at
//! suite scale (jit-parallel-race-2026-06-29.md). Every JIT execution runs
//! inside a WATCHDOG worker thread.

#![cfg(target_arch = "aarch64")]

use std::collections::HashMap;
use std::sync::mpsc;
use std::time::Duration;

use trust_cg_codegen::Target;
use trust_cg_codegen::compiler::{Compiler, CompilerConfig};

// LINKED PRODUCTION functions (the second oracle) for the x86 classifiers:
use trust_cg_ir::X86Opcode as ProdX86;
use trust_cg_opt::effects::{
    MemoryEffect as ProdEffect, x86_is_removable as prod_x86_removable,
    x86_opcode_effect as prod_x86_effect, x86_produces_value as prod_x86_produces,
    x86_reads_flags as prod_x86_reads, x86_writes_flags as prod_x86_writes,
};

// ── shared harness (round-16/20 pattern) ─────────────────────────────────────

fn jit_module(text: &str, what: &str) -> trust_cg_codegen::jit::ExecutableBuffer {
    let module = trust_ir::parser::parse_module(text)
        .unwrap_or_else(|e| panic!("MIR-emitted `{what}` trust-ir text must parse: {e:?}"));
    let config = CompilerConfig::jit_fast(Target::Aarch64);
    Compiler::new(config)
        .compile_module_to_jit(&module, &HashMap::new())
        .unwrap_or_else(|e| panic!("trust-cg JIT compile of MIR-emitted `{what}` failed: {e:?}"))
        .buffer
}

/// Compile a module expecting a JIT FAILURE (the F4 pins). Returns the Debug
/// string of the error. Panics (auto-fires the pin) if compilation SUCCEEDS —
/// that means the frontend now host-links the empty-bodied leaf and the
/// function should be PROMOTED to full native==JIT verification.
fn jit_compile_err(text: &str, what: &str) -> String {
    let module = trust_ir::parser::parse_module(text)
        .unwrap_or_else(|e| panic!("F4-pin `{what}` trust-ir text must still parse: {e:?}"));
    let config = CompilerConfig::jit_fast(Target::Aarch64);
    match Compiler::new(config).compile_module_to_jit(&module, &HashMap::new()) {
        Ok(_) => panic!(
            "F4-PIN AUTO-FIRE: `{what}` now JIT-COMPILES — the empty-bodied leaf (array-iterator / \
             numeric intrinsic) appears host-linked. Promote this function to full native==JIT \
             verification and retire the pin."
        ),
        Err(e) => format!("{e:?}"),
    }
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

// ── x86 opcode oracle plumbing (mirrored 1:1 from the slice) ──────────────────

const X86_COUNT: u32 = 193;

/// Total reconstruction of the PRODUCTION X86Opcode from its declaration-order
/// tag — mirrors the slice's `x86_from_tag` EXACTLY.
fn prod_x86_from_tag(tag: u32) -> ProdX86 {
    use ProdX86::*;
    match tag {
        0 => AddRR,
        1 => AddRI,
        2 => AddRM,
        3 => SubRR,
        4 => SubRI,
        5 => SubRM,
        6 => ImulRR,
        7 => ImulRRI,
        8 => ImulRM,
        9 => Idiv,
        10 => Div,
        11 => Neg,
        12 => Inc,
        13 => Dec,
        14 => Cdq,
        15 => Cqo,
        16 => AndRR,
        17 => AndRI,
        18 => OrRR,
        19 => OrRI,
        20 => XorRR,
        21 => XorRI,
        22 => Not,
        23 => ShlRR,
        24 => ShlRI,
        25 => ShrRR,
        26 => ShrRI,
        27 => SarRR,
        28 => SarRI,
        29 => MovRR,
        30 => MovRI,
        31 => MovRM8,
        32 => MovRM16,
        33 => MovRM32,
        34 => MovRM,
        35 => MovMR8,
        36 => MovMR16,
        37 => MovMR32,
        38 => MovMR,
        39 => Movzx,
        40 => MovzxW,
        41 => MovsxB,
        42 => MovsxW,
        43 => Movsx,
        44 => Lea,
        45 => LeaSib,
        46 => MovRMSib,
        47 => MovMRSib,
        48 => LeaRip,
        49 => CmpRR,
        50 => CmpRI,
        51 => CmpRI8,
        52 => CmpRM,
        53 => TestRR,
        54 => TestRI,
        55 => TestRM,
        56 => Jmp,
        57 => Jcc,
        58 => Call,
        59 => CallR,
        60 => CallM,
        61 => Ret,
        62 => Addsd,
        63 => Subsd,
        64 => Mulsd,
        65 => Divsd,
        66 => Sqrtsd,
        67 => Andpd,
        68 => MovsdRR,
        69 => MovsdRM,
        70 => MovsdMR,
        71 => Ucomisd,
        72 => MovdquRM,
        73 => MovdquMR,
        74 => Addss,
        75 => Subss,
        76 => Mulss,
        77 => Divss,
        78 => Sqrtss,
        79 => Andps,
        80 => MovssRR,
        81 => MovssRM,
        82 => MovssMR,
        83 => Ucomiss,
        84 => Roundsd,
        85 => Roundss,
        86 => Minsd,
        87 => Maxsd,
        88 => Minss,
        89 => Maxss,
        90 => Cmpsd,
        91 => Cmpss,
        92 => MovssRipRel,
        93 => MovsdRipRel,
        94 => Cmovcc,
        95 => Setcc,
        96 => Cvtsi2sd,
        97 => Cvtsd2si,
        98 => Cvtsi2ss,
        99 => Cvtss2si,
        100 => Cvtsd2ss,
        101 => Cvtss2sd,
        102 => Bsf,
        103 => Bsr,
        104 => Tzcnt,
        105 => Lzcnt,
        106 => Popcnt,
        107 => BtRI,
        108 => Bswap,
        109 => Xchg,
        110 => Cmpxchg,
        111 => Mfence,
        112 => MovdToXmm,
        113 => MovdFromXmm,
        114 => MovqToXmm,
        115 => MovqFromXmm,
        116 => Push,
        117 => Pop,
        118 => Phi,
        119 => StackAlloc,
        120 => Nop,
        121 => NopMulti,
        122 => MovRR32,
        123 => MovRipRel,
        124 => Cmovcc32,
        125 => Mul,
        126 => Ud2,
        127 => Cvttsd2si,
        128 => Cvttss2si,
        129 => AtomicRmwCasLoop,
        130 => AtomicRmwCasLoop8,
        131 => AtomicRmwCasLoop16,
        132 => Pand,
        133 => Pandn,
        134 => Por,
        135 => Pxor,
        136 => Pcmpeqd,
        137 => Pshufd,
        138 => Pmovmskb,
        139 => MovdqaRR,
        140 => Pcmpgtd,
        141 => MovdqaRM,
        142 => MovdqaMR,
        143 => Paddd,
        144 => Psubd,
        145 => Punpckldq,
        146 => Punpcklqdq,
        147 => Paddq,
        148 => Psubq,
        149 => Paddb,
        150 => Paddw,
        151 => Psubb,
        152 => Psubw,
        153 => Pinsrd,
        154 => Pextrd,
        155 => V4I32MaskExtract,
        156 => Pmulld,
        157 => Pcmpeqq,
        158 => Pcmpgtq,
        159 => Ptest,
        160 => Pinsrq,
        161 => Pextrq,
        162 => V2I64MaskExtract,
        163 => Pblendvb,
        164 => V128BoolSelect,
        165 => Pmuludq,
        166 => Pmullw,
        167 => Pcmpeqb,
        168 => Pcmpeqw,
        169 => Pcmpgtb,
        170 => Pcmpgtw,
        171 => V16I8MaskExtract,
        172 => V8I16MaskExtract,
        173 => Pslld,
        174 => Psrld,
        175 => Psrad,
        176 => AdcRR,
        177 => SbbRR,
        178 => Addps,
        179 => Subps,
        180 => Mulps,
        181 => Divps,
        182 => Addpd,
        183 => Subpd,
        184 => Mulpd,
        185 => Divpd,
        186 => Punpcklbw,
        187 => Punpckhbw,
        188 => Packuswb,
        189 => TrapBoundsCheckExact,
        190 => TrapNullIfZeroExact,
        191 => TrapDivZeroExact,
        192 => TrapShiftRangeExact,
        _ => Nop,
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

/// POD mirror of the slice's `X86ClassProps` (repr C, 9 x u32, same field order).
#[repr(C)]
#[derive(Clone, Copy)]
struct X86ClassPropsC {
    mem_effect_tag: u32,
    eff_is_pure: u32,
    eff_reads_mem: u32,
    eff_writes_mem: u32,
    eff_is_barrier: u32,
    is_removable: u32,
    writes_flags: u32,
    reads_flags: u32,
    produces_value: u32,
}

impl X86ClassPropsC {
    fn poisoned() -> Self {
        X86ClassPropsC {
            mem_effect_tag: 0xDEAD,
            eff_is_pure: 0xDEAD,
            eff_reads_mem: 0xDEAD,
            eff_writes_mem: 0xDEAD,
            eff_is_barrier: 0xDEAD,
            is_removable: 0xDEAD,
            writes_flags: 0xDEAD,
            reads_flags: 0xDEAD,
            produces_value: 0xDEAD,
        }
    }
    fn as_row(&self) -> [u32; 9] {
        [
            self.mem_effect_tag,
            self.eff_is_pure,
            self.eff_reads_mem,
            self.eff_writes_mem,
            self.eff_is_barrier,
            self.is_removable,
            self.writes_flags,
            self.reads_flags,
            self.produces_value,
        ]
    }
}

/// The PRODUCTION x86-opcode property row, computed entirely from the LINKED
/// production functions (the dual oracle).
fn native_x86_row(tag: u32) -> [u32; 9] {
    let op = prod_x86_from_tag(tag);
    let eff = prod_x86_effect(op);
    [
        prod_effect_tag(eff),
        eff.is_pure() as u32,
        eff.reads_memory() as u32,
        eff.writes_memory() as u32,
        eff.is_barrier() as u32,
        prod_x86_removable(op) as u32,
        prod_x86_writes(op) as u32,
        prod_x86_reads(op) as u32,
        prod_x86_produces(op) as u32,
    ]
}

// ── the x86 classifier test ──────────────────────────────────────────────────

/// The x86-64 opcode classifier layer — EXHAUSTIVE over all 193 declared
/// X86Opcode variants, JIT vs the LINKED PRODUCTION `trust_cg_opt::effects`
/// x86 classifiers.
#[test]
fn trust_x86_opcode_class_all193_production_eq_jit() {
    let expected = X86_COUNT as usize;
    let rows = run_watchdogged::<(u32, [u32; 9])>("x86_class", expected, move |tx| {
        let buffer = jit_module(X86_CLASS_IR, "x86_class");
        // SAFETY: machine code for functy.0 = (u32, ptr) -> ().
        let f: unsafe extern "C" fn(u32, *mut X86ClassPropsC) =
            unsafe { std::mem::transmute(bind(&buffer, "x86_class_props_root")) };
        for tag in 0..X86_COUNT {
            let mut out = X86ClassPropsC::poisoned();
            unsafe { f(tag, &mut out) };
            if tx.send((tag, out.as_row())).is_err() {
                return;
            }
        }
    });
    // Exhaustive native==JIT over every declared opcode.
    for &(tag, row) in &rows {
        let expect = native_x86_row(tag);
        assert_eq!(
            row, expect,
            "x86_class(tag={tag}): JIT {row:?} != production {expect:?}"
        );
    }

    // field accessors (mirror X86ClassPropsC order)
    let get = |tag: u32| rows[tag as usize].1;
    let meff = |t: u32| get(t)[0];
    let eff_pure = |t: u32| get(t)[1];
    let eff_rd = |t: u32| get(t)[2];
    let eff_wr = |t: u32| get(t)[3];
    let eff_barrier = |t: u32| get(t)[4];
    let removable = |t: u32| get(t)[5];
    let wrf = |t: u32| get(t)[6];
    let rdf = |t: u32| get(t)[7];
    let produces = |t: u32| get(t)[8];

    // Representative tags (declaration order):
    //   AddRR=0 SubRR=3 ImulRR=6 Idiv=9 Div=10 Neg=11 AndRR=16 ShlRR=23
    //   MovRR=29 MovRI=30 MovRM=34 MovMR=38 Lea=44 CmpRR=49 TestRR=53
    //   Jmp=56 Jcc=57 Call=58 CallR=59 Ret=61 Cmovcc=94 Setcc=95 Mfence=111
    //   Push=116 Pop=117 Phi=118 StackAlloc=119 Nop=120 Xchg=109 Cmpxchg=110
    //   Cmovcc32=124 Mul=125 Ud2=126 AdcRR=176 SbbRR=177.

    // -- memory-effect classification (the alias/reorder foundation) --
    assert_eq!(meff(0), 0, "AddRR is Pure");
    assert_eq!(eff_pure(0), 1, "AddRR effect is_pure");
    assert_eq!(meff(34), 1, "MovRM (r64,[mem]) classifies Load");
    assert_eq!(eff_rd(34), 1, "MovRM reads memory");
    assert_eq!(eff_pure(34), 0, "MovRM is not pure");
    assert_eq!(meff(117), 1, "Pop classifies Load (reads stack)");
    assert_eq!(meff(38), 2, "MovMR ([mem],r64) classifies Store");
    assert_eq!(eff_wr(38), 1, "MovMR writes memory");
    assert_eq!(meff(116), 2, "Push classifies Store (writes stack)");
    assert_eq!(meff(58), 3, "Call classifies Call (barrier)");
    assert_eq!(eff_barrier(58), 1, "Call is a barrier");
    assert_eq!(meff(111), 3, "Mfence classifies Call (full barrier)");
    assert_eq!(eff_barrier(111), 1, "Mfence is a barrier");
    assert_eq!(meff(109), 2, "Xchg classifies Store (conservative atomic)");
    assert_eq!(meff(110), 2, "Cmpxchg classifies Store");
    assert_eq!(meff(119), 2, "StackAlloc classifies Store");
    assert_eq!(
        meff(56),
        0,
        "Jmp is Pure at the memory-effect level (flags via InstFlags)"
    );

    // -- removability (the x86 DCE gate) --
    assert_eq!(
        removable(29),
        1,
        "MovRR is removable (pure, flag-clobber-free)"
    );
    assert_eq!(removable(44), 1, "Lea is removable");
    assert_eq!(removable(0), 0, "AddRR NOT removable (sets RFLAGS)");
    assert_eq!(removable(16), 0, "AndRR NOT removable (sets RFLAGS)");
    assert_eq!(removable(49), 0, "CmpRR NOT removable");
    assert_eq!(removable(34), 0, "MovRM NOT removable (load)");
    assert_eq!(removable(58), 0, "Call NOT removable");
    assert_eq!(removable(120), 1, "Nop IS removable");
    assert_eq!(removable(118), 1, "Phi IS removable");

    // -- flag write/read classification (the scheduler's RFLAGS edges) --
    assert_eq!(wrf(0), 1, "AddRR writes flags");
    assert_eq!(wrf(16), 1, "AndRR writes flags");
    assert_eq!(wrf(23), 1, "ShlRR writes flags");
    assert_eq!(wrf(49), 1, "CmpRR writes flags");
    assert_eq!(wrf(29), 0, "MovRR does NOT write flags");
    assert_eq!(wrf(44), 0, "Lea does NOT write flags");
    assert_eq!(wrf(176), 1, "AdcRR writes flags");
    assert_eq!(rdf(94), 1, "Cmovcc reads flags");
    assert_eq!(rdf(95), 1, "Setcc reads flags");
    assert_eq!(rdf(57), 1, "Jcc reads flags");
    assert_eq!(rdf(124), 1, "Cmovcc32 reads flags");
    assert_eq!(
        rdf(176),
        1,
        "AdcRR reads flags (implicit carry-in — the i128 chain)"
    );
    assert_eq!(rdf(177), 1, "SbbRR reads flags (implicit borrow-in)");
    assert_eq!(rdf(0), 0, "AddRR does NOT read flags");
    assert_eq!(rdf(56), 0, "Jmp (unconditional) does NOT read flags");

    // -- produces-value (def-use liveness) --
    assert_eq!(produces(0), 1, "AddRR produces a value");
    assert_eq!(produces(49), 0, "CmpRR produces NO value (flags only)");
    assert_eq!(produces(38), 0, "MovMR produces NO value (store)");
    assert_eq!(produces(56), 0, "Jmp produces NO value");
    assert_eq!(
        produces(9),
        0,
        "Idiv produces NO value (fixed-reg implicit writes)"
    );
    assert_eq!(
        produces(125),
        0,
        "Mul produces NO value (fixed-reg implicit writes)"
    );

    // Cross-invariant #1: every x86-removable opcode is memory-pure.
    for t in 0..X86_COUNT {
        if removable(t) == 1 {
            assert_eq!(eff_pure(t), 1, "removable x86 tag {t} must be memory-pure");
        }
    }
    // Cross-invariant #2: AdcRR/SbbRR both read AND write flags (the carry chain).
    for &t in &[176u32, 177] {
        assert_eq!(rdf(t), 1, "carry-chain tag {t} reads flags");
        assert_eq!(wrf(t), 1, "carry-chain tag {t} writes flags");
    }

    // NEGATIVE CONTROL (armed): an x86_is_removable that DROPS the flag-clobber
    // whitelist (a plausible bug: "pure => removable") would call AddRR
    // removable — production must not (ADD sets RFLAGS).
    let blind_removable = |t: u32| {
        let op = prod_x86_from_tag(t);
        // pure alone, WITHOUT the flag-clobber whitelist gate.
        prod_x86_effect(op).is_pure() as u32
    };
    assert_ne!(
        blind_removable(0),
        removable(0),
        "negative control must FAIL: AddRR removable if flag whitelist dropped"
    );
    assert_eq!(
        blind_removable(0),
        1,
        "the blind (buggy) oracle wrongly calls AddRR removable"
    );
    assert_eq!(
        removable(0),
        0,
        "production correctly rejects AddRR removal"
    );
}

/// ARMED CONTROL (x86 module): patch the UNIQUE `x86_reads_flags` switch in the
/// embedded fixture, swapping the AdcRR(176) arm for Psrad(175), JIT the
/// corrupted text, and prove `x86_reads_flags` MISFIRES on Psrad (a pure packed
/// shift) while dropping the AdcRR carry-in — a flags def/use classifier bug
/// that would license reordering across the i128 carry chain.
#[test]
fn trust_x86_opcode_class_armed_control_corrupted_reads_flags_caught_then_restored() {
    let anchor = "switch %4 [ 57: bb2 94: bb2 95: bb2 124: bb2 176: bb2 177: bb2 default: bb1 ]\n";
    assert_eq!(
        X86_CLASS_IR.matches(anchor).count(),
        1,
        "armed-control anchor must be unique in the fixture"
    );
    let corrupted = X86_CLASS_IR.replace(
        anchor,
        "switch %4 [ 57: bb2 94: bb2 95: bb2 124: bb2 175: bb2 177: bb2 default: bb1 ]\n",
    );
    assert_ne!(corrupted, X86_CLASS_IR);

    let expected = X86_COUNT as usize;
    let rows = run_watchdogged::<(u32, u32)>("x86_class CORRUPTED", expected, move |tx| {
        let buffer = jit_module(&corrupted, "x86_class CORRUPTED");
        let f: unsafe extern "C" fn(u32, *mut X86ClassPropsC) =
            unsafe { std::mem::transmute(bind(&buffer, "x86_class_props_root")) };
        for tag in 0..X86_COUNT {
            let mut out = X86ClassPropsC::poisoned();
            unsafe { f(tag, &mut out) };
            if tx.send((tag, out.as_row()[7])).is_err() {
                return;
            }
        }
    });
    let rdf = |t: u32| rows.iter().find(|q| q.0 == t).unwrap().1;
    assert_eq!(
        rdf(175),
        1,
        "ARMED: corrupted reads_flags misfires on Psrad(175)"
    );
    assert_eq!(
        rdf(176),
        0,
        "ARMED: corrupted reads_flags no longer fires on AdcRR(176)"
    );
    assert_eq!(
        prod_x86_reads(prod_x86_from_tag(176)) as u32,
        1,
        "production: AdcRR DOES read flags — the divergence is LOUD"
    );
    assert_eq!(
        prod_x86_reads(prod_x86_from_tag(175)) as u32,
        0,
        "production: Psrad does NOT read flags"
    );
    let diverged: Vec<u32> = (0..X86_COUNT)
        .filter(|&t| rdf(t) != prod_x86_reads(prod_x86_from_tag(t)) as u32)
        .collect();
    assert_eq!(
        diverged,
        vec![175, 176],
        "ARMED: exactly {{Psrad, AdcRR}} diverge"
    );

    // Restore: the pristine embedded text re-passes on the reads_flags field.
    let rows2 = run_watchdogged::<(u32, u32)>("x86_class RESTORED", expected, move |tx| {
        let buffer = jit_module(X86_CLASS_IR, "x86_class RESTORED");
        let f: unsafe extern "C" fn(u32, *mut X86ClassPropsC) =
            unsafe { std::mem::transmute(bind(&buffer, "x86_class_props_root")) };
        for tag in 0..X86_COUNT {
            let mut out = X86ClassPropsC::poisoned();
            unsafe { f(tag, &mut out) };
            if tx.send((tag, out.as_row()[7])).is_err() {
                return;
            }
        }
    });
    for &(t, v) in &rows2 {
        assert_eq!(
            v,
            prod_x86_reads(prod_x86_from_tag(t)) as u32,
            "RESTORED reads_flags must re-pass at tag {t}"
        );
    }
}

// ── strength-reduce / algebraic gate plumbing ─────────────────────────────────

#[repr(C)]
#[derive(Clone, Copy)]
struct SrPropsC {
    is_pow2: u32,
    in_width: u32,
    shamt_is_some: u32,
    shamt: u32,
}
impl SrPropsC {
    fn poisoned() -> Self {
        SrPropsC {
            is_pow2: 0xDEAD,
            in_width: 0xDEAD,
            shamt_is_some: 0xDEAD,
            shamt: 0xDEAD,
        }
    }
    fn as_row(&self) -> [u32; 4] {
        [self.is_pow2, self.in_width, self.shamt_is_some, self.shamt]
    }
}

/// Independent naive reference for the three strength-reduce gates ([B3]).
fn naive_sr(v: u64, k: i64, width: i64, max: i64) -> [u32; 4] {
    let is_pow2 = (v != 0 && (v & (v.wrapping_sub(1))) == 0) as u32;
    // Production `(1..width).contains(&k)`.
    let in_width = ((1..width).contains(&k)) as u32;
    // Production `(0..=max).contains(&k)`.
    let (shamt_is_some, shamt) = if (0..=max).contains(&k) {
        (1u32, k as u32)
    } else {
        (0, 0)
    };
    [is_pow2, in_width, shamt_is_some, shamt]
}

/// The strength-reduce / algebraic legality gates — swept over the power-of-two
/// and shift-range boundary edges, JIT vs the independent naive reference (which
/// uses the PRODUCTION `Range::contains` form to cross-check the [B2] rewrite).
#[test]
fn trust_strength_reduce_gates_edges_native_eq_jit() {
    // Full cross-product (v, k, width, max=width-1) spanning the pow2 and
    // shift-range boundaries.
    let mut inputs: Vec<(u64, i64, i64, i64)> = Vec::new();
    let vs: [u64; 12] = [
        0,
        1,
        2,
        3,
        4,
        7,
        8,
        16,
        1023,
        1024,
        0x8000_0000_0000_0000,
        u64::MAX,
    ];
    let ks: [i64; 10] = [-1, 0, 1, 2, 7, 31, 32, 63, 64, 65];
    let widths: [i64; 3] = [8, 32, 64];
    for &v in &vs {
        for &k in &ks {
            for &width in &widths {
                inputs.push((v, k, width, width - 1));
            }
        }
    }
    let expected = inputs.len();
    let inp = inputs.clone();
    let rows = run_watchdogged::<((u64, i64, i64, i64), [u32; 4])>(
        "strength_reduce",
        expected,
        move |tx| {
            let buffer = jit_module(SR_IR, "strength_reduce");
            // SAFETY: functy.0 = (u64, i64, i64, i64, ptr) -> ().
            let f: unsafe extern "C" fn(u64, i64, i64, i64, *mut SrPropsC) =
                unsafe { std::mem::transmute(bind(&buffer, "sr_props_root")) };
            for &(v, k, w, m) in &inp {
                let mut out = SrPropsC::poisoned();
                unsafe { f(v, k, w, m, &mut out) };
                if tx.send(((v, k, w, m), out.as_row())).is_err() {
                    return;
                }
            }
        },
    );
    for &((v, k, w, m), row) in &rows {
        assert_eq!(
            row,
            naive_sr(v, k, w, m),
            "sr({v:#x},k={k},w={w},max={m}): JIT {row:?} != naive-ref"
        );
    }
    let find =
        |v: u64, k: i64, w: i64, m: i64| rows.iter().find(|q| q.0 == (v, k, w, m)).unwrap().1;
    // is_power_of_two spot checks (field 0).
    assert_eq!(find(1, 0, 32, 31)[0], 1, "1 is a power of two");
    assert_eq!(find(8, 7, 8, 7)[0], 1, "8 is a power of two");
    assert_eq!(find(1024, 1, 32, 31)[0], 1, "1024 is a power of two");
    assert_eq!(
        find(0x8000_0000_0000_0000, 0, 32, 31)[0],
        1,
        "2^63 (u64) is a power of two"
    );
    assert_eq!(find(0, 0, 32, 31)[0], 0, "0 is NOT a power of two");
    assert_eq!(find(3, 1, 32, 31)[0], 0, "3 is NOT a power of two");
    assert_eq!(
        find(u64::MAX, 1, 32, 31)[0],
        0,
        "u64::MAX is NOT a power of two"
    );
    // shift_amount_in_width spot checks (field 1): 1 <= k < width.
    assert_eq!(find(0, 1, 32, 31)[1], 1, "k=1 in width 32");
    assert_eq!(find(0, 31, 32, 31)[1], 1, "k=31 in width 32");
    assert_eq!(
        find(0, 0, 32, 31)[1],
        0,
        "k=0 NOT in width (lower bound is 1)"
    );
    assert_eq!(
        find(0, 64, 64, 63)[1],
        0,
        "k=64 NOT in width 64 (upper is exclusive)"
    );
    assert_eq!(find(0, 63, 64, 63)[1], 1, "k=63 in width 64");
    // shift_amount spot checks (fields 2,3): 0 <= k <= max -> Some(k).
    assert_eq!(
        [find(0, 0, 32, 31)[2], find(0, 0, 32, 31)[3]],
        [1, 0],
        "k=0 <= max 31 -> Some(0)"
    );
    assert_eq!(
        [find(0, 31, 32, 31)[2], find(0, 31, 32, 31)[3]],
        [1, 31],
        "k=31 <= max 31 -> Some(31)"
    );
    assert_eq!(find(0, 32, 64, 63)[2], 1, "k=32 <= max 63 -> Some");
    assert_eq!(find(0, -1, 32, 31)[2], 0, "k=-1 < 0 -> None");
    assert_eq!(find(0, 64, 8, 7)[2], 0, "k=64 > max 7 -> None");

    // NEGATIVE CONTROL (armed): a shift_amount_in_width that uses `k >= 0`
    // (a plausible off-by-one) would call k=0 in-width — production requires
    // k >= 1 (a zero shift is an identity, not a strength-reduction target).
    let blind_in_width = |k: i64, width: i64| ((0..width).contains(&k)) as u32;
    assert_ne!(
        blind_in_width(0, 32),
        find(0, 0, 32, 31)[1],
        "negative control must FAIL: off-by-one lower bound admits k=0"
    );
    assert_eq!(
        blind_in_width(0, 32),
        1,
        "the blind oracle wrongly calls k=0 in-width"
    );
    assert_eq!(find(0, 0, 32, 31)[1], 0, "production correctly rejects k=0");
}

/// ARMED CONTROL (strength-reduce module): patch the UNIQUE `const i64 1`
/// (the `k >= 1` lower bound inside `shift_amount_in_width`) up to 2, JIT the
/// corrupted text, and prove the gate now rejects k=1 (shifting the legal
/// shift-amount floor) while the pristine module re-passes.
#[test]
fn trust_strength_reduce_armed_control_corrupted_in_width_floor_caught_then_restored() {
    let anchor = "    %5 = const i64 1\n";
    assert_eq!(
        SR_IR.matches(anchor).count(),
        1,
        "armed-control anchor must be unique in the fixture"
    );
    let corrupted = SR_IR.replace(anchor, "    %5 = const i64 2\n");
    assert_ne!(corrupted, SR_IR);

    // Probe k across the shifted floor at a fixed width/max.
    let probes: Vec<(u64, i64, i64, i64)> = vec![
        (0, 0, 32, 31),
        (0, 1, 32, 31),
        (0, 2, 32, 31),
        (0, 31, 32, 31),
    ];
    let expected = probes.len();
    let inp = probes.clone();
    let rows =
        run_watchdogged::<((u64, i64, i64, i64), [u32; 4])>("sr CORRUPTED", expected, move |tx| {
            let buffer = jit_module(&corrupted, "sr CORRUPTED");
            let f: unsafe extern "C" fn(u64, i64, i64, i64, *mut SrPropsC) =
                unsafe { std::mem::transmute(bind(&buffer, "sr_props_root")) };
            for &(v, k, w, m) in &inp {
                let mut out = SrPropsC::poisoned();
                unsafe { f(v, k, w, m, &mut out) };
                if tx.send(((v, k, w, m), out.as_row())).is_err() {
                    return;
                }
            }
        });
    let inw = |k: i64| rows.iter().find(|q| q.0 == (0, k, 32, 31)).unwrap().1[1];
    // Corrupted floor is now 2: k=1 rejected, k=2 accepted.
    assert_eq!(inw(1), 0, "ARMED: corrupted floor rejects k=1");
    assert_eq!(inw(0), 0, "ARMED: k=0 still rejected");
    assert_eq!(inw(2), 1, "ARMED: k=2 accepted under corrupted floor");
    assert_eq!(inw(31), 1, "ARMED: k=31 still accepted");
    // Production floor is 1: k=1 accepted.
    assert_eq!(
        ((1..32).contains(&1)) as u32,
        1,
        "production: k=1 IS in-width — the divergence is LOUD"
    );

    // Restore: pristine re-pass on the in_width field.
    let inp2 = probes.clone();
    let rows2 =
        run_watchdogged::<((u64, i64, i64, i64), [u32; 4])>("sr RESTORED", expected, move |tx| {
            let buffer = jit_module(SR_IR, "sr RESTORED");
            let f: unsafe extern "C" fn(u64, i64, i64, i64, *mut SrPropsC) =
                unsafe { std::mem::transmute(bind(&buffer, "sr_props_root")) };
            for &(v, k, w, m) in &inp2 {
                let mut out = SrPropsC::poisoned();
                unsafe { f(v, k, w, m, &mut out) };
                if tx.send(((v, k, w, m), out.as_row())).is_err() {
                    return;
                }
            }
        });
    for &((v, k, w, m), row) in &rows2 {
        assert_eq!(
            row,
            naive_sr(v, k, w, m),
            "RESTORED must re-pass at (v={v:#x},k={k})"
        );
    }
}

// ── F4 fail-loud pins (const-materialization deciders blocked at JIT link) ────

/// HISTORICAL F4 PIN (round-21 fixture at b2c58eb):
/// `single_movn_materialization` iterates a fixed `[u64;4]` array via
/// `into_iter`, which lowers to an empty-bodied leaf the JIT cannot resolve.
/// Asserts the exact `Jit(UnresolvedSymbol(... into_iter ...))` symptom.
#[test]
fn trust_single_movn_pinned_f4_unresolved_array_into_iter() {
    let err = jit_compile_err(MOVN_IR, "single_movn_materialization");
    assert!(
        err.contains("UnresolvedSymbol"),
        "F4 pin: expected UnresolvedSymbol, got {err}"
    );
    assert!(
        err.contains("into_iter"),
        "F4 pin: expected the array into_iter leaf, got {err}"
    );
}

/// F4 PIN: `move_wide_chunks` iterates a `[u16;4]` via slice `iter_mut`, which
/// lowers to an empty-bodied leaf the JIT cannot resolve.
#[test]
fn trust_move_wide_chunks_pinned_f4_unresolved_slice_iter_mut() {
    let err = jit_compile_err(CHUNKS_IR, "move_wide_chunks");
    assert!(
        err.contains("UnresolvedSymbol"),
        "F4 pin: expected UnresolvedSymbol, got {err}"
    );
    assert!(
        err.contains("iter_mut"),
        "F4 pin: expected the slice iter_mut leaf, got {err}"
    );
}

/// F4 PIN: the historical peephole `is_power_of_two` fixture (`Option<u32>`)
/// calls `trailing_zeros`, which lowers to an empty-bodied numeric-intrinsic
/// leaf the JIT cannot resolve.
#[test]
fn trust_is_power_of_two_peephole_pinned_f4_unresolved_trailing_zeros() {
    let err = jit_compile_err(POW2_IR, "is_power_of_two(peephole)");
    assert!(
        err.contains("UnresolvedSymbol"),
        "F4 pin: expected UnresolvedSymbol, got {err}"
    );
    assert!(
        err.contains("trailing_zeros"),
        "F4 pin: expected the trailing_zeros leaf, got {err}"
    );
}

// ── embedded fixtures (VERBATIM MIR-closure emits; regen per header) ──────────

/// VERBATIM MIR-closure emit of `x86_class_props_root`. x86-64 opcode classifier
/// layer (trust-cg-ir X86Opcode[repr(u8), B4/F5] + trust-cg-opt effects); slice
/// trust_x86_opcode_class_slice.rs. 26320 bytes; 12 members; validate 0;
/// re-parse OK; EXTERN-FREE.
const X86_CLASS_IR: &str = r####"; TrustIr text format v1
module "mir::closure::x86_class_props_root"
target "aarch64-apple-darwin" 8 little
file 0 "trust_x86_opcode_class_slice.rs"

functy.0 = (u32, ptr) -> ()

functy.1 = (ptr, u32) -> ()

functy.2 = (ptr, u8) -> ()

functy.3 = (u8) -> (u32)

functy.4 = (u8) -> (bool)

functy.5 = (u8) -> (bool)

functy.6 = (u8) -> (bool)

functy.7 = (u8) -> (bool)

functy.8 = (u8) -> (bool)

functy.9 = (u8) -> (bool)

functy.10 = (u8) -> (bool)

functy.11 = (u8) -> (bool)

fn @x86_class_props_root(functy.0) {
bb0(%0: u32, %1: ptr):
    %22 = alloca i8, align 1
    %23 = alloca i8, align 1
    call @func.1(%22, %0)
    br bb1(%1)
bb1(%2: ptr):
    %24 = load u8, ptr %22
    call @func.2(%23, %24)
    br bb2(%2)
bb2(%3: ptr):
    %25 = load u8, ptr %23
    %26 = call @func.3(%25)
    br bb3(%3, %26)
bb3(%4: ptr, %5: u32):
    store u32 %5, ptr %4
    %27 = load u8, ptr %23
    %28 = call @func.4(%27)
    br bb4(%4, %28)
bb4(%6: ptr, %7: bool):
    %29 = const u32 1
    %30 = const u32 0
    %31 = select u32 %7, %29, %30
    %32 = const i64 4
    %33 = gep i8, ptr %6, %32
    store u32 %31, ptr %33
    %34 = load u8, ptr %23
    %35 = call @func.5(%34)
    br bb5(%6, %35)
bb5(%8: ptr, %9: bool):
    %36 = const u32 1
    %37 = const u32 0
    %38 = select u32 %9, %36, %37
    %39 = const i64 8
    %40 = gep i8, ptr %8, %39
    store u32 %38, ptr %40
    %41 = load u8, ptr %23
    %42 = call @func.6(%41)
    br bb6(%8, %42)
bb6(%10: ptr, %11: bool):
    %43 = const u32 1
    %44 = const u32 0
    %45 = select u32 %11, %43, %44
    %46 = const i64 12
    %47 = gep i8, ptr %10, %46
    store u32 %45, ptr %47
    %48 = load u8, ptr %23
    %49 = call @func.7(%48)
    br bb7(%10, %49)
bb7(%12: ptr, %13: bool):
    %50 = const u32 1
    %51 = const u32 0
    %52 = select u32 %13, %50, %51
    %53 = const i64 16
    %54 = gep i8, ptr %12, %53
    store u32 %52, ptr %54
    %55 = load u8, ptr %22
    %56 = call @func.8(%55)
    br bb8(%12, %56)
bb8(%14: ptr, %15: bool):
    %57 = const u32 1
    %58 = const u32 0
    %59 = select u32 %15, %57, %58
    %60 = const i64 20
    %61 = gep i8, ptr %14, %60
    store u32 %59, ptr %61
    %62 = load u8, ptr %22
    %63 = call @func.9(%62)
    br bb9(%14, %63)
bb9(%16: ptr, %17: bool):
    %64 = const u32 1
    %65 = const u32 0
    %66 = select u32 %17, %64, %65
    %67 = const i64 24
    %68 = gep i8, ptr %16, %67
    store u32 %66, ptr %68
    %69 = load u8, ptr %22
    %70 = call @func.10(%69)
    br bb10(%16, %70)
bb10(%18: ptr, %19: bool):
    %71 = const u32 1
    %72 = const u32 0
    %73 = select u32 %19, %71, %72
    %74 = const i64 28
    %75 = gep i8, ptr %18, %74
    store u32 %73, ptr %75
    %76 = load u8, ptr %22
    %77 = call @func.11(%76)
    br bb11(%18, %77)
bb11(%20: ptr, %21: bool):
    %78 = const u32 1
    %79 = const u32 0
    %80 = select u32 %21, %78, %79
    %81 = const i64 32
    %82 = gep i8, ptr %20, %81
    store u32 %80, ptr %82
    ret
}

fn @x86_from_tag(functy.1) {
bb0(%0: ptr, %1: u32):
    switch %1 [ 0: bb194 1: bb193 2: bb192 3: bb191 4: bb190 5: bb189 6: bb188 7: bb187 8: bb186 9: bb185 10: bb184 11: bb183 12: bb182 13: bb181 14: bb180 15: bb179 16: bb178 17: bb177 18: bb176 19: bb175 20: bb174 21: bb173 22: bb172 23: bb171 24: bb170 25: bb169 26: bb168 27: bb167 28: bb166 29: bb165 30: bb164 31: bb163 32: bb162 33: bb161 34: bb160 35: bb159 36: bb158 37: bb157 38: bb156 39: bb155 40: bb154 41: bb153 42: bb152 43: bb151 44: bb150 45: bb149 46: bb148 47: bb147 48: bb146 49: bb145 50: bb144 51: bb143 52: bb142 53: bb141 54: bb140 55: bb139 56: bb138 57: bb137 58: bb136 59: bb135 60: bb134 61: bb133 62: bb132 63: bb131 64: bb130 65: bb129 66: bb128 67: bb127 68: bb126 69: bb125 70: bb124 71: bb123 72: bb122 73: bb121 74: bb120 75: bb119 76: bb118 77: bb117 78: bb116 79: bb115 80: bb114 81: bb113 82: bb112 83: bb111 84: bb110 85: bb109 86: bb108 87: bb107 88: bb106 89: bb105 90: bb104 91: bb103 92: bb102 93: bb101 94: bb100 95: bb99 96: bb98 97: bb97 98: bb96 99: bb95 100: bb94 101: bb93 102: bb92 103: bb91 104: bb90 105: bb89 106: bb88 107: bb87 108: bb86 109: bb85 110: bb84 111: bb83 112: bb82 113: bb81 114: bb80 115: bb79 116: bb78 117: bb77 118: bb76 119: bb75 120: bb74 121: bb73 122: bb72 123: bb71 124: bb70 125: bb69 126: bb68 127: bb67 128: bb66 129: bb65 130: bb64 131: bb63 132: bb62 133: bb61 134: bb60 135: bb59 136: bb58 137: bb57 138: bb56 139: bb55 140: bb54 141: bb53 142: bb52 143: bb51 144: bb50 145: bb49 146: bb48 147: bb47 148: bb46 149: bb45 150: bb44 151: bb43 152: bb42 153: bb41 154: bb40 155: bb39 156: bb38 157: bb37 158: bb36 159: bb35 160: bb34 161: bb33 162: bb32 163: bb31 164: bb30 165: bb29 166: bb28 167: bb27 168: bb26 169: bb25 170: bb24 171: bb23 172: bb22 173: bb21 174: bb20 175: bb19 176: bb18 177: bb17 178: bb16 179: bb15 180: bb14 181: bb13 182: bb12 183: bb11 184: bb10 185: bb9 186: bb8 187: bb7 188: bb6 189: bb5 190: bb4 191: bb3 192: bb2 default: bb1 ]
bb1:
    %2 = const i8 120
    store i8 %2, ptr %0
    br bb195
bb2:
    %3 = const i8 -64
    store i8 %3, ptr %0
    br bb195
bb3:
    %4 = const i8 -65
    store i8 %4, ptr %0
    br bb195
bb4:
    %5 = const i8 -66
    store i8 %5, ptr %0
    br bb195
bb5:
    %6 = const i8 -67
    store i8 %6, ptr %0
    br bb195
bb6:
    %7 = const i8 -68
    store i8 %7, ptr %0
    br bb195
bb7:
    %8 = const i8 -69
    store i8 %8, ptr %0
    br bb195
bb8:
    %9 = const i8 -70
    store i8 %9, ptr %0
    br bb195
bb9:
    %10 = const i8 -71
    store i8 %10, ptr %0
    br bb195
bb10:
    %11 = const i8 -72
    store i8 %11, ptr %0
    br bb195
bb11:
    %12 = const i8 -73
    store i8 %12, ptr %0
    br bb195
bb12:
    %13 = const i8 -74
    store i8 %13, ptr %0
    br bb195
bb13:
    %14 = const i8 -75
    store i8 %14, ptr %0
    br bb195
bb14:
    %15 = const i8 -76
    store i8 %15, ptr %0
    br bb195
bb15:
    %16 = const i8 -77
    store i8 %16, ptr %0
    br bb195
bb16:
    %17 = const i8 -78
    store i8 %17, ptr %0
    br bb195
bb17:
    %18 = const i8 -79
    store i8 %18, ptr %0
    br bb195
bb18:
    %19 = const i8 -80
    store i8 %19, ptr %0
    br bb195
bb19:
    %20 = const i8 -81
    store i8 %20, ptr %0
    br bb195
bb20:
    %21 = const i8 -82
    store i8 %21, ptr %0
    br bb195
bb21:
    %22 = const i8 -83
    store i8 %22, ptr %0
    br bb195
bb22:
    %23 = const i8 -84
    store i8 %23, ptr %0
    br bb195
bb23:
    %24 = const i8 -85
    store i8 %24, ptr %0
    br bb195
bb24:
    %25 = const i8 -86
    store i8 %25, ptr %0
    br bb195
bb25:
    %26 = const i8 -87
    store i8 %26, ptr %0
    br bb195
bb26:
    %27 = const i8 -88
    store i8 %27, ptr %0
    br bb195
bb27:
    %28 = const i8 -89
    store i8 %28, ptr %0
    br bb195
bb28:
    %29 = const i8 -90
    store i8 %29, ptr %0
    br bb195
bb29:
    %30 = const i8 -91
    store i8 %30, ptr %0
    br bb195
bb30:
    %31 = const i8 -92
    store i8 %31, ptr %0
    br bb195
bb31:
    %32 = const i8 -93
    store i8 %32, ptr %0
    br bb195
bb32:
    %33 = const i8 -94
    store i8 %33, ptr %0
    br bb195
bb33:
    %34 = const i8 -95
    store i8 %34, ptr %0
    br bb195
bb34:
    %35 = const i8 -96
    store i8 %35, ptr %0
    br bb195
bb35:
    %36 = const i8 -97
    store i8 %36, ptr %0
    br bb195
bb36:
    %37 = const i8 -98
    store i8 %37, ptr %0
    br bb195
bb37:
    %38 = const i8 -99
    store i8 %38, ptr %0
    br bb195
bb38:
    %39 = const i8 -100
    store i8 %39, ptr %0
    br bb195
bb39:
    %40 = const i8 -101
    store i8 %40, ptr %0
    br bb195
bb40:
    %41 = const i8 -102
    store i8 %41, ptr %0
    br bb195
bb41:
    %42 = const i8 -103
    store i8 %42, ptr %0
    br bb195
bb42:
    %43 = const i8 -104
    store i8 %43, ptr %0
    br bb195
bb43:
    %44 = const i8 -105
    store i8 %44, ptr %0
    br bb195
bb44:
    %45 = const i8 -106
    store i8 %45, ptr %0
    br bb195
bb45:
    %46 = const i8 -107
    store i8 %46, ptr %0
    br bb195
bb46:
    %47 = const i8 -108
    store i8 %47, ptr %0
    br bb195
bb47:
    %48 = const i8 -109
    store i8 %48, ptr %0
    br bb195
bb48:
    %49 = const i8 -110
    store i8 %49, ptr %0
    br bb195
bb49:
    %50 = const i8 -111
    store i8 %50, ptr %0
    br bb195
bb50:
    %51 = const i8 -112
    store i8 %51, ptr %0
    br bb195
bb51:
    %52 = const i8 -113
    store i8 %52, ptr %0
    br bb195
bb52:
    %53 = const i8 -114
    store i8 %53, ptr %0
    br bb195
bb53:
    %54 = const i8 -115
    store i8 %54, ptr %0
    br bb195
bb54:
    %55 = const i8 -116
    store i8 %55, ptr %0
    br bb195
bb55:
    %56 = const i8 -117
    store i8 %56, ptr %0
    br bb195
bb56:
    %57 = const i8 -118
    store i8 %57, ptr %0
    br bb195
bb57:
    %58 = const i8 -119
    store i8 %58, ptr %0
    br bb195
bb58:
    %59 = const i8 -120
    store i8 %59, ptr %0
    br bb195
bb59:
    %60 = const i8 -121
    store i8 %60, ptr %0
    br bb195
bb60:
    %61 = const i8 -122
    store i8 %61, ptr %0
    br bb195
bb61:
    %62 = const i8 -123
    store i8 %62, ptr %0
    br bb195
bb62:
    %63 = const i8 -124
    store i8 %63, ptr %0
    br bb195
bb63:
    %64 = const i8 -125
    store i8 %64, ptr %0
    br bb195
bb64:
    %65 = const i8 -126
    store i8 %65, ptr %0
    br bb195
bb65:
    %66 = const i8 -127
    store i8 %66, ptr %0
    br bb195
bb66:
    %67 = const i8 -128
    store i8 %67, ptr %0
    br bb195
bb67:
    %68 = const i8 127
    store i8 %68, ptr %0
    br bb195
bb68:
    %69 = const i8 126
    store i8 %69, ptr %0
    br bb195
bb69:
    %70 = const i8 125
    store i8 %70, ptr %0
    br bb195
bb70:
    %71 = const i8 124
    store i8 %71, ptr %0
    br bb195
bb71:
    %72 = const i8 123
    store i8 %72, ptr %0
    br bb195
bb72:
    %73 = const i8 122
    store i8 %73, ptr %0
    br bb195
bb73:
    %74 = const i8 121
    store i8 %74, ptr %0
    br bb195
bb74:
    %75 = const i8 120
    store i8 %75, ptr %0
    br bb195
bb75:
    %76 = const i8 119
    store i8 %76, ptr %0
    br bb195
bb76:
    %77 = const i8 118
    store i8 %77, ptr %0
    br bb195
bb77:
    %78 = const i8 117
    store i8 %78, ptr %0
    br bb195
bb78:
    %79 = const i8 116
    store i8 %79, ptr %0
    br bb195
bb79:
    %80 = const i8 115
    store i8 %80, ptr %0
    br bb195
bb80:
    %81 = const i8 114
    store i8 %81, ptr %0
    br bb195
bb81:
    %82 = const i8 113
    store i8 %82, ptr %0
    br bb195
bb82:
    %83 = const i8 112
    store i8 %83, ptr %0
    br bb195
bb83:
    %84 = const i8 111
    store i8 %84, ptr %0
    br bb195
bb84:
    %85 = const i8 110
    store i8 %85, ptr %0
    br bb195
bb85:
    %86 = const i8 109
    store i8 %86, ptr %0
    br bb195
bb86:
    %87 = const i8 108
    store i8 %87, ptr %0
    br bb195
bb87:
    %88 = const i8 107
    store i8 %88, ptr %0
    br bb195
bb88:
    %89 = const i8 106
    store i8 %89, ptr %0
    br bb195
bb89:
    %90 = const i8 105
    store i8 %90, ptr %0
    br bb195
bb90:
    %91 = const i8 104
    store i8 %91, ptr %0
    br bb195
bb91:
    %92 = const i8 103
    store i8 %92, ptr %0
    br bb195
bb92:
    %93 = const i8 102
    store i8 %93, ptr %0
    br bb195
bb93:
    %94 = const i8 101
    store i8 %94, ptr %0
    br bb195
bb94:
    %95 = const i8 100
    store i8 %95, ptr %0
    br bb195
bb95:
    %96 = const i8 99
    store i8 %96, ptr %0
    br bb195
bb96:
    %97 = const i8 98
    store i8 %97, ptr %0
    br bb195
bb97:
    %98 = const i8 97
    store i8 %98, ptr %0
    br bb195
bb98:
    %99 = const i8 96
    store i8 %99, ptr %0
    br bb195
bb99:
    %100 = const i8 95
    store i8 %100, ptr %0
    br bb195
bb100:
    %101 = const i8 94
    store i8 %101, ptr %0
    br bb195
bb101:
    %102 = const i8 93
    store i8 %102, ptr %0
    br bb195
bb102:
    %103 = const i8 92
    store i8 %103, ptr %0
    br bb195
bb103:
    %104 = const i8 91
    store i8 %104, ptr %0
    br bb195
bb104:
    %105 = const i8 90
    store i8 %105, ptr %0
    br bb195
bb105:
    %106 = const i8 89
    store i8 %106, ptr %0
    br bb195
bb106:
    %107 = const i8 88
    store i8 %107, ptr %0
    br bb195
bb107:
    %108 = const i8 87
    store i8 %108, ptr %0
    br bb195
bb108:
    %109 = const i8 86
    store i8 %109, ptr %0
    br bb195
bb109:
    %110 = const i8 85
    store i8 %110, ptr %0
    br bb195
bb110:
    %111 = const i8 84
    store i8 %111, ptr %0
    br bb195
bb111:
    %112 = const i8 83
    store i8 %112, ptr %0
    br bb195
bb112:
    %113 = const i8 82
    store i8 %113, ptr %0
    br bb195
bb113:
    %114 = const i8 81
    store i8 %114, ptr %0
    br bb195
bb114:
    %115 = const i8 80
    store i8 %115, ptr %0
    br bb195
bb115:
    %116 = const i8 79
    store i8 %116, ptr %0
    br bb195
bb116:
    %117 = const i8 78
    store i8 %117, ptr %0
    br bb195
bb117:
    %118 = const i8 77
    store i8 %118, ptr %0
    br bb195
bb118:
    %119 = const i8 76
    store i8 %119, ptr %0
    br bb195
bb119:
    %120 = const i8 75
    store i8 %120, ptr %0
    br bb195
bb120:
    %121 = const i8 74
    store i8 %121, ptr %0
    br bb195
bb121:
    %122 = const i8 73
    store i8 %122, ptr %0
    br bb195
bb122:
    %123 = const i8 72
    store i8 %123, ptr %0
    br bb195
bb123:
    %124 = const i8 71
    store i8 %124, ptr %0
    br bb195
bb124:
    %125 = const i8 70
    store i8 %125, ptr %0
    br bb195
bb125:
    %126 = const i8 69
    store i8 %126, ptr %0
    br bb195
bb126:
    %127 = const i8 68
    store i8 %127, ptr %0
    br bb195
bb127:
    %128 = const i8 67
    store i8 %128, ptr %0
    br bb195
bb128:
    %129 = const i8 66
    store i8 %129, ptr %0
    br bb195
bb129:
    %130 = const i8 65
    store i8 %130, ptr %0
    br bb195
bb130:
    %131 = const i8 64
    store i8 %131, ptr %0
    br bb195
bb131:
    %132 = const i8 63
    store i8 %132, ptr %0
    br bb195
bb132:
    %133 = const i8 62
    store i8 %133, ptr %0
    br bb195
bb133:
    %134 = const i8 61
    store i8 %134, ptr %0
    br bb195
bb134:
    %135 = const i8 60
    store i8 %135, ptr %0
    br bb195
bb135:
    %136 = const i8 59
    store i8 %136, ptr %0
    br bb195
bb136:
    %137 = const i8 58
    store i8 %137, ptr %0
    br bb195
bb137:
    %138 = const i8 57
    store i8 %138, ptr %0
    br bb195
bb138:
    %139 = const i8 56
    store i8 %139, ptr %0
    br bb195
bb139:
    %140 = const i8 55
    store i8 %140, ptr %0
    br bb195
bb140:
    %141 = const i8 54
    store i8 %141, ptr %0
    br bb195
bb141:
    %142 = const i8 53
    store i8 %142, ptr %0
    br bb195
bb142:
    %143 = const i8 52
    store i8 %143, ptr %0
    br bb195
bb143:
    %144 = const i8 51
    store i8 %144, ptr %0
    br bb195
bb144:
    %145 = const i8 50
    store i8 %145, ptr %0
    br bb195
bb145:
    %146 = const i8 49
    store i8 %146, ptr %0
    br bb195
bb146:
    %147 = const i8 48
    store i8 %147, ptr %0
    br bb195
bb147:
    %148 = const i8 47
    store i8 %148, ptr %0
    br bb195
bb148:
    %149 = const i8 46
    store i8 %149, ptr %0
    br bb195
bb149:
    %150 = const i8 45
    store i8 %150, ptr %0
    br bb195
bb150:
    %151 = const i8 44
    store i8 %151, ptr %0
    br bb195
bb151:
    %152 = const i8 43
    store i8 %152, ptr %0
    br bb195
bb152:
    %153 = const i8 42
    store i8 %153, ptr %0
    br bb195
bb153:
    %154 = const i8 41
    store i8 %154, ptr %0
    br bb195
bb154:
    %155 = const i8 40
    store i8 %155, ptr %0
    br bb195
bb155:
    %156 = const i8 39
    store i8 %156, ptr %0
    br bb195
bb156:
    %157 = const i8 38
    store i8 %157, ptr %0
    br bb195
bb157:
    %158 = const i8 37
    store i8 %158, ptr %0
    br bb195
bb158:
    %159 = const i8 36
    store i8 %159, ptr %0
    br bb195
bb159:
    %160 = const i8 35
    store i8 %160, ptr %0
    br bb195
bb160:
    %161 = const i8 34
    store i8 %161, ptr %0
    br bb195
bb161:
    %162 = const i8 33
    store i8 %162, ptr %0
    br bb195
bb162:
    %163 = const i8 32
    store i8 %163, ptr %0
    br bb195
bb163:
    %164 = const i8 31
    store i8 %164, ptr %0
    br bb195
bb164:
    %165 = const i8 30
    store i8 %165, ptr %0
    br bb195
bb165:
    %166 = const i8 29
    store i8 %166, ptr %0
    br bb195
bb166:
    %167 = const i8 28
    store i8 %167, ptr %0
    br bb195
bb167:
    %168 = const i8 27
    store i8 %168, ptr %0
    br bb195
bb168:
    %169 = const i8 26
    store i8 %169, ptr %0
    br bb195
bb169:
    %170 = const i8 25
    store i8 %170, ptr %0
    br bb195
bb170:
    %171 = const i8 24
    store i8 %171, ptr %0
    br bb195
bb171:
    %172 = const i8 23
    store i8 %172, ptr %0
    br bb195
bb172:
    %173 = const i8 22
    store i8 %173, ptr %0
    br bb195
bb173:
    %174 = const i8 21
    store i8 %174, ptr %0
    br bb195
bb174:
    %175 = const i8 20
    store i8 %175, ptr %0
    br bb195
bb175:
    %176 = const i8 19
    store i8 %176, ptr %0
    br bb195
bb176:
    %177 = const i8 18
    store i8 %177, ptr %0
    br bb195
bb177:
    %178 = const i8 17
    store i8 %178, ptr %0
    br bb195
bb178:
    %179 = const i8 16
    store i8 %179, ptr %0
    br bb195
bb179:
    %180 = const i8 15
    store i8 %180, ptr %0
    br bb195
bb180:
    %181 = const i8 14
    store i8 %181, ptr %0
    br bb195
bb181:
    %182 = const i8 13
    store i8 %182, ptr %0
    br bb195
bb182:
    %183 = const i8 12
    store i8 %183, ptr %0
    br bb195
bb183:
    %184 = const i8 11
    store i8 %184, ptr %0
    br bb195
bb184:
    %185 = const i8 10
    store i8 %185, ptr %0
    br bb195
bb185:
    %186 = const i8 9
    store i8 %186, ptr %0
    br bb195
bb186:
    %187 = const i8 8
    store i8 %187, ptr %0
    br bb195
bb187:
    %188 = const i8 7
    store i8 %188, ptr %0
    br bb195
bb188:
    %189 = const i8 6
    store i8 %189, ptr %0
    br bb195
bb189:
    %190 = const i8 5
    store i8 %190, ptr %0
    br bb195
bb190:
    %191 = const i8 4
    store i8 %191, ptr %0
    br bb195
bb191:
    %192 = const i8 3
    store i8 %192, ptr %0
    br bb195
bb192:
    %193 = const i8 2
    store i8 %193, ptr %0
    br bb195
bb193:
    %194 = const i8 1
    store i8 %194, ptr %0
    br bb195
bb194:
    %195 = const i8 0
    store i8 %195, ptr %0
    br bb195
bb195:
    ret
}

fn @x86_opcode_effect(functy.2) {
bb0(%0: ptr, %1: u8):
    %2 = alloca i8, align 1
    store u8 %1, ptr %2
    %3 = load i8, ptr %2
    %4 = bitcast i8 %3 to u8
    switch %4 [ 0: bb23 1: bb23 2: bb26 3: bb23 4: bb23 5: bb26 6: bb23 7: bb23 8: bb26 9: bb22 10: bb22 11: bb23 12: bb23 13: bb23 14: bb21 15: bb21 16: bb19 17: bb19 18: bb19 19: bb19 20: bb19 21: bb19 22: bb19 23: bb18 24: bb18 25: bb18 26: bb18 27: bb18 28: bb18 29: bb16 30: bb16 31: bb26 32: bb26 33: bb26 34: bb26 35: bb25 36: bb25 37: bb25 38: bb25 39: bb16 40: bb16 41: bb16 42: bb16 43: bb16 44: bb15 45: bb15 46: bb26 47: bb25 48: bb15 49: bb17 50: bb17 51: bb17 52: bb26 53: bb17 54: bb17 55: bb26 56: bb6 57: bb6 58: bb24 59: bb24 60: bb24 61: bb6 62: bb13 63: bb13 64: bb13 65: bb13 66: bb13 67: bb13 68: bb16 69: bb26 70: bb25 71: bb17 72: bb26 73: bb25 74: bb13 75: bb13 76: bb13 77: bb13 78: bb13 79: bb13 80: bb16 81: bb26 82: bb25 83: bb17 84: bb13 85: bb13 86: bb13 87: bb13 88: bb13 89: bb13 90: bb13 91: bb13 92: bb26 93: bb26 94: bb14 95: bb14 96: bb12 97: bb12 98: bb12 99: bb12 100: bb12 101: bb12 102: bb10 103: bb10 104: bb10 105: bb10 106: bb10 107: bb17 108: bb10 109: bb9 110: bb8 111: bb24 112: bb11 113: bb11 114: bb11 115: bb11 116: bb25 117: bb26 118: bb5 119: bb4 120: bb3 121: bb3 122: bb16 123: bb26 124: bb14 125: bb22 126: bb6 127: bb12 128: bb12 129: bb7 130: bb7 131: bb7 132: bb19 133: bb19 134: bb19 135: bb19 136: bb13 137: bb13 138: bb13 139: bb16 140: bb13 141: bb26 142: bb25 143: bb13 144: bb13 145: bb13 146: bb13 147: bb13 148: bb13 149: bb13 150: bb13 151: bb13 152: bb13 153: bb13 154: bb13 155: bb3 156: bb13 157: bb13 158: bb13 159: bb26 160: bb13 161: bb13 162: bb3 163: bb13 164: bb3 165: bb13 166: bb13 167: bb13 168: bb13 169: bb13 170: bb13 171: bb3 172: bb3 173: bb13 174: bb13 175: bb13 176: bb20 177: bb20 178: bb13 179: bb13 180: bb13 181: bb13 182: bb13 183: bb13 184: bb13 185: bb13 186: bb13 187: bb13 188: bb13 189: bb2 190: bb2 191: bb2 192: bb2 default: bb1 ]
bb1:
    unreachable
bb2:
    %5 = const i8 0
    store i8 %5, ptr %0
    br bb27
bb3:
    %6 = const i8 0
    store i8 %6, ptr %0
    br bb27
bb4:
    %7 = const i8 2
    store i8 %7, ptr %0
    br bb27
bb5:
    %8 = const i8 0
    store i8 %8, ptr %0
    br bb27
bb6:
    %9 = const i8 0
    store i8 %9, ptr %0
    br bb27
bb7:
    %10 = const i8 2
    store i8 %10, ptr %0
    br bb27
bb8:
    %11 = const i8 2
    store i8 %11, ptr %0
    br bb27
bb9:
    %12 = const i8 2
    store i8 %12, ptr %0
    br bb27
bb10:
    %13 = const i8 0
    store i8 %13, ptr %0
    br bb27
bb11:
    %14 = const i8 0
    store i8 %14, ptr %0
    br bb27
bb12:
    %15 = const i8 0
    store i8 %15, ptr %0
    br bb27
bb13:
    %16 = const i8 0
    store i8 %16, ptr %0
    br bb27
bb14:
    %17 = const i8 0
    store i8 %17, ptr %0
    br bb27
bb15:
    %18 = const i8 0
    store i8 %18, ptr %0
    br bb27
bb16:
    %19 = const i8 0
    store i8 %19, ptr %0
    br bb27
bb17:
    %20 = const i8 0
    store i8 %20, ptr %0
    br bb27
bb18:
    %21 = const i8 0
    store i8 %21, ptr %0
    br bb27
bb19:
    %22 = const i8 0
    store i8 %22, ptr %0
    br bb27
bb20:
    %23 = const i8 0
    store i8 %23, ptr %0
    br bb27
bb21:
    %24 = const i8 0
    store i8 %24, ptr %0
    br bb27
bb22:
    %25 = const i8 0
    store i8 %25, ptr %0
    br bb27
bb23:
    %26 = const i8 0
    store i8 %26, ptr %0
    br bb27
bb24:
    %27 = const i8 3
    store i8 %27, ptr %0
    br bb27
bb25:
    %28 = const i8 2
    store i8 %28, ptr %0
    br bb27
bb26:
    %29 = const i8 1
    store i8 %29, ptr %0
    br bb27
bb27:
    ret
}

fn @mem_effect_tag(functy.3) {
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

fn @MemoryEffect__is_pure(functy.4) {
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

fn @MemoryEffect__reads_memory(functy.5) {
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

fn @MemoryEffect__writes_memory(functy.6) {
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

fn @MemoryEffect__is_barrier(functy.7) {
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

fn @x86_is_removable(functy.8) {
bb0(%0: u8):
    %3 = alloca i8, align 1
    %4 = alloca i8, align 1
    store u8 %0, ptr %3
    %5 = load u8, ptr %3
    call @func.2(%4, %5)
    br bb1
bb1:
    %6 = load u8, ptr %4
    %7 = call @func.4(%6)
    br bb2(%7)
bb2(%1: bool):
    condbr %1, bb3, bb4
bb3:
    %8 = load i8, ptr %3
    %9 = bitcast i8 %8 to u8
    switch %9 [ 29: bb6 30: bb6 39: bb6 40: bb6 41: bb6 42: bb6 43: bb6 44: bb6 45: bb6 48: bb6 68: bb6 80: bb6 96: bb6 97: bb6 98: bb6 99: bb6 100: bb6 101: bb6 108: bb6 112: bb6 113: bb6 114: bb6 115: bb6 118: bb6 120: bb6 122: bb6 127: bb6 128: bb6 132: bb6 133: bb6 134: bb6 135: bb6 136: bb6 137: bb6 138: bb6 139: bb6 140: bb6 145: bb6 146: bb6 147: bb6 148: bb6 149: bb6 150: bb6 151: bb6 152: bb6 153: bb6 154: bb6 157: bb6 158: bb6 160: bb6 161: bb6 163: bb6 164: bb6 167: bb6 168: bb6 169: bb6 170: bb6 default: bb5 ]
bb4:
    %10 = const bool false
    br bb7(%10)
bb5:
    %11 = const bool false
    br bb7(%11)
bb6:
    %12 = const bool true
    br bb7(%12)
bb7(%2: bool):
    ret %2
}

fn @x86_writes_flags(functy.9) {
bb0(%0: u8):
    %2 = alloca i8, align 1
    store u8 %0, ptr %2
    %3 = load i8, ptr %2
    %4 = bitcast i8 %3 to u8
    switch %4 [ 0: bb2 1: bb2 2: bb2 3: bb2 4: bb2 5: bb2 6: bb2 7: bb2 8: bb2 9: bb2 10: bb2 11: bb2 12: bb2 13: bb2 16: bb2 17: bb2 18: bb2 19: bb2 20: bb2 21: bb2 22: bb2 23: bb2 24: bb2 25: bb2 26: bb2 27: bb2 28: bb2 49: bb2 50: bb2 51: bb2 52: bb2 53: bb2 54: bb2 55: bb2 71: bb2 83: bb2 102: bb2 103: bb2 104: bb2 105: bb2 106: bb2 107: bb2 110: bb2 125: bb2 129: bb2 130: bb2 131: bb2 155: bb2 159: bb2 162: bb2 171: bb2 172: bb2 176: bb2 177: bb2 default: bb1 ]
bb1:
    %5 = const bool false
    br bb3(%5)
bb2:
    %6 = const bool true
    br bb3(%6)
bb3(%1: bool):
    ret %1
}

fn @x86_reads_flags(functy.10) {
bb0(%0: u8):
    %2 = alloca i8, align 1
    store u8 %0, ptr %2
    %3 = load i8, ptr %2
    %4 = bitcast i8 %3 to u8
    switch %4 [ 57: bb2 94: bb2 95: bb2 124: bb2 176: bb2 177: bb2 default: bb1 ]
bb1:
    %5 = const bool false
    br bb3(%5)
bb2:
    %6 = const bool true
    br bb3(%6)
bb3(%1: bool):
    ret %1
}

fn @x86_produces_value(functy.11) {
bb0(%0: u8):
    %2 = alloca i8, align 1
    store u8 %0, ptr %2
    %3 = load i8, ptr %2
    %4 = bitcast i8 %3 to u8
    switch %4 [ 9: bb2 10: bb2 14: bb2 15: bb2 35: bb2 36: bb2 37: bb2 38: bb2 47: bb2 49: bb2 50: bb2 51: bb2 52: bb2 53: bb2 54: bb2 55: bb2 56: bb2 57: bb2 58: bb2 59: bb2 60: bb2 61: bb2 70: bb2 71: bb2 73: bb2 82: bb2 83: bb2 107: bb2 110: bb2 111: bb2 116: bb2 119: bb2 120: bb2 121: bb2 125: bb2 126: bb2 142: bb2 159: bb2 189: bb2 190: bb2 191: bb2 192: bb2 default: bb1 ]
bb1:
    %5 = const bool false
    br bb3(%5)
bb2:
    %6 = const bool true
    br bb3(%6)
bb3(%1: bool):
    %7 = const bool false
    %8 = icmp eq bool %1, %7
    ret %8
}
"####;

/// VERBATIM MIR-closure emit of `sr_props_root` (is_power_of_two /
/// shift_amount_in_width / shift_amount); slice trust_strength_reduce_slice.rs.
/// 2725 bytes; 4 members; validate 0; re-parse OK; EXTERN-FREE.
const SR_IR: &str = r####"; TrustIr text format v1
module "mir::closure::sr_props_root"
target "aarch64-apple-darwin" 8 little
file 0 "trust_strength_reduce_slice.rs"

functy.0 = (u64, i64, i64, i64, ptr) -> ()

functy.1 = (u64) -> (bool)

functy.2 = (i64, i64) -> (bool)

functy.3 = (ptr, i64, i64) -> ()

fn @sr_props_root(functy.0) {
bb0(%0: u64, %1: i64, %2: i64, %3: i64, %4: ptr):
    %17 = alloca (i32, i32), align 4
    %18 = call @func.1(%0)
    br bb1(%1, %2, %3, %4, %18)
bb1(%5: i64, %6: i64, %7: i64, %8: ptr, %9: bool):
    %19 = const u32 1
    %20 = const u32 0
    %21 = select u32 %9, %19, %20
    store u32 %21, ptr %8
    %22 = call @func.2(%5, %6)
    br bb2(%5, %7, %8, %22)
bb2(%10: i64, %11: i64, %12: ptr, %13: bool):
    %23 = const u32 1
    %24 = const u32 0
    %25 = select u32 %13, %23, %24
    %26 = const i64 4
    %27 = gep i8, ptr %12, %26
    store u32 %25, ptr %27
    call @func.3(%17, %10, %11)
    br bb3(%12)
bb3(%14: ptr):
    %28 = load i32, ptr %17
    %29 = sext i32 %28 to i64
    switch %29 [ 0: bb5(%14) 1: bb6(%14) default: bb4 ]
bb4:
    unreachable
bb5(%15: ptr):
    %30 = const u32 0
    %31 = const i64 8
    %32 = gep i8, ptr %15, %31
    store u32 %30, ptr %32
    %33 = const u32 0
    %34 = const i64 12
    %35 = gep i8, ptr %15, %34
    store u32 %33, ptr %35
    br bb7
bb6(%16: ptr):
    %36 = const i64 4
    %37 = gep i8, ptr %17, %36
    %38 = load u32, ptr %37
    %39 = const u32 1
    %40 = const i64 8
    %41 = gep i8, ptr %16, %40
    store u32 %39, ptr %41
    %42 = const i64 12
    %43 = gep i8, ptr %16, %42
    store u32 %38, ptr %43
    br bb7
bb7:
    ret
}

fn @is_power_of_two(functy.1) {
bb0(%0: u64):
    %3 = const u64 0
    %4 = icmp ne u64 %0, %3
    condbr %4, bb1(%0), bb2
bb1(%1: u64):
    %5 = const u64 1
    %6 = sub u64 %1, %5
    %7 = and u64 %1, %6
    %8 = const u64 0
    %9 = icmp eq u64 %7, %8
    br bb3(%9)
bb2:
    %10 = const bool false
    br bb3(%10)
bb3(%2: bool):
    ret %2
}

fn @shift_amount_in_width(functy.2) {
bb0(%0: i64, %1: i64):
    %5 = const i64 1
    %6 = icmp sge i64 %0, %5
    condbr %6, bb1(%0, %1), bb2
bb1(%2: i64, %3: i64):
    %7 = icmp slt i64 %2, %3
    br bb3(%7)
bb2:
    %8 = const bool false
    br bb3(%8)
bb3(%4: bool):
    ret %4
}

fn @shift_amount(functy.3) {
bb0(%0: ptr, %1: i64, %2: i64):
    %6 = const i64 0
    %7 = icmp sge i64 %1, %6
    condbr %7, bb1(%1, %2), bb3
bb1(%3: i64, %4: i64):
    %8 = icmp sle i64 %3, %4
    condbr %8, bb2(%3), bb3
bb2(%5: i64):
    %9 = trunc i64 %5 to u32
    %10 = const i64 4
    %11 = gep i8, ptr %0, %10
    store u32 %9, ptr %11
    %12 = const i32 1
    store i32 %12, ptr %0
    br bb4
bb3:
    %13 = const i32 0
    store i32 %13, ptr %0
    br bb4
bb4:
    ret
}
"####;

/// Historical MIR-closure emit of `movn_props_root`
/// (`single_movn_materialization`) from pinned slice revision b2c58eb. It is
/// retained as an F4 frontend/JIT regression and does not model the current
/// hw0-only MOVN materializer. 4316 bytes; validate 0; F4-PINNED
/// (UnresolvedSymbol at JIT link — the array `into_iter` empty leaf).
const MOVN_IR: &str = r####"; TrustIr text format v1
module "mir::closure::movn_props_root"
target "aarch64-apple-darwin" 8 little
file 0 "trust_const_materialize_slice.rs"

functy.0 = (u64, ptr) -> ()

functy.1 = (ptr, ptr) -> ()

functy.2 = (ptr, ptr) -> ()

functy.3 = (ptr, u64) -> ()

fn @movn_props_root(functy.0) {
bb0(%0: u64, %1: ptr):
    %5 = alloca (i64, i64, i64), align 8
    call @func.3(%5, %0)
    br bb1(%1)
bb1(%2: ptr):
    %6 = load i64, ptr %5
    switch %6 [ 0: bb3(%2) 1: bb4(%2) default: bb2 ]
bb2:
    unreachable
bb3(%3: ptr):
    %7 = const u32 0
    store u32 %7, ptr %3
    %8 = const u32 0
    %9 = const i64 4
    %10 = gep i8, ptr %3, %9
    store u32 %8, ptr %10
    %11 = const u32 0
    %12 = const i64 8
    %13 = gep i8, ptr %3, %12
    store u32 %11, ptr %13
    br bb5
bb4(%4: ptr):
    %14 = const i64 8
    %15 = gep i8, ptr %5, %14
    %16 = load u16, ptr %15
    %17 = const i64 16
    %18 = gep i8, ptr %5, %17
    %19 = load u64, ptr %18
    %20 = const u32 1
    store u32 %20, ptr %4
    %21 = zext u16 %16 to u32
    %22 = const i64 4
    %23 = gep i8, ptr %4, %22
    store u32 %21, ptr %23
    %24 = trunc u64 %19 to u32
    %25 = const i64 8
    %26 = gep i8, ptr %4, %25
    store u32 %24, ptr %26
    br bb5
bb5:
    ret
}

fn @_RNvXs_NtNtCs2EYQwhfuABO_4core5array4iterAyj4_NtNtNtNtB8_4iter6traits7collect12IntoIterator9into_iterCsd0PXGAomuj0_29trust_const_materialize_slice(functy.1) {
}

fn @_RNvXs2_NtNtCs2EYQwhfuABO_4core5array4iterINtB5_8IntoIteryKj4_ENtNtNtNtB9_4iter6traits8iterator8Iterator4nextCsd0PXGAomuj0_29trust_const_materialize_slice(functy.2) {
}

fn @single_movn_materialization(functy.3) {
bb0(%0: ptr, %1: u64):
    %8 = alloca (i64, i64, i64, i64, i64, i64), align 8
    %9 = alloca (i64, i64, i64, i64), align 8
    %10 = alloca (i64, i64, i64, i64, i64, i64), align 8
    %11 = alloca (i64, i64), align 8
    %12 = alloca (i64, i64), align 8
    %13 = not u64 %1
    %14 = const u64 0
    store u64 %14, ptr %9
    %15 = const u64 16
    %16 = const i64 8
    %17 = gep i8, ptr %9, %16
    store u64 %15, ptr %17
    %18 = const u64 32
    %19 = const i64 16
    %20 = gep i8, ptr %9, %19
    store u64 %18, ptr %20
    %21 = const u64 48
    %22 = const i64 24
    %23 = gep i8, ptr %9, %22
    store u64 %21, ptr %23
    call @func.1(%8, %9)
    br bb1(%13)
bb1(%2: u64):
    %24 = load i64, ptr %8
    store i64 %24, ptr %10
    %25 = const i64 8
    %26 = gep i8, ptr %8, %25
    %27 = const i64 8
    %28 = gep i8, ptr %10, %27
    %29 = load i64, ptr %26
    store i64 %29, ptr %28
    %30 = const i64 16
    %31 = gep i8, ptr %8, %30
    %32 = const i64 16
    %33 = gep i8, ptr %10, %32
    %34 = load i64, ptr %31
    store i64 %34, ptr %33
    %35 = const i64 24
    %36 = gep i8, ptr %8, %35
    %37 = const i64 24
    %38 = gep i8, ptr %10, %37
    %39 = load i64, ptr %36
    store i64 %39, ptr %38
    %40 = const i64 32
    %41 = gep i8, ptr %8, %40
    %42 = const i64 32
    %43 = gep i8, ptr %10, %42
    %44 = load i64, ptr %41
    store i64 %44, ptr %43
    %45 = const i64 40
    %46 = gep i8, ptr %8, %45
    %47 = const i64 40
    %48 = gep i8, ptr %10, %47
    %49 = load i64, ptr %46
    store i64 %49, ptr %48
    br bb2(%2)
bb2(%3: u64):
    call @func.2(%11, %10)
    br bb3(%3)
bb3(%4: u64):
    %50 = load i64, ptr %11
    switch %50 [ 0: bb6 1: bb5(%4) default: bb4 ]
bb4:
    unreachable
bb5(%5: u64):
    %51 = const i64 8
    %52 = gep i8, ptr %11, %51
    %53 = load u64, ptr %52
    %54 = const u64 65535
    %55 = shl u64 %54, %53
    %56 = not u64 %55
    %57 = and u64 %5, %56
    %58 = const u64 0
    %59 = icmp eq u64 %57, %58
    condbr %59, bb7(%5, %53), bb2(%5)
bb6:
    br bb8
bb7(%6: u64, %7: u64):
    %60 = lshr u64 %6, %7
    %61 = const u64 65535
    %62 = and u64 %60, %61
    %63 = trunc u64 %62 to u16
    store u16 %63, ptr %12
    %64 = const i64 8
    %65 = gep i8, ptr %12, %64
    store u64 %7, ptr %65
    %66 = const i64 8
    %67 = gep i8, ptr %0, %66
    %68 = load i64, ptr %12
    store i64 %68, ptr %67
    %69 = const i64 8
    %70 = gep i8, ptr %12, %69
    %71 = const i64 8
    %72 = gep i8, ptr %67, %71
    %73 = load i64, ptr %70
    store i64 %73, ptr %72
    %74 = const i64 1
    store i64 %74, ptr %0
    br bb9
bb8:
    %75 = const i64 0
    store i64 %75, ptr %0
    br bb9
bb9:
    ret
}
"####;

/// VERBATIM MIR-closure emit of `chunks_root` (move_wide_chunks);
/// slice trust_const_materialize_slice.rs. 5685 bytes; validate 0; F4-PINNED
/// (UnresolvedSymbol at JIT link — the slice `iter_mut` empty leaf).
const CHUNKS_IR: &str = r####"; TrustIr text format v1
module "mir::closure::chunks_root"
target "aarch64-apple-darwin" 8 little
file 0 "trust_const_materialize_slice.rs"

functy.0 = (u64, u32, ptr) -> ()

functy.1 = (ptr, ptr) -> ()

functy.2 = (ptr, ptr) -> ()

functy.3 = (ptr, ptr, u64) -> ()

functy.4 = (ptr, ptr) -> ()

functy.5 = (ptr, ptr) -> ()

functy.6 = (ptr, i64, u64) -> ()

fn @chunks_root(functy.0) {
bb0(%0: u64, %1: u32, %2: ptr):
    %12 = alloca (i16, i16, i16, i16), align 2
    %13 = bitcast u64 %0 to i64
    %14 = zext u32 %1 to u64
    call @func.6(%12, %13, %14)
    br bb1(%2)
bb1(%3: ptr):
    %15 = const u64 0
    %16 = const u64 4
    %17 = icmp ult u64 %15, %16
    condbr %17, bb2(%3, %15), bb6
bb2(%4: ptr, %5: u64):
    %18 = gep u16, ptr %12, %5
    %19 = load u16, ptr %18
    %20 = zext u16 %19 to u32
    store u32 %20, ptr %4
    %21 = const u64 1
    %22 = const u64 4
    %23 = icmp ult u64 %21, %22
    condbr %23, bb3(%4, %21), bb6
bb3(%6: ptr, %7: u64):
    %24 = gep u16, ptr %12, %7
    %25 = load u16, ptr %24
    %26 = zext u16 %25 to u32
    %27 = const i64 4
    %28 = gep i8, ptr %6, %27
    store u32 %26, ptr %28
    %29 = const u64 2
    %30 = const u64 4
    %31 = icmp ult u64 %29, %30
    condbr %31, bb4(%6, %29), bb6
bb4(%8: ptr, %9: u64):
    %32 = gep u16, ptr %12, %9
    %33 = load u16, ptr %32
    %34 = zext u16 %33 to u32
    %35 = const i64 8
    %36 = gep i8, ptr %8, %35
    store u32 %34, ptr %36
    %37 = const u64 3
    %38 = const u64 4
    %39 = icmp ult u64 %37, %38
    condbr %39, bb5(%8, %37), bb6
bb5(%10: ptr, %11: u64):
    %40 = gep u16, ptr %12, %11
    %41 = load u16, ptr %40
    %42 = zext u16 %41 to u32
    %43 = const i64 12
    %44 = gep i8, ptr %10, %43
    store u32 %42, ptr %44
    ret
bb6:
    unreachable
}

fn @_RNvMNtCs2EYQwhfuABO_4core5sliceSt8iter_mutCsd0PXGAomuj0_29trust_const_materialize_slice(functy.1) {
}

fn @_RNvYINtNtNtCs2EYQwhfuABO_4core5slice4iter7IterMuttENtNtNtNtB9_4iter6traits8iterator8Iterator9enumerateCsd0PXGAomuj0_29trust_const_materialize_slice(functy.2) {
}

fn @_RNvYINtNtNtNtCs2EYQwhfuABO_4core4iter8adapters9enumerate9EnumerateINtNtNtBb_5slice4iter7IterMuttEENtNtNtB9_6traits8iterator8Iterator4takeCsd0PXGAomuj0_29trust_const_materialize_slice(functy.3) {
}

fn @_RNvXNtNtNtCs2EYQwhfuABO_4core4iter6traits7collectINtNtNtB6_8adapters4take4TakeINtNtBQ_9enumerate9EnumerateINtNtNtB8_5slice4iter7IterMuttEEENtB2_12IntoIterator9into_iterCsd0PXGAomuj0_29trust_const_materialize_slice(functy.4) {
}

fn @_RNvXs_NtNtNtCs2EYQwhfuABO_4core4iter8adapters4takeINtB4_4TakeINtNtB6_9enumerate9EnumerateINtNtNtBa_5slice4iter7IterMuttEEENtNtNtB8_6traits8iterator8Iterator4nextCsd0PXGAomuj0_29trust_const_materialize_slice(functy.5) {
}

fn @move_wide_chunks(functy.6) {
bb0(%0: ptr, %1: i64, %2: u64):
    %12 = alloca (i16, i16, i16, i16), align 2
    %13 = alloca (i64, i64, i64, i64), align 8
    %14 = alloca (i64, i64, i64, i64), align 8
    %15 = alloca (i64, i64, i64), align 8
    %16 = alloca (i64, i64), align 8
    %17 = alloca (i64, i64), align 8
    %18 = alloca (i64, i64, i64, i64), align 8
    %19 = alloca (i64, i64), align 8
    %20 = bitcast i64 %1 to u64
    %21 = const u16 0
    store u16 %21, ptr %12
    %22 = const u16 0
    %23 = const i64 2
    %24 = gep i8, ptr %12, %23
    store u16 %22, ptr %24
    %25 = const u16 0
    %26 = const i64 4
    %27 = gep i8, ptr %12, %26
    store u16 %25, ptr %27
    %28 = const u16 0
    %29 = const i64 6
    %30 = gep i8, ptr %12, %29
    store u16 %28, ptr %30
    store ptr %12, ptr %17
    %31 = const i64 8
    %32 = gep i8, ptr %17, %31
    %33 = const u64 4
    store u64 %33, ptr %32
    call @func.1(%16, %17)
    br bb1(%2, %20)
bb1(%3: u64, %4: u64):
    call @func.2(%15, %16)
    br bb2(%3, %4)
bb2(%5: u64, %6: u64):
    call @func.3(%14, %15, %5)
    br bb3(%6)
bb3(%7: u64):
    call @func.4(%13, %14)
    br bb4(%7)
bb4(%8: u64):
    %34 = load i64, ptr %13
    store i64 %34, ptr %18
    %35 = const i64 8
    %36 = gep i8, ptr %13, %35
    %37 = const i64 8
    %38 = gep i8, ptr %18, %37
    %39 = load i64, ptr %36
    store i64 %39, ptr %38
    %40 = const i64 16
    %41 = gep i8, ptr %13, %40
    %42 = const i64 16
    %43 = gep i8, ptr %18, %42
    %44 = load i64, ptr %41
    store i64 %44, ptr %43
    %45 = const i64 24
    %46 = gep i8, ptr %13, %45
    %47 = const i64 24
    %48 = gep i8, ptr %18, %47
    %49 = load i64, ptr %46
    store i64 %49, ptr %48
    br bb5(%8)
bb5(%9: u64):
    call @func.5(%19, %18)
    br bb6(%9)
bb6(%10: u64):
    %50 = const i64 8
    %51 = gep i8, ptr %19, %50
    %52 = load i64, ptr %51
    %53 = const i64 0
    %54 = icmp eq i64 %52, %53
    %55 = const i64 0
    %56 = const i64 1
    %57 = select i64 %54, %55, %56
    switch %57 [ 0: bb9 1: bb8(%10) default: bb7 ]
bb7:
    unreachable
bb8(%11: u64):
    %58 = load u64, ptr %19
    %59 = const i64 8
    %60 = gep i8, ptr %19, %59
    %61 = load ptr, ptr %60
    %62 = const u64 16
    %63 = mul u64 %58, %62
    %64 = lshr u64 %11, %63
    %65 = const u64 65535
    %66 = and u64 %64, %65
    %67 = trunc u64 %66 to u16
    store u16 %67, ptr %61
    br bb5(%11)
bb9:
    %68 = load i16, ptr %12
    store i16 %68, ptr %0
    %69 = const i64 2
    %70 = gep i8, ptr %12, %69
    %71 = const i64 2
    %72 = gep i8, ptr %0, %71
    %73 = load i16, ptr %70
    store i16 %73, ptr %72
    %74 = const i64 4
    %75 = gep i8, ptr %12, %74
    %76 = const i64 4
    %77 = gep i8, ptr %0, %76
    %78 = load i16, ptr %75
    store i16 %78, ptr %77
    %79 = const i64 6
    %80 = gep i8, ptr %12, %79
    %81 = const i64 6
    %82 = gep i8, ptr %0, %81
    %83 = load i16, ptr %80
    store i16 %83, ptr %82
    ret
}
"####;

/// VERBATIM MIR-closure emit of the historical `pow2_props_root` peephole
/// fixture in trust_const_materialize_slice.rs. 1576 bytes; validate 0;
/// F4-PINNED (UnresolvedSymbol at JIT link — the `trailing_zeros` empty leaf).
const POW2_IR: &str = r####"; TrustIr text format v1
module "mir::closure::pow2_props_root"
target "aarch64-apple-darwin" 8 little
file 0 "trust_const_materialize_slice.rs"

functy.0 = (i64, ptr) -> ()

functy.1 = (i64) -> (u32)

functy.2 = (ptr, i64) -> ()

fn @pow2_props_root(functy.0) {
bb0(%0: i64, %1: ptr):
    %5 = alloca (i32, i32), align 4
    call @func.2(%5, %0)
    br bb1(%1)
bb1(%2: ptr):
    %6 = load i32, ptr %5
    %7 = sext i32 %6 to i64
    switch %7 [ 0: bb3(%2) 1: bb4(%2) default: bb2 ]
bb2:
    unreachable
bb3(%3: ptr):
    %8 = const u32 0
    store u32 %8, ptr %3
    %9 = const u32 0
    %10 = const i64 4
    %11 = gep i8, ptr %3, %10
    store u32 %9, ptr %11
    br bb5
bb4(%4: ptr):
    %12 = const i64 4
    %13 = gep i8, ptr %5, %12
    %14 = load u32, ptr %13
    %15 = const u32 1
    store u32 %15, ptr %4
    %16 = const i64 4
    %17 = gep i8, ptr %4, %16
    store u32 %14, ptr %17
    br bb5
bb5:
    ret
}

fn @_RNvMs1_NtCs2EYQwhfuABO_4core3numx14trailing_zeros(functy.1) {
}

fn @is_power_of_two(functy.2) {
bb0(%0: ptr, %1: i64):
    %5 = const i64 0
    %6 = icmp sgt i64 %1, %5
    condbr %6, bb1(%1), bb4
bb1(%2: i64):
    %7 = const i64 1
    %8 = sub i64 %2, %7
    %9 = and i64 %2, %8
    %10 = const i64 0
    %11 = icmp eq i64 %9, %10
    condbr %11, bb2(%2), bb4
bb2(%3: i64):
    %12 = call @func.1(%3)
    br bb3(%12)
bb3(%4: u32):
    %13 = const i64 4
    %14 = gep i8, ptr %0, %13
    store u32 %4, ptr %14
    %15 = const i32 1
    store i32 %15, ptr %0
    br bb5
bb4:
    %16 = const i32 0
    store i32 %16, ptr %0
    br bb5
bb5:
    ret
}
"####;
