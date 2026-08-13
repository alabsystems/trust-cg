//! TRUST-SELF ROUND 33: AUDIT THE x86-64 fcmp CONDITION-CODE LOWERING FOR A
//! NaN BUG — the x86 analog of the aarch64 owner-#10 `fcmp one` miscompile.
//!
//! THE AARCH64 BUG (owner #10, rounds 31/32): `select_fcmp` lowers ordered
//! not-equal (`FloatCC::NotEqual`) to a bare `CSET NE`. A NaN `FCMP` sets
//! NZCV=0b0011 (Z=0), so `CSET NE` yields 1 — but IEEE ordered `!=` must be
//! FALSE on NaN. The blast radius (bare/select/branch) all consume that one
//! wrong boolean; a single fix at `from_floatcc`/`select_fcmp` corrects it.
//!
//! THIS ROUND asks: does the x86-64 backend have an fcmp-one-ANALOGOUS bug —
//! an `FloatCC` whose x86 lowering gives the WRONG answer on a NaN operand?
//! x86 uses a DIFFERENT flag model: `UCOMISD` sets ZF=PF=CF=1 on an unordered
//! (NaN) compare, and the PARITY flag PF is the unordered signal. So x86's
//! NaN bugs would be distinct from aarch64's.
//!
//! VERIFICATION PATH: (b) — x86 machine code CANNOT be executed on this
//! aarch64 host. `tests/e2e_x86_64_triple_oracle.rs` (and its `x86_64_corpus`
//! gate `x86_64_oracle_enabled` → `is_x86_64()` = `cfg!(target_arch="x86_64")`)
//! EARLY-RETURNS on aarch64: there is no x86 emulator/Rosetta path that flips
//! `cfg!(target_arch)`. So instead of running x86, we verify the x86 fcmp
//! CC-MAPPING LOGIC as a pure integer function:
//!   * native == JIT: the mapping table + UCOMISD flag model + SETcc evaluator
//!     + the SETcc/AND-SETNP/OR-SETP composition are transcribed VERBATIM from
//!       `x86_64_isel.rs` into a slice, emitted via the stage1 emit-closure
//!       frontend, and JIT-compiled by trust-cg on this aarch64 host — proving
//!       TRUST ITSELF compiles the mapping faithfully.
//!   * DUAL ORACLE: the LINKED PRODUCTION `trust_cg_lower::x86_float_cmp_strategy`
//!     is composed the same way in-process; JIT must equal it (catches
//!     transcription drift).
//!   * IEEE ORACLE (independent): a first-principles ordered/unordered NaN-rule
//!     oracle (ordered=false-on-NaN, unordered=true-on-NaN). JIT must equal it
//!     over the FULL {14 FloatCC} × {lhs<rhs, ==, >, NaN} = 56-cell matrix.
//!
//! WHAT THE AUDIT READS (the REAL table — not invented; x86_64_isel.rs):
//!   `x86_float_cmp_strategy` (:649) maps all 14 `FloatCC` to one of:
//!     SingleCC(cc)     — SETcc                     (:8579)
//!     AndNotParity(cc) — SETcc && SETNP  (ordered, exclude NaN)  (:8593)
//!     OrParity(cc)     — SETcc || SETP   (unordered, include NaN)(:8628)
//!   `select_fcmp` (:8549) emits exactly those sequences and defines a B1
//!   boolean. The deprecated bare `x86cc_from_floatcc` (:680, drops parity) is
//!   called ONLY in unit tests — NEVER in real lowering. Both consumers,
//!   `select_condbranch` (:10570, CMP+Jcc NE) and `select_select` (:7061,
//!   CMP+CMOVcc), read the MATERIALIZED boolean — there is NO fused
//!   float-condition Jcc/CMOV path (same structure as aarch64: one fix point).
//!
//! RESULT (see the per-predicate verdict test): CLEAN BILL. Every one of the 14
//! predicates is IEEE-correct on NaN AND on the ordered cases. The reason x86 is
//! clean where aarch64 is buggy: (1) NaN sets ZF=1 so `SETNE`/ordered-`!=` is
//! already FALSE (the direct analog cell); and (2) x86 EXPLICITLY parity-guards
//! the predicates that need it (Equal/LessThan/LessThanOrEqual via AND-SETNP;
//! UnorderedNotEqual/UnorderedGreaterThan/UnorderedGreaterThanOrEqual via
//! OR-SETP), whereas aarch64 only special-cased UnorderedEqual.
//!
//! FAIL-LOUD CONTROLS prove the audit is not vacuous:
//!   * `..._parity_guard_load_bearing`: if the parity fixup were dropped (bare
//!     SingleCC for every predicate — the x86 analog of the aarch64 bare CSET),
//!     the IEEE oracle catches a NaN miscompile on EXACTLY 6 of the 7
//!     parity-guarded predicates.
//!   * `..._buggy_jit_miscompiles_equal_on_nan`: a MUTATED slice (Equal →
//!     bare SingleCC(E)) JIT-compiled through the SAME pipeline miscompiles the
//!     Equal/NaN cell (JIT=true vs IEEE=false) — the machine-code path would
//!     surface a real x86 table bug.
//!   * `..._aarch64_bug_is_x86_clean`: the aarch64 wrong answer for ONe(NaN)
//!     (=true) is REFUTED by the x86 lowering (=false), on both JIT and IEEE.
//!
//! Slice (VERBATIM transcription): tests/slices/trust_x86_fcmp_cc_audit_slice.rs.
//! Fixtures (emit-closure @ stage1): tests/slices/trust_x86_fcmp_cc_audit.tir,
//! tests/slices/trust_x86_fcmp_cc_audit_buggy.tir (control). Both validate=0,
//! EXTERN-FREE, re-parse OK.
//!
//! INVENTORY: this is a PURE AUDIT of an existing table (no NEW Trust production
//! fn de-modeled beyond `x86_float_cmp_strategy`, already covered by the R16 x86
//! condcode round's family); Trust-itself inventory UNCHANGED at ~250.
//!
//! COVERAGE NOTE: gated to aarch64 (the JIT target). Run ONE AT A TIME
//! (`--test-threads=1`): the JIT engine is not thread-safe at suite scale.

#![cfg(target_arch = "aarch64")]

use std::collections::HashMap;
use std::sync::mpsc;
use std::time::Duration;

use trust_cg_codegen::Target;
use trust_cg_codegen::compiler::{Compiler, CompilerConfig};

use trust_cg_ir::X86CondCode as ProdCc;
use trust_cg_lower::instructions::FloatCC as ProdFcc;
use trust_cg_lower::{X86FloatCmpStrategy, x86_float_cmp_strategy};

// ── embedded emit-closure fixtures ───────────────────────────────────────────
const X86_FCMP_AUDIT_IR: &str = include_str!("slices/trust_x86_fcmp_cc_audit.tir");
const X86_FCMP_BUGGY_IR: &str = include_str!("slices/trust_x86_fcmp_cc_audit_buggy.tir");

// ── shared harness (round-16/18 pattern) ─────────────────────────────────────

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

// ── POD mirror of the slice `FcmpAuditProps` ─────────────────────────────────
#[repr(C)]
#[derive(Clone, Copy, Debug, PartialEq)]
struct FcmpAuditRow {
    strat_kind: u32,
    strat_cc: u32,
    cf: u32,
    zf: u32,
    pf: u32,
    x86_lowered: u32,
}

impl FcmpAuditRow {
    fn poisoned() -> Self {
        FcmpAuditRow {
            strat_kind: 0xDEAD,
            strat_cc: 0xDEAD,
            cf: 0xDEAD,
            zf: 0xDEAD,
            pf: 0xDEAD,
            x86_lowered: 0xDEAD,
        }
    }
}

// The 14 FloatCC tags (matches the slice `floatcc_from_tag` decoder order).
const N_FCC: u32 = 14;
// The 4 UCOMISD scenarios: 0=Less(lhs<rhs) 1=Equal 2=Greater 3=Unordered/NaN.
const N_SCEN: u32 = 4;

fn prod_fcc_from_tag(tag: u32) -> ProdFcc {
    match tag {
        0 => ProdFcc::Equal,
        1 => ProdFcc::NotEqual,
        2 => ProdFcc::LessThan,
        3 => ProdFcc::LessThanOrEqual,
        4 => ProdFcc::GreaterThan,
        5 => ProdFcc::GreaterThanOrEqual,
        6 => ProdFcc::Ordered,
        7 => ProdFcc::Unordered,
        8 => ProdFcc::UnorderedEqual,
        9 => ProdFcc::UnorderedNotEqual,
        10 => ProdFcc::UnorderedLessThan,
        11 => ProdFcc::UnorderedLessThanOrEqual,
        12 => ProdFcc::UnorderedGreaterThan,
        _ => ProdFcc::UnorderedGreaterThanOrEqual,
    }
}

fn fcc_name(tag: u32) -> &'static str {
    match tag {
        0 => "Equal",
        1 => "NotEqual",
        2 => "LessThan",
        3 => "LessThanOrEqual",
        4 => "GreaterThan",
        5 => "GreaterThanOrEqual",
        6 => "Ordered",
        7 => "Unordered",
        8 => "UnorderedEqual",
        9 => "UnorderedNotEqual",
        10 => "UnorderedLessThan",
        11 => "UnorderedLessThanOrEqual",
        12 => "UnorderedGreaterThan",
        _ => "UnorderedGreaterThanOrEqual",
    }
}

fn scen_name(s: u32) -> &'static str {
    match s {
        0 => "lhs<rhs",
        1 => "lhs==rhs",
        2 => "lhs>rhs",
        _ => "NaN(unordered)",
    }
}

// ── the faithful UCOMISD flag model (Intel SDM Vol.1 §8.1.2) ──────────────────
// Returns (cf, zf, pf).
fn ucomisd_flags(scenario: u32) -> (bool, bool, bool) {
    match scenario {
        0 => (true, false, false),  // Less:    CF=1,ZF=0,PF=0
        1 => (false, true, false),  // Equal:   CF=0,ZF=1,PF=0
        2 => (false, false, false), // Greater: CF=0,ZF=0,PF=0
        _ => (true, true, true),    // NaN:     CF=1,ZF=1,PF=1
    }
}

// ── SETcc flag semantics per X86CondCode 4-bit encoding ──────────────────────
fn eval_setcc_tag(cc_tag: u32, cf: bool, zf: bool, pf: bool) -> bool {
    match cc_tag {
        0x4 => zf,         // E
        0x5 => !zf,        // NE
        0x2 => cf,         // B
        0x3 => !cf,        // AE
        0x6 => cf || zf,   // BE
        0x7 => !cf && !zf, // A
        0xA => pf,         // P
        0xB => !pf,        // NP
        other => panic!("eval_setcc_tag: cc {other:#x} not reachable on the fcmp domain"),
    }
}

// ── native lowering using the LINKED PRODUCTION strategy (dual oracle) ────────
// Composes exactly as select_fcmp emits: SingleCC → SETcc; AndNotParity →
// SETcc && SETNP; OrParity → SETcc || SETP.
fn prod_strategy_kind_cc(fcc: ProdFcc) -> (u32, u32) {
    match x86_float_cmp_strategy(fcc) {
        X86FloatCmpStrategy::SingleCC(c) => (0, c.encoding() as u32),
        X86FloatCmpStrategy::AndNotParity(c) => (1, c.encoding() as u32),
        X86FloatCmpStrategy::OrParity(c) => (2, c.encoding() as u32),
    }
}

fn native_x86_lowered(fcc: ProdFcc, scenario: u32) -> bool {
    let (cf, zf, pf) = ucomisd_flags(scenario);
    match x86_float_cmp_strategy(fcc) {
        X86FloatCmpStrategy::SingleCC(c) => eval_setcc_tag(c.encoding() as u32, cf, zf, pf),
        X86FloatCmpStrategy::AndNotParity(c) => {
            eval_setcc_tag(c.encoding() as u32, cf, zf, pf)
                && eval_setcc_tag(ProdCc::NP.encoding() as u32, cf, zf, pf)
        }
        X86FloatCmpStrategy::OrParity(c) => {
            eval_setcc_tag(c.encoding() as u32, cf, zf, pf)
                || eval_setcc_tag(ProdCc::P.encoding() as u32, cf, zf, pf)
        }
    }
}

// ── the INDEPENDENT IEEE oracle (first-principles ordered/unordered rules) ────
// scenario: 0=lhs<rhs 1=lhs==rhs 2=lhs>rhs 3=NaN(unordered). Ordered predicates
// are FALSE on NaN; unordered predicates are TRUE on NaN — derived from the
// comparison meaning, NOT from any x86 flag reasoning.
fn ieee_oracle(fcc_tag: u32, scenario: u32) -> bool {
    let lt = scenario == 0;
    let eq = scenario == 1;
    let gt = scenario == 2;
    let uno = scenario == 3;
    match fcc_tag {
        0 => eq,               // Equal  (OEQ)
        1 => lt || gt,         // NotEqual (ONE = ordered && a!=b)
        2 => lt,               // LessThan (OLT)
        3 => lt || eq,         // LessThanOrEqual (OLE)
        4 => gt,               // GreaterThan (OGT)
        5 => gt || eq,         // GreaterThanOrEqual (OGE)
        6 => !uno,             // Ordered (neither NaN)
        7 => uno,              // Unordered (some NaN)
        8 => eq || uno,        // UnorderedEqual (UEQ)
        9 => lt || gt || uno,  // UnorderedNotEqual (UNE)
        10 => lt || uno,       // UnorderedLessThan (ULT)
        11 => lt || eq || uno, // UnorderedLessThanOrEqual (ULE)
        12 => gt || uno,       // UnorderedGreaterThan (UGT)
        _ => gt || eq || uno,  // UnorderedGreaterThanOrEqual (UGE)
    }
}

// ── JIT sweep of the full 56-cell matrix ─────────────────────────────────────
fn jit_audit_rows(
    ir: &'static str,
    root_sym: &'static str,
    what: &'static str,
) -> Vec<((u32, u32), FcmpAuditRow)> {
    let expected = (N_FCC * N_SCEN) as usize;
    run_watchdogged::<((u32, u32), FcmpAuditRow)>(what, expected, move |tx| {
        let buffer = jit_module(ir, what);
        // SAFETY: machine code for functy.0 = (u32, u32, ptr) -> ().
        let f: unsafe extern "C" fn(u32, u32, *mut FcmpAuditRow) =
            unsafe { std::mem::transmute(bind(&buffer, root_sym)) };
        for tag in 0..N_FCC {
            for scen in 0..N_SCEN {
                let mut out = FcmpAuditRow::poisoned();
                unsafe { f(tag, scen, &mut out) };
                if tx.send(((tag, scen), out)).is_err() {
                    return;
                }
            }
        }
    })
}

// ============================================================================
// TEST 1 — the 56-cell triple oracle: native(production) == JIT == IEEE.
// ============================================================================
#[test]
fn x86_fcmp_cc_table_native_eq_jit_eq_ieee() {
    let rows = jit_audit_rows(X86_FCMP_AUDIT_IR, "x86_fcmp_audit_root", "x86_fcmp_audit");
    assert_eq!(
        rows.len(),
        (N_FCC * N_SCEN) as usize,
        "must sweep all 56 cells"
    );

    for &((tag, scen), row) in &rows {
        // POD was genuinely written by the JIT machine code (not a silent no-op).
        assert_ne!(
            row,
            FcmpAuditRow::poisoned(),
            "{}/{}: JIT left the output POD poisoned (no store)",
            fcc_name(tag),
            scen_name(scen)
        );

        // (a) flag model faithfully materialized by the JIT.
        let (cf, zf, pf) = ucomisd_flags(scen);
        assert_eq!(
            row.cf,
            cf as u32,
            "{}/{}: cf",
            fcc_name(tag),
            scen_name(scen)
        );
        assert_eq!(
            row.zf,
            zf as u32,
            "{}/{}: zf",
            fcc_name(tag),
            scen_name(scen)
        );
        assert_eq!(
            row.pf,
            pf as u32,
            "{}/{}: pf",
            fcc_name(tag),
            scen_name(scen)
        );

        // (b) DUAL ORACLE: JIT strategy tag/cc == LINKED PRODUCTION strategy.
        let fcc = prod_fcc_from_tag(tag);
        let (pkind, pcc) = prod_strategy_kind_cc(fcc);
        assert_eq!(
            row.strat_kind,
            pkind,
            "{}: JIT strat_kind {} != production {}",
            fcc_name(tag),
            row.strat_kind,
            pkind
        );
        assert_eq!(
            row.strat_cc,
            pcc,
            "{}: JIT strat_cc {:#x} != production {:#x}",
            fcc_name(tag),
            row.strat_cc,
            pcc
        );

        // (c) native == JIT: the composed lowering boolean equals the linked
        // production strategy composed the same way.
        let native = native_x86_lowered(fcc, scen);
        assert_eq!(
            row.x86_lowered,
            native as u32,
            "{}/{}: JIT lowered {} != native(production) {}",
            fcc_name(tag),
            scen_name(scen),
            row.x86_lowered,
            native as u32
        );

        // (d) CORRECTNESS: JIT == INDEPENDENT IEEE oracle.
        let ieee = ieee_oracle(tag, scen);
        assert_eq!(
            row.x86_lowered,
            ieee as u32,
            "MISCOMPILE {}/{}: x86 lowering {} != IEEE {}",
            fcc_name(tag),
            scen_name(scen),
            row.x86_lowered,
            ieee as u32
        );
    }
}

// ============================================================================
// TEST 2 — THE AUDIT DELIVERABLE: per-predicate x86-NaN verdict map.
// For every one of the 14 predicates, the x86 lowering on a NaN operand must
// equal the IEEE requirement (ordered=false, unordered=true).
// ============================================================================
#[test]
fn x86_fcmp_nan_verdict_map() {
    let rows = jit_audit_rows(X86_FCMP_AUDIT_IR, "x86_fcmp_audit_root", "x86_fcmp_nan");
    // Index by (tag,scen).
    let get = |tag: u32, scen: u32| -> FcmpAuditRow {
        rows.iter()
            .find(|((t, s), _)| *t == tag && *s == scen)
            .map(|(_, r)| *r)
            .unwrap_or_else(|| panic!("missing cell {tag}/{scen}"))
    };

    // The IEEE NaN requirement per predicate (true = must be TRUE on NaN).
    // Ordered predicates 0..=6 → false; unordered 7..=13 (except the two
    // "ordered-flavoured" comparisons are all unordered here) → true.
    let ordered_false: [u32; 7] = [0, 1, 2, 3, 4, 5, 6]; // Eq,Ne,Lt,Le,Gt,Ge,Ordered
    let unordered_true: [u32; 7] = [7, 8, 9, 10, 11, 12, 13];

    for &tag in &ordered_false {
        let r = get(tag, 3); // scenario 3 = NaN
        assert_eq!(
            r.x86_lowered,
            0,
            "ORDERED predicate {} must be FALSE on NaN, x86 lowering gave {} (analog of aarch64 owner-#10)",
            fcc_name(tag),
            r.x86_lowered
        );
        assert_eq!(
            r.x86_lowered,
            ieee_oracle(tag, 3) as u32,
            "{} NaN vs IEEE",
            fcc_name(tag)
        );
    }
    for &tag in &unordered_true {
        let r = get(tag, 3);
        assert_eq!(
            r.x86_lowered,
            1,
            "UNORDERED predicate {} must be TRUE on NaN, x86 lowering gave {}",
            fcc_name(tag),
            r.x86_lowered
        );
        assert_eq!(
            r.x86_lowered,
            ieee_oracle(tag, 3) as u32,
            "{} NaN vs IEEE",
            fcc_name(tag)
        );
    }

    // Spot-pin the direct analog of the aarch64 bug: ordered NotEqual on NaN.
    // aarch64 mis-lowers this to TRUE; x86 SETNE reads ZF=1 → FALSE (correct).
    let one_nan = get(1, 3);
    assert_eq!(
        one_nan.strat_kind, 0,
        "x86 NotEqual is a bare SingleCC (like aarch64)"
    );
    assert_eq!(
        one_nan.strat_cc,
        ProdCc::NE.encoding() as u32,
        "x86 NotEqual → SETNE"
    );
    assert_eq!(
        one_nan.x86_lowered, 0,
        "x86 ordered NotEqual(NaN) is FALSE — the aarch64 bug is x86-CLEAN"
    );
}

// ============================================================================
// TEST 3 — CONTROL A: the parity guard is LOAD-BEARING (in-process).
// If the fixup were dropped (bare SingleCC for every predicate — the x86
// analog of aarch64's bare CSET), the IEEE oracle catches a NaN miscompile on
// EXACTLY the parity-guarded predicates that flip (6 of the 7).
// ============================================================================
#[test]
fn x86_fcmp_parity_guard_load_bearing() {
    // A bare-CC lowering ignores AND-SETNP / OR-SETP.
    fn bare_cc_lowered(fcc: ProdFcc, scenario: u32) -> bool {
        let (cf, zf, pf) = ucomisd_flags(scenario);
        let (_kind, cc) = prod_strategy_kind_cc(fcc);
        eval_setcc_tag(cc, cf, zf, pf)
    }

    let mut caught: Vec<u32> = Vec::new();
    for tag in 0..N_FCC {
        let fcc = prod_fcc_from_tag(tag);
        // Only the NaN column can differ (bare vs guarded agree off-NaN by
        // construction — the guard only touches the PF=1 case). Verify that too.
        for scen in 0..3 {
            assert_eq!(
                bare_cc_lowered(fcc, scen),
                native_x86_lowered(fcc, scen),
                "{} off-NaN: bare and guarded lowering must agree",
                fcc_name(tag)
            );
        }
        let bare_nan = bare_cc_lowered(fcc, 3);
        let ieee_nan = ieee_oracle(tag, 3);
        if bare_nan != ieee_nan {
            caught.push(tag);
        }
    }

    // The guard is required by exactly these predicates for NaN-correctness:
    //   Equal(0), LessThan(2), LessThanOrEqual(3)             [ordered, AND-SETNP]
    //   UnorderedNotEqual(9), UnorderedGreaterThan(12),
    //   UnorderedGreaterThanOrEqual(13)                       [unordered, OR-SETP]
    // UnorderedEqual(8)'s bare SETE is coincidentally NaN-correct (ZF=1), so it
    // is NOT in the catch set even though production guards it with OR-SETP.
    let expected_catch = vec![0u32, 2, 3, 9, 12, 13];
    assert_eq!(
        caught, expected_catch,
        "dropping the parity guard must miscompile exactly these predicates on NaN"
    );
    // And it is genuinely non-empty — a bare-CC x86 backend WOULD be buggy.
    assert!(
        !caught.is_empty(),
        "control must catch at least one miscompile"
    );
}

// ============================================================================
// TEST 4 — CONTROL C: a MUTATED slice (Equal → bare SingleCC(E), the parity
// guard dropped) JIT-compiled through the SAME pipeline miscompiles the
// Equal/NaN cell. Proves the machine-code path — not just the model — surfaces
// a real x86 fcmp table bug.
// ============================================================================
#[test]
fn x86_fcmp_buggy_jit_miscompiles_equal_on_nan() {
    let rows = jit_audit_rows(X86_FCMP_BUGGY_IR, "x86_fcmp_buggy_root", "x86_fcmp_buggy");
    let get = |tag: u32, scen: u32| -> FcmpAuditRow {
        rows.iter()
            .find(|((t, s), _)| *t == tag && *s == scen)
            .map(|(_, r)| *r)
            .unwrap_or_else(|| panic!("missing cell {tag}/{scen}"))
    };

    // The mutation: Equal is now a bare SingleCC(E) (kind 0), not AndNotParity.
    let eq_nan = get(0, 3);
    assert_eq!(
        eq_nan.strat_kind, 0,
        "buggy slice lowers Equal as bare SingleCC"
    );
    assert_eq!(
        eq_nan.strat_cc,
        ProdCc::E.encoding() as u32,
        "primary cc is still E"
    );

    // THE MISCOMPILE: bare SETE reads ZF=1 on NaN → TRUE, but IEEE ordered-equal
    // on NaN is FALSE. The JIT machine code returns the WRONG answer, and the
    // IEEE oracle catches it.
    assert_eq!(
        eq_nan.x86_lowered, 1,
        "buggy Equal/NaN JIT must return TRUE (bare SETE reads ZF=1)"
    );
    assert_ne!(
        eq_nan.x86_lowered,
        ieee_oracle(0, 3) as u32,
        "the audit harness MUST catch the injected x86 fcmp NaN bug"
    );

    // Off-NaN Equal is unaffected (bare SETE == guarded on ordered inputs).
    assert_eq!(get(0, 0).x86_lowered, 0, "Equal(lhs<rhs) still false");
    assert_eq!(get(0, 1).x86_lowered, 1, "Equal(lhs==rhs) still true");
    assert_eq!(get(0, 2).x86_lowered, 0, "Equal(lhs>rhs) still false");

    // Every OTHER predicate in the buggy module is still correct (the mutation
    // is isolated to Equal) — confirms the control is surgical, not a blanket
    // break.
    for tag in 1..N_FCC {
        for scen in 0..N_SCEN {
            let r = get(tag, scen);
            assert_eq!(
                r.x86_lowered,
                ieee_oracle(tag, scen) as u32,
                "buggy module: non-Equal predicate {}/{} unexpectedly changed",
                fcc_name(tag),
                scen_name(scen)
            );
        }
    }
}

// ============================================================================
// TEST 5 — CONTROL B / cross-tie: the aarch64 owner-#10 wrong answer is
// x86-CLEAN. On aarch64, ONe(finite,NaN) mis-returns TRUE; on x86 the SAME
// predicate returns FALSE (correct), on both the JIT and the IEEE oracle.
// ============================================================================
#[test]
fn x86_fcmp_aarch64_bug_is_x86_clean() {
    let rows = jit_audit_rows(X86_FCMP_AUDIT_IR, "x86_fcmp_audit_root", "x86_fcmp_xtie");
    let one_nan = rows
        .iter()
        .find(|((t, s), _)| *t == 1 && *s == 3)
        .map(|(_, r)| *r)
        .expect("ONe/NaN cell present");

    // The aarch64 miscompile returns TRUE here (its documented wrong answer).
    let aarch64_wrong = 1u32;
    // x86 returns FALSE.
    assert_eq!(one_nan.x86_lowered, 0, "x86 ONe(NaN) JIT = false");
    assert_eq!(ieee_oracle(1, 3) as u32, 0, "IEEE ONe(NaN) = false");
    assert_ne!(
        one_nan.x86_lowered, aarch64_wrong,
        "x86 does NOT reproduce the aarch64 owner-#10 wrong answer"
    );

    // And the WHOLE NaN column agrees with IEEE (the clean-bill core, restated).
    for tag in 0..N_FCC {
        let r = rows
            .iter()
            .find(|((t, s), _)| *t == tag && *s == 3)
            .map(|(_, r)| *r)
            .unwrap();
        assert_eq!(
            r.x86_lowered,
            ieee_oracle(tag, 3) as u32,
            "x86 {} on NaN must match IEEE",
            fcc_name(tag)
        );
    }
}
