// Trust-toolchain slice — the x86-64 FLOATING-POINT COMPARE condition-code
// lowering table, transcribed VERBATIM from
// trust-cg/crates/trust-cg-lower/src/x86_64_isel.rs (working tree, round 33).
//
// SELF-APPLICATION of verify-native==JIT to TRUST ITSELF (round 33): the x86
// analog of the aarch64 owner-#10 `fcmp one` NaN miscompile audit. The aarch64
// backend mis-lowers ordered-not-equal (`FloatCC::NotEqual`) to a bare `CSET NE`
// which reads Z=0 on a NaN FCMP and so returns TRUE (IEEE requires FALSE). This
// slice lets us MACHINE-CHECK whether the x86-64 backend has any fcmp-one-
// analogous bug: an `FloatCC` whose x86 lowering gives the WRONG boolean when an
// operand is NaN.
//
// The x86 flag model is FUNDAMENTALLY DIFFERENT from aarch64: `UCOMISD` sets the
// parity flag PF=1 (plus ZF=1, CF=1) on an unordered (NaN) compare, and x86 reads
// the *parity* flag as the unordered signal. So x86's NaN-handling bugs would be
// distinct from aarch64's. We transcribe:
//   * `x86_float_cmp_strategy` (isel.rs) — the FULL 14-arm FloatCC -> strategy
//     table (SingleCC / AndNotParity=AND-SETNP / OrParity=OR-SETP), VERBATIM.
//   * the faithful `UCOMISD` flag model (Intel SDM Vol.1 §8.1.2; the exact table
//     in the isel.rs doc comment: Equal CF0/ZF1/PF0, Less CF1/ZF0/PF0,
//     Greater CF0/ZF0/PF0, NaN CF1/ZF1/PF1).
//   * `eval_setcc` — the x86 SETcc flag semantics per X86CondCode (x86_64_ops.rs
//     discriminant table: E=ZF, NE=!ZF, B=CF, AE=!CF, BE=CF|ZF, A=!CF&!ZF,
//     P=PF, NP=!PF).
//   * `x86_lowered_bool` — the COMPOSITION that mirrors `select_fcmp` byte-for-
//     byte: SingleCC -> SETcc; AndNotParity -> SETcc && SETNP; OrParity ->
//     SETcc || SETP. (isel.rs `select_fcmp` emits exactly SETcc[+AND SETNP]/
//     [+OR SETP].)
//
// EMIT: stage1 `trust_ir_mir --mir-emit-closure x86_fcmp_audit_root`;
// `-C overflow-checks=off -C debug-assertions=off`. Integer-only (no floats,
// no strings) — routes cleanly through the emit-closure frontend despite its
// float gap (round-31 Finding A): the whole audit is over integer scenario tags.
//
// MODELED BOUNDARIES:
//   [B1] The strategy enum is transcribed VERBATIM (SingleCC/AndNotParity/
//        OrParity each carrying an X86CondCode). The linked production
//        `trust_cg_lower::x86_float_cmp_strategy` is the dual oracle in the test
//        (strat_kind + strat_cc asserted equal for all 14), so any transcription
//        drift is caught.
//   [B2] `FloatCC`/`X86CondCode`/strategy are exposed as u32 `tag`s at the root
//        (round-5 enum<->tag plumbing). The transcribed table is UNMODIFIED.
//   [B3] The UCOMISD flag model is the ISA truth for the four total-order
//        outcomes (lhs<rhs / lhs==rhs / lhs>rhs / unordered). It is not itself
//        "compiled Trust code under test" — it is the reference the mapping is
//        audited against; the mapping-table logic IS the compiled code.

// ── FloatCC (instructions.rs:767) — 14 variants, VERBATIM ────────────────────
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum FloatCC {
    Equal,
    NotEqual,
    LessThan,
    LessThanOrEqual,
    GreaterThan,
    GreaterThanOrEqual,
    Ordered,
    Unordered,
    UnorderedEqual,
    UnorderedNotEqual,
    UnorderedLessThan,
    UnorderedLessThanOrEqual,
    UnorderedGreaterThan,
    UnorderedGreaterThanOrEqual,
}

// ── X86CondCode (x86_64_ops.rs:1099) — repr(u8), discriminant = 4-bit tttn ────
#[derive(Clone, Copy, PartialEq, Eq)]
#[repr(u8)]
pub enum X86CondCode {
    O = 0x0,
    NO = 0x1,
    B = 0x2,
    AE = 0x3,
    E = 0x4,
    NE = 0x5,
    BE = 0x6,
    A = 0x7,
    S = 0x8,
    NS = 0x9,
    P = 0xA,
    NP = 0xB,
    L = 0xC,
    GE = 0xD,
    LE = 0xE,
    G = 0xF,
}

impl X86CondCode {
    #[inline]
    pub const fn encoding(self) -> u8 {
        self as u8
    }
}

// ── X86FloatCmpStrategy (isel.rs:595) — VERBATIM ─────────────────────────────
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum X86FloatCmpStrategy {
    /// Single condition code suffices (no parity fixup needed).
    SingleCC(X86CondCode),
    /// Two `SETcc` + `AND`: `result = SETcc(cc) & SETNP` (ordered — exclude NaN).
    AndNotParity(X86CondCode),
    /// Two `SETcc` + `OR`: `result = SETcc(cc) | SETP` (unordered — include NaN).
    OrParity(X86CondCode),
}

// ── x86_float_cmp_strategy (isel.rs:649) — the FULL 14-arm table, VERBATIM ────
pub fn x86_float_cmp_strategy(cc: FloatCC) -> X86FloatCmpStrategy {
    match cc {
        // Ordered — single CC (NaN already gives the correct false result)
        FloatCC::NotEqual => X86FloatCmpStrategy::SingleCC(X86CondCode::NE),
        FloatCC::GreaterThan => X86FloatCmpStrategy::SingleCC(X86CondCode::A),
        FloatCC::GreaterThanOrEqual => X86FloatCmpStrategy::SingleCC(X86CondCode::AE),
        FloatCC::Ordered => X86FloatCmpStrategy::SingleCC(X86CondCode::NP),

        // Ordered — need AND with NP to exclude NaN
        FloatCC::Equal => X86FloatCmpStrategy::AndNotParity(X86CondCode::E),
        FloatCC::LessThan => X86FloatCmpStrategy::AndNotParity(X86CondCode::B),
        FloatCC::LessThanOrEqual => X86FloatCmpStrategy::AndNotParity(X86CondCode::BE),

        // Unordered — single CC (NaN already gives the correct true result)
        FloatCC::Unordered => X86FloatCmpStrategy::SingleCC(X86CondCode::P),
        FloatCC::UnorderedLessThan => X86FloatCmpStrategy::SingleCC(X86CondCode::B),
        FloatCC::UnorderedLessThanOrEqual => X86FloatCmpStrategy::SingleCC(X86CondCode::BE),

        // Unordered — need OR with P to include NaN
        FloatCC::UnorderedEqual => X86FloatCmpStrategy::OrParity(X86CondCode::E),
        FloatCC::UnorderedNotEqual => X86FloatCmpStrategy::OrParity(X86CondCode::NE),
        FloatCC::UnorderedGreaterThan => X86FloatCmpStrategy::OrParity(X86CondCode::A),
        FloatCC::UnorderedGreaterThanOrEqual => X86FloatCmpStrategy::OrParity(X86CondCode::AE),
    }
}

// ── UCOMISD flag model (Intel SDM Vol.1 §8.1.2; isel.rs:583-587) ─────────────
// Scenario tags for `UCOMISD lhs, rhs`:
//   0 => Less    (lhs < rhs):  CF=1, ZF=0, PF=0
//   1 => Equal   (lhs == rhs): CF=0, ZF=1, PF=0
//   2 => Greater (lhs > rhs):  CF=0, ZF=0, PF=0
//   3 => Unordered (NaN):      CF=1, ZF=1, PF=1
// Returns (cf, zf, pf).
fn ucomisd_flags(scenario: u32) -> (bool, bool, bool) {
    match scenario {
        0 => (true, false, false),
        1 => (false, true, false),
        2 => (false, false, false),
        _ => (true, true, true),
    }
}

// ── SETcc flag semantics (x86_64_ops.rs discriminant comments) ───────────────
// Only the 8 fcmp-relevant codes are reachable from the strategy table; the
// remaining OF/SF/signed codes are given their standard meaning for totality but
// are DEAD on the fcmp domain.
fn eval_setcc(cc: X86CondCode, cf: bool, zf: bool, pf: bool) -> bool {
    match cc {
        X86CondCode::E => zf,
        X86CondCode::NE => !zf,
        X86CondCode::B => cf,
        X86CondCode::AE => !cf,
        X86CondCode::BE => cf || zf,
        X86CondCode::A => !cf && !zf,
        X86CondCode::P => pf,
        X86CondCode::NP => !pf,
        // Dead on the fcmp domain (OF/SF unknown here; conservative constants).
        X86CondCode::O => false,
        X86CondCode::NO => true,
        X86CondCode::S => false,
        X86CondCode::NS => true,
        X86CondCode::L => false,
        X86CondCode::GE => true,
        X86CondCode::LE => zf,
        X86CondCode::G => !zf,
    }
}

// ── x86_lowered_bool — the COMPOSITION that mirrors select_fcmp emission ──────
// SingleCC(cc)     -> SETcc(cc)                 (isel.rs:8579)
// AndNotParity(cc) -> SETcc(cc) & SETNP         (isel.rs:8593, AND with NP)
// OrParity(cc)     -> SETcc(cc) | SETP          (isel.rs:8628, OR with P)
fn x86_lowered_bool(cc: FloatCC, cf: bool, zf: bool, pf: bool) -> bool {
    match x86_float_cmp_strategy(cc) {
        X86FloatCmpStrategy::SingleCC(c) => eval_setcc(c, cf, zf, pf),
        X86FloatCmpStrategy::AndNotParity(c) => {
            eval_setcc(c, cf, zf, pf) && eval_setcc(X86CondCode::NP, cf, zf, pf)
        }
        X86FloatCmpStrategy::OrParity(c) => {
            eval_setcc(c, cf, zf, pf) || eval_setcc(X86CondCode::P, cf, zf, pf)
        }
    }
}

// ── enum<->tag plumbing ──────────────────────────────────────────────────────
fn floatcc_from_tag(tag: u8) -> FloatCC {
    match tag {
        0 => FloatCC::Equal,
        1 => FloatCC::NotEqual,
        2 => FloatCC::LessThan,
        3 => FloatCC::LessThanOrEqual,
        4 => FloatCC::GreaterThan,
        5 => FloatCC::GreaterThanOrEqual,
        6 => FloatCC::Ordered,
        7 => FloatCC::Unordered,
        8 => FloatCC::UnorderedEqual,
        9 => FloatCC::UnorderedNotEqual,
        10 => FloatCC::UnorderedLessThan,
        11 => FloatCC::UnorderedLessThanOrEqual,
        12 => FloatCC::UnorderedGreaterThan,
        _ => FloatCC::UnorderedGreaterThanOrEqual,
    }
}

// strategy kind tag: 0=SingleCC, 1=AndNotParity, 2=OrParity
fn strat_kind_tag(s: X86FloatCmpStrategy) -> u32 {
    match s {
        X86FloatCmpStrategy::SingleCC(_) => 0,
        X86FloatCmpStrategy::AndNotParity(_) => 1,
        X86FloatCmpStrategy::OrParity(_) => 2,
    }
}

fn strat_primary_cc(s: X86FloatCmpStrategy) -> u32 {
    match s {
        X86FloatCmpStrategy::SingleCC(c) => c.encoding() as u32,
        X86FloatCmpStrategy::AndNotParity(c) => c.encoding() as u32,
        X86FloatCmpStrategy::OrParity(c) => c.encoding() as u32,
    }
}

// ── out-POD + #[no_mangle] mono ROOT ─────────────────────────────────────────
#[repr(C)]
pub struct FcmpAuditProps {
    pub strat_kind: u32,   // 0=SingleCC 1=AndNotParity 2=OrParity
    pub strat_cc: u32,     // primary condition-code 4-bit tag
    pub cf: u32,           // UCOMISD flag model for the scenario
    pub zf: u32,
    pub pf: u32,
    pub x86_lowered: u32,  // the composed lowering boolean (the thing under audit)
}

/// ROOT: for a (FloatCC tag, UCOMISD scenario tag), report the x86 lowering
/// strategy and the resulting boolean the emitted machine code would compute.
#[no_mangle]
pub fn x86_fcmp_audit_root(floatcc_tag: u32, scenario: u32, out: &mut FcmpAuditProps) {
    let cc = floatcc_from_tag(floatcc_tag as u8);
    let strat = x86_float_cmp_strategy(cc);
    let (cf, zf, pf) = ucomisd_flags(scenario);
    out.strat_kind = strat_kind_tag(strat);
    out.strat_cc = strat_primary_cc(strat);
    out.cf = cf as u32;
    out.zf = zf as u32;
    out.pf = pf as u32;
    out.x86_lowered = x86_lowered_bool(cc, cf, zf, pf) as u32;
}
