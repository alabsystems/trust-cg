// trust-cg-verify/aarch64_source_condition.rs - TV-3 source-CONDITION binding
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Which AArch64 condition codes a correct lowering of a given LIR source
//! instruction may place on an emitted `CSET`/`CSEL`.
//!
//! # The hole this closes
//!
//! A proof that an INSTRUCTION is correct is not a claim that the PROGRAM
//! implements its source. The AArch64 NZCV-consumer bindings in
//! [`crate::function_verifier`] cite a theorem NAMED BY THE CONDITION the
//! emitted instruction itself carries — `cset_reaching_cmp_query` reads the
//! `cc` immediate out of the `CSET` and looks up `Icmp_<that cond>_I<w>` — and
//! then check only that the TV-1 stamped source instruction has the right
//! coarse [`OpClass`](crate::provenance_xcheck::OpClass). `Icmp { cond: SLT }`
//! and `Icmp { cond: UGT }` are both `OpClass::IntCmp`, so the condition was
//! never compared against the source at all: the citation was derived from the
//! instruction under test. Mutating ONLY the `cc` immediate of a `CSET`
//! lowered from `icmp slt` therefore kept the row `Verified` — it just moved
//! the citation from `Icmp_SLT_I64` to `Icmp_SGT_I64`, a true theorem about a
//! program this is not. `CMP a,b ; CSET MI` is a genuine miscompile of signed
//! `a < b` (at `a = i64::MIN, b = 1` it answers 0 where `a < b` is 1).
//!
//! This module supplies the missing conjunct: the set of condition codes a
//! correct lowering of THIS source instruction can emit, computed from the
//! source side alone. A binding that requires the emitted `cc` to be in that
//! set is no longer self-attesting.
//!
//! # Where the tables come from
//!
//! Every row is read off an ISel emission site, cited by function. The tables
//! are a statement about what `trust-cg-lower` emits, so they are
//! OVER-approximations by construction (a union across every lowering that can
//! fire for that opcode) — never a claim that a particular condition IS the
//! right one for a particular emission. What they establish is the converse,
//! which is the fact the citation needed: a condition OUTSIDE the set cannot
//! come from a correct lowering of this source instruction, so the row must
//! fail closed instead of citing a theorem for it.
//!
//! WHAT THE SETS DO NOT ESTABLISH. For a source whose lowering emits SEVERAL
//! conditional instructions on DIFFERENT conditions — the i128 comparison's
//! `{hi_cc, EQ, lo_cc}` triple — a set admits all three at every one of the
//! three positions, so the right three conditions in the wrong ORDER pass it.
//! The binding site therefore does not use the set for that case: it derives
//! each `CSET`'s ROLE from data flow and admits exactly
//! [`i128_cmp_role_condition`] for it (see `cset_reaching_cmp_query`).

use crate::provenance_xcheck::LirSourceInst;
use trust_cg_lower::instructions::{FloatCC, IntCC, Opcode as LirOpcode};

// ---------------------------------------------------------------------------
// Condition-code immediates
// ---------------------------------------------------------------------------

/// The `AArch64CC` discriminants as they appear in a `MachOperand::Imm`.
///
/// `trust_cg_lower::isel::AArch64CC` is a plain `#[repr]`-less enum whose
/// declaration order IS the encoding `cc_from_isel_immediate` reads, and
/// `icmp_family_query` already decodes the same numbers. Spelled out here so
/// the tables below read as conditions rather than as integers.
pub mod cc {
    /// Equal (Z=1).
    pub const EQ: i64 = 0;
    /// Not equal (Z=0).
    pub const NE: i64 = 1;
    /// Unsigned higher or same (C=1).
    pub const HS: i64 = 2;
    /// Unsigned lower (C=0).
    pub const LO: i64 = 3;
    /// Negative (N=1).
    pub const MI: i64 = 4;
    /// Positive or zero (N=0).
    pub const PL: i64 = 5;
    /// Overflow (V=1).
    pub const VS: i64 = 6;
    /// No overflow (V=0).
    pub const VC: i64 = 7;
    /// Unsigned higher (C=1 & Z=0).
    pub const HI: i64 = 8;
    /// Unsigned lower or same (C=0 | Z=1).
    pub const LS: i64 = 9;
    /// Signed greater or equal (N=V).
    pub const GE: i64 = 10;
    /// Signed less than (N!=V).
    pub const LT: i64 = 11;
    /// Signed greater than (Z=0 & N=V).
    pub const GT: i64 = 12;
    /// Signed less or equal (Z=1 | N!=V).
    pub const LE: i64 = 13;
    /// Number of architectural condition codes with a `cc` mnemonic (`AL`/`NV`
    /// are not encodable in the alias forms this module reasons about).
    pub const COUNT: i64 = 14;
}

/// A set of AArch64 condition codes, as a bitmask over the 14 encodable `cc`
/// values. Allocation-free: the verifier walk builds one per candidate
/// instruction.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub struct CcSet(u16);

impl CcSet {
    /// The empty set. A binding holding this must fail closed: it means no
    /// correct lowering of the source instruction emits this instruction at
    /// all, so the emission is a misattribution.
    pub const EMPTY: Self = Self(0);

    /// The set containing exactly `codes`.
    pub const fn of(codes: &[i64]) -> Self {
        let mut mask = 0u16;
        let mut i = 0;
        while i < codes.len() {
            let code = codes[i];
            // A code outside the encodable range is dropped rather than
            // silently aliasing into the mask; every table entry below is a
            // `cc::` constant, so this cannot fire from in-tree data.
            if code >= 0 && code < cc::COUNT {
                mask |= 1 << code;
            }
            i += 1;
        }
        Self(mask)
    }

    /// Union.
    pub const fn union(self, other: Self) -> Self {
        Self(self.0 | other.0)
    }

    /// Does this set admit the condition immediate `code`?
    pub const fn contains(self, code: i64) -> bool {
        if code < 0 || code >= cc::COUNT {
            return false;
        }
        self.0 & (1 << code) != 0
    }

    /// True for the empty set.
    pub const fn is_empty(self) -> bool {
        self.0 == 0
    }

    /// The codes in this set, ascending — diagnostics and tests only.
    pub fn codes(self) -> Vec<i64> {
        (0..cc::COUNT).filter(|&c| self.contains(c)).collect()
    }
}

// ---------------------------------------------------------------------------
// CSET
// ---------------------------------------------------------------------------

/// `AArch64CC::from_intcc` — the scalar `Icmp` lowering's condition
/// (`isel.rs`'s `AArch64CC::from_intcc`, used by `select_cmp`).
const fn from_intcc(cond: IntCC) -> i64 {
    match cond {
        IntCC::Equal => cc::EQ,
        IntCC::NotEqual => cc::NE,
        IntCC::SignedLessThan => cc::LT,
        IntCC::SignedGreaterThanOrEqual => cc::GE,
        IntCC::SignedGreaterThan => cc::GT,
        IntCC::SignedLessThanOrEqual => cc::LE,
        IntCC::UnsignedLessThan => cc::LO,
        IntCC::UnsignedGreaterThanOrEqual => cc::HS,
        IntCC::UnsignedGreaterThan => cc::HI,
        IntCC::UnsignedLessThanOrEqual => cc::LS,
    }
}

/// The complement of a single-`cc` predicate, as `AArch64CC::invert` computes
/// it. Used by the select-condition fold (`Eq`-sense inverts the folded
/// compare's code).
const fn invert(code: i64) -> i64 {
    match code {
        cc::EQ => cc::NE,
        cc::NE => cc::EQ,
        cc::HS => cc::LO,
        cc::LO => cc::HS,
        cc::MI => cc::PL,
        cc::PL => cc::MI,
        cc::VS => cc::VC,
        cc::VC => cc::VS,
        cc::HI => cc::LS,
        cc::LS => cc::HI,
        cc::GE => cc::LT,
        cc::LT => cc::GE,
        cc::GT => cc::LE,
        _ => cc::GT,
    }
}

/// The two halves of `select_i128_cmp`'s ordered lowering: the HIGH-limb
/// condition and the (always unsigned) LOW-limb condition
/// (`isel.rs::select_i128_cmp`).
const fn i128_cmp_limb_conditions(cond: IntCC) -> CcSet {
    let hi = match cond {
        IntCC::SignedLessThan | IntCC::SignedLessThanOrEqual => cc::LT,
        IntCC::SignedGreaterThan | IntCC::SignedGreaterThanOrEqual => cc::GT,
        IntCC::UnsignedLessThan | IntCC::UnsignedLessThanOrEqual => cc::LO,
        IntCC::UnsignedGreaterThan | IntCC::UnsignedGreaterThanOrEqual => cc::HI,
        // Equal / NotEqual take the EQ/NE lowering, which emits two CSETs on
        // `from_intcc(cond)` and no limb-condition pair at all.
        IntCC::Equal => cc::EQ,
        IntCC::NotEqual => cc::NE,
    };
    let lo = match cond {
        IntCC::SignedLessThan | IntCC::UnsignedLessThan => cc::LO,
        IntCC::SignedGreaterThan | IntCC::UnsignedGreaterThan => cc::HI,
        IntCC::SignedLessThanOrEqual | IntCC::UnsignedLessThanOrEqual => cc::LS,
        IntCC::SignedGreaterThanOrEqual | IntCC::UnsignedGreaterThanOrEqual => cc::HS,
        IntCC::Equal => cc::EQ,
        IntCC::NotEqual => cc::NE,
    };
    // The ordered lowering also emits a `CSET EQ` on the high limbs, to select
    // between the high and low decisions.
    let eq = match cond {
        IntCC::Equal | IntCC::NotEqual => from_intcc(cond),
        _ => cc::EQ,
    };
    CcSet::of(&[hi, lo, eq])
}

/// The ROLE a `CSET` plays inside `select_i128_cmp`'s limb decomposition.
///
/// The role is a fact about DATA FLOW — which comparison the `CSET` reads and
/// which combiner reads it — and is derived by
/// `function_verifier`'s i128 data-flow module, never from the `CSET`'s own
/// condition. [`i128_cmp_role_condition`] then names the ONE condition a correct
/// lowering puts on that role.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum I128CmpCsetRole {
    /// `EQ`: one of the two per-limb tests, combined by an `AND` (`CMP hi ;
    /// CSET cc ; CMP lo ; CSET cc ; AND`) — both limbs equal.
    LimbConjunct,
    /// `NE`: one of the two per-limb tests, combined by an `ORR` — either limb
    /// differs.
    LimbDisjunct,
    /// Ordered: the high limbs' strict ordering (`hi_cc`), read by the final
    /// `ORR`.
    HighDecision,
    /// Ordered: the high limbs' equality (`EQ`), read by the `AND`.
    HighEqual,
    /// Ordered: the low limbs' (always unsigned) ordering (`lo_cc`), read by
    /// the `AND`.
    LowDecision,
}

/// The single condition code `select_i128_cmp` places on a `CSET` in `role`
/// for an i128 `Icmp { cond }` — or `None` when the lowering of `cond` has no
/// `CSET` in that role (an `EQ`/`NE` comparison has no high/low decision; an
/// ordered one has no limb pair; `EQ` combines its limbs with `AND` and `NE`
/// with `ORR`, never the other way round — `hi_eq | lo_eq` is not `a == b`).
///
/// This is POSITIONAL exactness in the only sense that survives reordering: at
/// emission count 2 or 3, [`cset_conditions_for_emission_count`] admits the
/// whole `{hi_cc, EQ, lo_cc}` triple at EVERY position, so the right three
/// conditions in the wrong order passed. Keyed on role, each position admits
/// exactly one.
pub const fn i128_cmp_role_condition(cond: IntCC, role: I128CmpCsetRole) -> Option<i64> {
    match (cond, role) {
        (IntCC::Equal, I128CmpCsetRole::LimbConjunct) => Some(cc::EQ),
        (IntCC::NotEqual, I128CmpCsetRole::LimbDisjunct) => Some(cc::NE),
        (IntCC::Equal | IntCC::NotEqual, _)
        | (_, I128CmpCsetRole::LimbConjunct | I128CmpCsetRole::LimbDisjunct) => None,
        (_, I128CmpCsetRole::HighEqual) => Some(cc::EQ),
        (_, I128CmpCsetRole::HighDecision) => Some(match cond {
            IntCC::SignedLessThan | IntCC::SignedLessThanOrEqual => cc::LT,
            IntCC::SignedGreaterThan | IntCC::SignedGreaterThanOrEqual => cc::GT,
            IntCC::UnsignedLessThan | IntCC::UnsignedLessThanOrEqual => cc::LO,
            IntCC::UnsignedGreaterThan | IntCC::UnsignedGreaterThanOrEqual => cc::HI,
            IntCC::Equal | IntCC::NotEqual => return None,
        }),
        (_, I128CmpCsetRole::LowDecision) => Some(match cond {
            IntCC::SignedLessThan | IntCC::UnsignedLessThan => cc::LO,
            IntCC::SignedGreaterThan | IntCC::UnsignedGreaterThan => cc::HI,
            IntCC::SignedLessThanOrEqual | IntCC::UnsignedLessThanOrEqual => cc::LS,
            IntCC::SignedGreaterThanOrEqual | IntCC::UnsignedGreaterThanOrEqual => cc::HS,
            IntCC::Equal | IntCC::NotEqual => return None,
        }),
    }
}

/// `AArch64CC::from_floatcc`, plus the SECOND code of the two-CC FP forms.
///
/// `select_fcmp` materialises `NotEqual` (ordered-not-equal) as `NE && VC` and
/// `UnorderedEqual` as `EQ || VS`, i.e. two `CSET`s combined with `AND`/`ORR`;
/// every other `FloatCC` is one `CSET` on a single code. Both codes of a
/// two-CC form are admitted, because both are emitted.
fn fcmp_conditions(cond: FloatCC) -> CcSet {
    match cond {
        FloatCC::Equal => CcSet::of(&[cc::EQ]),
        // ONE = NE && VC (isel.rs `select_fcmp`, the `NotEqual` arm).
        FloatCC::NotEqual => CcSet::of(&[cc::NE, cc::VC]),
        FloatCC::LessThan => CcSet::of(&[cc::MI]),
        FloatCC::LessThanOrEqual => CcSet::of(&[cc::LS]),
        FloatCC::GreaterThan => CcSet::of(&[cc::GT]),
        FloatCC::GreaterThanOrEqual => CcSet::of(&[cc::GE]),
        FloatCC::Ordered => CcSet::of(&[cc::VC]),
        FloatCC::Unordered => CcSet::of(&[cc::VS]),
        // UEQ = EQ || VS.
        FloatCC::UnorderedEqual => CcSet::of(&[cc::EQ, cc::VS]),
        FloatCC::UnorderedNotEqual => CcSet::of(&[cc::NE]),
        FloatCC::UnorderedLessThan => CcSet::of(&[cc::LT]),
        FloatCC::UnorderedLessThanOrEqual => CcSet::of(&[cc::LE]),
        FloatCC::UnorderedGreaterThan => CcSet::of(&[cc::HI]),
        FloatCC::UnorderedGreaterThanOrEqual => CcSet::of(&[cc::HS]),
    }
}

/// The condition codes a correct AArch64 lowering of `source` may place on an
/// emitted `CSET`, given that the lowering emitted `emitted` of them in total
/// (counted over the instructions carrying the SAME TV-1 source stamp).
///
/// The count is what separates the SCALAR comparison lowering from the i128
/// limb decomposition, and it matters: `select_cmp` emits ONE `CSET` on
/// `from_intcc(cond)`, while `select_i128_cmp` emits TWO (`EQ`/`NE`) or THREE
/// (`{hi_cc, EQ, lo_cc}`). Taking the union unconditionally would admit `CSET
/// EQ` and `CSET LO` for a SCALAR signed less-than — a true `Icmp_Eq_I64` /
/// `Icmp_ULT_I64` theorem about the wrong predicate, which is the same class of
/// defect as reading the condition off the instruction in the first place.
///
/// A count the tables do not predict (0, or more than 3) fails closed. A pass
/// that moved or eliminated one of the limb selects therefore costs a promotion
/// rather than widening the admissible set.
pub fn cset_conditions_for_emission_count(source: &LirOpcode, emitted: usize) -> CcSet {
    match source {
        LirOpcode::Icmp { cond } => match emitted {
            // `select_cmp`: exactly one CSET, on the comparison's own code.
            1 => CcSet::of(&[from_intcc(*cond)]),
            // `select_i128_cmp`: the EQ/NE pair, or the ordered triple.
            2 | 3 => CcSet::of(&[from_intcc(*cond)]).union(i128_cmp_limb_conditions(*cond)),
            _ => CcSet::EMPTY,
        },
        // No other source's CSET set is emission-count dependent: the checked
        // idioms materialise exactly one overflow bit per lowering, and the
        // two-CSET `Fcmp` forms are already both admitted by
        // `fcmp_conditions`.
        other => cset_conditions(other),
    }
}

/// The condition codes a correct AArch64 lowering of `source` may place on an
/// emitted `CSET`, over EVERY lowering that can fire for it.
///
/// This is the count-insensitive union. Prefer
/// [`cset_conditions_for_emission_count`] at a binding site — this one admits
/// the i128 limb conditions even for a scalar comparison.
///
/// [`CcSet::EMPTY`] means NO lowering of that source opcode emits a `CSET`, so
/// a `CSET` stamped from it is a misattribution and the caller must fail
/// closed. The match is EXHAUSTIVE by design (no wildcard): a new LIR opcode
/// must be consciously classified here before this compiles, so the binding can
/// never silently admit new condition-carrying surface.
pub fn cset_conditions(source: &LirOpcode) -> CcSet {
    use LirOpcode as O;
    match source {
        // `select_cmp` (scalar, `isel.rs`) emits ONE `CSET from_intcc(cond)`;
        // `select_i128_cmp` emits the EQ/NE pair or the ordered
        // `{hi_cc, EQ, lo_cc}` triple. Which one fires depends on the operand
        // TYPE, which is not recoverable here, so the union is taken.
        O::Icmp { cond } => CcSet::of(&[from_intcc(*cond)]).union(i128_cmp_limb_conditions(*cond)),
        // `select_fcmp` materialises the FP predicate; single-CC forms emit one
        // `CSET`, the two two-CC forms emit two.
        O::Fcmp { cond } => fcmp_conditions(*cond),
        // Checked integer arithmetic. `select_checked_add_sub` picks the
        // overflow condition from the SIGNEDNESS (`Sadd`/`Ssub` -> V, `Uadd` ->
        // C set, `Usub` -> C clear); `select_checked_smul`/`_umul` compare the
        // high half and materialise `NE`; `select_overflow_narrow` re-checks a
        // narrow result and materialises `VS`. The narrow `VS` is admitted for
        // every kind because that path is width-driven, not signedness-driven.
        O::CheckedSadd | O::CheckedSsub => CcSet::of(&[cc::VS]),
        O::CheckedUadd => CcSet::of(&[cc::HS, cc::VS]),
        O::CheckedUsub => CcSet::of(&[cc::LO, cc::VS]),
        O::CheckedSmul | O::CheckedUmul => CcSet::of(&[cc::NE, cc::VS]),
        // Everything else: no in-tree lowering emits a `CSET` while dispatching
        // it. This is the SAFE direction — an emission the tables do not
        // predict fails closed rather than being credited — and it is not
        // load-bearing for the pre-existing bindings, which independently
        // require the source's coarse class to be `IntCmp` or `Overflow`
        // before they consult this table at all.
        O::Iconst { .. }
        | O::Iconst128 { .. }
        | O::Fconst { .. }
        | O::V4I32Zero
        | O::V2I64Zero
        | O::Copy
        | O::Iadd
        | O::Isub
        | O::Imul
        | O::Ineg
        | O::Udiv
        | O::Sdiv
        | O::Urem
        | O::Srem
        | O::GuardDivZero { .. }
        | O::GuardNull { .. }
        | O::GuardShiftRange { .. }
        | O::GuardOverflow { .. }
        | O::GuardBoundsCheck { .. }
        | O::GuardBoundsCheckDyn { .. }
        | O::Assert
        | O::Bnot
        | O::Band
        | O::Bor
        | O::Bxor
        | O::BandNot
        | O::BorNot
        | O::CtPop
        | O::Crc32 { .. }
        | O::Fneg
        | O::Fabs
        | O::Fsqrt
        | O::Ffloor
        | O::Fceil
        | O::Ftrunc
        | O::Ishl
        | O::Ushr
        | O::Sshr
        | O::Sextend { .. }
        | O::Uextend { .. }
        | O::ExtractBits { .. }
        | O::SextractBits { .. }
        | O::InsertBits { .. }
        | O::V4I32MaskExtract
        | O::V16I8MaskExtract
        | O::V8I16MaskExtract
        | O::V2I64MaskExtract { .. }
        | O::V4I32PackLanes
        | O::V2I64PackLanes
        | O::V16I8PackLanes
        | O::V8I16PackLanes
        | O::V8I8PackLanes
        | O::V2I64Add
        | O::V2I64Sub
        | O::V2I64Mul
        | O::V4I32Add
        | O::V4I32Sub
        | O::V4I32Mul
        | O::V16I8Add
        | O::V16I8Sub
        | O::V16I8Mul
        | O::V8I16Add
        | O::V8I16Sub
        | O::V8I16Mul
        | O::V16I8Icmp { .. }
        | O::V8I16Icmp { .. }
        | O::V4I32Icmp { .. }
        | O::V2I64Icmp { .. }
        | O::V8I8Icmp { .. }
        | O::V4I32ExtractLane { .. }
        | O::V4I32InsertLane { .. }
        | O::V2I64ExtractLane { .. }
        | O::V2I64InsertLane { .. }
        | O::V16I8ExtractLane { .. }
        | O::V16I8InsertLane { .. }
        | O::V8I16ExtractLane { .. }
        | O::V8I16InsertLane { .. }
        | O::V4F32Fadd
        | O::V4F32Fsub
        | O::V4F32Fmul
        | O::V4F32Fdiv
        | O::V2F64Fadd
        | O::V2F64Fsub
        | O::V2F64Fmul
        | O::V2F64Fdiv
        | O::V4F32Fmuladd
        | O::V2F64Fmuladd
        | O::V2F64ExtractLane { .. }
        | O::Select { .. }
        | O::Fadd
        | O::Fsub
        | O::Fmul
        | O::Fdiv
        | O::Fma
        | O::Fmuladd
        | O::Aarch64FmaddAsm
        | O::Aarch64FsqrtAsm
        | O::Aarch64FrintnAsm
        | O::Fmin
        | O::Fmax
        | O::FcvtToInt { .. }
        | O::FcvtToUint { .. }
        | O::FcvtFromInt { .. }
        | O::FcvtFromUint { .. }
        | O::FPExt
        | O::FPTrunc
        | O::Trunc { .. }
        | O::Bitcast { .. }
        | O::GlobalRef { .. }
        | O::FunctionAddr { .. }
        | O::ExternRef { .. }
        | O::TlsRef { .. }
        | O::StackAddr { .. }
        | O::StructGep { .. }
        | O::ArrayGep { .. }
        | O::Jump { .. }
        | O::Brif { .. }
        | O::Trap
        | O::Return
        | O::Switch { .. }
        | O::LandingPad { .. }
        | O::Resume
        | O::Call { .. }
        | O::CallIndirect
        | O::CallVariadic { .. }
        | O::Invoke { .. }
        | O::Load { .. }
        | O::VolatileLoad { .. }
        | O::Store { .. }
        | O::VolatileStore { .. }
        | O::AtomicLoad { .. }
        | O::AtomicStore { .. }
        | O::AtomicRmw { .. }
        | O::CmpXchg { .. }
        | O::Fence { .. }
        | O::Memcpy
        | O::Memmove
        | O::Memset => CcSet::EMPTY,
    }
}

// ---------------------------------------------------------------------------
// CSEL
// ---------------------------------------------------------------------------

/// The condition codes a correct AArch64 lowering of `source` may place on an
/// emitted `CSEL`.
///
/// `select_csel` (`isel.rs`) tests the select's boolean with `CMP cond,#0` and
/// uses `from_intcc(Select.cond)` — UNLESS `detect_select_cond_folds` folded
/// the compare that defines the boolean into the select's own flag test, in
/// which case the `CSEL` carries the FOLDED compare's code, or its complement
/// when the select's own sense is `Eq`. That is why this takes the whole
/// [`LirSourceInst`]: the folded condition belongs to a DIFFERENT LIR
/// instruction (`cond_def_opcode`), and reading it off the emitted `CSEL` is
/// exactly the self-attestation this module exists to remove.
///
/// The i128 variable-shift decomposition also emits `CSEL`s while lowering
/// `Ishl`/`Ushr`/`Sshr`; its two guard conditions are `EQ` (the `shift == 0`
/// spill guard) and `HS` (the `shift >= 64` selector).
pub fn csel_conditions(source: &LirSourceInst) -> CcSet {
    use LirOpcode as O;
    match &source.opcode {
        O::Select { cond } => {
            let own = CcSet::of(&[from_intcc(*cond)]);
            // The fold only fires for the boolean-sense selects (`Ne` keeps the
            // folded code, `Eq` inverts it); anything else stays on the
            // `CMP cond,#0` path and carries the select's own code.
            if !matches!(cond, IntCC::NotEqual | IntCC::Equal) {
                return own;
            }
            let folded = match source.cond_def_opcode.as_ref() {
                // A folded `Icmp` re-emits `CMP`/`CMP #imm`; a folded `Band`
                // + `Icmp` pair becomes a single `TST` on the same code.
                Some(O::Icmp { cond: inner }) => {
                    let code = from_intcc(*inner);
                    CcSet::of(&[code, invert(code)])
                }
                // A folded single-CC `Fcmp` re-emits `FCMP` straight into the
                // CSEL; the two-CC forms (`NotEqual`, `UnorderedEqual`) are
                // never folded, so only the single-CC codes and their
                // complements can appear.
                Some(O::Fcmp { cond: inner }) => {
                    let mut set = CcSet::EMPTY;
                    for code in fcmp_conditions(*inner).codes() {
                        set = set.union(CcSet::of(&[code, invert(code)]));
                    }
                    set
                }
                _ => CcSet::EMPTY,
            };
            own.union(folded)
        }
        // The i128 variable-shift funnel (`select_i128_shl`/`_lshr`/`_ashr`).
        O::Ishl | O::Ushr | O::Sshr => CcSet::of(&[cc::EQ, cc::HS]),
        // Every other source: no in-tree lowering emits a `CSEL` while
        // dispatching it, so one stamped from it fails closed. Written as a
        // catch-all DELIBERATELY, unlike `cset_conditions`: `CSEL` bindings
        // additionally require the source's coarse class, so this arm is
        // reached only for `Select`/`Shift`-class sources, and an exhaustive
        // list here would duplicate that file's 120-arm enumeration without
        // adding a decision.
        _ => CcSet::EMPTY,
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    const ALL_INTCC: &[IntCC] = &[
        IntCC::Equal,
        IntCC::NotEqual,
        IntCC::SignedLessThan,
        IntCC::SignedGreaterThanOrEqual,
        IntCC::SignedGreaterThan,
        IntCC::SignedLessThanOrEqual,
        IntCC::UnsignedLessThan,
        IntCC::UnsignedGreaterThanOrEqual,
        IntCC::UnsignedGreaterThan,
        IntCC::UnsignedLessThanOrEqual,
    ];

    /// THE fact witness 1 turns on: no integer comparison's lowering can put
    /// `MI`, `PL`, `VS` or `VC` on a `CSET`. Those four are exactly the
    /// conditions with no `Icmp_*` registry family member, i.e. the four for
    /// which `NoProofMapping` used to be the LAST barrier.
    #[test]
    fn no_integer_compare_admits_a_flag_only_condition() {
        for cond in ALL_INTCC {
            let set = cset_conditions(&LirOpcode::Icmp { cond: *cond });
            for code in [cc::MI, cc::PL, cc::VS, cc::VC] {
                assert!(
                    !set.contains(code),
                    "Icmp {cond:?} must not admit cc {code}: {:?}",
                    set.codes()
                );
            }
        }
    }

    /// The scalar lowering's own condition is always admitted — the genuine
    /// path must keep promoting.
    #[test]
    fn every_integer_compare_admits_its_own_scalar_condition() {
        for cond in ALL_INTCC {
            let set = cset_conditions(&LirOpcode::Icmp { cond: *cond });
            assert!(
                set.contains(from_intcc(*cond)),
                "Icmp {cond:?} must admit its own scalar cc"
            );
        }
    }

    /// And a condition from a DIFFERENT comparison is refused. `SLT -> SGT` is
    /// the mutation the inventory gate was blind to before this module: both
    /// have an `Icmp_*` family member, so the citation simply moved.
    #[test]
    fn a_foreign_comparison_condition_is_refused() {
        let slt = cset_conditions(&LirOpcode::Icmp {
            cond: IntCC::SignedLessThan,
        });
        assert!(!slt.contains(cc::GT), "SLT must not admit GT");
        assert!(!slt.contains(cc::GE), "SLT must not admit GE");
        assert!(!slt.contains(cc::LE), "SLT must not admit LE");
        assert!(!slt.contains(cc::HI), "SLT must not admit HI");
        assert!(!slt.contains(cc::NE), "SLT must not admit NE");
        // The i128 limb decomposition of a signed less-than legitimately emits
        // LT (high limbs), EQ (high limbs equal) and LO (low limbs, unsigned).
        assert_eq!(slt.codes(), vec![cc::EQ, cc::LO, cc::LT]);
    }

    /// The checked-arithmetic rows disambiguate SIGNED from UNSIGNED on the
    /// SOURCE side, which is the fact `cset_checked_overflow_query` used to
    /// take from the emitted condition.
    #[test]
    fn checked_arithmetic_conditions_are_signedness_split() {
        assert!(cset_conditions(&LirOpcode::CheckedSadd).contains(cc::VS));
        assert!(!cset_conditions(&LirOpcode::CheckedSadd).contains(cc::HS));
        assert!(cset_conditions(&LirOpcode::CheckedUadd).contains(cc::HS));
        assert!(cset_conditions(&LirOpcode::CheckedUsub).contains(cc::LO));
        assert!(!cset_conditions(&LirOpcode::CheckedUsub).contains(cc::HS));
    }

    /// A non-condition-carrying source admits nothing, so a `CSET` stamped
    /// from it fails closed.
    #[test]
    fn an_unconditional_source_admits_no_cset() {
        assert!(cset_conditions(&LirOpcode::Iadd).is_empty());
        assert!(cset_conditions(&LirOpcode::Copy).is_empty());
        assert!(cset_conditions(&LirOpcode::Select { cond: IntCC::Equal }).is_empty());
    }

    /// A `CSEL` from an UNFOLDED select carries the select's own code; with a
    /// folded `Icmp` it carries that compare's code or its complement, and
    /// NOTHING else.
    #[test]
    fn csel_conditions_track_the_folded_compare() {
        let unfolded = LirSourceInst {
            digest: trust_cg_ir::provenance::SourceInstDigest(0),
            class: crate::provenance_xcheck::OpClass::Select,
            opcode_debug: String::new(),
            opcode: LirOpcode::Select {
                cond: IntCC::NotEqual,
            },
            cond_def_opcode: None,
            args: Vec::new(),
            results: Vec::new(),
            value_flow: Default::default(),
        };
        assert_eq!(csel_conditions(&unfolded).codes(), vec![cc::NE]);

        let folded = LirSourceInst {
            cond_def_opcode: Some(LirOpcode::Icmp {
                cond: IntCC::UnsignedLessThan,
            }),
            ..unfolded.clone()
        };
        // NE (unfolded route) plus LO and its complement HS (folded route).
        assert_eq!(
            csel_conditions(&folded).codes(),
            vec![cc::NE, cc::HS, cc::LO]
        );
        assert!(!csel_conditions(&folded).contains(cc::MI));
    }

    /// The i128 variable-shift funnel's two guards, and only those.
    #[test]
    fn i128_shift_csel_admits_only_the_two_chain_guards() {
        for opcode in [LirOpcode::Ishl, LirOpcode::Ushr, LirOpcode::Sshr] {
            let source = LirSourceInst {
                digest: trust_cg_ir::provenance::SourceInstDigest(0),
                class: crate::provenance_xcheck::OpClass::Shift,
                opcode_debug: String::new(),
                opcode,
                cond_def_opcode: None,
                args: Vec::new(),
                results: Vec::new(),
                value_flow: Default::default(),
            };
            assert_eq!(csel_conditions(&source).codes(), vec![cc::EQ, cc::HS]);
        }
    }

    /// The emission COUNT separates the scalar lowering from the i128 limb
    /// decomposition. At count 1 only the comparison's own code is admitted;
    /// the limb conditions appear only when the lowering emitted the limb
    /// selects too.
    #[test]
    fn the_emission_count_separates_scalar_from_i128_limbs() {
        let slt = LirOpcode::Icmp {
            cond: IntCC::SignedLessThan,
        };
        assert_eq!(
            cset_conditions_for_emission_count(&slt, 1).codes(),
            vec![cc::LT],
            "a SCALAR signed less-than emits exactly CSET LT"
        );
        for count in [2, 3] {
            assert_eq!(
                cset_conditions_for_emission_count(&slt, count).codes(),
                vec![cc::EQ, cc::LO, cc::LT],
                "the i128 limb decomposition emits LT, EQ and LO"
            );
        }
        for count in [0, 4, 9] {
            assert!(
                cset_conditions_for_emission_count(&slt, count).is_empty(),
                "an unpredicted emission count must fail closed, count={count}"
            );
        }
        // Non-comparison sources are count-insensitive.
        assert_eq!(
            cset_conditions_for_emission_count(&LirOpcode::CheckedUadd, 1).codes(),
            cset_conditions(&LirOpcode::CheckedUadd).codes()
        );
    }

    /// The role table is a REFINEMENT of the count-2/3 set, never a widening:
    /// every role admits exactly one condition from that set, the roles
    /// together cover exactly the i128 decomposition's conditions, and a role
    /// the lowering does not have admits nothing.
    #[test]
    fn every_i128_limb_role_admits_exactly_one_condition_of_the_set() {
        use I128CmpCsetRole::*;
        for cond in ALL_INTCC {
            let (count, roles, absent): (usize, &[I128CmpCsetRole], &[I128CmpCsetRole]) = match cond
            {
                IntCC::Equal => (
                    2,
                    &[LimbConjunct],
                    &[LimbDisjunct, HighDecision, HighEqual, LowDecision],
                ),
                IntCC::NotEqual => (
                    2,
                    &[LimbDisjunct],
                    &[LimbConjunct, HighDecision, HighEqual, LowDecision],
                ),
                _ => (
                    3,
                    &[HighDecision, HighEqual, LowDecision],
                    &[LimbConjunct, LimbDisjunct],
                ),
            };
            let set = cset_conditions_for_emission_count(&LirOpcode::Icmp { cond: *cond }, count);
            let mut covered = CcSet::EMPTY;
            for role in roles {
                let code = i128_cmp_role_condition(*cond, *role)
                    .unwrap_or_else(|| panic!("{cond:?}/{role:?} admits nothing"));
                assert!(
                    set.contains(code),
                    "{cond:?}/{role:?} admits {code} outside the set"
                );
                covered = covered.union(CcSet::of(&[code]));
            }
            assert_eq!(covered, i128_cmp_limb_conditions(*cond), "{cond:?}");
            for role in absent {
                assert_eq!(
                    i128_cmp_role_condition(*cond, *role),
                    None,
                    "{cond:?}/{role:?}"
                );
            }
        }
        // The case the SET could not tell apart: a signed `<` admits `LT` only
        // on the high decision, `EQ` only on the high equality, `LO` only low.
        let slt = IntCC::SignedLessThan;
        assert_eq!(i128_cmp_role_condition(slt, HighDecision), Some(cc::LT));
        assert_eq!(i128_cmp_role_condition(slt, HighEqual), Some(cc::EQ));
        assert_eq!(i128_cmp_role_condition(slt, LowDecision), Some(cc::LO));
    }

    /// `CcSet` is a set: union is idempotent, out-of-range codes are refused.
    #[test]
    fn ccset_is_a_set() {
        let set = CcSet::of(&[cc::EQ, cc::EQ, cc::LT]);
        assert_eq!(set.codes(), vec![cc::EQ, cc::LT]);
        assert_eq!(set.union(set), set);
        assert!(!set.contains(-1));
        assert!(!set.contains(cc::COUNT));
        assert!(!set.contains(99));
        assert!(CcSet::EMPTY.is_empty());
    }
}
