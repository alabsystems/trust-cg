//! Semantics for decoded A64 conditional-select instruction words.
//!
//! This module does not register a proof, authorize a lowering, or mint a
//! verification receipt by itself. Its concrete and symbolic models are the
//! machine side of the per-instruction select/CSET obligations that
//! `aarch64_flag_consumer_proofs` builds and registers; the correspondence
//! claims, controls and evidence strength are stated there. No source
//! operation is inferred from the emitted opcode.
//!
//! Reference: Arm DDI 0602 ID062025 (ISA XML 2025-06), CSEL pp373–374,
//! CSINC pp379–380, CSINV pp381–382, CSNEG pp383–384, and ConditionHolds p5947.
//! <https://documentation-service.arm.com/static/685eb35c3cb5b729562ba389>
//!
//! Only X0–X30, SP and packed NZCV are represented. There is no PC, memory,
//! exception, timing, DIT, source-CFG, or executable-publication theorem here.

use crate::nzcv::NzcvFlags;
use crate::smt::{SmtExpr, SmtSort};
use trust_cg_ir::CondCode;

/// The four architectural variants, not a source-language operation binding.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ConditionalSelectOperation {
    Csel,
    Csinc,
    Csinv,
    Csneg,
}

/// The architectural data width, including the W-write upper-half clearing.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ConditionalSelectWidth {
    W32,
    X64,
}

impl ConditionalSelectWidth {
    pub const fn bits(self) -> u32 {
        match self {
            Self::W32 => 32,
            Self::X64 => 64,
        }
    }

    const fn mask(self) -> u64 {
        match self {
            Self::W32 => u32::MAX as u64,
            Self::X64 => u64::MAX,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, thiserror::Error)]
pub enum ConditionalSelectError {
    #[error("word {0:#010x} is not a conditional-select-family encoding")]
    InvalidEncoding(u32),
    #[error("packed NZCV {0:#x} is not a four-bit value")]
    InvalidNzcv(u8),
    #[error("condition {0:#x} is not a four-bit encoding")]
    InvalidCondition(u8),
    #[error("symbolic {0} has the wrong sort for the architectural state")]
    InvalidSymbolicSort(&'static str),
}

/// Concrete register pre/post state. Register 31 is deliberately absent: these
/// instructions read it as zero and discard writes, never read or write SP.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RegisterState {
    pub x: [u64; 31],
    pub sp: u64,
    /// N, Z, C, V in bits 3, 2, 1, 0, respectively; upper bits must be zero.
    pub nzcv: u8,
}

/// Symbolic state is constructed from width-correct variables, then composed
/// only through this model. Private fields prevent callers from injecting a
/// malformed or wrong-sort AST as an architectural register. Variables are
/// named `x0` through `x30`, `sp`, and `nzcv`; no authority attaches to names.
#[derive(Clone, Debug)]
pub struct SymbolicRegisterState {
    x: [SmtExpr; 31],
    sp: SmtExpr,
    nzcv: SmtExpr,
}

impl SymbolicRegisterState {
    pub fn variables() -> Self {
        Self {
            x: std::array::from_fn(|index| SmtExpr::var(format!("x{index}"), 64)),
            sp: SmtExpr::var("sp", 64),
            nzcv: SmtExpr::var("nzcv", 4),
        }
    }

    /// Build a state from caller expressions. Every general register and SP
    /// must be a 64-bit bitvector and NZCV a 4-bit one; a wrong-sort AST is
    /// refused rather than silently composed.
    pub fn from_parts(
        x: [SmtExpr; 31],
        sp: SmtExpr,
        nzcv: SmtExpr,
    ) -> Result<Self, ConditionalSelectError> {
        if x.iter()
            .any(|register| register.sort() != SmtSort::BitVec(64))
        {
            return Err(ConditionalSelectError::InvalidSymbolicSort("register"));
        }
        if sp.sort() != SmtSort::BitVec(64) {
            return Err(ConditionalSelectError::InvalidSymbolicSort("SP"));
        }
        if nzcv.sort() != SmtSort::BitVec(4) {
            return Err(ConditionalSelectError::InvalidSymbolicSort("NZCV"));
        }
        Ok(Self { x, sp, nzcv })
    }

    pub fn register(&self, index: usize) -> Option<&SmtExpr> {
        self.x.get(index)
    }

    pub fn sp(&self) -> &SmtExpr {
        &self.sp
    }

    pub fn nzcv(&self) -> &SmtExpr {
        &self.nzcv
    }

    /// Replace one architectural register slot with a caller-supplied term.
    ///
    /// The slot keeps its architectural sort: `value` is admitted only as a
    /// 64-bit bitvector, which is what [`Self::variables`] puts there and what
    /// [`DecodedConditionalSelect::execute_symbolic`] reads and writes. A
    /// wrong-sort term, or an index outside X0–X30, is REFUSED rather than
    /// silently admitted — the same invariant the private fields exist to
    /// protect. Register 31 has no slot here (it reads as zero and discards
    /// writes), so `index >= 31` refuses.
    ///
    /// This grants no authority: substituting a term does not make the
    /// resulting state a proof of anything. It exists so a separately checked
    /// obligation can name its own source operands in the architectural model
    /// instead of re-deriving the model from the spec.
    #[must_use]
    pub fn with_register(mut self, index: u8, value: SmtExpr) -> Option<Self> {
        if value.sort() != crate::smt::SmtSort::BitVec(64) {
            return None;
        }
        *self.x.get_mut(usize::from(index))? = value;
        Some(self)
    }

    /// Replace the packed NZCV slot with a caller-supplied term.
    ///
    /// Admitted only as the architectural 4-bit bitvector (N,Z,C,V in bits
    /// 3..0) — the sort [`Self::variables`] declares and the one
    /// [`condition_expression`] indexes. Any other sort is REFUSED.
    #[must_use]
    pub fn with_nzcv(mut self, nzcv: SmtExpr) -> Option<Self> {
        if nzcv.sort() != crate::smt::SmtSort::BitVec(4) {
            return None;
        }
        self.nzcv = nzcv;
        Some(self)
    }
}

/// Exact decoded fields. Instances can only be obtained from an admitted word;
/// neither a caller-supplied mnemonic nor the compiler's encoder is consulted.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct DecodedConditionalSelect {
    width: ConditionalSelectWidth,
    operation: ConditionalSelectOperation,
    destination: u8,
    true_source: u8,
    false_source: u8,
    condition: u8,
}

impl DecodedConditionalSelect {
    pub fn decode(word: u32) -> Result<Self, ConditionalSelectError> {
        // Fixed S=0, bits28:21=11010100, bit11=0. Bit30 (op) and
        // bit10 (o2) select the four variants; bit31 is the data width.
        if word & 0x3fe0_0800 != 0x1a80_0000 {
            return Err(ConditionalSelectError::InvalidEncoding(word));
        }
        let operation = match ((word >> 30) & 1, (word >> 10) & 1) {
            (0, 0) => ConditionalSelectOperation::Csel,
            (0, 1) => ConditionalSelectOperation::Csinc,
            (1, 0) => ConditionalSelectOperation::Csinv,
            _ => ConditionalSelectOperation::Csneg,
        };
        Ok(Self {
            width: if word >> 31 == 0 {
                ConditionalSelectWidth::W32
            } else {
                ConditionalSelectWidth::X64
            },
            operation,
            destination: (word & 31) as u8,
            true_source: ((word >> 5) & 31) as u8,
            false_source: ((word >> 16) & 31) as u8,
            condition: ((word >> 12) & 15) as u8,
        })
    }

    pub const fn width(self) -> ConditionalSelectWidth {
        self.width
    }

    pub const fn operation(self) -> ConditionalSelectOperation {
        self.operation
    }

    /// `(Rd, Rn, Rm)`, with 31 denoting ZR, never SP.
    pub const fn registers(self) -> (u8, u8, u8) {
        (self.destination, self.true_source, self.false_source)
    }

    pub const fn condition(self) -> u8 {
        self.condition
    }

    /// Interpret one decoded instruction without mutating the supplied state.
    pub fn execute(self, before: &RegisterState) -> Result<RegisterState, ConditionalSelectError> {
        let holds = condition_holds(self.condition, before.nzcv)?;
        let read =
            |index: u8| before.x.get(usize::from(index)).copied().unwrap_or(0) & self.width.mask();
        // Both reads precede the architectural write, including Rd==Rn/Rm.
        let rn = read(self.true_source);
        let rm = read(self.false_source);
        let result = if holds {
            rn
        } else {
            match self.operation {
                ConditionalSelectOperation::Csel => rm,
                ConditionalSelectOperation::Csinc => rm.wrapping_add(1),
                ConditionalSelectOperation::Csinv => !rm,
                ConditionalSelectOperation::Csneg => (!rm).wrapping_add(1),
            }
        } & self.width.mask();
        let mut after = before.clone();
        if let Some(destination) = after.x.get_mut(usize::from(self.destination)) {
            // Assigning the masked value to the full X slot models W zero-ext.
            *destination = result;
        }
        Ok(after)
    }

    /// Build bitvector expressions for the same architectural pre/post-state
    /// relation. This constructs no ProofObligation and runs no proof checker.
    pub fn execute_symbolic(self, before: &SymbolicRegisterState) -> SymbolicRegisterState {
        self.execute_symbolic_condition(
            before,
            condition_expression(self.condition, before.nzcv.clone()),
        )
    }

    /// Execute using explicit Bool-sorted NZCV terms instead of extracting
    /// the condition's bits from the state's packed NZCV expression.
    ///
    /// The explicit flags OVERRIDE `before.nzcv`: the returned packed slot is
    /// exactly `pack_nzcv(flags)`, even when the old slot differs. Registers and
    /// SP still come from `before`; all source reads precede the destination
    /// write. Every flag must have Bool sort, including flags the condition
    /// does not consume. This builds a relation, not proof or lowering credit.
    pub fn execute_symbolic_with_flag_terms(
        self,
        before: &SymbolicRegisterState,
        flags: &NzcvFlags,
    ) -> Result<SymbolicRegisterState, ConditionalSelectError> {
        if [&flags.n, &flags.z, &flags.c, &flags.v]
            .into_iter()
            .any(|flag| flag.sort() != SmtSort::Bool)
        {
            return Err(ConditionalSelectError::InvalidSymbolicSort("NZCV flag"));
        }
        let condition = condition_holds_flags(self.condition, flags)?;
        let mut after = self.execute_symbolic_condition(before, condition);
        after.nzcv = crate::nzcv::pack_nzcv(flags);
        Ok(after)
    }

    // Both public interfaces retain one select-arm/read-before-write/W-write
    // implementation. The packed interface keeps its prior condition AST.
    fn execute_symbolic_condition(
        self,
        before: &SymbolicRegisterState,
        condition: SmtExpr,
    ) -> SymbolicRegisterState {
        let width = self.width.bits();
        let read = |index: u8| {
            let value = before
                .x
                .get(usize::from(index))
                .cloned()
                .unwrap_or_else(|| SmtExpr::bv_const(0, 64));
            if width == 32 {
                value.extract(31, 0)
            } else {
                value
            }
        };
        let rn = read(self.true_source);
        let rm = read(self.false_source);
        let false_value = match self.operation {
            ConditionalSelectOperation::Csel => rm,
            ConditionalSelectOperation::Csinc => rm.bvadd(SmtExpr::bv_const(1, width)),
            ConditionalSelectOperation::Csinv => {
                rm.bvxor(SmtExpr::bv_const(self.width.mask(), width))
            }
            ConditionalSelectOperation::Csneg => rm
                .bvxor(SmtExpr::bv_const(self.width.mask(), width))
                .bvadd(SmtExpr::bv_const(1, width)),
        };
        let result = SmtExpr::ite(condition, rn, false_value);
        let result = if width == 32 {
            result.zero_ext(32)
        } else {
            result
        };
        let mut after = before.clone();
        if let Some(destination) = after.x.get_mut(usize::from(self.destination)) {
            *destination = result;
        }
        after
    }
}

/// Architectural ConditionHolds over a four-bit condition and packed NZCV.
/// In particular, both AL (14) and NV (15) are true; neither complements the
/// other. Invalid external nibble values are rejected, not silently masked.
pub fn condition_holds(condition: u8, nzcv: u8) -> Result<bool, ConditionalSelectError> {
    CondCode::from_encoding(i64::from(condition))
        .ok_or(ConditionalSelectError::InvalidCondition(condition))?
        .holds(nzcv)
        .ok_or(ConditionalSelectError::InvalidNzcv(nzcv))
}

fn condition_expression(condition: u8, nzcv: SmtExpr) -> SmtExpr {
    let bit = |index| {
        nzcv.clone()
            .extract(index, index)
            .eq_expr(SmtExpr::bv_const(1, 1))
    };
    condition_over_flags(
        condition,
        &NzcvFlags {
            n: bit(3),
            z: bit(2),
            c: bit(1),
            v: bit(0),
        },
    )
}

/// Architectural ConditionHolds for a four-bit condition field over
/// Bool-sorted flags (no packed-NZCV extraction), as a Bool expression. AL and
/// NV are both true. Values above 15 are rejected, not masked.
pub fn condition_holds_flags(
    condition: u8,
    flags: &NzcvFlags,
) -> Result<SmtExpr, ConditionalSelectError> {
    if condition > 15 {
        return Err(ConditionalSelectError::InvalidCondition(condition));
    }
    Ok(condition_over_flags(condition, flags))
}

/// ConditionHolds over Bool-sorted flags, for a condition already in 0..=15.
fn condition_over_flags(condition: u8, flags: &NzcvFlags) -> SmtExpr {
    let (n, z, c, v) = (
        flags.n.clone(),
        flags.z.clone(),
        flags.c.clone(),
        flags.v.clone(),
    );
    let base = match condition >> 1 {
        0 => z,
        1 => c,
        2 => n,
        3 => v,
        4 => c.and_expr(z.not_expr()),
        5 => n.eq_expr(v),
        6 => n.eq_expr(v).and_expr(z.not_expr()),
        _ => SmtExpr::bool_const(true),
    };
    if condition & 1 != 0 && condition != 15 {
        base.not_expr()
    } else {
        base
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::smt::{EvalEnv, EvalResult, SmtSort};

    // Independent condition oracle: each literal's bit k is the truth value
    // for packed NZCV k. This truth-table transcription does not call the
    // model's grouped condition decoder or the production compiler helpers.
    const TRUTH: [u16; 16] = [
        0xf0f0, 0x0f0f, 0xcccc, 0x3333, 0xff00, 0x00ff, 0xaaaa, 0x5555, 0x0c0c, 0xf3f3, 0xaa55,
        0x55aa, 0x0a05, 0xf5fa, 0xffff, 0xffff,
    ];
    const BASES: [(u32, ConditionalSelectOperation); 4] = [
        (0x1a80_0000, ConditionalSelectOperation::Csel),
        (0x1a80_0400, ConditionalSelectOperation::Csinc),
        (0x5a80_0000, ConditionalSelectOperation::Csinv),
        (0x5a80_0400, ConditionalSelectOperation::Csneg),
    ];
    const LAYOUTS: [(u8, u8, u8); 12] = [
        (0, 1, 2),
        (1, 1, 2),
        (2, 1, 2),
        (0, 1, 1),
        (1, 1, 1),
        (0, 31, 2),
        (0, 1, 31),
        (31, 1, 2),
        (0, 31, 31),
        (31, 31, 31),
        (30, 29, 28),
        (30, 30, 30),
    ];
    const VALUES: [u64; 10] = [
        0,
        1,
        2,
        u64::MAX,
        0x7fff_ffff,
        0x8000_0000,
        0xffff_ffff,
        0x8000_0000_0000_0000,
        0x0123_4567_89ab_cdef,
        0xfedc_ba98_7654_3210,
    ];

    fn word(base: u32, x64: bool, cc: u8, (rd, rn, rm): (u8, u8, u8)) -> u32 {
        base | ((x64 as u32) << 31)
            | (u32::from(rm) << 16)
            | (u32::from(cc) << 12)
            | (u32::from(rn) << 5)
            | u32::from(rd)
    }

    fn state(flags: u8, rn: u8, rm: u8, a: u64, b: u64) -> RegisterState {
        let mut result = RegisterState {
            x: std::array::from_fn(|index| 0xa510_cafe_0000_0000 | index as u64),
            sp: 0x1234_0000_0080,
            nzcv: flags,
        };
        if rn < 31 {
            result.x[usize::from(rn)] = a;
        }
        if rm < 31 {
            result.x[usize::from(rm)] = b;
        }
        result
    }

    fn oracle(
        before: &RegisterState,
        x64: bool,
        variant: usize,
        cc: u8,
        (rd, rn, rm): (u8, u8, u8),
    ) -> RegisterState {
        // Intent arguments come from the test matrix, not decoded output.
        let read = |r: u8| if r == 31 { 0 } else { before.x[usize::from(r)] };
        let take_true = TRUTH[usize::from(cc)] & (1u16 << before.nzcv) != 0;
        let selected = if take_true {
            read(rn)
        } else {
            let b = read(rm);
            match variant {
                0 => b,
                1 => b.wrapping_add(1),
                2 => b ^ u64::MAX,
                3 => 0u64.wrapping_sub(b),
                _ => unreachable!("test inventory has exactly four operations"),
            }
        };
        let mut after = before.clone();
        if rd != 31 {
            after.x[usize::from(rd)] = if x64 {
                selected
            } else {
                u64::from(selected as u32)
            };
        }
        after
    }

    #[test]
    fn condition_table_covers_every_nzcv_and_condition_without_nv_inversion() {
        let mut cases = 0;
        for cc in 0..16u8 {
            let expression = condition_expression(cc, SmtExpr::var("nzcv", 4));
            for flags in 0..16u8 {
                let expected = TRUTH[usize::from(cc)] & (1u16 << flags) != 0;
                assert_eq!(condition_holds(cc, flags), Ok(expected));
                let mut env = EvalEnv::default();
                env.insert("nzcv".into(), flags.into());
                assert_eq!(expression.eval(&env), EvalResult::Bool(expected));
                cases += 1;
            }
        }
        assert_eq!(cases, 256);
        for flags in 0..16 {
            assert_eq!(condition_holds(14, flags), Ok(true));
            assert_eq!(condition_holds(15, flags), Ok(true));
        }
        for invalid in 16..=255 {
            assert!(condition_holds(invalid, 0).is_err());
            assert!(condition_holds(0, invalid).is_err());
        }
    }

    #[test]
    fn decoder_checks_fixed_fields_and_all_register_fields() {
        let mut accepted = 0;
        for (base, operation) in BASES {
            for x64 in [false, true] {
                for cc in 0..16 {
                    for r in 0..32 {
                        let layout = (r, (r + 7) % 32, (r + 19) % 32);
                        let raw = word(base, x64, cc, layout);
                        let decoded = DecodedConditionalSelect::decode(raw).unwrap();
                        assert_eq!(decoded.operation(), operation);
                        assert_eq!(decoded.condition(), cc);
                        assert_eq!(decoded.registers(), layout);
                        assert_eq!(decoded.width().bits(), if x64 { 64 } else { 32 });
                        for fixed_bit in [11, 21, 22, 23, 24, 25, 26, 27, 28, 29] {
                            assert!(
                                DecodedConditionalSelect::decode(raw ^ (1 << fixed_bit)).is_err()
                            );
                        }
                        accepted += 1;
                    }
                }
            }
        }
        assert_eq!(accepted, 4096);
        for other in [0, u32::MAX, 0xd65f_03c0, 0x9e62_0020, 0x1e22_0c20] {
            assert!(DecodedConditionalSelect::decode(other).is_err());
        }
    }

    #[test]
    fn concrete_values_aliases_zr_width_and_full_poststate_match_independent_oracle() {
        let mut cases = 0usize;
        for (variant, (base, _)) in BASES.into_iter().enumerate() {
            for x64 in [false, true] {
                for cc in 0..16 {
                    for layout @ (_, rn, rm) in LAYOUTS {
                        let decoded =
                            DecodedConditionalSelect::decode(word(base, x64, cc, layout)).unwrap();
                        for flags in 0..16 {
                            for a in VALUES {
                                for b in VALUES {
                                    let before = state(flags, rn, rm, a, b);
                                    let original = before.clone();
                                    assert_eq!(
                                        decoded.execute(&before).unwrap(),
                                        oracle(&before, x64, variant, cc, layout)
                                    );
                                    assert_eq!(
                                        before, original,
                                        "input state must remain immutable"
                                    );
                                    cases += 1;
                                }
                            }
                        }
                    }
                }
            }
        }
        assert_eq!(cases, 2_457_600);
        let decoded = DecodedConditionalSelect::decode(0x9a82_0020).unwrap();
        for invalid in 16..=255 {
            assert_eq!(
                decoded.execute(&state(invalid, 1, 2, 1, 2)),
                Err(ConditionalSelectError::InvalidNzcv(invalid))
            );
        }
    }

    #[test]
    fn symbolic_model_is_width_correct_and_matches_independent_poststate() {
        let symbols = SymbolicRegisterState::variables();
        assert!(symbols.register(31).is_none());
        let mut cases = 0usize;
        for (variant, (base, _)) in BASES.into_iter().enumerate() {
            for x64 in [false, true] {
                for cc in 0..16 {
                    for layout @ (rd, rn, rm) in LAYOUTS {
                        let decoded =
                            DecodedConditionalSelect::decode(word(base, x64, cc, layout)).unwrap();
                        let after = decoded.execute_symbolic(&symbols);
                        assert_eq!(after.nzcv().sort(), SmtSort::BitVec(4));
                        assert_eq!(after.sp().sort(), SmtSort::BitVec(64));
                        assert_eq!(after.nzcv(), symbols.nzcv());
                        assert_eq!(after.sp(), symbols.sp());
                        for index in 0..31 {
                            assert_eq!(after.register(index).unwrap().sort(), SmtSort::BitVec(64));
                            if index != usize::from(rd) {
                                assert_eq!(after.register(index), symbols.register(index));
                            }
                        }
                        for flags in 0..16 {
                            for (a, b) in [
                                (0, u64::MAX),
                                (u64::MAX, 1),
                                (0x7fff_ffff, 0x8000_0000),
                                (0x8000_0000_0000_0000, 0xfedc_ba98_7654_3210),
                            ] {
                                let before = state(flags, rn, rm, a, b);
                                let mut env = EvalEnv::default();
                                for (index, value) in before.x.iter().enumerate() {
                                    env.insert(format!("x{index}"), *value);
                                }
                                env.insert("sp".into(), before.sp);
                                env.insert("nzcv".into(), flags.into());
                                let expected = oracle(&before, x64, variant, cc, layout);
                                if rd < 31 {
                                    assert_eq!(
                                        after.register(usize::from(rd)).unwrap().eval(&env),
                                        EvalResult::Bv(expected.x[usize::from(rd)])
                                    );
                                }
                                assert_eq!(after.sp().eval(&env), EvalResult::Bv(expected.sp));
                                assert_eq!(
                                    after.nzcv().eval(&env),
                                    EvalResult::Bv(expected.nzcv.into())
                                );
                                cases += 1;
                            }
                        }
                    }
                }
            }
        }
        assert_eq!(cases, 98_304);
    }

    #[test]
    fn decoded_word_mutations_and_stale_state_answers_are_observably_wrong() {
        let before = state(4, 1, 2, 0xfeed_0000_0000_0017, 0x1234_0000_0000_0042);
        let correct = DecodedConditionalSelect::decode(0x9a82_0020)
            .unwrap()
            .execute(&before)
            .unwrap();
        // Wrong cc, swapped Rn/Rm, W instead of X, and wrong destination.
        for wrong in [0x9a82_1020, 0x9a81_0040, 0x1a82_0020, 0x9a82_0023] {
            assert_ne!(
                DecodedConditionalSelect::decode(wrong)
                    .unwrap()
                    .execute(&before)
                    .unwrap(),
                correct
            );
        }
        // Every wrong variant has a witness while the false arm is selected.
        let before = state(0, 1, 2, 11, 42);
        for (index, (base, _)) in BASES.iter().enumerate() {
            for (other_index, (other, _)) in BASES.iter().enumerate() {
                if index != other_index {
                    let left =
                        DecodedConditionalSelect::decode(word(*base, true, 0, (0, 1, 2))).unwrap();
                    let right =
                        DecodedConditionalSelect::decode(word(*other, true, 0, (0, 1, 2))).unwrap();
                    assert_ne!(
                        left.execute(&before).unwrap(),
                        right.execute(&before).unwrap()
                    );
                }
            }
        }
        let expected = DecodedConditionalSelect::decode(0x1a82_0020)
            .unwrap()
            .execute(&before)
            .unwrap();
        let mut wrong_upper = expected.clone();
        wrong_upper.x[0] |= before.x[0] & 0xffff_ffff_0000_0000;
        assert_ne!(wrong_upper, expected);
        let mut wrong_flags = expected.clone();
        wrong_flags.nzcv ^= 1;
        assert_ne!(wrong_flags, expected);
        let mut wrong_sp = expected.clone();
        wrong_sp.sp = expected.x[0];
        assert_ne!(wrong_sp, expected);

        // Read-before-write: zeroing the destination first corrupts an aliased
        // false source. The actual model must use the original value 42.
        let aliased =
            DecodedConditionalSelect::decode(word(0x5a80_0400, true, 0, (2, 1, 2))).unwrap();
        let mut stale = before.clone();
        stale.x[2] = 0;
        assert_ne!(
            aliased.execute(&before).unwrap(),
            aliased.execute(&stale).unwrap()
        );

        // AL/NV inversion plus arm swap is NOT an equivalent transformation.
        for cc in [14, 15] {
            let ordinary =
                DecodedConditionalSelect::decode(word(0x1a80_0000, true, cc, (0, 1, 2))).unwrap();
            let wrong =
                DecodedConditionalSelect::decode(word(0x1a80_0000, true, cc ^ 1, (0, 2, 1)))
                    .unwrap();
            assert_ne!(
                ordinary.execute(&before).unwrap(),
                wrong.execute(&before).unwrap()
            );
        }
    }

    #[test]
    fn symbolic_composition_reuses_written_register_not_original_variable() {
        let before = state(0, 1, 2, 11, u64::MAX);
        let increment =
            DecodedConditionalSelect::decode(word(0x1a80_0400, false, 0, (2, 1, 2))).unwrap();
        let negate =
            DecodedConditionalSelect::decode(word(0x5a80_0400, true, 0, (1, 2, 2))).unwrap();
        let concrete = negate
            .execute(&increment.execute(&before).unwrap())
            .unwrap();
        let symbolic = negate
            .execute_symbolic(&increment.execute_symbolic(&SymbolicRegisterState::variables()));
        let mut env = EvalEnv::default();
        for (index, value) in before.x.iter().enumerate() {
            env.insert(format!("x{index}"), *value);
        }
        env.insert("sp".into(), before.sp);
        env.insert("nzcv".into(), before.nzcv.into());
        assert_eq!(concrete.x[1], 0);
        assert_eq!(concrete.x[2], 0);
        for (index, value) in concrete.x[..31].iter().enumerate() {
            assert_eq!(
                symbolic.register(index).unwrap().eval(&env),
                EvalResult::Bv(*value)
            );
        }
        assert_eq!(symbolic.sp().eval(&env), EvalResult::Bv(before.sp));
        assert_eq!(
            symbolic.nzcv().eval(&env),
            EvalResult::Bv(before.nzcv.into())
        );
    }

    fn flag_terms() -> NzcvFlags {
        let flag = |name| SmtExpr::var(name, 1).eq_expr(SmtExpr::bv_const(1, 1));
        NzcvFlags {
            n: flag("term_n"),
            z: flag("term_z"),
            c: flag("term_c"),
            v: flag("term_v"),
        }
    }

    #[test]
    fn legacy_packed_interface_retains_exact_value_ast() {
        let before = SymbolicRegisterState::variables();
        for (variant, (base, _)) in BASES.into_iter().enumerate() {
            for x64 in [false, true] {
                let width = if x64 { 64 } else { 32 };
                let mask = if x64 { u64::MAX } else { u32::MAX as u64 };
                for cc in 0..16 {
                    for layout @ (rd, rn, rm) in LAYOUTS {
                        let decoded =
                            DecodedConditionalSelect::decode(word(base, x64, cc, layout)).unwrap();
                        let after = decoded.execute_symbolic(&before);
                        assert_eq!(after.nzcv(), before.nzcv());
                        if rd == 31 {
                            continue;
                        }
                        // Literal pre-factorization AST recipe: this guards
                        // existing registered expression/hash clients, not
                        // just concrete semantic equivalence after a rewrite.
                        let read = |register: u8| {
                            let value = before
                                .register(usize::from(register))
                                .cloned()
                                .unwrap_or_else(|| SmtExpr::bv_const(0, 64));
                            if x64 { value } else { value.extract(31, 0) }
                        };
                        let false_value = match variant {
                            0 => read(rm),
                            1 => read(rm).bvadd(SmtExpr::bv_const(1, width)),
                            2 => read(rm).bvxor(SmtExpr::bv_const(mask, width)),
                            _ => read(rm)
                                .bvxor(SmtExpr::bv_const(mask, width))
                                .bvadd(SmtExpr::bv_const(1, width)),
                        };
                        let expected = SmtExpr::ite(
                            condition_expression(cc, before.nzcv().clone()),
                            read(rn),
                            false_value,
                        );
                        let expected = if x64 { expected } else { expected.zero_ext(32) };
                        assert_eq!(after.register(usize::from(rd)), Some(&expected));
                    }
                }
            }
        }
    }

    #[test]
    fn explicit_flag_terms_match_packed_interface_and_independent_poststate() {
        let symbols = SymbolicRegisterState::variables();
        let flags = flag_terms();
        let packed = crate::nzcv::pack_nzcv(&flags);
        let consistent = symbols.clone().with_nzcv(packed.clone()).unwrap();
        let mut cases = 0;
        for (variant, (base, _)) in BASES.into_iter().enumerate() {
            for x64 in [false, true] {
                for cc in 0..16 {
                    for layout @ (rd, rn, rm) in LAYOUTS {
                        let decoded =
                            DecodedConditionalSelect::decode(word(base, x64, cc, layout)).unwrap();
                        let legacy = decoded.execute_symbolic(&consistent);
                        let direct = decoded
                            .execute_symbolic_with_flag_terms(&symbols, &flags)
                            .unwrap();
                        assert_eq!(legacy.nzcv(), &packed);
                        assert_eq!(direct.nzcv(), &packed);
                        assert_eq!(direct.sp(), symbols.sp());
                        assert_eq!(symbols.nzcv(), &SmtExpr::var("nzcv", 4));
                        for index in 0..31 {
                            assert_eq!(direct.register(index).unwrap().sort(), SmtSort::BitVec(64));
                            if index != usize::from(rd) {
                                assert_eq!(direct.register(index), symbols.register(index));
                            }
                        }
                        for nzcv in 0..16 {
                            for (a, b) in [
                                (0, u64::MAX),
                                (u64::MAX, 1),
                                (0x7fff_ffff, 0x8000_0000),
                                (0x8000_0000_0000_0000, 0xfedc_ba98_7654_3210),
                            ] {
                                let before = state(nzcv, rn, rm, a, b);
                                let expected = oracle(&before, x64, variant, cc, layout);
                                let mut env = EvalEnv::default();
                                for (index, value) in before.x.iter().enumerate() {
                                    env.insert(format!("x{index}"), *value);
                                }
                                env.insert("sp".into(), before.sp);
                                // Old packed state deliberately disagrees;
                                // explicit terms are the new API's input.
                                env.insert("nzcv".into(), u64::from(nzcv ^ 15));
                                for (index, name) in ["term_n", "term_z", "term_c", "term_v"]
                                    .into_iter()
                                    .enumerate()
                                {
                                    env.insert(name.into(), u64::from((nzcv >> (3 - index)) & 1));
                                }
                                if rd < 31 {
                                    let expected = EvalResult::Bv(expected.x[usize::from(rd)]);
                                    assert_eq!(
                                        direct.register(usize::from(rd)).unwrap().eval(&env),
                                        expected
                                    );
                                    assert_eq!(
                                        legacy.register(usize::from(rd)).unwrap().eval(&env),
                                        expected
                                    );
                                }
                                assert_eq!(direct.sp().eval(&env), EvalResult::Bv(expected.sp));
                                assert_eq!(
                                    direct.nzcv().eval(&env),
                                    EvalResult::Bv(u64::from(nzcv))
                                );
                                cases += 1;
                            }
                        }
                    }
                }
            }
        }
        assert_eq!(cases, 98_304);
    }

    #[test]
    fn explicit_flag_terms_refuse_every_wrong_sort_and_avoid_unused_flags() {
        let before = SymbolicRegisterState::variables();
        // Even AL does not bypass the complete explicit-state sort contract.
        let always =
            DecodedConditionalSelect::decode(word(0x1a80_0000, true, 14, (0, 1, 2))).unwrap();
        for index in 0..4 {
            let mut flags = flag_terms();
            *match index {
                0 => &mut flags.n,
                1 => &mut flags.z,
                2 => &mut flags.c,
                _ => &mut flags.v,
            } = SmtExpr::bv_const(1, 1);
            assert_eq!(
                always
                    .execute_symbolic_with_flag_terms(&before, &flags)
                    .err(),
                Some(ConditionalSelectError::InvalidSymbolicSort("NZCV flag"))
            );
        }
        let flags = flag_terms();
        let lt = DecodedConditionalSelect::decode(word(0x1a80_0000, true, 11, (0, 1, 2))).unwrap();
        let direct = lt
            .execute_symbolic_with_flag_terms(&before, &flags)
            .unwrap();
        let value = direct.register(0).unwrap().to_string();
        assert!(value.contains("term_n") && value.contains("term_v"));
        assert!(!value.contains("term_z") && !value.contains("term_c"));
        let packed = direct.nzcv().to_string();
        assert!(packed.contains("term_z") && packed.contains("term_c"));
        let legacy = lt.execute_symbolic(&before);
        assert_eq!(
            legacy.nzcv(),
            before.nzcv(),
            "old interface retains its packed slot"
        );
    }
}

#[path = "aarch64_csel_binding.rs"]
mod binding;
pub use binding::{
    ConditionalSelectBindingError, bind_conditional_select_word, conditional_select_register_fields,
};
