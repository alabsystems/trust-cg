// trust-cg-verify/src/fp_bv_lowering.rs - sound FP -> BV lowering for certificates
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Lower a floating-point obligation to pure bit-vector form, so the proof of
//! its UNSAT can be an Alethe certificate the independent checker replays.
//!
//! # Why
//!
//! The strict gate counts an obligation only when AY's UNSAT arrives with an
//! Alethe proof that Clean fully verifies. Clean's Carcara has no
//! `FloatingPoint` sort, no `RoundingMode` sort and no `fp.*` rule, so no
//! query that mentions them can ever be certified, however AY answers it —
//! 443 of the 699 obligations the 2026-09-28 gate run could not certify were
//! exactly that. This module rewrites such a query into `QF_BV`, a logic whose
//! proofs Clean already replays, without changing what an UNSAT answer means.
//!
//! # The lowering
//!
//! Every FP-sorted term `t` of format `(eb, sb)` is lowered to a bit-vector
//! term `R(t)` of width `W = eb + sb` whose value is AN IEEE-754 bit pattern of
//! the value of `t` — the pattern itself for a finite or infinite value, any
//! NaN pattern for NaN (SMT-LIB has one NaN value, so the payload is not
//! observable). Then:
//!
//! * `((_ to_fp eb sb) b)` (the bit reinterpretation) is `b`; an FP constant
//!   is its bits; an FP input variable becomes a `W`-bit input.
//! * `fp.neg` flips the sign bit and `fp.abs` clears it (a NaN stays a NaN
//!   pattern either way); `ite` over FP lowers branch-wise.
//! * the predicates get their exact bit-level meaning, with
//!   `nan(x) := (x & ABS) >u EXP`,
//!   `key(x) := sign(x) ? -(x & ABS) : (x & ABS)` read as a signed `W`-bit
//!   integer — `key` is order-preserving on non-NaN values and identifies
//!   exactly `+0` and `-0` — and
//!   `fp.lt a b := !nan a & !nan b & key a <s key b`,
//!   `fp.leq a b := !nan a & !nan b & key a <=s key b`,
//!   `fp.eq a b := !nan a & !nan b & key a = key b`,
//!   `fp.gt`/`fp.geq` by swapping, and `isNaN`/`isInfinite`/`isZero`/
//!   `isNormal` on the exponent and magnitude fields.
//! * SMT-LIB `=` on FP (identity of values: NaN = NaN, `+0 != -0`) is
//!   `canon(R a) = canon(R b)` with `canon(x) := nan(x) ? QNAN : x`.
//! * every ROUNDING operation (`fp.add/sub/mul/div/sqrt/fma/roundToIntegral`,
//!   the numeric `to_fp` conversions, `fp.to_sbv`/`fp.to_ubv`) is abstracted:
//!   each distinct application `op(args)` becomes a fresh `W`-bit variable, and
//!   for every pair of applications of the same operator (same rounding mode,
//!   formats, width and out-of-range mode) the query gains the functional
//!   consistency constraint `args1 = args2 => v1 = v2` (Ackermann's
//!   reduction).
//! * a conversion additionally gets the one EXACT fact that holds where no
//!   rounding happens ([`conversion_fact`]): an integer `x` with `|x| <= 2^sb`
//!   converts to its exact pattern, and under RTZ a finite value whose
//!   truncation fits the destination converts to that truncation. Each is a
//!   true statement about the real conversion, stated as an implication, so a
//!   value outside its domain is left exactly as abstract as before.
//!
//! # Why an UNSAT answer about the lowered query is an UNSAT answer about the
//! original
//!
//! Take any model `M` of the original negated obligation. Extend it: give each
//! FP input its IEEE pattern, and give each abstraction variable `v` for
//! `op(args)` an IEEE pattern of `op` applied to the values `args` denote in
//! `M`. By induction on terms, every lowered FP term evaluates to a pattern of
//! the original term's value, and every Bool or bit-vector term evaluates to
//! the original term's value — the predicate definitions above are exact on
//! patterns, `canon` identifies precisely the patterns of one value, and
//! rounding results are the values `M` computes. Two applications of one
//! operator whose argument patterns are equal denote equal argument values,
//! so their results are equal and the consistency constraints hold; the
//! conversion facts hold because they are facts about the real conversions.
//! So `M` extends to a model of the lowered query: if the lowered query is
//! UNSAT, so is the original. The converse fails on purpose — the abstraction forgets
//! what rounding computes — so a lowered SAT is NEVER a counterexample; the
//! caller answers it from the exact FP query instead.
//!
//! What this adds to the trusted base, and nothing else: the bit-level
//! definitions above (validated against the host's IEEE-754 unit and against
//! [`crate::fp_bitmodel`]'s integer-only model in this module's tests, and
//! checkable against AY's own FP theory by
//! `lowered_predicates_agree_with_ay_fp_theory`), and this module's
//! transcription of them. A construct the lowering does not know — an FP
//! argument to an uninterpreted function, FP inside an array or a quantifier,
//! a format wider than 64 bits — makes [`lower_fp_to_bv`] decline, and the
//! caller keeps the exact FP query.

use std::collections::HashMap;
use std::sync::Arc;

use crate::smt::{RoundingMode, SmtExpr, SmtSort};

/// The lowered form of one Bool formula.
#[derive(Debug, Clone, PartialEq)]
pub struct FpBvLowering {
    /// The lowered formula conjoined with every consistency constraint:
    /// `c_1 and ... and c_k and lowered(formula)`. Pure bit-vector / Bool
    /// (plus whatever non-FP arrays or uninterpreted functions the original
    /// already had).
    pub formula: SmtExpr,
    /// Bit-vector constants the lowered formula introduces: one per FP input
    /// (same name, width `eb + sb`) and one per abstracted application.
    pub declarations: Vec<(String, u32)>,
    /// Every abstracted rounding-operation application, in order: the
    /// variable that stands for it, its width, and the original FP term it
    /// abstracts (what a model of the original gives that variable).
    pub abstractions: Vec<(String, u32, SmtExpr)>,
    /// The exact conversion facts ([`conversion_fact`]) for the abstracted
    /// conversions, NOT conjoined into [`Self::formula`]: they only matter
    /// where the obligation depends on what a conversion computes, and they
    /// make every other proof larger, so a caller asks without them first
    /// ([`Self::formula_with_conversion_facts`]).
    pub conversion_facts: Vec<SmtExpr>,
}

impl FpBvLowering {
    /// [`Self::formula`] conjoined with every conversion fact, or `None` when
    /// there is none (the plain formula is then the only question).
    pub fn formula_with_conversion_facts(&self) -> Option<SmtExpr> {
        if self.conversion_facts.is_empty() {
            return None;
        }
        Some(
            self.conversion_facts
                .iter()
                .rev()
                .fold(self.formula.clone(), |acc, fact| fact.clone().and_expr(acc)),
        )
    }
}

/// Why [`lower_fp_to_bv`] declined.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum FpBvDecline {
    /// The formula mentions no floating point: there is nothing to lower.
    NoFloatingPoint,
    /// A construct outside the lowering (named).
    Unsupported(String),
}

/// Lower `formula` — a Bool formula over the bit-vector variables of the
/// obligation plus the FP variables `fp_inputs` (`name`, `eb`, `sb`) — to
/// pure bit-vector form. See the module docs for the construction and why an
/// UNSAT of the result is an UNSAT of `formula`.
///
/// `reserved` names every variable the formula or its query already declares;
/// the abstraction variables are chosen outside it.
pub fn lower_fp_to_bv(
    formula: &SmtExpr,
    fp_inputs: &[(String, u32, u32)],
    reserved: &[String],
) -> Result<FpBvLowering, FpBvDecline> {
    let fp_vars: HashMap<String, (u32, u32)> = fp_inputs
        .iter()
        .map(|(name, eb, sb)| (name.clone(), (*eb, *sb)))
        .collect();
    let mut lowerer = Lowerer {
        fp_vars,
        reserved: reserved.to_vec(),
        applications: Vec::new(),
        index: HashMap::new(),
    };
    if !lowerer.mentions_fp(formula) {
        return Err(FpBvDecline::NoFloatingPoint);
    }
    for (name, eb, sb) in fp_inputs {
        format_width(*eb, *sb).map_err(FpBvDecline::Unsupported)?;
        lowerer.reserved.push(name.clone());
    }
    let lowered = lowerer.lower(formula).map_err(FpBvDecline::Unsupported)?;

    let mut declarations: Vec<(String, u32)> = fp_inputs
        .iter()
        .filter(|(name, _, _)| mentions_var(formula, name))
        .map(|(name, eb, sb)| (name.clone(), eb + sb))
        .collect();
    let mut constraints = Vec::new();
    for (i, first) in lowerer.applications.iter().enumerate() {
        declarations.push((first.var.clone(), first.width));
        for second in &lowerer.applications[i + 1..] {
            if first.operator != second.operator {
                continue;
            }
            // Same operator key => same arity and argument widths.
            let premise = first
                .args
                .iter()
                .zip(&second.args)
                .filter(|(a, b)| a != b)
                .map(|(a, b)| a.clone().eq_expr(b.clone()))
                .reduce(SmtExpr::and_expr);
            let conclusion = var(&first.var, first.width).eq_expr(var(&second.var, second.width));
            constraints.push(match premise {
                Some(premise) => premise.not_expr().or_expr(conclusion),
                // Structurally equal arguments are interned to ONE variable,
                // so this arm is unreachable; keep it total anyway.
                None => conclusion,
            });
        }
    }
    // Exact conversion facts: true of the real operations, so the model
    // extension of the module docs still satisfies them. Kept apart; see
    // `FpBvLowering::conversion_facts`.
    let mut conversion_facts = Vec::new();
    for app in &lowerer.applications {
        if let Some(conversion) = app.conversion
            && let Some(fact) = conversion_fact(conversion, &app.args[0], &var(&app.var, app.width))
        {
            conversion_facts.push(fact);
        }
    }
    let formula = constraints
        .into_iter()
        .rev()
        .fold(lowered, |acc, constraint| constraint.and_expr(acc));
    let abstractions = lowerer
        .applications
        .into_iter()
        .map(|app| (app.var, app.width, app.origin))
        .collect();
    Ok(FpBvLowering {
        formula,
        declarations,
        abstractions,
        conversion_facts,
    })
}

/// One abstracted rounding-operation application.
struct Application {
    /// Operator key: operation, rounding mode, formats, widths.
    operator: String,
    /// Lowered argument patterns.
    args: Vec<SmtExpr>,
    /// The fresh variable standing for the result.
    var: String,
    /// Result width.
    width: u32,
    /// The first original term interned to this application.
    origin: SmtExpr,
    /// What is known exactly about this conversion's result, if anything.
    conversion: Option<Conversion>,
}

/// A conversion whose result the lowering states exactly on the part of its
/// domain where no rounding happens ([`conversion_fact`]).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Conversion {
    /// `((_ to_fp eb sb) rm x)`, `x` read as a `width`-bit SIGNED integer.
    FromSigned { width: u32, eb: u32, sb: u32 },
    /// `fp.to_sbv`/`fp.to_ubv` under RTZ: truncation toward zero.
    Truncate {
        eb: u32,
        sb: u32,
        width: u32,
        signed: bool,
    },
}

struct Lowerer {
    fp_vars: HashMap<String, (u32, u32)>,
    reserved: Vec<String>,
    applications: Vec<Application>,
    index: HashMap<(String, Vec<SmtExpr>), usize>,
}

fn var(name: &str, width: u32) -> SmtExpr {
    SmtExpr::var(name, width)
}

/// Total width of an `(eb, sb)` format the lowering supports.
fn format_width(eb: u32, sb: u32) -> Result<u32, String> {
    let width = eb.checked_add(sb).ok_or("FP format width overflows")?;
    if eb < 2 || sb < 2 || width > 64 {
        return Err(format!(
            "FP format (_ FloatingPoint {eb} {sb}) is outside the lowering (2 <= eb, 2 <= sb, eb+sb <= 64)"
        ));
    }
    Ok(width)
}

/// The bit masks of a `W = eb + sb` pattern. The x86-64 body theorem
/// (slice 21) states its compares and conversion bounds with the same
/// predicates (`nan`, `key`, `ordered`), so both lanes share one exact
/// bit-level transcription.
#[derive(Clone, Copy)]
pub(crate) struct Masks {
    width: u32,
    /// Every bit but the sign.
    abs: u64,
    /// The exponent field (all ones there, zero elsewhere): +infinity's pattern.
    exp: u64,
    /// The sign bit.
    sign: u64,
    /// The quiet NaN `canon` maps every NaN pattern to.
    qnan: u64,
}

impl Masks {
    pub(crate) fn of(eb: u32, sb: u32) -> Result<Self, String> {
        let width = format_width(eb, sb)?;
        let sign = 1u64 << (width - 1);
        let abs = sign - 1;
        let exp = ((1u64 << eb) - 1) << (sb - 1);
        let qnan = exp | (1u64 << (sb - 2));
        Ok(Self {
            width,
            abs,
            exp,
            sign,
            qnan,
        })
    }

    fn konst(&self, value: u64) -> SmtExpr {
        SmtExpr::bv_const(value, self.width)
    }

    /// `(x & ABS) >u EXP`: exponent all ones and a non-zero significand.
    pub(crate) fn nan(&self, x: &SmtExpr) -> SmtExpr {
        x.clone()
            .bvand(self.konst(self.abs))
            .bvugt(self.konst(self.exp))
    }

    /// `x & ABS = EXP`.
    fn infinite(&self, x: &SmtExpr) -> SmtExpr {
        x.clone()
            .bvand(self.konst(self.abs))
            .eq_expr(self.konst(self.exp))
    }

    /// `x & ABS = 0`.
    fn zero(&self, x: &SmtExpr) -> SmtExpr {
        x.clone().bvand(self.konst(self.abs)).eq_expr(self.konst(0))
    }

    /// The exponent field is neither all zeros nor all ones.
    fn normal(&self, x: &SmtExpr) -> SmtExpr {
        let field = x.clone().bvand(self.konst(self.exp));
        field
            .clone()
            .eq_expr(self.konst(0))
            .not_expr()
            .and_expr(field.eq_expr(self.konst(self.exp)).not_expr())
    }

    /// Signed order key: `sign ? -(x & ABS) : (x & ABS)`. Order-preserving on
    /// non-NaN patterns; equal exactly for equal values (`+0` and `-0` both
    /// map to 0).
    pub(crate) fn key(&self, x: &SmtExpr) -> SmtExpr {
        let magnitude = x.clone().bvand(self.konst(self.abs));
        let negative = x
            .clone()
            .extract(self.width - 1, self.width - 1)
            .eq_expr(SmtExpr::bv_const(1, 1));
        SmtExpr::ite(negative, magnitude.clone().bvneg(), magnitude)
    }

    /// Neither operand is NaN.
    pub(crate) fn ordered(&self, a: &SmtExpr, b: &SmtExpr) -> SmtExpr {
        self.nan(a).not_expr().and_expr(self.nan(b).not_expr())
    }

    /// Every NaN pattern to `QNAN`; every other pattern to itself.
    fn canon(&self, x: &SmtExpr) -> SmtExpr {
        SmtExpr::ite(self.nan(x), self.konst(self.qnan), x.clone())
    }
}

/// `x` (of width `from`) at width `to`: zero-extended or truncated.
fn resize(x: SmtExpr, from: u32, to: u32) -> SmtExpr {
    match to.cmp(&from) {
        std::cmp::Ordering::Equal => x,
        std::cmp::Ordering::Greater => x.zero_ext(to - from),
        std::cmp::Ordering::Less => x.extract(to - 1, 0),
    }
}

/// `lhs => rhs`.
fn implies(lhs: SmtExpr, rhs: SmtExpr) -> SmtExpr {
    lhs.not_expr().or_expr(rhs)
}

/// The exact fact the lowering states about one conversion application whose
/// argument pattern is `arg` and whose abstraction variable is `result`.
/// `None` when the format leaves nothing exact to state.
///
/// * `FromSigned`: an integer `x` with `|x| <= 2^sb` is representable, so every
///   rounding mode returns its exact value: `+0` for 0, else sign, biased
///   exponent `bias + msb(|x|)`, and the bits of `|x|` below its msb as the
///   fraction.
/// * `Truncate`: a finite value whose truncation toward zero fits the
///   destination converts to that truncation — `0` when `|v| < 1`, else the
///   significand `1.frac` shifted by the unbiased exponent `k`, negated for a
///   negative signed value. Stated only for `k <= width - 2` (signed) or an
///   unsigned value with `k <= width - 1`; NaN, infinities and every
///   out-of-range value (unspecified in SMT-LIB) get no fact.
fn conversion_fact(conversion: Conversion, arg: &SmtExpr, result: &SmtExpr) -> Option<SmtExpr> {
    match conversion {
        Conversion::FromSigned { width, eb, sb } => {
            let emax = (1u32 << (eb - 1)) - 1;
            let exact_exp = sb.min(width - 1);
            if exact_exp > emax || width > 64 {
                return None;
            }
            let guard = if exact_exp >= width - 1 {
                SmtExpr::bool_const(true)
            } else {
                let bound = 1u64 << exact_exp;
                arg.clone()
                    .bvsge(SmtExpr::bv_const(bound.wrapping_neg(), width))
                    .and_expr(arg.clone().bvsle(SmtExpr::bv_const(bound, width)))
            };
            let sign = arg.clone().extract(width - 1, width - 1);
            let magnitude = SmtExpr::ite(
                sign.clone().eq_expr(SmtExpr::bv_const(1, 1)),
                arg.clone().bvneg(),
                arg.clone(),
            );
            let room = width.max(sb);
            let magnitude = resize(magnitude, width, room);
            let mut pattern = SmtExpr::bv_const(0, eb + sb);
            for k in 0..=exact_exp.min(width - 1) {
                let aligned = if k < sb {
                    magnitude
                        .clone()
                        .bvshl(SmtExpr::bv_const(u64::from(sb - 1 - k), room))
                } else {
                    magnitude
                        .clone()
                        .bvlshr(SmtExpr::bv_const(u64::from(k - (sb - 1)), room))
                };
                let encoded = sign
                    .clone()
                    .concat(SmtExpr::bv_const(u64::from(emax + k), eb))
                    .concat(aligned.extract(sb - 2, 0));
                let msb_here = magnitude
                    .clone()
                    .extract(k, k)
                    .eq_expr(SmtExpr::bv_const(1, 1));
                pattern = SmtExpr::ite(msb_here, encoded, pattern);
            }
            Some(implies(guard, result.clone().eq_expr(pattern)))
        }
        Conversion::Truncate {
            eb,
            sb,
            width,
            signed,
        } => {
            let total = eb + sb;
            let emax = (1u32 << (eb - 1)) - 1;
            if !(2..=64).contains(&width) {
                return None;
            }
            let exponent = arg.clone().extract(total - 2, sb - 1);
            let fraction = arg.clone().extract(sb - 2, 0);
            let negative = arg
                .clone()
                .extract(total - 1, total - 1)
                .eq_expr(SmtExpr::bv_const(1, 1));
            let zero = SmtExpr::bv_const(0, width);
            // |v| < 1: zero, subnormal, or a normal below the bias.
            let tiny = exponent
                .clone()
                .bvult(SmtExpr::bv_const(u64::from(emax), eb));
            let mut fact = implies(tiny, result.clone().eq_expr(zero));
            let top = if signed { width - 2 } else { width - 1 }.min(emax);
            let room = width.max(sb);
            let significand = resize(SmtExpr::bv_const(1, 1).concat(fraction), sb, room);
            for k in 0..=top {
                let shifted = if k < sb {
                    significand
                        .clone()
                        .bvlshr(SmtExpr::bv_const(u64::from(sb - 1 - k), room))
                } else {
                    significand
                        .clone()
                        .bvshl(SmtExpr::bv_const(u64::from(k - (sb - 1)), room))
                };
                let integer = resize(shifted, room, width);
                let at_k = exponent
                    .clone()
                    .eq_expr(SmtExpr::bv_const(u64::from(emax + k), eb));
                let (condition, value) = if signed {
                    (
                        at_k,
                        SmtExpr::ite(negative.clone(), integer.clone().bvneg(), integer),
                    )
                } else {
                    (at_k.and_expr(negative.clone().not_expr()), integer)
                };
                fact = fact.and_expr(implies(condition, result.clone().eq_expr(value)));
            }
            Some(fact)
        }
    }
}

fn rounding(rm: &RoundingMode) -> &'static str {
    match rm {
        RoundingMode::RNE => "rne",
        RoundingMode::RNA => "rna",
        RoundingMode::RTP => "rtp",
        RoundingMode::RTN => "rtn",
        RoundingMode::RTZ => "rtz",
    }
}

/// Whether `formula` mentions the variable `name` at all.
fn mentions_var(formula: &SmtExpr, name: &str) -> bool {
    formula.any_node(|node| matches!(node, SmtExpr::Var { name: n, .. } if n == name))
}

impl Lowerer {
    /// The FP format of an FP-sorted term; `None` for every other sort.
    fn format_of(&self, expr: &SmtExpr) -> Option<(u32, u32)> {
        match expr {
            SmtExpr::Var { name, .. } => self.fp_vars.get(name).copied(),
            SmtExpr::FPConst { eb, sb, .. }
            | SmtExpr::BvToFP { eb, sb, .. }
            | SmtExpr::FPToFP { eb, sb, .. }
            | SmtExpr::BvBitsToFP { eb, sb, .. } => Some((*eb, *sb)),
            SmtExpr::FPAdd { lhs, .. }
            | SmtExpr::FPSub { lhs, .. }
            | SmtExpr::FPMul { lhs, .. }
            | SmtExpr::FPDiv { lhs, .. } => self.format_of(lhs),
            SmtExpr::FPSqrt { operand, .. }
            | SmtExpr::FPRoundToIntegral { operand, .. }
            | SmtExpr::FPAbs { operand }
            | SmtExpr::FPNeg { operand } => self.format_of(operand),
            SmtExpr::FPFma { a, .. } => self.format_of(a),
            SmtExpr::Ite { then_expr, .. } => self.format_of(then_expr),
            SmtExpr::UF { ret_sort, .. } | SmtExpr::UFDecl { ret_sort, .. } => match ret_sort {
                SmtSort::FloatingPoint(eb, sb) => Some((*eb, *sb)),
                _ => None,
            },
            SmtExpr::Select { array, .. } => match array.sort() {
                SmtSort::Array(_, element) => match *element {
                    SmtSort::FloatingPoint(eb, sb) => Some((eb, sb)),
                    _ => None,
                },
                _ => None,
            },
            _ => None,
        }
    }

    /// Whether `expr` has any FP node or FP variable in it.
    fn mentions_fp(&self, expr: &SmtExpr) -> bool {
        expr.any_node(|node| match node {
            SmtExpr::Var { name, .. } => self.fp_vars.contains_key(name),
            SmtExpr::FPAdd { .. }
            | SmtExpr::FPSub { .. }
            | SmtExpr::FPMul { .. }
            | SmtExpr::FPDiv { .. }
            | SmtExpr::FPNeg { .. }
            | SmtExpr::FPEq { .. }
            | SmtExpr::FPLt { .. }
            | SmtExpr::FPGt { .. }
            | SmtExpr::FPGe { .. }
            | SmtExpr::FPLe { .. }
            | SmtExpr::FPConst { .. }
            | SmtExpr::FPSqrt { .. }
            | SmtExpr::FPRoundToIntegral { .. }
            | SmtExpr::FPAbs { .. }
            | SmtExpr::FPFma { .. }
            | SmtExpr::FPIsNaN { .. }
            | SmtExpr::FPIsInf { .. }
            | SmtExpr::FPIsZero { .. }
            | SmtExpr::FPIsNormal { .. }
            | SmtExpr::FPToSBv { .. }
            | SmtExpr::FPToUBv { .. }
            | SmtExpr::BvToFP { .. }
            | SmtExpr::FPToFP { .. }
            | SmtExpr::BvBitsToFP { .. } => true,
            SmtExpr::UF { args, ret_sort, .. } => {
                matches!(ret_sort, SmtSort::FloatingPoint(..))
                    || args.iter().any(|arg| self.format_of(arg).is_some())
            }
            SmtExpr::UFDecl {
                arg_sorts,
                ret_sort,
                ..
            } => std::iter::once(ret_sort)
                .chain(arg_sorts)
                .any(|sort| matches!(sort, SmtSort::FloatingPoint(..))),
            _ => false,
        })
    }

    fn fresh_name(&self) -> String {
        let mut n = self.applications.len();
        loop {
            let candidate = format!("tcg_fpbv_{n}");
            if !self.reserved.iter().any(|r| r == &candidate)
                && !self.applications.iter().any(|a| a.var == candidate)
            {
                return candidate;
            }
            n += 1;
        }
    }

    /// The variable standing for `operator(args)`, interned on the lowered
    /// argument patterns.
    fn apply(
        &mut self,
        operator: String,
        args: Vec<SmtExpr>,
        width: u32,
        origin: &SmtExpr,
    ) -> SmtExpr {
        self.apply_conversion(operator, args, width, origin, None)
    }

    fn apply_conversion(
        &mut self,
        operator: String,
        args: Vec<SmtExpr>,
        width: u32,
        origin: &SmtExpr,
        conversion: Option<Conversion>,
    ) -> SmtExpr {
        let key = (operator, args);
        if let Some(&i) = self.index.get(&key) {
            let app = &self.applications[i];
            return var(&app.var, app.width);
        }
        let name = self.fresh_name();
        let (operator, args) = key.clone();
        self.index.insert(key, self.applications.len());
        self.applications.push(Application {
            operator,
            args,
            var: name.clone(),
            width,
            origin: origin.clone(),
            conversion,
        });
        var(&name, width)
    }

    /// Lower an FP-sorted term to its pattern, checking it has format `(eb, sb)`.
    fn pattern(&mut self, expr: &SmtExpr) -> Result<(SmtExpr, Masks, u32, u32), String> {
        let (eb, sb) = self
            .format_of(expr)
            .ok_or_else(|| format!("expected an FP term, found {expr}"))?;
        let masks = Masks::of(eb, sb)?;
        Ok((self.lower(expr)?, masks, eb, sb))
    }

    fn binary_fp(
        &mut self,
        name: &str,
        rm: &RoundingMode,
        lhs: &SmtExpr,
        rhs: &SmtExpr,
        origin: &SmtExpr,
    ) -> Result<SmtExpr, String> {
        let (l, masks, eb, sb) = self.pattern(lhs)?;
        let (r, ..) = self.pattern(rhs)?;
        let operator = format!("{name}.{}.{eb}.{sb}", rounding(rm));
        Ok(self.apply(operator, vec![l, r], masks.width, origin))
    }

    fn predicate(
        &mut self,
        lhs: &SmtExpr,
        rhs: &SmtExpr,
        relation: fn(SmtExpr, SmtExpr) -> SmtExpr,
    ) -> Result<SmtExpr, String> {
        let (a, masks, ..) = self.pattern(lhs)?;
        let (b, ..) = self.pattern(rhs)?;
        Ok(masks
            .ordered(&a, &b)
            .and_expr(relation(masks.key(&a), masks.key(&b))))
    }

    fn lower(&mut self, expr: &SmtExpr) -> Result<SmtExpr, String> {
        if !self.mentions_fp(expr) {
            return Ok(expr.clone());
        }
        Ok(match expr {
            // -- FP leaves --------------------------------------------------
            SmtExpr::Var { name, .. } => {
                let (eb, sb) = self.fp_vars[name];
                var(name, format_width(eb, sb)?)
            }
            SmtExpr::FPConst { bits, eb, sb } => Masks::of(*eb, *sb)?.konst(*bits),
            SmtExpr::BvBitsToFP { operand, eb, sb } => {
                let width = format_width(*eb, *sb)?;
                if operand.sort() != SmtSort::BitVec(width) {
                    return Err(format!(
                        "to_fp reinterpretation of a non-{width}-bit operand"
                    ));
                }
                self.lower(operand)?
            }

            // -- exact sign-bit operations ----------------------------------
            SmtExpr::FPNeg { operand } => {
                let (x, masks, ..) = self.pattern(operand)?;
                x.bvxor(masks.konst(masks.sign))
            }
            SmtExpr::FPAbs { operand } => {
                let (x, masks, ..) = self.pattern(operand)?;
                x.bvand(masks.konst(masks.abs))
            }

            // -- exact predicates -------------------------------------------
            SmtExpr::FPIsNaN { operand } => {
                let (x, masks, ..) = self.pattern(operand)?;
                masks.nan(&x)
            }
            SmtExpr::FPIsInf { operand } => {
                let (x, masks, ..) = self.pattern(operand)?;
                masks.infinite(&x)
            }
            SmtExpr::FPIsZero { operand } => {
                let (x, masks, ..) = self.pattern(operand)?;
                masks.zero(&x)
            }
            SmtExpr::FPIsNormal { operand } => {
                let (x, masks, ..) = self.pattern(operand)?;
                masks.normal(&x)
            }
            SmtExpr::FPLt { lhs, rhs } => self.predicate(lhs, rhs, SmtExpr::bvslt)?,
            SmtExpr::FPLe { lhs, rhs } => self.predicate(lhs, rhs, SmtExpr::bvsle)?,
            SmtExpr::FPGt { lhs, rhs } => self.predicate(rhs, lhs, SmtExpr::bvslt)?,
            SmtExpr::FPGe { lhs, rhs } => self.predicate(rhs, lhs, SmtExpr::bvsle)?,
            SmtExpr::FPEq { lhs, rhs } => self.predicate(lhs, rhs, SmtExpr::eq_expr)?,
            SmtExpr::Eq { lhs, rhs } if self.format_of(lhs).is_some() => {
                let (a, masks, ..) = self.pattern(lhs)?;
                let (b, ..) = self.pattern(rhs)?;
                masks.canon(&a).eq_expr(masks.canon(&b))
            }

            // -- rounding operations: abstracted ----------------------------
            SmtExpr::FPAdd { rm, lhs, rhs } => self.binary_fp("fp.add", rm, lhs, rhs, expr)?,
            SmtExpr::FPSub { rm, lhs, rhs } => self.binary_fp("fp.sub", rm, lhs, rhs, expr)?,
            SmtExpr::FPMul { rm, lhs, rhs } => self.binary_fp("fp.mul", rm, lhs, rhs, expr)?,
            SmtExpr::FPDiv { rm, lhs, rhs } => self.binary_fp("fp.div", rm, lhs, rhs, expr)?,
            SmtExpr::FPSqrt { rm, operand } => {
                let (x, masks, eb, sb) = self.pattern(operand)?;
                self.apply(
                    format!("fp.sqrt.{}.{eb}.{sb}", rounding(rm)),
                    vec![x],
                    masks.width,
                    expr,
                )
            }
            SmtExpr::FPRoundToIntegral { rm, operand } => {
                let (x, masks, eb, sb) = self.pattern(operand)?;
                self.apply(
                    format!("fp.roundToIntegral.{}.{eb}.{sb}", rounding(rm)),
                    vec![x],
                    masks.width,
                    expr,
                )
            }
            SmtExpr::FPFma { rm, a, b, c } => {
                let (x, masks, eb, sb) = self.pattern(a)?;
                let (y, ..) = self.pattern(b)?;
                let (z, ..) = self.pattern(c)?;
                self.apply(
                    format!("fp.fma.{}.{eb}.{sb}", rounding(rm)),
                    vec![x, y, z],
                    masks.width,
                    expr,
                )
            }
            SmtExpr::BvToFP {
                rm,
                operand,
                eb,
                sb,
            } => {
                let width = format_width(*eb, *sb)?;
                let source = operand.bv_width();
                let x = self.lower(operand)?;
                // `((_ to_fp eb sb) rm bv)` reads `bv` as a SIGNED integer.
                self.apply_conversion(
                    format!("sbv{source}.to_fp.{}.{eb}.{sb}", rounding(rm)),
                    vec![x],
                    width,
                    expr,
                    Some(Conversion::FromSigned {
                        width: source,
                        eb: *eb,
                        sb: *sb,
                    }),
                )
            }
            SmtExpr::FPToFP {
                rm,
                operand,
                eb,
                sb,
            } => {
                let width = format_width(*eb, *sb)?;
                let (x, _, from_eb, from_sb) = self.pattern(operand)?;
                self.apply(
                    format!("fp{from_eb}.{from_sb}.to_fp.{}.{eb}.{sb}", rounding(rm)),
                    vec![x],
                    width,
                    expr,
                )
            }
            SmtExpr::FPToSBv {
                rm,
                operand,
                width,
                mode,
            } => {
                let (x, _, eb, sb) = self.pattern(operand)?;
                // The out-of-range mode is part of the operator: two modes are
                // two functions, so a mode mismatch between the sides is never
                // unified away.
                let truncates = matches!(rm, RoundingMode::RTZ);
                self.apply_conversion(
                    format!("fp{eb}.{sb}.to_sbv{width}.{}.{mode:?}", rounding(rm)),
                    vec![x],
                    *width,
                    expr,
                    truncates.then_some(Conversion::Truncate {
                        eb,
                        sb,
                        width: *width,
                        signed: true,
                    }),
                )
            }
            SmtExpr::FPToUBv { rm, operand, width } => {
                let (x, _, eb, sb) = self.pattern(operand)?;
                let truncates = matches!(rm, RoundingMode::RTZ);
                self.apply_conversion(
                    format!("fp{eb}.{sb}.to_ubv{width}.{}", rounding(rm)),
                    vec![x],
                    *width,
                    expr,
                    truncates.then_some(Conversion::Truncate {
                        eb,
                        sb,
                        width: *width,
                        signed: false,
                    }),
                )
            }

            // -- FP-sorted ite: branch-wise ----------------------------------
            SmtExpr::Ite {
                cond,
                then_expr,
                else_expr,
            } => SmtExpr::ite(
                self.lower(cond)?,
                self.lower(then_expr)?,
                self.lower(else_expr)?,
            ),

            // -- constructs the lowering does not reach ----------------------
            SmtExpr::UF { .. }
            | SmtExpr::UFDecl { .. }
            | SmtExpr::Select { .. }
            | SmtExpr::Store { .. }
            | SmtExpr::ConstArray { .. }
            | SmtExpr::MemLoad { .. }
            | SmtExpr::ForAll { .. }
            | SmtExpr::Exists { .. } => {
                return Err(format!("floating point under {}", head(expr)));
            }

            // -- everything else: same node, lowered children ----------------
            other => self.rebuild(other)?,
        })
    }

    /// Rebuild a non-FP node over lowered children.
    fn rebuild(&mut self, expr: &SmtExpr) -> Result<SmtExpr, String> {
        let mut low = |child: &Arc<SmtExpr>| -> Result<Arc<SmtExpr>, String> {
            Ok(Arc::new(self.lower(child)?))
        };
        Ok(match expr {
            SmtExpr::BvAdd { lhs, rhs, width } => SmtExpr::BvAdd {
                lhs: low(lhs)?,
                rhs: low(rhs)?,
                width: *width,
            },
            SmtExpr::BvSub { lhs, rhs, width } => SmtExpr::BvSub {
                lhs: low(lhs)?,
                rhs: low(rhs)?,
                width: *width,
            },
            SmtExpr::BvMul { lhs, rhs, width } => SmtExpr::BvMul {
                lhs: low(lhs)?,
                rhs: low(rhs)?,
                width: *width,
            },
            SmtExpr::BvSDiv { lhs, rhs, width } => SmtExpr::BvSDiv {
                lhs: low(lhs)?,
                rhs: low(rhs)?,
                width: *width,
            },
            SmtExpr::BvUDiv { lhs, rhs, width } => SmtExpr::BvUDiv {
                lhs: low(lhs)?,
                rhs: low(rhs)?,
                width: *width,
            },
            SmtExpr::BvURem { lhs, rhs, width } => SmtExpr::BvURem {
                lhs: low(lhs)?,
                rhs: low(rhs)?,
                width: *width,
            },
            SmtExpr::TrapIfZero {
                guard,
                value,
                width,
            } => SmtExpr::TrapIfZero {
                guard: low(guard)?,
                value: low(value)?,
                width: *width,
            },
            SmtExpr::BvNeg { operand, width } => SmtExpr::BvNeg {
                operand: low(operand)?,
                width: *width,
            },
            SmtExpr::Eq { lhs, rhs } => SmtExpr::Eq {
                lhs: low(lhs)?,
                rhs: low(rhs)?,
            },
            SmtExpr::Not { operand } => SmtExpr::Not {
                operand: low(operand)?,
            },
            SmtExpr::And { lhs, rhs } => SmtExpr::And {
                lhs: low(lhs)?,
                rhs: low(rhs)?,
            },
            SmtExpr::Or { lhs, rhs } => SmtExpr::Or {
                lhs: low(lhs)?,
                rhs: low(rhs)?,
            },
            SmtExpr::BvSlt { lhs, rhs, width } => SmtExpr::BvSlt {
                lhs: low(lhs)?,
                rhs: low(rhs)?,
                width: *width,
            },
            SmtExpr::BvSge { lhs, rhs, width } => SmtExpr::BvSge {
                lhs: low(lhs)?,
                rhs: low(rhs)?,
                width: *width,
            },
            SmtExpr::BvUge { lhs, rhs, width } => SmtExpr::BvUge {
                lhs: low(lhs)?,
                rhs: low(rhs)?,
                width: *width,
            },
            SmtExpr::BvSgt { lhs, rhs, width } => SmtExpr::BvSgt {
                lhs: low(lhs)?,
                rhs: low(rhs)?,
                width: *width,
            },
            SmtExpr::BvSle { lhs, rhs, width } => SmtExpr::BvSle {
                lhs: low(lhs)?,
                rhs: low(rhs)?,
                width: *width,
            },
            SmtExpr::BvUlt { lhs, rhs, width } => SmtExpr::BvUlt {
                lhs: low(lhs)?,
                rhs: low(rhs)?,
                width: *width,
            },
            SmtExpr::BvUgt { lhs, rhs, width } => SmtExpr::BvUgt {
                lhs: low(lhs)?,
                rhs: low(rhs)?,
                width: *width,
            },
            SmtExpr::BvUle { lhs, rhs, width } => SmtExpr::BvUle {
                lhs: low(lhs)?,
                rhs: low(rhs)?,
                width: *width,
            },
            SmtExpr::Extract {
                high,
                low: bit,
                operand,
                width,
            } => SmtExpr::Extract {
                high: *high,
                low: *bit,
                operand: low(operand)?,
                width: *width,
            },
            SmtExpr::BvAnd { lhs, rhs, width } => SmtExpr::BvAnd {
                lhs: low(lhs)?,
                rhs: low(rhs)?,
                width: *width,
            },
            SmtExpr::BvOr { lhs, rhs, width } => SmtExpr::BvOr {
                lhs: low(lhs)?,
                rhs: low(rhs)?,
                width: *width,
            },
            SmtExpr::BvXor { lhs, rhs, width } => SmtExpr::BvXor {
                lhs: low(lhs)?,
                rhs: low(rhs)?,
                width: *width,
            },
            SmtExpr::BvShl { lhs, rhs, width } => SmtExpr::BvShl {
                lhs: low(lhs)?,
                rhs: low(rhs)?,
                width: *width,
            },
            SmtExpr::BvLshr { lhs, rhs, width } => SmtExpr::BvLshr {
                lhs: low(lhs)?,
                rhs: low(rhs)?,
                width: *width,
            },
            SmtExpr::BvAshr { lhs, rhs, width } => SmtExpr::BvAshr {
                lhs: low(lhs)?,
                rhs: low(rhs)?,
                width: *width,
            },
            SmtExpr::Concat { hi, lo, width } => SmtExpr::Concat {
                hi: low(hi)?,
                lo: low(lo)?,
                width: *width,
            },
            SmtExpr::ZeroExtend {
                operand,
                extra_bits,
                width,
            } => SmtExpr::ZeroExtend {
                operand: low(operand)?,
                extra_bits: *extra_bits,
                width: *width,
            },
            SmtExpr::SignExtend {
                operand,
                extra_bits,
                width,
            } => SmtExpr::SignExtend {
                operand: low(operand)?,
                extra_bits: *extra_bits,
                width: *width,
            },
            other => {
                return Err(format!(
                    "unexpected node {} over floating point",
                    head(other)
                ));
            }
        })
    }
}

/// A short name for an expression's head, for decline messages.
fn head(expr: &SmtExpr) -> String {
    let text = expr.to_string();
    let end = text
        .char_indices()
        .skip(1)
        .find(|(_, c)| c.is_whitespace() || *c == ')')
        .map_or(text.len(), |(i, _)| i);
    text[..end.min(48)].to_string()
}

#[cfg(test)]
#[path = "fp_bv_lowering_tests.rs"]
mod tests;
