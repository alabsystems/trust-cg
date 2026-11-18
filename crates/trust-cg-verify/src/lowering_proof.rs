// trust-cg-verify/lowering_proof.rs - Lowering rule proof obligations
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// Defines proof obligations for trust_ir -> AArch64 lowering rules and a
// verification harness that checks semantic equivalence.
//
// The core technique: for a lowering rule `trust_ir_inst -> AArch64_inst(s)`,
// assert `NOT(trust_ir_result == aarch64_result)` and check for UNSAT.
// If UNSAT, the rule is proven correct for all inputs.
//
// Reference: Alive2 (PLDI 2021)

//! Proof obligations for lowering rule verification.
//!
//! A [`ProofObligation`] pairs the trust_ir-side and AArch64-side semantic
//! expressions and can be checked for equivalence using either a mock
//! solver (exhaustive/random testing) or a real SMT solver (ay).

use crate::smt::{BATCH_LANES, BatchScratch, BatchTape, EvalEnv, FlatProg, SVal, SmtExpr, mask};
use crate::verify::VerificationResult;
use std::collections::HashMap;
use std::sync::Arc;

#[cfg(test)]
mod canonical_conjunction_tests;
mod checked_fcmp;
mod checked_fp_values;
#[cfg(test)]
mod exhaustive_block_tests;
#[cfg(test)]
mod exhaustive_domain_tests;

/// Canonical original-query construction, shared by every serializer and
/// producer. Request/replay reuse must bind this protocol as well as content.
pub(crate) const CANONICAL_PROOF_FORMULA_PROTOCOL: &str =
    "trust-cg.proof-formula.midpoint-conjunction.v2";

/// Whether finite evaluation must validate and sample the stored scalar FP
/// comparison or value trees. Shared by primary/memo dispatch and strength accounting.
pub(crate) fn uses_checked_scalar_fp_evaluation(obligation: &ProofObligation) -> bool {
    checked_fcmp::applies(obligation) || checked_fp_values::applies(obligation)
}

/// Translation validation check kind, aligned with tRust trust-transval's `CheckKind`.
///
/// trust-transval (tRust's translation validation crate) classifies verification
/// conditions into four categories: ControlFlow, DataFlow, ReturnValue,
/// Termination. Trust Codegen extends this taxonomy with machine-specific categories
/// for instruction lowering, peephole optimizations, memory model, register
/// allocation, and SIMD vectorization.
///
/// This is distinct from `proof_database::ProofCategory`, which provides a
/// fine-grained Trust Codegen-specific classification (36 variants for individual proof
/// modules). `TransvalCheckKind` is a coarse-grained taxonomy designed for
/// interoperability with tRust's translation validation pipeline.
///
/// Reference: `~/tRust/crates/trust-transval/src/vc_core.rs`
/// Reference: `trust_types::CheckKind`
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum TransvalCheckKind {
    /// Data flow preservation: a trust_ir expression evaluates to the same value
    /// as the corresponding AArch64 expression.
    /// Maps to trust-transval `CheckKind::DataFlow`.
    DataFlow,

    /// Control flow preservation: branch conditions are preserved across
    /// the lowering transformation.
    /// Maps to trust-transval `CheckKind::ControlFlow`.
    ControlFlow,

    /// Return value preservation: function output is preserved.
    /// Maps to trust-transval `CheckKind::ReturnValue`.
    ReturnValue,

    /// Termination preservation: if the source terminates, the target must too.
    /// Maps to trust-transval `CheckKind::Termination`.
    Termination,

    /// Instruction lowering: trust_ir instruction -> AArch64 instruction sequence.
    /// Trust Codegen-specific; trust-transval does not reason about machine instructions.
    InstructionLowering,

    /// Peephole optimization: machine-level rewrite preserves semantics.
    PeepholeOptimization,

    /// Memory model: load/store semantics preserved across lowering.
    MemoryModel,

    /// Register allocation: spill/reload preserves register values.
    RegisterAllocation,

    /// SIMD vectorization: scalar-to-vector mapping is correct.
    Vectorization,
}

impl std::fmt::Display for TransvalCheckKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            TransvalCheckKind::DataFlow => write!(f, "data_flow"),
            TransvalCheckKind::ControlFlow => write!(f, "control_flow"),
            TransvalCheckKind::ReturnValue => write!(f, "return_value"),
            TransvalCheckKind::Termination => write!(f, "termination"),
            TransvalCheckKind::InstructionLowering => write!(f, "instruction_lowering"),
            TransvalCheckKind::PeepholeOptimization => write!(f, "peephole"),
            TransvalCheckKind::MemoryModel => write!(f, "memory"),
            TransvalCheckKind::RegisterAllocation => write!(f, "regalloc"),
            TransvalCheckKind::Vectorization => write!(f, "vectorization"),
        }
    }
}

impl TransvalCheckKind {
    /// Return all check-kind variants in declaration order.
    pub fn all_kinds() -> &'static [TransvalCheckKind] {
        &[
            TransvalCheckKind::DataFlow,
            TransvalCheckKind::ControlFlow,
            TransvalCheckKind::ReturnValue,
            TransvalCheckKind::Termination,
            TransvalCheckKind::InstructionLowering,
            TransvalCheckKind::PeepholeOptimization,
            TransvalCheckKind::MemoryModel,
            TransvalCheckKind::RegisterAllocation,
            TransvalCheckKind::Vectorization,
        ]
    }

    /// Convert to the category string used by `ProofResult` and `VerificationReport`.
    ///
    /// This provides backward compatibility with the existing string-based
    /// category system while enabling typed categorization.
    pub fn as_category_str(&self) -> &'static str {
        match self {
            TransvalCheckKind::DataFlow => "data_flow",
            TransvalCheckKind::ControlFlow => "control_flow",
            TransvalCheckKind::ReturnValue => "return_value",
            TransvalCheckKind::Termination => "termination",
            TransvalCheckKind::InstructionLowering => "arithmetic",
            TransvalCheckKind::PeepholeOptimization => "peephole",
            TransvalCheckKind::MemoryModel => "memory",
            TransvalCheckKind::RegisterAllocation => "regalloc",
            TransvalCheckKind::Vectorization => "vectorization",
        }
    }

    /// Returns true if this category has a direct equivalent in trust-transval's
    /// `CheckKind` enum (i.e., it is one of the four standard translation
    /// validation check kinds).
    pub fn is_transval_compatible(&self) -> bool {
        matches!(
            self,
            TransvalCheckKind::DataFlow
                | TransvalCheckKind::ControlFlow
                | TransvalCheckKind::ReturnValue
                | TransvalCheckKind::Termination
        )
    }
}

/// Where the machine (target) side of a [`ProofObligation`] came from.
///
/// This is the Phase-2 operand-reconstruction provenance tag (task #63). It
/// records HOW the `aarch64_expr` (machine-side) of an obligation was built,
/// which is the discriminator the credit rule uses to decide whether a proof
/// has genuine lowering content.
///
/// # Why this matters (the #61 / strict-gate connection)
///
/// The static lowering proofs in the database build BOTH sides of the
/// obligation from the SAME symbolic vars `a, b` — e.g. `proof_iadd_i32` builds
/// `trust_ir_expr = encode_trust_ir_binop(Iadd, a, b) = a.bvadd(b)` AND
/// `aarch64_expr = encode_add_rr(a, b) = a.bvadd(b)`. Those are STRUCTURALLY
/// equal, so [`ProofObligation::is_genuinely_proven`] (#61) correctly refuses to
/// count them: a degenerate `X == X` obligation can never be refuted by a wrong
/// isel choice, because the machine side was hand-written to match.
///
/// A [`MachineSideProvenance::Reconstructed`] obligation is different in kind:
/// its target expression was rebuilt from the real emitted opcode and positional
/// operands rather than copied from a static proof template. This tag records
/// that target-side fact only. It does **not** itself prove that the source
/// expression was independently recovered from the actual lowering input, nor
/// that symbolic operands were bound to that input's exact values. Current
/// architecture reconstructors may infer the nominal source family from the
/// emitted opcode, so a wrong source selection can otherwise self-attest as
/// `E == E`. Any complete lowering claim must pair this target-side provenance
/// with separately enforced exact source/operand provenance.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum MachineSideProvenance {
    /// Machine side was taken from a STATIC database builder that constructs the
    /// `aarch64_expr` by hand (the legacy path). Such obligations are only ever
    /// credited if they are *also* non-degenerate per
    /// [`ProofObligation::is_genuinely_proven`]; this is the default for every
    /// pre-existing builder, so STEP 0 of #63 is a pure no-behavior-change tag.
    StaticDb,

    /// Machine side was RECONSTRUCTED from the real emitted machine instruction
    /// at verify time (its opcode and positional operands), per
    /// `function_verifier::reconstruct_alu_obligation`. This is the only
    /// provenance the existing reconstruction-reporting rule recognizes (see
    /// [`ProofObligation::is_reconstructed`]). This tag alone is not authority
    /// for a local structural-identity Formal proof.
    Reconstructed {
        /// Stable identifier of the REAL machine opcode the machine side was
        /// built from (the `{:?}` of the `AArch64Opcode`). Recorded for audit /
        /// reporting; the reconstruction itself uses the typed opcode, never a
        /// string lookup.
        from_opcode: String,
        /// Arity of the reconstructed instruction's SOURCE operand schema
        /// (2 for binary `dst, src1, src2`; 1 for unary `dst, src`).
        arity: u8,
    },
}

/// A proof obligation asserting semantic equivalence of a lowering rule.
///
/// Given:
/// - `trust_ir_expr`: the trust_ir instruction's semantics as an SmtExpr
/// - `aarch64_expr`: the AArch64 instruction(s) semantics as an SmtExpr
/// - `inputs`: symbolic variable names and their bitvector widths
/// - `preconditions`: optional constraints (e.g., divisor != 0)
///
/// The proof obligation is:
/// ```text
/// forall inputs satisfying preconditions:
///     trust_ir_expr == aarch64_expr
/// ```
///
/// To verify via SMT: assert `NOT(trust_ir_expr == aarch64_expr)` under
/// preconditions and check for UNSAT.
///
/// `PartialEq`/`Eq`/`Hash` are derived so an obligation's FULL CONTENT (both
/// expression trees, inputs, preconditions, fp_inputs, category, provenance
/// and name) can serve as a structural cache key — see
/// [`memoized_verify_by_evaluation`] (PROOF-2): verdict caches must never key
/// on the name alone, because reconstructed obligations bake operand
/// immediates/displacements/scales into the expressions while omitting them
/// from the name.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct ProofObligation {
    /// Human-readable rule name, e.g., "Iadd_I32 -> ADDWrr".
    pub name: String,
    /// trust_ir semantics expression.
    pub trust_ir_expr: SmtExpr,
    /// AArch64 semantics expression.
    pub aarch64_expr: SmtExpr,
    /// Symbolic input variables: (name, bit-width).
    pub inputs: Vec<(String, u32)>,
    /// Optional preconditions that must hold (e.g., divisor != 0).
    pub preconditions: Vec<SmtExpr>,
    /// Symbolic floating-point input variables: (name, exponent_bits, significand_bits).
    ///
    /// These are declared as `(_ FloatingPoint eb sb)` in SMT-LIB2.
    /// Empty for purely bitvector proof obligations.
    pub fp_inputs: Vec<(String, u32, u32)>,

    /// Typed proof category, aligned with trust-transval's `CheckKind`.
    ///
    /// When set, this provides a structured categorization that can be mapped
    /// to trust-transval's verification condition taxonomy. When `None`, the
    /// category is determined by which module creates the proof obligation
    /// and the string-based category in `ProofResult`.
    ///
    /// See [`TransvalCheckKind`] for the full taxonomy.
    pub category: Option<TransvalCheckKind>,

    /// Provenance of the machine (target) side of this obligation (#63).
    ///
    /// Defaults to [`MachineSideProvenance::StaticDb`] for every static database
    /// builder (set mechanically in STEP 0 — no behavior change). The Phase-2
    /// pilot reconstruction path
    /// (`function_verifier::reconstruct_alu_obligation`) sets
    /// [`MachineSideProvenance::Reconstructed`], which is the sole provenance
    /// that [`Self::is_reconstructed`] credits.
    pub machine_side_provenance: MachineSideProvenance,
}

impl ProofObligation {
    /// STRICT static-template proven-honesty predicate (task #61).
    ///
    /// A static-database lowering proof counts as *genuinely proven / covered /
    /// verified* IFF it is NON-DEGENERATE — its trust_ir-side and machine-side
    /// semantic expressions are STRUCTURALLY DISTINCT (`SmtExpr` derives
    /// `PartialEq`, smt.rs):
    ///
    /// ```text
    /// is_genuinely_proven  <=>  trust_ir_expr != aarch64_expr
    /// ```
    ///
    /// This is the sole criterion for crediting a
    /// [`MachineSideProvenance::StaticDb`] proof. There is no name-ledger or
    /// allowlist exemption for a static `X == X`: it asserts only
    /// `NOT(X == X)` is UNSAT and cannot be refuted by a wrong emitted opcode or
    /// operand placement, because neither side came from that instruction.
    ///
    /// Static degenerate (`X == X`) obligations may still exist in the database
    /// as documented debt / model-consistency entries, but they contribute zero
    /// to any proven/covered/verified tally. Real-operand reconstructed
    /// obligations are reported through a separate legacy rule keyed by
    /// [`Self::is_reconstructed`]; that target-side tag alone must not be treated
    /// as exact source/operand provenance.
    pub fn is_genuinely_proven(&self) -> bool {
        self.trust_ir_expr != self.aarch64_expr
    }

    /// True IFF the machine side of this obligation was RECONSTRUCTED from the
    /// real emitted instruction (task #63 Phase-2 pilot).
    ///
    /// This is the provenance discriminator the reconstruction credit rule keys
    /// on: a reconstructed obligation is credited `Verified` IFF
    /// `is_reconstructed() && discharge == Valid`. Unlike
    /// [`Self::is_genuinely_proven`], this does NOT require the two SMT
    /// expressions to be structurally distinct — a commutative ALU
    /// reconstruction commonly produces `bvadd == bvadd`. This predicate says
    /// nothing about whether the source operation and operands were
    /// independently bound: callers needing complete lowering authority must
    /// enforce that provenance separately.
    pub fn is_reconstructed(&self) -> bool {
        matches!(
            self.machine_side_provenance,
            MachineSideProvenance::Reconstructed { .. }
        )
    }

    /// Structural identity: `trust_ir_expr == aarch64_expr`, the exact negation
    /// of [`Self::is_genuinely_proven`]. For static-database provenance this is a
    /// degenerate obligation that proves nothing about a lowering. Existing
    /// reports distinguish target-side reconstruction via
    /// [`Self::is_reconstructed`], but that distinction alone does not make an
    /// exact identity complete source-lowering evidence.
    pub fn is_degenerate(&self) -> bool {
        !self.is_genuinely_proven()
    }

    /// Build the negated equivalence formula for SMT solving.
    ///
    /// Returns `AND(all preconditions, NOT(trust_ir == aarch64))`.
    /// If this is UNSAT, the lowering is correct.
    ///
    /// Canonical connective shape is midpoint-balanced. Every original opaque
    /// leaf remains in the historical written order: reverse(preconditions),
    /// then the disequality. No leaf is simplified, flattened or deduplicated.
    pub fn negated_equivalence(&self) -> SmtExpr {
        // The count comes from the stored Vec plus the sole terminal. Consume
        // each term exactly once without a second O(n) premise inventory. Each
        // recursive range is halved, so connective work is O(n), construction
        // frames are O(log n), and there are exactly n original And nodes.
        fn build(terms: &mut impl Iterator<Item = SmtExpr>, count: usize) -> SmtExpr {
            if count == 1 {
                return terms.next().expect("canonical original leaf inventory");
            }
            let left = count / 2;
            let lhs = build(terms, left);
            let rhs = build(terms, count - left);
            lhs.and_expr(rhs)
        }

        let equiv = self
            .trust_ir_expr
            .clone()
            .eq_expr(self.aarch64_expr.clone());
        let not_equiv = equiv.not_expr();

        let count = self
            .preconditions
            .len()
            .checked_add(1)
            .expect("non-zero-sized Vec leaf count plus one cannot overflow");
        let mut terms = self
            .preconditions
            .iter()
            .rev()
            .cloned()
            .chain(std::iter::once(not_equiv));
        let formula = build(&mut terms, count);
        assert!(
            terms.next().is_none(),
            "complete canonical original inventory"
        );
        formula
    }

    /// Serialize the proof obligation to SMT-LIB2 format (for ay CLI).
    pub fn to_smt2(&self) -> String {
        use crate::ay_bridge::{expand_bounded_quantifiers, infer_obligation_logic_for_smt2};

        let mut lines = Vec::new();

        // Keep this legacy serializer close to the source expression shape.
        // Solver entry points use ay_bridge::prepare_formula_for_smt for
        // stronger simplification before invoking AY.
        let raw_formula = self.negated_equivalence();
        let formula = expand_bounded_quantifiers(&raw_formula);

        // Infer logic from the emitted formula plus declarations.
        let logic = infer_obligation_logic_for_smt2(self, &raw_formula, &formula, &[]);
        lines.push(format!("(set-logic {})", logic));

        // Declare symbolic bitvector inputs
        for (name, width) in &self.inputs {
            lines.push(format!("(declare-const {} (_ BitVec {}))", name, width));
        }

        // Declare symbolic floating-point inputs
        for (name, eb, sb) in &self.fp_inputs {
            lines.push(format!(
                "(declare-const {} (_ FloatingPoint {} {}))",
                name, eb, sb
            ));
        }

        // Declare the fresh, UNCONSTRAINED poison constants any TrapIfZero node
        // (x86 IDIV/DIV #DE-trap model) lowers to. Leaving them unconstrained makes
        // the solver treat the value at divisor==0 as arbitrary, so it cannot prove
        // the machine side equals the source side at the trap without the
        // divisor!=0 precondition — the SMT lane mirrors the native lane. See
        // `SmtExpr::TrapIfZero` / `collect_trap_poison_decls`.
        for (name, width) in crate::smt::collect_trap_poison_decls(&formula) {
            lines.push(format!("(declare-const {} (_ BitVec {}))", name, width));
        }

        // Assert the negated equivalence (with quantifiers expanded where possible)
        lines.push(format!("(assert {})", formula));
        lines.push("(check-sat)".to_string());

        lines.join("\n")
    }
}

/// Build the in-range precondition for a shift-lowering proof: `amount < width`.
///
/// trust-ir's pinned contract (interpret.rs `shift_amount`, 0ce2d7e lines
/// 3473-3484) returns `Err(ub("shift amount N is out of range for B-bit
/// integer"))` whenever the shift amount `rhs.raw >= bits` — i.e. a shift by
/// `>= width` is UNDEFINED BEHAVIOR in the source, NOT a clamp-to-0. The
/// verifier's SMT evaluator, by contrast, clamps `shift >= width` to 0
/// (`smt.rs` ~2011-2077) on BOTH the trust_ir and machine sides identically,
/// and AArch64 hardware masks the amount by `width-1`. So the unconditioned
/// shift obligation was asserting equivalence in a region (`[width, 2^width)`)
/// where the source contract leaves the value UNDEFINED, and the agreement
/// there was a vacuous artifact of using the same in-house clamp model on both
/// sides (the #57 divergence).
///
/// Scoping every shift obligation with `amount < width` restricts the claim to
/// the in-range region `[0, width)` where the source IS defined — exactly where
/// the lowering is a genuine 1:1 identity (Ishl->bvshl, Ushr->bvlshr,
/// Sshr->bvashr; a wrong opcode such as Ushr->Sshr still refutes on negative
/// operands). The out-of-range region is left out of the proof rather than
/// proven via a clamp model the source does not endorse.
///
/// `width` here is the integer type width; the shift-amount operand is itself a
/// `width`-bit bitvector (the proofs use same-width operands), so the bound is a
/// `width`-bit unsigned-less-than against `bv_const(width, width)`.
pub fn shift_in_range_precondition(amount: SmtExpr, width: u32) -> SmtExpr {
    amount.bvult(SmtExpr::bv_const(u64::from(width), width))
}

// ---------------------------------------------------------------------------
// Mock verification (concrete evaluation)
// ---------------------------------------------------------------------------

/// Default number of random samples for statistical verification of
/// 32/64-bit proof obligations. Edge cases are always tested first
/// (0, 1, MAX, midpoints), then this many random trials follow.
///
/// A fixed sample count does not establish a universal confidence bound:
/// detection depends on the input distribution and the particular defect.
/// This is **not** a formal proof. Use AY plus independent Clean checking via
/// [`crate::ay_bridge::verify_with_ay`] for supported represented obligations.
pub const DEFAULT_SAMPLE_COUNT: u64 = 100_000;

/// Exhaustive work budget, expressed as the width of each of two inputs.
/// The default permits 2^(2 * 8) tuples, regardless of how input bits are split.
/// Two 16-bit inputs still require 2^32 evaluations and are sampled by default.
pub const EXHAUSTIVE_WIDTH_THRESHOLD: u32 = 8;

/// Configuration for the verification evaluation engine.
///
/// Controls sampling parameters for statistical (non-exhaustive) verification.
///
/// # Verification strength levels
///
/// | Level | Width | Inputs | Strategy | Guarantee |
/// |-------|-------|--------|----------|-----------|
/// | **Exhaustive** | Total <= 16 bits by default | Distinct integer inputs | Complete Cartesian domain | Complete for that domain |
/// | **Statistical** | Above the domain budget | any | Edge cases + N random samples | Probabilistic (configurable N) |
/// | **Formal** | supported | supported | AY + independent Clean checking | Complete for the represented obligation |
///
/// # Path to formal verification
///
/// The current `verify_by_evaluation` uses **mock verification**: exhaustive
/// for small widths, statistical sampling for larger widths. This catches most
/// bugs but cannot prove correctness for all 2^64 input combinations.
///
/// Evaluation and formal discharge are distinct APIs. [`crate::ay_bridge`]
/// uses aterm's packaged AY solver and independent Clean checker. The native
/// AY experiment was retired; there is no native-AY Cargo feature.
///
/// Statistical sampling is never instruction credit under either policy: the
/// function verifiers report a sampled discharge as `Unverified`.
/// Whether a function verifier replays source-bound obligations through the live
/// AY + independent-checker authority.
///
/// This is explicit verifier policy, not an environment switch. Library and
/// diagnostic verifiers keep [`EvaluationOnly`](Self::EvaluationOnly); compiler
/// proof-promotion verifiers select
/// [`SourceBoundReplay`](Self::SourceBoundReplay), under which an enforced,
/// source-paired AArch64 walk replays its checked frame and arithmetic
/// obligations formally. No policy upgrades a registry theorem or a sampled
/// verdict: the former live formal-on-miss route was deleted with the
/// withdrawal of substring, representative and statistical credit.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum ProofReplayPolicy {
    /// Evaluation evidence only; no live solver is entered.
    #[default]
    EvaluationOnly,
    /// Replay checked source-bound obligations through AY + an independent
    /// checker. Inconclusive replays leave the instruction uncredited.
    SourceBoundReplay,
}

#[derive(Debug, Clone)]
pub struct VerificationConfig {
    /// Number of random samples for statistical verification of widths
    /// above [`EXHAUSTIVE_WIDTH_THRESHOLD`]. Defaults to [`DEFAULT_SAMPLE_COUNT`].
    ///
    /// Higher values increase confidence but slow down verification.
    /// At N=1,000,000 a single 32-bit proof takes ~100ms on modern hardware.
    pub sample_count: u64,

    /// Exhaustive work budget, expressed as the width of each of two inputs.
    /// Defaults to [`EXHAUSTIVE_WIDTH_THRESHOLD`] (8): at most 2^16 tuples.
    /// Actual input widths are summed, so one 16-bit input or several narrower
    /// inputs have the same budget as two 8-bit inputs. FP is never enumerated.
    ///
    /// A single 16-bit input already fits the default budget (65,536 tuples).
    /// Raising this to 16 also permits 16-bit two-input proofs, requiring 2^32
    /// evaluations, so it can be very slow.
    pub exhaustive_threshold: u32,

    /// Whether source-bound obligations are replayed through live proof
    /// authority.
    pub proof_replay_policy: ProofReplayPolicy,
}

impl Default for VerificationConfig {
    fn default() -> Self {
        Self {
            sample_count: DEFAULT_SAMPLE_COUNT,
            exhaustive_threshold: EXHAUSTIVE_WIDTH_THRESHOLD,
            proof_replay_policy: ProofReplayPolicy::EvaluationOnly,
        }
    }
}

impl VerificationConfig {
    /// Create a configuration with the given sample count.
    pub fn with_sample_count(sample_count: u64) -> Self {
        Self {
            sample_count,
            ..Default::default()
        }
    }

    /// Configuration for a compiler verifier whose reports may authorize proof
    /// promotion. This does not weaken failure behavior: only a checked live
    /// [`AYResult::Verified`](crate::ay_bridge::AYResult::Verified) of a
    /// source-bound obligation credits `Formal`; every inconclusive replay
    /// leaves its instructions uncredited.
    pub fn for_proof_promotion() -> Self {
        Self {
            proof_replay_policy: ProofReplayPolicy::SourceBoundReplay,
            ..Self::default()
        }
    }

    pub(crate) fn replays_source_bound_obligations(&self) -> bool {
        self.proof_replay_policy == ProofReplayPolicy::SourceBoundReplay
    }
}

/// One policy shared by dispatch, memo shortcuts and strength accounting.
/// Count complete input tuples, not the first input's width. This both avoids
/// undersampling wider later inputs and permits complete small-domain checks
/// without increasing the historical two-input worst-case work budget.
pub(crate) fn exhaustive_input_count(
    obligation: &ProofObligation,
    config: &VerificationConfig,
) -> Option<u64> {
    if obligation.inputs.is_empty()
        || !obligation.fp_inputs.is_empty()
        || uses_checked_scalar_fp_evaluation(obligation)
    {
        return None;
    }
    let budget_bits = config.exhaustive_threshold.saturating_mul(2).min(63);
    let mut bits = 0u32;
    for (index, (name, width)) in obligation.inputs.iter().enumerate() {
        if *width == 0
            || *width > 63
            || obligation.inputs[..index]
                .iter()
                .any(|(earlier, _)| earlier == name)
        {
            return None;
        }
        bits = bits.checked_add(*width)?;
        if bits > budget_bits {
            return None;
        }
    }
    1u64.checked_shl(bits)
}

fn needs_multi_input_sampling(obligation: &ProofObligation) -> bool {
    obligation.inputs.len() > 2
        || obligation
            .inputs
            .windows(2)
            .any(|pair| pair[0].1 != pair[1].1)
}

/// Every uninterpreted function `obligation`'s terms mention — both sides and
/// every precondition — sorted and deduplicated.
pub(crate) fn evaluator_uninterpreted_functions(obligation: &ProofObligation) -> Vec<String> {
    let mut names = obligation.trust_ir_expr.uninterpreted_functions();
    names.extend(obligation.aarch64_expr.uninterpreted_functions());
    for pre in &obligation.preconditions {
        names.extend(pre.uninterpreted_functions());
    }
    names.sort();
    names.dedup();
    names
}

/// The terms of `obligation` that carry an uninterpreted function, in term
/// order: `source expression`, `machine expression`, `precondition {index}` —
/// the same names the point-level `Inconclusive` reasons use, so a
/// precondition is identified by its position whichever path declines it.
fn evaluator_uninterpreted_function_sites(obligation: &ProofObligation) -> Vec<String> {
    let carries = |term: &SmtExpr| !term.uninterpreted_functions().is_empty();
    let mut sites = Vec::new();
    if carries(&obligation.trust_ir_expr) {
        sites.push("source expression".to_string());
    }
    if carries(&obligation.aarch64_expr) {
        sites.push("machine expression".to_string());
    }
    for (index, pre) in obligation.preconditions.iter().enumerate() {
        if carries(pre) {
            sites.push(format!("precondition {index}"));
        }
    }
    sites
}

/// The evaluator's answer for an obligation it cannot decide AT ALL: one whose
/// terms carry an uninterpreted function.
///
/// Concrete evaluation assigns a value to every declared input and computes
/// both sides; a UF has no interpretation here (`SmtExpr::try_eval` errors on
/// it), so no sampled or exhaustive point is evidence for OR against the
/// obligation. The honest outcome is a named, fail-closed non-verdict —
/// `Unknown`, never `Valid`, never a panic. (The frame theorems bind initial
/// memory as the zero-argument UF `entry_memory`; they are solver-lane
/// obligations that merely sit in the same registry.) Deciding this on the
/// whole obligation, before any point is evaluated, also covers a UF that no
/// tested point reaches: `try_eval` evaluates only the taken arm of an `ite`,
/// so a point-level check alone could compare such an obligation as equal.
/// The reason names every function and every term that carries one, and is
/// deterministic in the obligation alone, so a sequential and a chunked sweep
/// agree on it.
pub(crate) fn evaluator_undecidable(obligation: &ProofObligation) -> Option<VerificationResult> {
    let names = evaluator_uninterpreted_functions(obligation);
    if names.is_empty() {
        return None;
    }
    let listed = names
        .iter()
        .map(|name| format!("'{name}'"))
        .collect::<Vec<_>>()
        .join(", ");
    let sites = evaluator_uninterpreted_function_sites(obligation).join(", ");
    Some(VerificationResult::Unknown {
        reason: format!(
            "evaluator cannot decide: uninterpreted function {listed} (in {sites}); \
             concrete evaluation has no interpretation for it, so no tested point is \
             evidence either way — this obligation needs the solver lane"
        ),
    })
}

/// Verify a proof obligation by exhaustive testing for small widths
/// or random sampling for larger widths, using default configuration.
///
/// # Verification strategy
///
/// - **Integer domains within budget**: Exhaustive -- tests every tuple using
///   each input's own width (at most 65,536 tuples by default).
/// - **Larger uniform domains, inputs <= 2**: Statistical -- tests 6 edge cases per input
///   (0, 1, MAX, MAX-1, midpoint, midpoint-1) in all combinations (36 pairs),
///   then [`DEFAULT_SAMPLE_COUNT`] (100,000) random samples using a deterministic
///   LCG seeded from the proof obligation name.
/// - **Larger mixed-width or 3+ input domains**: Statistical -- tests edge cases, then
///   [`DEFAULT_SAMPLE_COUNT`] random samples with per-input width masking.
///
/// # Guarantees
///
/// Within the exhaustive budget: **complete** for the declared input domain.
/// Above it: **statistical**, not a proof. A fixed sample count establishes no
/// universal confidence bound; detection depends on the defect and distribution.
///
/// Either way, a sweep in which no tested point satisfies the obligation's
/// preconditions compared nothing and returns [`VerificationResult::Unknown`],
/// never `Valid`: the exhaustive sweep says so directly, the sampled sweeps
/// with a "vacuous sample" reason (sampling cannot tell an unsatisfiable
/// precondition from one it never hit).
///
/// An obligation whose terms carry an **uninterpreted function** is outside
/// concrete evaluation altogether and returns `Unknown` naming the function
/// (see [`evaluator_undecidable`]) — never `Valid`, never a panic. Any other
/// term `SmtExpr::try_eval` refuses likewise stops the sweep with `Unknown`.
///
/// For formal guarantees on 32/64-bit widths, use
/// [`crate::ay_bridge::verify_with_ay`] or enable the `ay` feature.
pub fn verify_by_evaluation(obligation: &ProofObligation) -> VerificationResult {
    verify_by_evaluation_with_config(obligation, &VerificationConfig::default())
}

/// Verify a proof obligation with a custom [`VerificationConfig`].
///
/// See [`verify_by_evaluation`] for strategy details. The `config` parameter
/// controls the number of random samples and the exhaustive width threshold.
pub fn verify_by_evaluation_with_config(
    obligation: &ProofObligation,
    config: &VerificationConfig,
) -> VerificationResult {
    // A term the evaluator cannot interpret is a NON-VERDICT for the whole
    // obligation, decided before any dispatch (including the identical-tree
    // shortcut below, which `memoized_verify_by_evaluation` replicates and
    // must exclude in lockstep): see `evaluator_undecidable`.
    if let Some(undecidable) = evaluator_undecidable(obligation) {
        return undecidable;
    }
    // Checked scalar FP must precede BOTH legacy FP substitution and the
    // identical-tree shortcut: equal malformed/unbound trees are not evidence.
    if uses_checked_scalar_fp_evaluation(obligation) {
        return if checked_fp_values::applies(obligation) {
            checked_fp_values::verify(obligation, config)
        } else {
            checked_fcmp::verify(obligation, config)
        };
    }
    let width = obligation.inputs.first().map(|(_, w)| *w).unwrap_or(32);
    let num_inputs = obligation.inputs.len();
    let exhaustive_count = exhaustive_input_count(obligation, config);

    // Legacy FP-only obligations (e.g. FADD/FSUB/FMUL/FDIV/FNEG/FABS/FSQRT
    // lowering proofs) carry their operands in `fp_inputs` rather than
    // `inputs`. Dispatch them to the dedicated FP evaluator which:
    //   1. substitutes a battery of IEEE-754 edge-case test vectors
    //      (including NaN, +/-0.0, +/-Inf, denormals, MAX/MIN) into the
    //      obligation's template expressions, and
    //   2. compares results with `fp_results_equal`, which treats
    //      "NaN on both sides" as equal -- the correct behaviour for FP
    //      lowering verification since Rust's derived `PartialEq` on
    //      `EvalResult::Float(f64)` follows IEEE-754 semantics where
    //      `NaN != NaN`. Without this dispatch, FDIV proofs spuriously
    //      report counterexamples like `trust_ir=Float(NaN), aarch64=Float(NaN)`
    //      because the placeholder `fp_const(0.0) / fp_const(0.0)` that
    //      `check_single_point` evaluates produces NaN on both sides
    //      (#388, issue tracked under #329 / #406).
    if num_inputs == 0 && !obligation.fp_inputs.is_empty() {
        // RECONSTRUCTED FP obligations (task: FP/div/madd extension) carry their
        // operands as DISTINCT NAMED FP leaves (`recon_a`/`recon_b`) so the
        // evaluator can preserve operand WIRING. The static-DB FP evaluator
        // (`verify_fp_by_evaluation`) rebuilds only the ROOT node with canonical
        // (a, b) ordering and so cannot distinguish a swapped non-commutative op
        // (FSUB(b,a) vs FSUB(a,b)) — it would wrongly pass a wrong-wiring bug. The
        // reconstruction evaluator substitutes per-leaf-NAME into BOTH sides, so a
        // swapped FDIV/FSUB machine side genuinely diverges from the source side
        // for asymmetric inputs ⇒ REFUTE. Routed only for `is_reconstructed()`
        // obligations; static-DB FP proofs keep their existing path unchanged.
        if obligation.is_reconstructed() {
            return verify_fp_reconstructed_by_evaluation(obligation);
        }
        return verify_fp_by_evaluation(obligation);
    }

    // Establish the complete supported scalar subset before considering the
    // identity shortcut. Unsupported expressions or preconditions must reach
    // the fallible interpreter and cannot gain a Valid verdict from equality.
    let compiled = CompiledObligation::try_new(obligation);
    let compiled = compiled.as_ref();

    // SOUND VERDICT-IDENTICAL SHORT-CIRCUIT (proof-lane floor).
    //
    // When the two modeled sides are the SAME expression tree, evaluation is a
    // deterministic pure function of `(expr, env)`, so both sides produce the
    // IDENTICAL `EvalResult` at every sampled point. `check_single_point` can
    // therefore only return `Equal`/`PreconditionUnmet` — a `Counterexample`
    // is STRUCTURALLY impossible. On the STATISTICAL dispatch below a
    // counterexample-free sweep returns `Valid` exactly when at least one
    // sampled point satisfied every precondition, and the vacuous-sample
    // `Unknown` otherwise (see `sampled_sweep_verdict`). So return `Valid`
    // directly — skipping the whole `DEFAULT_SAMPLE_COUNT` (100k) sweep — only
    // when that witness is already in hand: trivially with no preconditions,
    // else at a point of the sweep's own edge battery
    // (`identical_sides_edge_witness`). With no edge witness the full sweep
    // runs and decides between `Valid` and the vacuous-sample `Unknown` itself.
    //
    // This fires on the correctly-lowered commutative/associative integer ALU +
    // immediate-baked + address-of LEA reconstructed obligations
    // (`bvadd == bvadd`, `bvand == bvand`, `bvmul == bvmul`, LEA `base+disp ==
    // base+disp`, ...) that dominate a wrapping_add + loop-control MIXED
    // program. A wrong opcode / swapped non-commutative wiring / wrong
    // immediate makes the two sides STRUCTURALLY DISTINCT, so this does NOT
    // fire there and the full REFUTING sweep runs unchanged — refutation power
    // is exactly preserved.
    //
    // Restricted to the STATISTICAL path through the same input-domain policy
    // as dispatch and strength accounting: the exhaustive path can legitimately
    // downgrade a vacuous-precondition obligation to `Unknown` via
    // `sweep_verdict`, so it must still run. `fp_inputs` obligations are
    // handled/returned above.
    //
    // TRAP-FREE GUARD (LOAD-BEARING — do NOT drop): `EvalResult::semantically_equal`
    // is NOT reflexive for `Poison` — `semantically_equal(Poison, Poison) ==
    // false` (smt.rs, unit-tested), because a trapping x86 IDIV/DIV `#DE` has
    // no defined result and must refute against anything, even another trap.
    // The SOLE `Poison` producer is `SmtExpr::TrapIfZero` at an unguarded
    // `guard == 0` (both evaluators: tree-walk `try_eval` and the `FlatProg`
    // fast path). So an identical-sided tree containing ANY `TrapIfZero`
    // could make the sweep sample `guard == 0` and REFUTE (Poison vs Poison =>
    // not-equal => `Counterexample` => `Invalid`) — short-circuiting THAT to
    // `Valid` would credit `Valid` where the sweep refutes = a silent
    // proof-system miscompile. We therefore EXCLUDE any tree that contains a
    // `TrapIfZero` (`collect_trap_poison_decls` empty) and let it run the full
    // sweep. Requiring the complete compiled scalar subset also excludes
    // uninterpreted functions, missing input bindings and unsupported guards.
    // Within that subset, every trap-free satisfying point is `Equal`.
    if exhaustive_count.is_none()
        && let Some(co) = compiled
        && obligation.trust_ir_expr == obligation.aarch64_expr
        && crate::smt::collect_trap_poison_decls(&obligation.trust_ir_expr).is_empty()
        && identical_sides_edge_witness(obligation, co)
    {
        return VerificationResult::Valid;
    }

    if let Some(count) = exhaustive_count {
        verify_exhaustive(obligation, compiled, count)
    } else if needs_multi_input_sampling(obligation) {
        verify_random_multi(obligation, compiled, config.sample_count)
    } else {
        verify_random(obligation, compiled, width, config.sample_count)
    }
}

// ---------------------------------------------------------------------------
// Shared content-keyed evaluation memo (PROOF-2)
// ---------------------------------------------------------------------------

/// Process-wide memo key for [`memoized_verify_by_evaluation`]: the FULL
/// obligation content plus the evaluation-engine configuration knobs.
///
/// # Soundness (PROOF-2, roadmap 2026-07-01 — memo-key content identity)
///
/// The key must bind EVERYTHING that determines the verdict. The retired key
/// was `(obligation.name, sample_count, exhaustive_threshold)` — but
/// RECONSTRUCTED obligations bake operand immediates / displacements / scales
/// into their expression trees while OMITTING them from the name
/// (`x86_64_function_verifier::reconstruct_alu_obligation` /
/// `reconstruct_x86_lea`), so two obligations with the SAME name can carry
/// semantically DIFFERENT content. Under the old key a `Valid` verdict for
/// `AddRI imm=5` was replayed for `imm=7`, and a REFUTATION the second
/// instance would have produced (e.g. a wrong machine-side immediate or LEA
/// displacement) was never computed — a latent unsound verdict-replay class
/// and a hard blocker for broadening any persistent cache.
///
/// This key embeds the obligation ITSELF (structural `Eq` + `Hash` over both
/// expression trees, inputs, preconditions, fp_inputs, category, provenance
/// and name), so a lookup can NEVER return a verdict for different content:
/// `HashMap` confirms full structural equality on every hit, which is
/// strictly STRONGER than any digest-string key (zero collision risk, not
/// merely cryptographically negligible).
///
/// # Relation to solver memoization
///
/// The CLI solver's process-local memo keys by content: SHA-256 over the domain
/// tag, solver identity, and exact SMT2 bytes. This memo realizes the same
/// identity notion — verdict keyed by complete obligation content plus
/// discharging-engine identity — for
/// the in-process EVALUATION engine, whose "engine identity" is the
/// (`sample_count`, `exhaustive_threshold`) config rather than a solver
/// binary. It is intentionally structural rather than a serialized-text
/// digest, per the roadmap PROOF-2 reviewer correction (b): the hot
/// per-instruction path must not re-serialize full SMT2 text, and hashing the
/// in-memory trees is both cheaper and collision-free. Neither memo leaves the
/// process; persisted digests are correlation hints, never proof verdicts.
///
/// # Why the name stays in the key
///
/// The evaluator's sampling RNG is an LCG seeded from the obligation NAME
/// (see [`verify_random`] / [`verify_random_multi`]), so the verdict is a
/// deterministic function of (content, name, config) — all three are bound.
/// Keeping the name also makes the new key a strict REFINEMENT of the old
/// one: every old entry can only SPLIT into finer entries, never merge —
/// caching becomes strictly stricter, no gate is weakened.
#[derive(PartialEq, Eq)]
struct EvalMemoKey {
    /// The complete obligation, compared/hashed structurally.
    obligation: ProofObligation,
    /// [`VerificationConfig::sample_count`] used for the discharge.
    sample_count: u64,
    /// [`VerificationConfig::exhaustive_threshold`] used for the discharge.
    exhaustive_threshold: u32,
}

/// Shard count for the process-wide verdict memo. The per-function
/// certificate lane fans out across a bounded rayon pool (CT-5 / CT-7), so
/// the memo must not funnel every worker through ONE global lock: sharding by
/// key hash bounds contention to hash collisions. 16 comfortably exceeds the
/// pool width; the shard index is a pure function of the key, so lookup
/// behavior is deterministic and identical to the single-map memo.
const EVAL_MEMO_SHARDS: usize = 16;

/// One memo entry: a compute-once cell. The FIRST worker to reach a new key
/// claims the cell and runs the evaluation sweep inside `OnceLock::get_or_init`;
/// every concurrent worker needing the SAME verdict blocks on the cell (no
/// CPU) and reuses the result. Without this claim, the parallel cert lane
/// REPLICATED the discharge instead of dividing it: a merged module's
/// near-identical functions walk the same obligation stream in lockstep, so
/// under the old get/compute/insert memo every worker re-ran the same
/// 10^5-sample sweep during the shared miss window (measured: 8 workers burned
/// 2.4x the serial CPU with a WORSE wall time). Soundness is unchanged:
/// `verify_by_evaluation_with_config` is a deterministic pure function of the
/// key, so whichever thread computes, the verdict is identical — and a FAILED
/// verdict is memoized exactly as before (fail-closed verdicts repeat).
type EvalMemoCell = std::sync::Arc<std::sync::OnceLock<VerificationResult>>;

/// One memo shard: entries bucketed by [`memo_bucket_hash`]. Equality inside a
/// bucket is the FULL content (`EvalMemoKey: Eq`), so the bucket hash is only
/// a locator — colliding obligations (a reconstructed family sharing a name)
/// share a bucket and are told apart by comparison, never by hash.
type EvalMemoShard = HashMap<u64, Vec<(EvalMemoKey, EvalMemoCell)>>;

/// The memo's locator hash: the obligation's NAME, its input names and
/// widths, and the config knobs — never the expression trees. Hashing the
/// trees walked every node of an up-to-800-op obligation on every lookup
/// (twice: shard choice and map), on every instruction of every certificate
/// walk; the name + inputs pin the bucket just as well, and content equality
/// does the rest.
fn memo_bucket_hash(
    obligation: &ProofObligation,
    sample_count: u64,
    exhaustive_threshold: u32,
) -> u64 {
    use std::hash::{Hash, Hasher};
    let mut hasher = std::collections::hash_map::DefaultHasher::new();
    obligation.name.hash(&mut hasher);
    obligation.inputs.hash(&mut hasher);
    obligation.fp_inputs.len().hash(&mut hasher);
    obligation.preconditions.len().hash(&mut hasher);
    sample_count.hash(&mut hasher);
    exhaustive_threshold.hash(&mut hasher);
    hasher.finish()
}

/// The process-wide verdict memo shared by BOTH function verifiers
/// (`x86_64_function_verifier::X86FunctionVerifier` and
/// `function_verifier::FunctionVerifier`), sharded by key hash.
fn eval_memo() -> &'static [std::sync::Mutex<EvalMemoShard>; EVAL_MEMO_SHARDS] {
    static MEMO: std::sync::OnceLock<[std::sync::Mutex<EvalMemoShard>; EVAL_MEMO_SHARDS]> =
        std::sync::OnceLock::new();
    MEMO.get_or_init(|| std::array::from_fn(|_| std::sync::Mutex::new(HashMap::new())))
}

/// Shard for `key`, selected by the key's structural hash (computed OUTSIDE
/// any lock).
fn eval_memo_shard(bucket: u64) -> &'static std::sync::Mutex<EvalMemoShard> {
    &eval_memo()[(bucket as usize) % EVAL_MEMO_SHARDS]
}

/// Find the cell for `(obligation, config)` in `shard`'s bucket — full-content
/// comparison, no clone. A stored key is a clone of the first obligation seen
/// with that content, so it shares its `Arc` subtrees and the comparison takes
/// `Arc`'s pointer-equality fast path for repeats of the same registry entry.
fn memo_find(
    shard: &EvalMemoShard,
    bucket: u64,
    obligation: &ProofObligation,
    sample_count: u64,
    exhaustive_threshold: u32,
) -> Option<EvalMemoCell> {
    shard.get(&bucket)?.iter().find_map(|(key, cell)| {
        (key.sample_count == sample_count
            && key.exhaustive_threshold == exhaustive_threshold
            && key.obligation == *obligation)
            .then(|| std::sync::Arc::clone(cell))
    })
}

/// Discharge an obligation by evaluation, memoizing the verdict process-wide
/// under a CONTENT-COMPLETE key (see [`EvalMemoKey`] for the soundness
/// argument).
///
/// Per-compile proof certification re-discharges the SAME obligation for
/// every instruction instance that maps to it (a function with fifty ADDs
/// would otherwise run the Iadd evaluation sweep fifty times, at up to ~10^5
/// sampled evaluations each). The memo is SOUND because
/// [`verify_by_evaluation_with_config`] is a deterministic pure function of
/// exactly the key's fields: the obligation's expression trees / inputs /
/// preconditions / fp_inputs (evaluated), its provenance (routes the FP
/// reconstruction evaluator), its name (seeds the sampling LCG), and the two
/// config knobs. Two calls with equal keys are therefore guaranteed to return
/// the same verdict; two obligations differing ANYWHERE in content occupy
/// distinct entries.
///
/// A FAILED result is memoized too — fail-closed verdicts repeat, they do not
/// get masked.
pub fn memoized_verify_by_evaluation(
    obligation: &ProofObligation,
    config: &VerificationConfig,
) -> VerificationResult {
    // Identical-sided TRAP-FREE obligations with a precondition witness in
    // hand sweep to `Valid` (see the short-circuit in
    // `verify_by_evaluation_with_config`, whose predicate this replicates IN
    // LOCKSTEP — including the trap-free guard and the edge-battery witness):
    // return `Valid` WITHOUT cloning the obligation into an `EvalMemoKey`
    // (line below) or taking the shard lock. This is the SAME verdict the memo
    // would compute and store on this key; it is pure clone/lock elision that
    // removes the per-instruction clone on the <16-inst serial functions.
    // The predicate MUST exclude the same checked-comparison route as the
    // primary entry. Legacy FP-only obligations also return before the primary
    // shortcut and are excluded here by `fp_inputs.is_empty()`. The complete
    // supported scalar subset is required here too: equality alone cannot
    // evaluate an unsupported expression or precondition. Without an edge
    // witness the obligation takes the memo like any other, and the sweep
    // decides between `Valid` and the vacuous-sample `Unknown`.
    // The primary entry answers a UF-bearing obligation with a non-verdict
    // BEFORE its shortcut (`evaluator_undecidable`), so the elided shortcut
    // here must decline the same obligations — walked only once the two sides
    // already compare equal.
    if obligation.fp_inputs.is_empty()
        && !uses_checked_scalar_fp_evaluation(obligation)
        && exhaustive_input_count(obligation, config).is_none()
        && obligation.trust_ir_expr == obligation.aarch64_expr
        && crate::smt::collect_trap_poison_decls(&obligation.trust_ir_expr).is_empty()
        && evaluator_uninterpreted_functions(obligation).is_empty()
        && let Some(co) = CompiledObligation::try_new(obligation)
        && identical_sides_edge_witness(obligation, &co)
    {
        return VerificationResult::Valid;
    }
    let bucket = memo_bucket_hash(obligation, config.sample_count, config.exhaustive_threshold);
    // Claim (or find) this key's compute-once cell under the shard lock; the
    // lock is held only for the map access, NEVER during the sweep.
    let cell: EvalMemoCell = {
        let shard = eval_memo_shard(bucket);
        let mut map = shard.lock().expect("shared eval memo poisoned");
        match memo_find(
            &map,
            bucket,
            obligation,
            config.sample_count,
            config.exhaustive_threshold,
        ) {
            Some(cell) => cell,
            None => {
                // First sight of this content: the one place the obligation is
                // cloned into the memo.
                let cell = EvalMemoCell::default();
                map.entry(bucket).or_default().push((
                    EvalMemoKey {
                        obligation: obligation.clone(),
                        sample_count: config.sample_count,
                        exhaustive_threshold: config.exhaustive_threshold,
                    },
                    std::sync::Arc::clone(&cell),
                ));
                cell
            }
        }
    };
    // First thread to reach a new key computes; concurrent workers needing
    // the same verdict block here (no redundant sweep) and share the result.
    //
    // TCG_TIME_SWEEP attribution (inert unless the var is set): the sweep lane
    // is a FIXED per-binary cost — an empty `fn main() {}` and a 128-function
    // program both pay ~75-110ms of it, because the work is per-OBLIGATION-KIND
    // (each swept once per process and memoised) and not per certificate. That
    // makes the per-obligation cost the only thing worth knowing, and until
    // this print existed it was unobservable. Reports only keys that MISS the
    // memo, since a hit costs nothing.
    if !sweep_trace_enabled() {
        return cell
            .get_or_init(|| verify_by_evaluation_with_config(obligation, config))
            .clone();
    }
    let mut computed_ms = None;
    let verdict = cell
        .get_or_init(|| {
            let t = std::time::Instant::now();
            let v = verify_by_evaluation_with_config(obligation, config);
            computed_ms = Some(t.elapsed().as_secs_f64() * 1000.0);
            v
        })
        .clone();
    if let Some(ms) = computed_ms {
        // TCG_SWEEP_BT=<substring>: print the backtrace of the FIRST miss whose
        // name contains it, to find which discharge site owns a kind.
        if let Some(want) = std::env::var_os("TCG_SWEEP_BT")
            && obligation.name.contains(&*want.to_string_lossy())
        {
            static ONCE: std::sync::Once = std::sync::Once::new();
            ONCE.call_once(|| {
                eprintln!(
                    "TCG_SWEEP_BT {}\n{}",
                    obligation.name,
                    std::backtrace::Backtrace::force_capture()
                );
            });
        }
        let co = CompiledObligation::try_new(obligation);
        let compiled = co.is_some();
        let ops = co.as_ref().map(CompiledObligation::op_count).unwrap_or(0);
        let thread = std::thread::current();
        eprintln!(
            "TCG_TIME_SWEEP {ms:8.2}ms thread={} compiled={compiled} ops={ops} inputs={} widths={:?} \
             cat={:?} {}",
            thread.name().unwrap_or("?"),
            obligation.inputs.len(),
            obligation
                .inputs
                .iter()
                .map(|(_, width)| *width)
                .collect::<Vec<_>>(),
            obligation.category,
            obligation.name,
        );
    }
    verdict
}

/// Whether `TCG_TIME_SWEEP` per-obligation attribution is on. Read once.
fn sweep_trace_enabled() -> bool {
    static ON: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *ON.get_or_init(|| std::env::var_os("TCG_TIME_SWEEP").is_some())
}

/// PROOF-4 B1: discharge a FIXED `ProofDatabase` registry obligation,
/// preferring a replayable committed proof over the evaluation sweep.
///
/// - **Exhaustive** (<= 8-bit, <= 2-input) obligations: the evaluation sweep IS
///   a complete proof for the width — `Exhaustive` strength. No tier-0
///   consultation (there is nothing stronger to prefer).
/// - **Statistical** (> 8-bit / > 2-input) obligations: an exact portable
///   certificate replay, or a committed tier-0 candidate revalidated by a live
///   solver in this process, yields `Formal`. Otherwise the result is the
///   evaluation sweep at its honest `Statistical` strength. No policy spends a
///   live solve on a miss: that formal-on-miss upgrade route existed only to
///   lift registry credit and was deleted with it. The persisted row is never
///   proof authority by itself.
///
/// This discharges the THEOREM. It is not instruction credit: the function
/// verifiers never bind a registry theorem to an emitted instruction.
pub fn discharge_registry_obligation(
    obligation: &ProofObligation,
    config: &VerificationConfig,
) -> (VerificationResult, crate::verify::VerificationStrength) {
    use crate::verify::VerificationStrength;
    let base = VerificationStrength::for_obligation_with_config(obligation, config);
    if matches!(base, VerificationStrength::Statistical { .. }) {
        // Portable DRAT authority is solver-independent and binds the exact
        // canonical DB query.  Consult it before tier-0 so a missing, dirty, or
        // differently-versioned solver cannot hide a replayable proof.
        if crate::verdict_db::portable_cert_verified_obligation(obligation) {
            return (VerificationResult::Valid, VerificationStrength::Formal);
        }
        match crate::verdict_db::tier0_lookup_obligation(obligation) {
            crate::verdict_db::Tier0LookupOutcome::Verified => {
                return (VerificationResult::Valid, VerificationStrength::Formal);
            }
            crate::verdict_db::Tier0LookupOutcome::Refuted { counterexample } => {
                return (
                    VerificationResult::Invalid {
                        counterexample: format!(
                            "live tier-0 candidate revalidation refuted the obligation: \
                             {counterexample}"
                        ),
                    },
                    base,
                );
            }
            crate::verdict_db::Tier0LookupOutcome::Inconclusive
            | crate::verdict_db::Tier0LookupOutcome::Miss => {}
        }
    }
    (memoized_verify_by_evaluation(obligation, config), base)
}

/// Discharge a target-reconstructed obligation without overstating its source
/// authority.
///
/// `instance` is reconstructed from the real emitted opcode and positional
/// operands. `canonical` is the corresponding free-immediate theorem retained
/// for exact-query/certificate generation. Neither object currently binds the
/// inferred source opcode, width, or fresh symbolic operands to the exact LIR /
/// trust-ir instruction that caused the emission. A solver or portable
/// certificate can therefore prove the represented target-derived theorem but
/// cannot, by itself, prove this particular source-to-target lowering.
///
/// Until that relationship is represented by an independently checked binding
/// token, every reconstructed obligation stays on its honest evaluation tier:
/// `Exhaustive` for the small complete domain, otherwise `Statistical`. The
/// canonical tier-0 rows and portable certificates remain useful, independently
/// replayable theorem artifacts, but confer no per-instruction `Formal` credit.
///
/// This function is the UNBOUND route and its behavior is exactly that. When a
/// caller HOLDS the binding token, it calls
/// [`discharge_reconstructed_obligation_with_exact_source_binding`] instead;
/// that token is unforgeable outside
/// [`crate::x86_source_operand_binding::bind_exact_source_operands`], so the
/// two routes cannot be confused and this one can never answer `Formal`.
pub fn discharge_reconstructed_obligation(
    instance: &ProofObligation,
    _canonical: &ProofObligation,
    config: &VerificationConfig,
) -> (VerificationResult, crate::verify::VerificationStrength) {
    use crate::verify::VerificationStrength;

    // Do NOT promote `instance.trust_ir_expr == instance.aarch64_expr` locally
    // based only on `Reconstructed` provenance. That tag binds how the target
    // tree was produced, but current architecture reconstructors can infer the
    // nominal source op from the emitted opcode and do not bind symbolic inputs
    // to the exact source operands. A bad source Iadd -> machine SUB can therefore
    // self-reconstruct as `bvsub == bvsub`. A checked solver can prove that
    // represented equality, but callers still need separately enforced exact
    // source+operand provenance to turn it into a complete lowering claim. This
    // function must not synthesize a local Formal verdict from identity alone.
    // Pinned end-to-end by
    // `reconstructed_identity_cannot_formally_self_attest_wrong_source_opcode`.
    let base = VerificationStrength::for_obligation_with_config(instance, config);
    (memoized_verify_by_evaluation(instance, config), base)
}

/// Discharge a target-reconstructed obligation whose symbolic inputs ARE bound
/// to the exact operands of an identified source instruction (TV-1 EXTENDED).
///
/// This is the same reconstructed route as
/// [`discharge_reconstructed_obligation`] over the same obligation; the only
/// difference is that the caller has supplied an
/// [`crate::x86_source_operand_binding::ExactSourceOperandBinding`], the witness
/// that the third provenance ingredient — operand identity — was checked. That
/// witness cannot be constructed outside
/// [`crate::x86_source_operand_binding::bind_exact_source_operands`], so the
/// `Formal` credit below is reachable only through the checked binding.
///
/// # Why `Formal` is warranted HERE and refused there
///
/// [`discharge_reconstructed_obligation`] refuses a local `Formal` verdict
/// because the reconstruction's source side is inferred from the emitted opcode
/// and its symbols are fresh: a bad source `Iadd` lowered to a machine `SUB`
/// self-reconstructs as `bvsub == bvsub`, which a solver proves without saying
/// anything about the lowering. Under the witness both defects are excluded:
/// the source operation was checked EQUAL to the replayed source instruction's
/// opcode (so the obligation reads `⟦S⟧ == ⟦M⟧` and a wrong selection refutes),
/// and each symbol stands for the exact machine operand ISel recorded for the
/// corresponding operand of that instruction. Nothing in the chain is sampled:
/// the binding is a decidable syntactic check and the equality is discharged by
/// an exact portable DRAT certificate or a tier-0 candidate revalidated by a
/// live checked solver, both keyed on THIS obligation's content.
///
/// # WHAT THIS REACHES IN PRACTICE, measured
///
/// Those two are now the WHOLE list. The E0.2/E0.5 withdrawal deleted
/// `try_formal_on_miss`, the tier-0 MISS arm that ran one live checked solve, so
/// a freshly reconstructed obligation with no committed artifact has nothing
/// left to reach `Formal` with and takes the fallback below. MEASURED on Linux
/// x86-64 (`reports/perf/2026-09-27-linux-x86-64-xd01-on-current-upstream/`),
/// that is every bound row on the eight floor targets: the binding's current
/// contribution is refutation and refusal, not credit. The `Formal` arm is kept
/// because it is the honest verdict for a bound obligation that DOES have a
/// committed certificate or row, and because it is the arm a future
/// source-bound live lane for x86-64 would discharge through — not because
/// anything on this host takes it today.
///
/// A non-`Formal` outcome falls back to
/// [`discharge_reconstructed_obligation`] verbatim, so a missing artifact, a
/// disabled verdict database, or an inconclusive answer LOWERS to the existing
/// honest tier rather than granting anything.
///
/// The binding's boundary (what a `Formal` credit here does and does not cover)
/// is stated on [`crate::x86_source_operand_binding`]; it is not repeated here
/// so the two cannot drift.
pub(crate) fn discharge_reconstructed_obligation_with_exact_source_binding(
    instance: &ProofObligation,
    canonical: &ProofObligation,
    config: &VerificationConfig,
    _binding: &crate::x86_source_operand_binding::ExactSourceOperandBinding,
) -> (VerificationResult, crate::verify::VerificationStrength) {
    use crate::verify::VerificationStrength;

    // The INSTANCE obligation is what gets routed, never the parametric
    // `canonical` form: crediting the instance from a free-immediate
    // generalization would need a substitution argument the binding does not
    // supply. `canonical` stays an artifact-identity carrier here, exactly as on
    // the unbound route.
    //
    // WHICH ROUTE, after E0.2/E0.5. The live formal-on-miss upgrade is gone, so
    // the only ways this obligation reaches `Formal` are the two that replay a
    // committed artifact against THIS obligation's content: an exact portable
    // DRAT certificate, or a tier-0 candidate revalidated by a live checked
    // solver. Both are content-keyed on the instance, neither is a name lookup,
    // and neither was reintroduced here — `discharge_registry_obligation` is
    // called for those two lanes only, and it spends no solve on a miss.
    let (result, strength) = discharge_registry_obligation(instance, config);
    if matches!(strength, VerificationStrength::Formal)
        && matches!(result, VerificationResult::Valid)
    {
        return (result, strength);
    }
    // A REFUTATION from the registry route is the mechanism's content and must
    // not be discarded by falling back to sampling.
    if matches!(result, VerificationResult::Invalid { .. }) {
        return (result, strength);
    }
    discharge_reconstructed_obligation(instance, canonical, config)
}

/// Test-only probe: does the shared memo hold a verdict for exactly this
/// (obligation content, config) key? Lets the PROOF-2 refutation tests assert
/// that same-name/different-immediate obligations occupy DISTINCT entries.
#[cfg(test)]
pub(crate) fn eval_memo_contains(
    obligation: &ProofObligation,
    config: &VerificationConfig,
) -> bool {
    let bucket = memo_bucket_hash(obligation, config.sample_count, config.exhaustive_threshold);
    let map = eval_memo_shard(bucket)
        .lock()
        .expect("shared eval memo poisoned");
    memo_find(
        &map,
        bucket,
        obligation,
        config.sample_count,
        config.exhaustive_threshold,
    )
    // An entry only counts once its verdict is COMPUTED (a claimed but
    // in-flight cell is not a memoized verdict yet).
    .is_some_and(|cell| cell.get().is_some())
}

/// Random-sampling verification for obligations with any number of inputs.
///
/// Each input gets random values masked to its own width. This handles
/// mixed-width inputs (e.g., base:BV64, value:BV32, mem_default:BV8).
fn verify_random_multi(
    obligation: &ProofObligation,
    compiled: Option<&CompiledObligation>,
    trials: u64,
) -> VerificationResult {
    let rng_state = sample_seed(&obligation.name);

    // Reuse ONE env across every sample: the keys (input names) are inserted
    // once, then only the VALUES are updated in place each iteration. This avoids
    // a fresh HashMap allocation + per-input String-key clone on every one of the
    // up-to-100k samples. Verdict-identical: the env contents at each check are
    // exactly what `build_env_edge`/`build_env_multi` produced before.
    let mut env = multi_input_sweep_env(obligation);

    // Reused FlatProg scratch tape (owned by the sample loop, like `env`), so the
    // compiled fast path allocates nothing per sample.
    let mut scratch: Vec<SVal> = Vec::new();

    // Edge cases: cycle through multiple edge-case combinations. Every point
    // at which the preconditions held is counted: sampling CANNOT distinguish
    // an unsatisfiable precondition from a merely-rare one, so a sweep in which
    // NO point satisfied them has compared nothing and ends `Unknown`, never
    // `Valid` (`sampled_sweep_verdict`).
    let edge_satisfied =
        match multi_input_edge_battery(obligation, compiled, &mut env, &mut scratch) {
            Ok(satisfied) => satisfied,
            Err(verdict) => return verdict,
        };

    // Random trials: the SAME sample sequence the sequential loop always drew,
    // split into ordered chunks across the current rayon pool (or run whole on
    // this thread when there is no pool) — see `fan_out_chunks`.
    let (chunks, per) = if compiled.is_some() {
        sample_chunking(trials)
    } else {
        (1, trials)
    };
    let random = if chunks <= 1 {
        random_chunk_multi(obligation, compiled, rng_state, 0, trials, &env)
    } else {
        let job = {
            let ob = Arc::new(obligation.clone());
            let co = compiled.map(|c| Arc::new(c.clone()));
            let env = Arc::new(env.clone());
            Arc::new(move |start, count| {
                random_chunk_multi(&ob, co.as_deref(), rng_state, start, count, &env)
            })
        };
        fan_out_chunks(trials, chunks, per, job)
    };
    let random_satisfied = match random {
        Ok(satisfied) => satisfied,
        Err(verdict) => return verdict,
    };

    // Precondition-directed trials (NEW-CG-SAMPLER): the uniform draws above
    // are consecutive outputs of one LCG, so they can never reach a
    // precondition that RELATES inputs (two aligned addresses, `x == y`) or
    // pins one to a constant. These points come from an independent stream and
    // are built from the preconditions' own constants and from earlier inputs,
    // then checked exactly like every other point: a point that misses the
    // preconditions compares nothing, one that meets them compares both sides.
    let directed = directed_trial_count(obligation, trials);
    let directed_satisfied = match directed_chunk_multi(obligation, compiled, directed, &mut env) {
        Ok(satisfied) => satisfied,
        Err(verdict) => return verdict,
    };
    sampled_sweep_verdict(
        edge_satisfied
            .saturating_add(random_satisfied)
            .saturating_add(directed_satisfied),
        MULTI_INPUT_EDGE_COMBOS
            .saturating_add(trials)
            .saturating_add(directed),
    )
}

/// Edge-case combinations the multi-input sweep evaluates before its random
/// trials (`fill_env_edge` indices `0..MULTI_INPUT_EDGE_COMBOS`).
const MULTI_INPUT_EDGE_COMBOS: u64 = 36;

/// Most precondition-directed trials one multi-input sweep adds.
const DIRECTED_TRIAL_CAP: u64 = 16_384;

/// Precondition-directed trials for `obligation`: none without preconditions
/// (every uniform draw already satisfies them), otherwise as many as the
/// uniform trials up to [`DIRECTED_TRIAL_CAP`] — so a sweep configured with no
/// random trials stays the edge battery alone.
fn directed_trial_count(obligation: &ProofObligation, trials: u64) -> u64 {
    if obligation.preconditions.is_empty() {
        0
    } else {
        trials.min(DIRECTED_TRIAL_CAP)
    }
}

/// Every bitvector constant in `obligation`'s preconditions, plus 0 and 1:
/// the values a precondition such as `is_fixed == 1`, `region_len == 4` or
/// `x < 2^24` names or bounds.
fn precondition_constants(obligation: &ProofObligation) -> Vec<u64> {
    fn walk(expr: &SmtExpr, out: &mut Vec<u64>) {
        if let SmtExpr::BvConst { value, .. } = expr {
            out.push(*value);
        }
        expr.for_each_child(&mut |child| walk(child, out));
    }
    let mut constants = vec![0, 1];
    for pre in &obligation.preconditions {
        walk(pre, &mut constants);
    }
    constants.sort_unstable();
    constants.dedup();
    constants
}

/// SplitMix64: the directed trials' generator. Its outputs are independent
/// of the sampling LCG and have no fixed relation between consecutive draws.
#[inline]
fn splitmix64(state: &mut u64) -> u64 {
    *state = state.wrapping_add(0x9e37_79b9_7f4a_7c15);
    let mut z = *state;
    z = (z ^ (z >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
    z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
    z ^ (z >> 31)
}

/// Fill `env` with one precondition-directed point. Each input independently
/// takes one of: a uniform value; a constant from the preconditions; a small
/// value; a uniform value aligned to 2..64 bytes; an EARLIER input's value
/// plus a small signed power-of-two offset (equal, adjacent or disjoint
/// addresses, `x == y`); or an edge value. Every value is masked to its
/// input's width.
fn fill_env_directed(
    env: &mut EvalEnv,
    inputs: &[(String, u32)],
    constants: &[u64],
    state: &mut u64,
    chosen: &mut Vec<u64>,
) {
    chosen.clear();
    for (index, (name, width)) in inputs.iter().enumerate() {
        let draw = splitmix64(state);
        let pick = splitmix64(state);
        let value = match draw % 8 {
            2 => constants[(pick % constants.len() as u64) as usize],
            3 => pick % 64,
            4 => pick & !((1u64 << (1 + pick % 6)) - 1),
            5 | 6 if index > 0 => {
                let base = chosen[(pick % index as u64) as usize];
                let magnitude = if pick & (1 << 16) == 0 {
                    0
                } else {
                    1u64 << ((pick >> 8) % 8)
                };
                if pick & (1 << 17) == 0 {
                    base.wrapping_add(magnitude)
                } else {
                    base.wrapping_sub(magnitude)
                }
            }
            7 => {
                let top = mask(u64::MAX, *width);
                let sign = 1u64 << width.saturating_sub(1).min(63);
                [0, 1, top, top.wrapping_sub(1), sign, sign.wrapping_sub(1)][(pick % 6) as usize]
            }
            _ => pick,
        };
        let value = mask(value, *width);
        chosen.push(value);
        if let Some(slot) = env.get_mut(name) {
            *slot = value;
        }
    }
}

/// A precondition the directed trials solve directly, after drawing a point.
enum DirectedRepair {
    /// `input == expr` (either side), `expr` not naming `input`: assign it.
    Assign {
        name: String,
        width: u32,
        expr: SmtExpr,
    },
    /// `(input & mask) == value` (either operand order), `value` within
    /// `mask`: force those bits.
    Bits {
        name: String,
        width: u32,
        mask: u64,
        value: u64,
    },
}

/// Whether `expr` reads the variable `name`.
fn mentions_var(expr: &SmtExpr, name: &str) -> bool {
    if let SmtExpr::Var { name: var, .. } = expr {
        return var == name;
    }
    let mut found = false;
    expr.for_each_child(&mut |child| found = found || mentions_var(child, name));
    found
}

/// The equality preconditions of `obligation` that pin one input: to another
/// expression (`assigned_preg == fixed_preg`, `expected == *addr_a`,
/// `region_len == 4`) or to fixed low bits (`addr & 7 == 0`). Every other
/// precondition is left to the draw.
fn directed_repairs(obligation: &ProofObligation) -> Vec<DirectedRepair> {
    let input = |expr: &SmtExpr| match expr {
        SmtExpr::Var { name, width }
            if obligation
                .inputs
                .iter()
                .any(|(input, w)| input == name && w == width) =>
        {
            Some((name.clone(), *width))
        }
        _ => None,
    };
    let mut repairs = Vec::new();
    for pre in &obligation.preconditions {
        let SmtExpr::Eq { lhs, rhs } = pre else {
            continue;
        };
        for (side, other) in [(lhs, rhs), (rhs, lhs)] {
            if let Some((name, width)) = input(side) {
                if !mentions_var(other, &name) {
                    repairs.push(DirectedRepair::Assign {
                        name,
                        width,
                        expr: (**other).clone(),
                    });
                    break;
                }
                continue;
            }
            let (SmtExpr::BvAnd { lhs: a, rhs: b, .. }, SmtExpr::BvConst { value, .. }) =
                (side.as_ref(), other.as_ref())
            else {
                continue;
            };
            let bits = match (a.as_ref(), b.as_ref()) {
                (var, SmtExpr::BvConst { value: mask, .. })
                | (SmtExpr::BvConst { value: mask, .. }, var) => input(var).map(|v| (v, *mask)),
                _ => None,
            };
            if let Some(((name, width), mask)) = bits
                && value & !mask == 0
            {
                repairs.push(DirectedRepair::Bits {
                    name,
                    width,
                    mask,
                    value: *value,
                });
                break;
            }
        }
    }
    repairs
}

/// Apply `repairs` in precondition order to the drawn point in `env`. A
/// repair whose expression does not evaluate to a bitvector leaves the drawn
/// value; the point is checked against every precondition either way.
fn apply_directed_repairs(env: &mut EvalEnv, repairs: &[DirectedRepair]) {
    for repair in repairs {
        match repair {
            DirectedRepair::Assign { name, width, expr } => {
                if let Ok(crate::smt::EvalResult::Bv(value)) = expr.try_eval(&*env)
                    && let Some(slot) = env.get_mut(name)
                {
                    *slot = mask(value, *width);
                }
            }
            DirectedRepair::Bits {
                name,
                width,
                mask: bits,
                value,
            } => {
                if let Some(slot) = env.get_mut(name) {
                    *slot = mask((*slot & !bits) | value, *width);
                }
            }
        }
    }
}

/// The multi-input sweep's `count` precondition-directed points: each is
/// drawn by [`fill_env_directed`], then the equality preconditions that pin
/// one input are solved for it ([`directed_repairs`]). Seeded from the
/// obligation name so the sweep stays reproducible. Returns as
/// [`random_chunk_multi`] does.
fn directed_chunk_multi(
    obligation: &ProofObligation,
    compiled: Option<&CompiledObligation>,
    count: u64,
    env: &mut EvalEnv,
) -> Result<u64, VerificationResult> {
    if count == 0 {
        return Ok(0);
    }
    let constants = precondition_constants(obligation);
    let repairs = directed_repairs(obligation);
    let mut state = sample_seed(&obligation.name) ^ 0x5eed_d1ec_7ed0_0001;
    let mut chosen = Vec::with_capacity(obligation.inputs.len());
    let mut scratch: Vec<SVal> = Vec::new();
    let mut satisfied = 0u64;
    for _ in 0..count {
        fill_env_directed(env, &obligation.inputs, &constants, &mut state, &mut chosen);
        apply_directed_repairs(env, &repairs);
        check_single_point(obligation, compiled, env, &mut scratch).tally(&mut satisfied)?;
    }
    Ok(satisfied)
}

/// The multi-input sweep's reusable env: one slot per input name.
fn multi_input_sweep_env(obligation: &ProofObligation) -> EvalEnv {
    let mut env = EvalEnv::default();
    for (name, _) in &obligation.inputs {
        env.insert(name.clone(), 0);
    }
    env
}

/// The multi-input sweep's edge battery: `Ok(n)` with the number of points at
/// which every precondition held (and the two sides agreed), or the first
/// terminal verdict.
fn multi_input_edge_battery(
    obligation: &ProofObligation,
    compiled: Option<&CompiledObligation>,
    env: &mut EvalEnv,
    scratch: &mut Vec<SVal>,
) -> Result<u64, VerificationResult> {
    let mut satisfied = 0u64;
    for edge_idx in 0..MULTI_INPUT_EDGE_COMBOS as usize {
        fill_env_edge(env, &obligation.inputs, edge_idx);
        check_single_point(obligation, compiled, env, scratch).tally(&mut satisfied)?;
    }
    Ok(satisfied)
}

/// Enumerate the complete Cartesian input domain: every tuple of the declared
/// inputs, once, in mixed-radix order (the last coordinate changes fastest),
/// stopping at the first tuple whose sides differ.
///
/// A compiled obligation takes [`verify_exhaustive_blocked`], which visits
/// the same tuples in the same order and decides each one the way
/// [`check_single_point`] does; an uncompiled one takes the per-tuple
/// [`verify_exhaustive_scalar`] loop.
fn verify_exhaustive(
    obligation: &ProofObligation,
    compiled: Option<&CompiledObligation>,
    input_count: u64,
) -> VerificationResult {
    match compiled {
        Some(co) => verify_exhaustive_blocked(obligation, co, input_count),
        None => verify_exhaustive_scalar(obligation, None, input_count),
    }
}

/// Tuples evaluated per tape pass by [`verify_exhaustive_blocked`].
const EXHAUSTIVE_BLOCK: usize = 256;

/// [`verify_exhaustive`] for a compiled obligation, [`EXHAUSTIVE_BLOCK`]
/// tuples per tape pass, on untagged lanes ([`FlatProg::eval_lanes`]).
///
/// What it checks is exactly what [`verify_exhaustive_scalar`] checks:
///
/// - **The tuples.** The same mixed-radix counter, started at all-zero and
///   advanced once per tuple, fills the lanes of consecutive blocks until
///   `input_count` tuples have been filled; the last block is partial when
///   `input_count` is not a multiple of the block. Lane `l` of input slot `s`
///   is `vars[s * EXHAUSTIVE_BLOCK + l]`, the value the scalar loop's
///   environment holds at slot `s` for that tuple. (Input `s` is environment
///   slot `s` because an exhaustive domain has no repeated input name:
///   [`exhaustive_input_count`] refuses one.)
/// - **The values.** [`FlatProg::eval_lanes`] computes every tape node with
///   the same `smt::eval_flat_op` that [`FlatProg::eval`] uses, and checks
///   that every computed value is stored without loss, so each lane's root,
///   decoded, is the `SVal` the scalar evaluator returns for that tuple.
/// - **The decision.** Lanes are decided in tuple order with
///   [`check_single_point`]'s compiled-path rule on the same `EvalResult`s:
///   a tuple at which any precondition is not `as_bool` is unmet, otherwise
///   the sides are compared with `semantically_equal`.
/// - **The failure.** The first lane, in tuple order, that is not equal is
///   decided by [`check_single_point`] itself at an environment built exactly
///   as the scalar loop builds it, so a counterexample is the same tuple with
///   the same text. If that scalar decision does not confirm the
///   disagreement, the two evaluators disagree, which their shared node
///   semantics rules out; the sweep then stops with `Unknown` rather than
///   choosing between them.
///
/// A tape with a value the lanes cannot hold (a `Bv128` or `Poison` at the
/// first tuple, or at any later tuple a value of another variant than its
/// node held at the first) sends the whole sweep, from its first tuple, to
/// [`verify_exhaustive_scalar`]; no decision taken before that is kept.
fn verify_exhaustive_blocked(
    obligation: &ProofObligation,
    co: &CompiledObligation,
    input_count: u64,
) -> VerificationResult {
    const B: usize = EXHAUSTIVE_BLOCK;
    let per_tuple = || {
        #[cfg(test)]
        exhaustive_visit_probe::restart();
        verify_exhaustive_scalar(obligation, Some(co), input_count)
    };
    let mut first = EvalEnv::default();
    for (name, _) in &obligation.inputs {
        first.insert(name.clone(), 0);
    }
    let Some(pre_kinds) = co
        .preconds
        .iter()
        .map(|pc| pc.lane_kinds(&first))
        .collect::<Option<Vec<_>>>()
    else {
        return per_tuple();
    };
    let (Some(src_kinds), Some(tgt_kinds)) = (
        co.trust_ir.lane_kinds(&first),
        co.aarch64.lane_kinds(&first),
    ) else {
        return per_tuple();
    };
    let src_root = src_kinds[co.trust_ir.root_index()];
    let tgt_root = tgt_kinds[co.aarch64.root_index()];
    let same_root_kind = src_root == tgt_root;

    let widths: Vec<u32> = obligation.inputs.iter().map(|(_, w)| *w).collect();
    let slots = widths.len();
    let mut counter = vec![0u64; slots];
    let mut vars = vec![0u64; slots * B];
    let mut met = [true; B];
    let mut cols_pre: Vec<u64> = Vec::new();
    let mut cols_src: Vec<u64> = Vec::new();
    let mut cols_tgt: Vec<u64> = Vec::new();
    let mut saw_satisfying = false;
    let mut filled = 0u64;
    while filled < input_count {
        let lanes = (input_count - filled).min(B as u64) as usize;
        for lane in 0..lanes {
            for (slot, value) in counter.iter().enumerate() {
                vars[slot * B + lane] = *value;
            }
            for (slot, width) in widths.iter().enumerate().rev() {
                counter[slot] += 1;
                if counter[slot] < (1u64 << *width) {
                    break;
                }
                counter[slot] = 0;
            }
        }
        filled += lanes as u64;

        met[..lanes].fill(true);
        for (pc, kinds) in co.preconds.iter().zip(&pre_kinds) {
            let Some(root) = pc.eval_lanes(kinds, &vars, B, lanes, &mut cols_pre) else {
                return per_tuple();
            };
            let root_kind = kinds[pc.root_index()];
            for (lane, payload) in root.iter().enumerate() {
                if !root_kind.decode(*payload).to_eval().as_bool() {
                    met[lane] = false;
                }
            }
        }
        let Some(source) = co
            .trust_ir
            .eval_lanes(&src_kinds, &vars, B, lanes, &mut cols_src)
        else {
            return per_tuple();
        };
        let Some(target) = co
            .aarch64
            .eval_lanes(&tgt_kinds, &vars, B, lanes, &mut cols_tgt)
        else {
            return per_tuple();
        };
        for lane in 0..lanes {
            #[cfg(test)]
            exhaustive_visit_probe::record(&vars, B, lane, slots);
            let lane_met = met[lane];
            let target_lane = target[lane];
            // Test-only fault injection: makes this sweep disagree with the
            // per-tuple decision at one tuple, so the disagreement arm below
            // is exercised. Compiled out of every non-test build.
            #[cfg(test)]
            let (lane_met, target_lane) = exhaustive_visit_probe::fault(
                filled - lanes as u64 + lane as u64,
                lane_met,
                target_lane,
            );
            if !lane_met {
                continue;
            }
            // Same kind and same payload decode to the same `Bv` or `Bool`,
            // which `semantically_equal` holds equal; any other lane is
            // decided by `semantically_equal` itself.
            if (same_root_kind && source[lane] == target_lane)
                || src_root
                    .decode(source[lane])
                    .to_eval()
                    .semantically_equal(&tgt_root.decode(target_lane).to_eval())
            {
                saw_satisfying = true;
                continue;
            }
            let mut env = EvalEnv::default();
            for (slot, (name, _)) in obligation.inputs.iter().enumerate() {
                env.insert(name.clone(), vars[slot * B + lane]);
            }
            let mut scratch: Vec<SVal> = Vec::new();
            return match check_single_point(obligation, Some(co), &env, &mut scratch) {
                PointCheck::Counterexample(result) => result,
                PointCheck::Inconclusive(reason) => VerificationResult::Unknown { reason },
                PointCheck::Equal | PointCheck::PreconditionUnmet => VerificationResult::Unknown {
                    reason: format!(
                        "the blocked and per-tuple evaluators disagree at inputs {env:?}; \
                         no verdict"
                    ),
                },
            };
        }
    }
    sweep_verdict(obligation, saw_satisfying)
}

/// Test-only record of the tuples an exhaustive sweep decides, in decision
/// order, as the input values its tapes read: the blocked sweep's lanes, or
/// the per-tuple loop's environment. Off unless a test
/// turns it on for its own thread.
#[cfg(test)]
pub(crate) mod exhaustive_visit_probe {
    use std::cell::RefCell;

    thread_local! {
        static VISITS: RefCell<Option<Vec<Vec<u64>>>> = const { RefCell::new(None) };
        static FAULT: std::cell::Cell<Option<(Fault, u64)>> = const { std::cell::Cell::new(None) };
    }

    /// A deliberate disagreement the blocked sweep takes at one tuple index.
    #[derive(Clone, Copy, Debug)]
    pub(crate) enum Fault {
        /// Flip bit 0 of the expansion side's stored root payload.
        FlipTarget,
        /// Treat the tuple's preconditions as met.
        ForceMet,
    }

    /// Inject `fault` at tuple index `tuple` (mixed-radix order, from 0) on
    /// this thread until [`clear_fault`].
    pub(crate) fn inject_fault(fault: Fault, tuple: u64) {
        FAULT.with(|f| f.set(Some((fault, tuple))));
    }

    pub(crate) fn clear_fault() {
        FAULT.with(|f| f.set(None));
    }

    pub(super) fn fault(tuple: u64, met: bool, target: u64) -> (bool, u64) {
        match FAULT.with(|f| f.get()) {
            Some((Fault::FlipTarget, at)) if at == tuple => (met, target ^ 1),
            Some((Fault::ForceMet, at)) if at == tuple => (true, target),
            _ => (met, target),
        }
    }

    /// Start recording on this thread, discarding any earlier record.
    pub(crate) fn start() {
        VISITS.with(|v| *v.borrow_mut() = Some(Vec::new()));
    }

    /// Forget what was recorded so far (the sweep starts again from its
    /// first tuple), keeping the recorder on.
    pub(super) fn restart() {
        VISITS.with(|v| {
            if let Some(visits) = v.borrow_mut().as_mut() {
                visits.clear();
            }
        });
    }

    /// Record one tuple given as its values.
    pub(super) fn record_values(values: Vec<u64>) {
        VISITS.with(|v| {
            if let Some(visits) = v.borrow_mut().as_mut() {
                visits.push(values);
            }
        });
    }

    /// Stop recording and return what was recorded since [`start`].
    pub(crate) fn take() -> Vec<Vec<u64>> {
        VISITS.with(|v| v.borrow_mut().take().unwrap_or_default())
    }

    pub(super) fn record(vars: &[u64], stride: usize, lane: usize, slots: usize) {
        VISITS.with(|v| {
            if let Some(visits) = v.borrow_mut().as_mut() {
                visits.push((0..slots).map(|slot| vars[slot * stride + lane]).collect());
            }
        });
    }
}

/// The per-tuple exhaustive loop: one environment, updated in place, and one
/// [`check_single_point`] per tuple. Scratch and the environment are
/// allocated once, not per tuple.
fn verify_exhaustive_scalar(
    obligation: &ProofObligation,
    compiled: Option<&CompiledObligation>,
    input_count: u64,
) -> VerificationResult {
    let mut scratch: Vec<SVal> = Vec::new();
    let mut env = EvalEnv::default();
    for (name, _) in &obligation.inputs {
        env.insert(name.clone(), 0);
    }
    let mut saw_satisfying = false;
    for _ in 0..input_count {
        #[cfg(test)]
        exhaustive_visit_probe::record_values(
            obligation
                .inputs
                .iter()
                .map(|(name, _)| *env.get(name).expect("exhaustive input must be bound"))
                .collect(),
        );
        match check_single_point(obligation, compiled, &env, &mut scratch) {
            PointCheck::Counterexample(result) => return result,
            PointCheck::Inconclusive(reason) => return VerificationResult::Unknown { reason },
            PointCheck::Equal => saw_satisfying = true,
            PointCheck::PreconditionUnmet => {}
        }
        for (name, width) in obligation.inputs.iter().rev() {
            let value = env.get_mut(name).expect("exhaustive input must be bound");
            *value += 1;
            if *value < (1u64 << *width) {
                break;
            }
            *value = 0;
        }
    }
    sweep_verdict(obligation, saw_satisfying)
}

/// Random-sampling verification for larger bit-widths.
fn verify_random(
    obligation: &ProofObligation,
    compiled: Option<&CompiledObligation>,
    width: u32,
    trials: u64,
) -> VerificationResult {
    // Simple pseudo-random: use a deterministic but well-distributed sequence.
    // We use a linear congruential generator seeded from the rule name hash.
    let rng_state = sample_seed(&obligation.name);

    // Reuse ONE env across all samples: insert the (≤2) input keys once, then
    // update their values in place each iteration — avoids a per-sample HashMap
    // alloc + String-key clone. Verdict-identical to the old per-sample
    // `build_env`.
    let mut env = two_input_sweep_env(obligation);

    // Reused FlatProg scratch tape across all samples.
    let mut scratch: Vec<SVal> = Vec::new();

    // Sampling path: it cannot prove a precondition unsatisfiable (only the
    // exhaustive path can), but it does not need to. Every point at which the
    // preconditions held is counted, and a sweep in which NO point satisfied
    // them compared nothing, so it ends `Unknown` rather than `Valid`
    // (`sampled_sweep_verdict`) — whether the precondition is unsatisfiable or
    // merely never sampled. The solver path's satisfiability gate remains the
    // protection for a precondition that sampling does satisfy.
    let edge_satisfied =
        match two_input_edge_battery(obligation, compiled, width, &mut env, &mut scratch) {
            Ok(satisfied) => satisfied,
            Err(verdict) => return verdict,
        };

    // Same sample sequence as ever, in ordered chunks across the current pool
    // (see `fan_out_chunks`); each sample draws twice from the LCG.
    let (chunks, per) = if compiled.is_some() {
        sample_chunking(trials)
    } else {
        (1, trials)
    };
    let random = if chunks <= 1 {
        random_chunk_2(obligation, compiled, width, rng_state, 0, trials, &env)
    } else {
        let job = {
            let ob = Arc::new(obligation.clone());
            let co = compiled.map(|c| Arc::new(c.clone()));
            let env = Arc::new(env);
            Arc::new(move |start, count| {
                random_chunk_2(&ob, co.as_deref(), width, rng_state, start, count, &env)
            })
        };
        fan_out_chunks(trials, chunks, per, job)
    };
    match random {
        Ok(random_satisfied) => sampled_sweep_verdict(
            edge_satisfied.saturating_add(random_satisfied),
            TWO_INPUT_EDGE_POINTS.saturating_add(trials),
        ),
        Err(verdict) => verdict,
    }
}

/// Points in the shared-width sweep's edge battery: every ordered pair of the
/// six [`two_input_edge_cases`] values.
const TWO_INPUT_EDGE_POINTS: u64 = 36;

/// The six edge values of the shared-width (≤ 2 input) sweep: 0, 1, max,
/// max - 1 and the sign-bit midpoints. EvalEnv stores concrete samples as u64,
/// so widths above 64 use the representable carrier's high bit; shifting a u64
/// by an i128-width count would panic in debug builds and provides no
/// additional sample information.
fn two_input_edge_cases(width: u32) -> [u64; 6] {
    let mask_val = mask(u64::MAX, width);
    let sampled_sign_bit = 1u64 << width.saturating_sub(1).min(63);
    [
        0,
        1,
        mask_val,
        mask_val.wrapping_sub(1),
        sampled_sign_bit,
        sampled_sign_bit.wrapping_sub(1),
    ]
}

/// The shared-width sweep's reusable env: slots for the (≤ 2) inputs it fills.
fn two_input_sweep_env(obligation: &ProofObligation) -> EvalEnv {
    let mut env = EvalEnv::default();
    for (name, _) in obligation.inputs.iter().take(2) {
        env.insert(name.clone(), 0);
    }
    env
}

/// The shared-width sweep's edge battery: `Ok(n)` with the number of points
/// at which every precondition held (and the two sides agreed), or the first
/// terminal verdict.
fn two_input_edge_battery(
    obligation: &ProofObligation,
    compiled: Option<&CompiledObligation>,
    width: u32,
    env: &mut EvalEnv,
    scratch: &mut Vec<SVal>,
) -> Result<u64, VerificationResult> {
    let edge_cases = two_input_edge_cases(width);
    let mut satisfied = 0u64;
    for a_val in edge_cases {
        for b_val in edge_cases {
            fill_env_2(env, &obligation.inputs, a_val, Some(b_val), width);
            check_single_point(obligation, compiled, env, scratch).tally(&mut satisfied)?;
        }
    }
    Ok(satisfied)
}

/// Fold a SAMPLING sweep (no counterexample, no inconclusive point) into its
/// verdict. `satisfied` counts the sampled points at which every precondition
/// held and the two sides were compared (and agreed); `attempted` counts every
/// sampled point, edge battery included.
///
/// A sweep with `satisfied == 0` compared NOTHING: every point was excluded by
/// the preconditions, so its lack of a counterexample is no evidence at all.
/// Sampling cannot tell an unsatisfiable precondition from one it merely never
/// hit, so it claims neither — the verdict is an explicit `Unknown`, never
/// `Valid`. This is the sampling twin of the exhaustive path's
/// [`sweep_verdict`], and the same rule the checked scalar FP lanes apply.
fn sampled_sweep_verdict(satisfied: u64, attempted: u64) -> VerificationResult {
    if satisfied == 0 {
        return VerificationResult::Unknown {
            reason: format!(
                "vacuous sample: none of the {attempted} sampled inputs satisfied the \
                 preconditions, so the sweep compared nothing; sampling cannot tell an \
                 unsatisfiable precondition from one it never hit"
            ),
        };
    }
    VerificationResult::Valid
}

/// Whether an identical-sided, trap-free compiled obligation's full sweep is
/// already known to return `Valid`: the sides cannot disagree at any point (see
/// the short-circuit in [`verify_by_evaluation_with_config`]), so the sweep's
/// verdict is `Valid` exactly when some sampled point satisfies every
/// precondition. With no preconditions every point does. Otherwise look for a
/// satisfying point in the sweep's OWN edge battery (the same points, in the
/// same env, that the dispatching sweep evaluates first); `false` means "not
/// known yet", and the caller runs the full sweep, which then decides between
/// `Valid` and the vacuous-sample `Unknown` on all of its points.
fn identical_sides_edge_witness(obligation: &ProofObligation, co: &CompiledObligation) -> bool {
    if obligation.preconditions.is_empty() {
        return true;
    }
    let mut scratch: Vec<SVal> = Vec::new();
    let edges = if needs_multi_input_sampling(obligation) {
        let mut env = multi_input_sweep_env(obligation);
        multi_input_edge_battery(obligation, Some(co), &mut env, &mut scratch)
    } else {
        let width = obligation.inputs.first().map(|(_, w)| *w).unwrap_or(32);
        let mut env = two_input_sweep_env(obligation);
        two_input_edge_battery(obligation, Some(co), width, &mut env, &mut scratch)
    };
    matches!(edges, Ok(satisfied) if satisfied > 0)
}

// ---------------------------------------------------------------------------
// Chunked random sampling
// ---------------------------------------------------------------------------
//
// A 100k-sample sweep is one obligation KIND's whole cost, and the sweep
// pre-warm (trust-cg-codegen `compile_module`) hands each kind to one worker of
// a wide pool. That made the pool's critical path the slowest single kind —
// measured at 9-13ms per compile round on the beat-llvm corpus, with 17-19
// workers idle behind it once their smaller kinds finished. The samples of one
// kind are independent, so the sequence is split into contiguous chunks that
// the SAME pool runs concurrently. What must not change, and does not:
//
// * The samples. The sampling RNG is an LCG, i.e. an affine map, so
//   `sample_lcg_jump` puts a chunk at exactly the state the sequential loop
//   would have reached (O(log n), no iteration). Chunk `i` therefore draws
//   precisely samples `[i·per, (i+1)·per)` of the original sequence.
// * The verdict AND the reported counterexample. Chunks are ordered; the first
//   `Err` in chunk order is the globally-first counterexample (or
//   inconclusive point), exactly what the sequential loop's early return
//   produced.
// * The evidence count. Every chunk returns how many of its samples satisfied
//   the preconditions, and the counts of ALL chunks are summed, so the
//   vacuous-sample decision (`sampled_sweep_verdict`) sees the same number
//   the sequential loop counts.
// * `DEFAULT_SAMPLE_COUNT` and the certificate it is stamped into. The count
//   of samples drawn is unchanged; only which thread draws them differs.
// * The recursive evaluator's stack. Only compiled (flat-tape) obligations are
//   spread; an uncompiled obligation keeps the caller's thread and stack.
// * The global rayon pool, which is NEVER used: with no enclosing pool the
//   caller's thread runs the whole sequence (an unbounded global pool was the
//   sched_yield regression of 2026-08).

/// The sampling LCG's seed for an obligation: a hash of its NAME, so a sweep
/// is reproducible from the certificate alone. Shared by both sample loops.
fn sample_seed(name: &str) -> u64 {
    let mut h: u64 = 0xcafe_babe_dead_beef;
    for byte in name.bytes() {
        h = h.wrapping_mul(SAMPLE_LCG_MUL).wrapping_add(byte as u64);
    }
    h
}

/// Multiplier of the sampling LCG — the constant `fill_env_multi` and the
/// 2-input loop have always used.
const SAMPLE_LCG_MUL: u64 = 6364136223846793005;
/// Increment of the sampling LCG.
const SAMPLE_LCG_INC: u64 = 1442695040888963407;

/// One step of the sampling LCG.
#[inline]
fn sample_lcg_step(state: u64) -> u64 {
    state
        .wrapping_mul(SAMPLE_LCG_MUL)
        .wrapping_add(SAMPLE_LCG_INC)
}

/// The LCG state after `n` steps from `state`, in O(log n).
///
/// The step is the affine map `f(x) = a·x + c (mod 2^64)`, so `f^n` is itself
/// affine, `A·x + C`, with `(A, C)` from binary exponentiation of affine maps:
/// `(a, c)² = (a², a·c + c)`, and `(a, c)∘(A, C) = (a·A, a·C + c)`. Every
/// power of `f` commutes with every other, so composition order is free.
fn sample_lcg_jump(state: u64, n: u64) -> u64 {
    let (mut acc_a, mut acc_c) = (1u64, 0u64);
    let (mut a, mut c) = (SAMPLE_LCG_MUL, SAMPLE_LCG_INC);
    let mut n = n;
    while n > 0 {
        if n & 1 == 1 {
            acc_c = a.wrapping_mul(acc_c).wrapping_add(c);
            acc_a = a.wrapping_mul(acc_a);
        }
        c = a.wrapping_mul(c).wrapping_add(c);
        a = a.wrapping_mul(a);
        n >>= 1;
    }
    acc_a.wrapping_mul(state).wrapping_add(acc_c)
}

/// Smallest chunk worth handing to another worker: below this the per-chunk
/// setup (an env clone, a scratch tape, a rayon task) is not paid back.
const MIN_SAMPLE_CHUNK: u64 = 4096;

/// How `trials` random samples are split: `(chunks, per_chunk)`.
///
/// `chunks == 1` means the caller's thread runs the whole sequence. That is the
/// case whenever this is NOT running on a rayon pool worker
/// (`current_thread_index() == None` — the global pool is never used), the
/// pool has a single worker (the bridge's certificate-walk pool), or there is
/// too little work to split. On the sweep pre-warm's wide pool each obligation
/// becomes up to `2 × threads` chunks, so the pool's critical path stops being
/// one obligation's whole loop on one thread.
/// The process-wide pool that runs sample-chunk helpers for EVERY sweep,
/// whichever thread owns the sweep — the certificate walk's single verifier
/// worker included. Registered by the compiler when it builds its sweep pool
/// and cleared when it releases it; with none registered, a sweep fans out
/// on the caller's own pool (if it is on one with ≥ 2 workers) or runs whole.
static SWEEP_HELPER_POOL: std::sync::OnceLock<
    std::sync::Mutex<Option<std::sync::Arc<rayon::ThreadPool>>>,
> = std::sync::OnceLock::new();

pub fn set_sweep_helper_pool(pool: Option<std::sync::Arc<rayon::ThreadPool>>) {
    *SWEEP_HELPER_POOL
        .get_or_init(|| std::sync::Mutex::new(None))
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner) = pool;
}

fn sweep_helper_pool() -> Option<std::sync::Arc<rayon::ThreadPool>> {
    SWEEP_HELPER_POOL
        .get()?
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner)
        .clone()
}

/// Where a sweep's chunk helpers would run and how wide that is: the
/// registered helper pool, else the caller's own pool. `None` = run whole.
fn sweep_helper_width() -> Option<(Option<std::sync::Arc<rayon::ThreadPool>>, u64)> {
    if let Some(pool) = sweep_helper_pool() {
        let threads = pool.current_num_threads() as u64;
        return (threads >= 2).then_some((Some(pool), threads));
    }
    rayon::current_thread_index()?;
    let threads = rayon::current_num_threads() as u64;
    (threads >= 2).then_some((None, threads))
}

fn sample_chunking(trials: u64) -> (u64, u64) {
    if trials < 2 * MIN_SAMPLE_CHUNK {
        return (1, trials);
    }
    let Some((_, threads)) = sweep_helper_width() else {
        return (1, trials);
    };
    let chunks = (trials / MIN_SAMPLE_CHUNK).min(threads * 2).max(1);
    (chunks, trials.div_ceil(chunks))
}

/// Fan `chunks` chunks of the sample sequence out across the CURRENT rayon
/// pool and return the FIRST terminal verdict (counterexample or inconclusive
/// point) in sequence order (chunks are ordered; a counterexample in chunk `i`
/// precedes every sample of `i+1`), else `Ok` with the total number of points
/// at which every precondition held, summed over ALL chunks — the evidence
/// count [`sampled_sweep_verdict`] needs. Every chunk runs to completion before
/// this returns, so the sum covers the whole sequence; a chunk with no
/// recorded result (which the protocol below rules out) fails closed as
/// `Unknown` rather than contributing zero.
///
/// The calling worker is inside a memo cell's compute-once closure
/// (`memoized_verify_by_evaluation`), and other workers that reach that cell
/// BLOCK on it. So the caller must never enter a rayon wait here: rayon's
/// `join`/`collect`/`scope` make a waiting worker execute OTHER queued jobs,
/// and a job that blocks on this very cell — or on a peer's cell whose owner
/// stole a job blocking on ours — hangs the compile (reproduced with gdb, two
/// callers of one uncached kind on a 2-worker pool). Instead:
///
/// * helpers are fire-and-forget `rayon::spawn`s (onto the current worker's
///   pool) that pull chunk indices from a shared counter until it is
///   exhausted;
/// * the caller pulls from the SAME counter, so it is never idle while chunks
///   remain and needs no helper to make progress;
/// * when the counter is exhausted it waits — on a plain condvar, not a rayon
///   latch — only for helpers that have already STARTED (a helper counts
///   itself in on entry), each of which is pure computation and finishes. A
///   helper that starts later finds the counter exhausted and exits. So the
///   caller never runs anyone else's job while holding a cell, and its wait
///   is bounded by one chunk per running helper.
fn fan_out_chunks(
    trials: u64,
    chunks: u64,
    per: u64,
    job: Arc<dyn Fn(u64, u64) -> Result<u64, VerificationResult> + Send + Sync>,
) -> Result<u64, VerificationResult> {
    use std::sync::atomic::{AtomicU64, Ordering};
    type Job = dyn Fn(u64, u64) -> Result<u64, VerificationResult> + Send + Sync;
    struct Shared {
        next: AtomicU64,
        results: std::sync::Mutex<Vec<Option<Result<u64, VerificationResult>>>>,
        in_flight: std::sync::Mutex<usize>,
        drained: std::sync::Condvar,
    }
    /// Pull and run chunks until the counter is exhausted; returns how many
    /// this caller ran.
    fn pull(shared: &Shared, job: &Job, trials: u64, chunks: u64, per: u64) -> u64 {
        let mut ran = 0;
        loop {
            let i = shared.next.fetch_add(1, Ordering::Relaxed);
            if i >= chunks {
                return ran;
            }
            let start = i * per;
            let count = trials.saturating_sub(start).min(per);
            let result = job(start, count);
            shared
                .results
                .lock()
                .unwrap_or_else(std::sync::PoisonError::into_inner)[i as usize] = Some(result);
            ran += 1;
        }
    }
    let shared = Arc::new(Shared {
        next: AtomicU64::new(0),
        results: std::sync::Mutex::new(vec![None; chunks as usize]),
        in_flight: std::sync::Mutex::new(0),
        drained: std::sync::Condvar::new(),
    });
    let (helper_pool, threads) = sweep_helper_width().unwrap_or((None, 1));
    let helpers = (threads as usize).saturating_sub(1).min(chunks as usize);
    for _ in 0..helpers {
        let shared = Arc::clone(&shared);
        let job = Arc::clone(&job);
        let task = move || {
            *shared
                .in_flight
                .lock()
                .unwrap_or_else(std::sync::PoisonError::into_inner) += 1;
            let _ = pull(&shared, &*job, trials, chunks, per);
            let mut n = shared
                .in_flight
                .lock()
                .unwrap_or_else(std::sync::PoisonError::into_inner);
            *n -= 1;
            if *n == 0 {
                shared.drained.notify_all();
            }
        };
        match &helper_pool {
            Some(pool) => pool.spawn(task),
            None => rayon::spawn(task),
        }
    }
    let owner_ran = pull(&shared, &*job, trials, chunks, per);
    {
        let mut n = shared
            .in_flight
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        while *n > 0 {
            n = shared
                .drained
                .wait(n)
                .unwrap_or_else(std::sync::PoisonError::into_inner);
        }
    }
    if sweep_trace_enabled() {
        // How much of this sweep the pool actually shared: chunks claimed
        // before the owner started pulling went to helpers that had already
        // started; the owner then raced the rest.
        eprintln!("TCG_FANOUT chunks={chunks} helpers_spawned={helpers} owner_ran={owner_ran}");
    }
    let results = std::mem::take(
        &mut *shared
            .results
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner),
    );
    let mut satisfied = 0u64;
    for (i, result) in results.into_iter().enumerate() {
        match result {
            Some(Ok(count)) => satisfied = satisfied.saturating_add(count),
            Some(Err(verdict)) => return Err(verdict),
            None => {
                return Err(VerificationResult::Unknown {
                    reason: format!("sample chunk {i} of {chunks} recorded no result"),
                });
            }
        }
    }
    Ok(satisfied)
}

/// One batch's per-lane decision (bit `l` = lane `l`): `met` = every
/// precondition held (`EvalResult::as_bool` of each), `fail` = met AND the
/// sides are not `semantically_equal` (so `fail` ⊆ `met`). Exactly
/// `check_single_point`'s decision per lane, on the batched tapes: equal iff
/// neither side is Poison, both roots have the same sort, and the values
/// agree. A failing lane is always re-checked by the scalar
/// `check_single_point` (which also renders the counterexample text), so a
/// spurious failure here costs one scalar evaluation and changes nothing.
struct BatchCheck {
    met: u8,
    fail: u8,
}

fn check_batch(
    cb: &CompiledBatch,
    inputs: &[[u64; BATCH_LANES]],
    scratch: &mut BatchScratch,
) -> BatchCheck {
    let mut met: u8 = u8::MAX;
    for pc in &cb.preconds {
        let root = pc.eval_batch(inputs, scratch);
        for l in 0..BATCH_LANES {
            if !root.lane_bool(l) {
                met &= !(1u8 << l);
            }
        }
        if met == 0 {
            return BatchCheck { met: 0, fail: 0 };
        }
    }
    let t = cb.trust_ir.eval_batch(inputs, scratch);
    let a = cb.aarch64.eval_batch(inputs, scratch);
    // `EvalResult == EvalResult`: `Bv` and `Bv128` are different variants and
    // never equal, so the sorts must match too.
    let same_sort = t.sort == a.sort;
    let mut fail: u8 = 0;
    for l in 0..BATCH_LANES {
        let bit = 1u8 << l;
        if met & bit == 0 {
            continue;
        }
        let equal =
            t.poison & bit == 0 && a.poison & bit == 0 && same_sort && t.lanes[l] == a.lanes[l];
        if !equal {
            fail |= bit;
        }
    }
    BatchCheck { met, fail }
}

/// Tally one batch into a chunk's running count of compared points: lanes the
/// batch found met and equal count directly; each failing lane is re-checked
/// by the scalar [`check_single_point`] at the identical env (`recheck_lane(l)`
/// fills lane `l` into the env and runs it), whose decision is authoritative —
/// `Equal` counts, `PreconditionUnmet` does not, and a counterexample or
/// inconclusive point is the chunk's terminal verdict.
fn tally_batch(
    check: BatchCheck,
    live: u8,
    satisfied: &mut u64,
    mut recheck_lane: impl FnMut(usize) -> PointCheck,
) -> Result<(), VerificationResult> {
    let met = check.met & live;
    let mut fail = check.fail & met;
    *satisfied = satisfied.saturating_add(u64::from((met & !fail).count_ones()));
    while fail != 0 {
        let l = fail.trailing_zeros() as usize;
        fail &= fail - 1;
        recheck_lane(l).tally(satisfied)?;
    }
    Ok(())
}

/// Lane buffers for a batch, one per `EvalEnv` SLOT — a slot per DISTINCT
/// input name in first-occurrence order, which is the env the scalar loop
/// fills (`EvalEnv::insert` dedups by name, so a repeated name overwrites its
/// slot and the LAST draw wins) and what `FlatOp::Var` indexes. Returns the
/// buffers and `slot_of[k]`, the slot input `k` writes. Buffers per input
/// INDEX would sweep a different sample whenever a name repeats. (A repeat
/// followed by a NEW name, `[a, a, b]`, is a latent panic in the compiled
/// scalar sweep itself — `FlatOp::Var` numbers by first position in `inputs`,
/// the env by distinct name — and no registry obligation has that shape.)
fn batch_lanes(inputs: &[(String, u32)]) -> (Vec<[u64; BATCH_LANES]>, Vec<usize>) {
    let mut names: Vec<&str> = Vec::with_capacity(inputs.len());
    let mut slot_of = Vec::with_capacity(inputs.len());
    for (name, _) in inputs {
        let slot = match names.iter().position(|n| n == name) {
            Some(slot) => slot,
            None => {
                names.push(name);
                names.len() - 1
            }
        };
        slot_of.push(slot);
    }
    (vec![[0u64; BATCH_LANES]; names.len()], slot_of)
}

/// Set a reused env's values to lane `l` of `lanes` (the values the scalar
/// fill functions would have written, so the counterexample text is the same).
fn fill_env_from_lanes(
    env: &mut EvalEnv,
    inputs: &[(String, u32)],
    lanes: &[[u64; BATCH_LANES]],
    slot_of: &[usize],
    l: usize,
) {
    for (k, (name, _)) in inputs.iter().enumerate() {
        if let Some(slot) = env.get_mut(name) {
            *slot = lanes[slot_of[k]][l];
        }
    }
}

/// Chunk `[start, start + count)` of the 2-input shared-width sample sequence.
/// `seed` is the LCG state before sample 0; every sample draws twice. `Ok(n)`:
/// no terminal point, and `n` of the chunk's points satisfied every
/// precondition (and agreed); `Err`: the chunk's first counterexample or
/// inconclusive point.
fn random_chunk_2(
    obligation: &ProofObligation,
    compiled: Option<&CompiledObligation>,
    width: u32,
    seed: u64,
    start: u64,
    count: u64,
    env_template: &EvalEnv,
) -> Result<u64, VerificationResult> {
    let mut rng_state = sample_lcg_jump(seed, start.wrapping_mul(2));
    let mut env = env_template.clone();
    let mut scratch: Vec<SVal> = Vec::new();
    let mut satisfied = 0u64;
    if let Some(cb) = compiled.and_then(|c| c.batch.as_ref()) {
        // Batched: the same draws in the same order, `BATCH_LANES` samples per
        // evaluation; a failing lane is confirmed (and rendered) by the scalar
        // check on the identical env. `fill_env_2` masks both values with the
        // shared width — as does `mask(rng, width)` — so lane == env value.
        let (mut lanes, slot_of) = batch_lanes(&obligation.inputs);
        let mut bscratch = BatchScratch::default();
        let mut done = 0u64;
        while done < count {
            let n = (count - done).min(BATCH_LANES as u64) as usize;
            // `l` is the LANE column; it indexes several `lanes` rows chosen by
            // `slot_of`, so no single-slice iterator expresses this loop.
            #[allow(clippy::needless_range_loop)]
            for l in 0..n {
                rng_state = sample_lcg_step(rng_state);
                let a_val = mask(rng_state, width);
                rng_state = sample_lcg_step(rng_state);
                let b_val = mask(rng_state, width);
                // In `fill_env_2` order: input 0 then input 1 (last write wins).
                if let Some(&slot) = slot_of.first() {
                    lanes[slot][l] = a_val;
                }
                if let Some(&slot) = slot_of.get(1) {
                    lanes[slot][l] = b_val;
                }
            }
            let live: u8 = if n == BATCH_LANES {
                u8::MAX
            } else {
                (1u8 << n) - 1
            };
            let check = check_batch(cb, &lanes, &mut bscratch);
            tally_batch(check, live, &mut satisfied, |l| {
                fill_env_from_lanes(&mut env, &obligation.inputs, &lanes, &slot_of, l);
                check_single_point(obligation, compiled, &env, &mut scratch)
            })?;
            done += n as u64;
        }
        return Ok(satisfied);
    }
    for _ in 0..count {
        rng_state = sample_lcg_step(rng_state);
        let a_val = mask(rng_state, width);
        rng_state = sample_lcg_step(rng_state);
        let b_val = mask(rng_state, width);
        fill_env_2(&mut env, &obligation.inputs, a_val, Some(b_val), width);
        check_single_point(obligation, compiled, &env, &mut scratch).tally(&mut satisfied)?;
    }
    Ok(satisfied)
}

/// Chunk `[start, start + count)` of the multi-input sample sequence; every
/// sample draws once per input (`fill_env_multi`). Returns as
/// [`random_chunk_2`] does.
fn random_chunk_multi(
    obligation: &ProofObligation,
    compiled: Option<&CompiledObligation>,
    seed: u64,
    start: u64,
    count: u64,
    env_template: &EvalEnv,
) -> Result<u64, VerificationResult> {
    let draws = obligation.inputs.len() as u64;
    let mut rng_state = sample_lcg_jump(seed, start.wrapping_mul(draws));
    let mut env = env_template.clone();
    let mut scratch: Vec<SVal> = Vec::new();
    let mut satisfied = 0u64;
    if let Some(cb) = compiled.and_then(|c| c.batch.as_ref()) {
        // Batched twin of the loop below: one draw per input per sample, masked
        // to that input's width exactly as `fill_env_multi` does.
        let (mut lanes, slot_of) = batch_lanes(&obligation.inputs);
        let mut bscratch = BatchScratch::default();
        let mut done = 0u64;
        while done < count {
            let n = (count - done).min(BATCH_LANES as u64) as usize;
            // `l` is the LANE column; it indexes several `lanes` rows chosen by
            // `slot_of`, so no single-slice iterator expresses this loop.
            #[allow(clippy::needless_range_loop)]
            for l in 0..n {
                // In `fill_env_multi` order: one draw per input; a repeated
                // name's slot keeps the last write.
                for (k, (_, w)) in obligation.inputs.iter().enumerate() {
                    rng_state = sample_lcg_step(rng_state);
                    lanes[slot_of[k]][l] = mask(rng_state, *w);
                }
            }
            let live: u8 = if n == BATCH_LANES {
                u8::MAX
            } else {
                (1u8 << n) - 1
            };
            let check = check_batch(cb, &lanes, &mut bscratch);
            tally_batch(check, live, &mut satisfied, |l| {
                fill_env_from_lanes(&mut env, &obligation.inputs, &lanes, &slot_of, l);
                check_single_point(obligation, compiled, &env, &mut scratch)
            })?;
            done += n as u64;
        }
        return Ok(satisfied);
    }
    for _ in 0..count {
        fill_env_multi(&mut env, &obligation.inputs, &mut rng_state);
        check_single_point(obligation, compiled, &env, &mut scratch).tally(&mut satisfied)?;
    }
    Ok(satisfied)
}

/// Update a REUSED env's values for the (≤2)-input shared-width sampling path
/// (keys already present). Same values as the old `build_env`, no realloc/clone.
fn fill_env_2(
    env: &mut EvalEnv,
    inputs: &[(String, u32)],
    a_val: u64,
    b_val: Option<u64>,
    width: u32,
) {
    if let Some((name, _)) = inputs.first()
        && let Some(slot) = env.get_mut(name)
    {
        *slot = mask(a_val, width);
    }
    if let Some((name, _)) = inputs.get(1)
        && let Some(bv) = b_val
        && let Some(slot) = env.get_mut(name)
    {
        *slot = mask(bv, width);
    }
}

/// Build an environment from input descriptors and per-input random values.
///
/// Unlike `build_env` which only handles 2 inputs with a shared width,
/// this function populates all inputs with values masked to their individual widths.
/// Update a REUSED env's values for the next random multi-input sample (keys are
/// already present). Same values as the old `build_env_multi`, no realloc/clone.
fn fill_env_multi(env: &mut EvalEnv, inputs: &[(String, u32)], rng_state: &mut u64) {
    for (name, width) in inputs {
        *rng_state = rng_state
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        if let Some(slot) = env.get_mut(name) {
            *slot = mask(*rng_state, *width);
        }
    }
}

/// Update a REUSED env's values with the edge-case combination `edge_idx` (keys
/// already present). Same values as the old `build_env_edge`, no realloc/clone.
fn fill_env_edge(env: &mut EvalEnv, inputs: &[(String, u32)], edge_idx: usize) {
    for (i, (name, width)) in inputs.iter().enumerate() {
        let edges = two_input_edge_cases(*width);
        let idx = (edge_idx.wrapping_add(i * 3)) % edges.len();
        if let Some(slot) = env.get_mut(name) {
            *slot = edges[idx];
        }
    }
}

/// Outcome of evaluating one concrete test point.
enum PointCheck {
    /// The point does not satisfy the obligation's preconditions.
    PreconditionUnmet,
    /// Preconditions hold and `trust_ir == aarch64` at this point.
    Equal,
    /// Preconditions hold but the two sides differ — a real counterexample.
    Counterexample(VerificationResult),
    /// Concrete evaluation could not interpret a required expression. This is
    /// NOT `PreconditionUnmet`: skipping such a point would let the sampling
    /// path finish having tested nothing. UF-bearing obligations are already
    /// declined whole by [`evaluator_undecidable`] before any sweep; this is
    /// the point-level backstop for everything else `try_eval` can refuse.
    Inconclusive(String),
}

impl PointCheck {
    /// Fold this point into a sweep: `Equal` is one more compared point (every
    /// precondition held), `PreconditionUnmet` compares nothing, and a
    /// counterexample or inconclusive point is the sweep's terminal verdict.
    fn tally(self, satisfied: &mut u64) -> Result<(), VerificationResult> {
        match self {
            Self::Equal => {
                *satisfied = satisfied.saturating_add(1);
                Ok(())
            }
            Self::PreconditionUnmet => Ok(()),
            Self::Counterexample(result) => Err(result),
            Self::Inconclusive(reason) => Err(VerificationResult::Unknown { reason }),
        }
    }
}

/// Evaluate the preconditions without treating an unsupported expression or
/// missing binding as a false guard. Those errors leave the sweep inconclusive.
///
/// EVERY precondition is evaluated before the conjunction is decided: stopping
/// at the first false one would never evaluate an unsupported precondition
/// listed after it, so an obligation whose early guard excludes every sampled
/// point would hide the later one's error and — when no point satisfies the
/// guards — report only a vacuous sample instead of naming the precondition
/// the evaluator cannot interpret. Whether an obligation's preconditions are
/// interpretable must not depend on their order. (The compiled fast path in
/// [`check_single_point`] may short-circuit: every compiled precondition is
/// in the supported subset, so none of them can fail to evaluate.)
fn preconditions_hold(obligation: &ProofObligation, env: &EvalEnv) -> Result<bool, String> {
    let mut all_hold = true;
    for (index, pre) in obligation.preconditions.iter().enumerate() {
        let value = pre
            .try_eval(env)
            .map_err(|error| format!("cannot concretely evaluate precondition {index}: {error}"))?;
        all_hold &= value.as_bool();
    }
    Ok(all_hold)
}

/// Check a single test point.
/// An obligation whose `trust_ir_expr`, `aarch64_expr`, and every precondition
/// all lie in the compiled integer/bitvector subset ([`FlatProg`]). Built ONCE
/// per obligation; the per-sample loop then evaluates the pre-flattened
/// [`FlatProg`] tapes (indexed env reads, a straight-line pass over a shared
/// scratch, no name hashing, no `SmtExpr` tree re-match, no recursion) instead of
/// the interpreter. Unlike the earlier ≤64-bit `CExpr`, `FlatProg` ALSO covers
/// the DIVISION subset (`bvsdiv`/`bvudiv`/`bvurem`, `TrapIfZero`, width > 64), so
/// division-heavy obligations no longer pay the fully-interpreted `try_eval` tax.
/// `try_new` returns `None` if any expression is out of subset, and the sampler
/// transparently uses the interpreted `try_eval` path — so the compiled path can
/// never change a verdict, only compute the same one faster (proven by
/// `flatprog_matches_interpreter_differential_fuzz` and
/// `compiled_fast_path_matches_interpreter_on_full_db`).
#[derive(Clone)]
struct CompiledObligation {
    trust_ir: FlatProg,
    aarch64: FlatProg,
    preconds: Vec<FlatProg>,
    /// The lane-batched twin of the three tapes, when every one of them is in
    /// `BatchProg`'s u64 subset. `None` keeps the sample loop on the scalar
    /// tapes above. See `check_batch`.
    batch: Option<CompiledBatch>,
}

/// The three tapes of a [`CompiledObligation`] as [`BatchTape`]s (narrow or
/// wide lane-batched evaluators).
#[derive(Clone)]
struct CompiledBatch {
    trust_ir: BatchTape,
    aarch64: BatchTape,
    preconds: Vec<BatchTape>,
}

impl CompiledObligation {
    /// Total tape nodes across all three programs — the per-sample work.
    fn op_count(&self) -> usize {
        self.trust_ir.op_count()
            + self.aarch64.op_count()
            + self.preconds.iter().map(FlatProg::op_count).sum::<usize>()
    }

    fn try_new(obligation: &ProofObligation) -> Option<Self> {
        let trust_ir = FlatProg::compile(&obligation.trust_ir_expr, &obligation.inputs)?;
        let aarch64 = FlatProg::compile(&obligation.aarch64_expr, &obligation.inputs)?;
        let mut preconds = Vec::with_capacity(obligation.preconditions.len());
        for pre in &obligation.preconditions {
            preconds.push(FlatProg::compile(pre, &obligation.inputs)?);
        }
        let batch = (|| {
            Some(CompiledBatch {
                trust_ir: BatchTape::from_flat(&trust_ir)?,
                aarch64: BatchTape::from_flat(&aarch64)?,
                preconds: preconds
                    .iter()
                    .map(BatchTape::from_flat)
                    .collect::<Option<Vec<_>>>()?,
            })
        })();
        Some(Self {
            trust_ir,
            aarch64,
            preconds,
            batch,
        })
    }
}

#[cfg(test)]
impl CompiledObligation {
    /// The same tapes with the batched twin withheld: the scalar sample loop,
    /// for pitting the batched path against it.
    fn try_new_scalar_only(obligation: &ProofObligation) -> Option<Self> {
        let mut co = Self::try_new(obligation)?;
        co.batch = None;
        Some(co)
    }
}

/// `verify_by_evaluation_with_config` with a caller-supplied compiled form
/// (test seam for scalar-vs-batched comparisons).
#[cfg(test)]
fn verify_by_evaluation_with_compiled(
    obligation: &ProofObligation,
    config: &VerificationConfig,
    compiled: Option<&CompiledObligation>,
) -> VerificationResult {
    if let Some(undecidable) = evaluator_undecidable(obligation) {
        return undecidable;
    }
    let width = obligation.inputs.first().map(|(_, w)| *w).unwrap_or(32);
    if let Some(count) = exhaustive_input_count(obligation, config) {
        verify_exhaustive(obligation, compiled, count)
    } else if needs_multi_input_sampling(obligation) {
        verify_random_multi(obligation, compiled, config.sample_count)
    } else {
        verify_random(obligation, compiled, width, config.sample_count)
    }
}

fn check_single_point(
    obligation: &ProofObligation,
    compiled: Option<&CompiledObligation>,
    env: &EvalEnv,
    scratch: &mut Vec<SVal>,
) -> PointCheck {
    // Fast path: pre-compiled scalar obligation. A compiled obligation has ALL
    // its (precondition + expression) variables among `inputs`, so the
    // interpreter's missing-binding error cannot apply here — every
    // precondition is in the supported scalar subset, matching
    // `preconditions_hold` when evaluation succeeds. `scratch` is a reused per-loop
    // buffer; each `FlatProg::eval` clears it and returns an owned `EvalResult`,
    // so reusing it across preconds/trust_ir/aarch64 is sound (no aliasing).
    if let Some(co) = compiled {
        for pc in &co.preconds {
            if !pc.eval(env, scratch).as_bool() {
                return PointCheck::PreconditionUnmet;
            }
        }
        let trust_ir_result = co.trust_ir.eval(env, scratch);
        let aarch64_result = co.aarch64.eval(env, scratch);
        return if trust_ir_result.semantically_equal(&aarch64_result) {
            PointCheck::Equal
        } else {
            PointCheck::Counterexample(VerificationResult::Invalid {
                counterexample: format!(
                    "inputs: {:?}, trust_ir={:?}, aarch64={:?}",
                    env, trust_ir_result, aarch64_result
                ),
            })
        };
    }

    match preconditions_hold(obligation, env) {
        Ok(true) => {}
        Ok(false) => return PointCheck::PreconditionUnmet,
        Err(reason) => return PointCheck::Inconclusive(reason),
    }

    // Fallible on purpose: `SmtExpr::eval` panics on anything `try_eval`
    // refuses, and a panic inside the process-wide memo cell takes a compile
    // down. Whatever cannot be evaluated is a non-verdict, not a crash.
    let trust_ir_result = match obligation.trust_ir_expr.try_eval(env) {
        Ok(result) => result,
        Err(error) => {
            return PointCheck::Inconclusive(format!(
                "cannot concretely evaluate source expression: {error}"
            ));
        }
    };
    let aarch64_result = match obligation.aarch64_expr.try_eval(env) {
        Ok(result) => result,
        Err(error) => {
            return PointCheck::Inconclusive(format!(
                "cannot concretely evaluate machine expression: {error}"
            ));
        }
    };

    // Use NaN-aware semantic equality: two `Float(NaN)` values are considered
    // equivalent because IEEE-754 `NaN != NaN` would otherwise produce spurious
    // counterexamples for FDIV(0,0), FSQRT(-1), and similar operations that
    // both trust_ir and the target encoder correctly lower to a NaN result. See
    // `EvalResult::semantically_equal` and #388.
    if !trust_ir_result.semantically_equal(&aarch64_result) {
        let cex = format!(
            "inputs: {:?}, trust_ir={:?}, aarch64={:?}",
            env, trust_ir_result, aarch64_result
        );
        PointCheck::Counterexample(VerificationResult::Invalid {
            counterexample: cex,
        })
    } else {
        PointCheck::Equal
    }
}

/// Fold the per-point result of an evaluation sweep into the final verdict,
/// guarding against a VACUOUS pass: if the obligation has preconditions and NO
/// tested point satisfied them, the sweep proves nothing (every point was
/// skipped), so it must return `Unknown` rather than `Valid`. Without this, an
/// unsatisfiable precondition (the no-solver twin of the MEM-1 / LOOP-1
/// false-negative) would make every wrong lowering pass vacuously.
fn sweep_verdict(obligation: &ProofObligation, saw_satisfying_point: bool) -> VerificationResult {
    if !obligation.preconditions.is_empty() && !saw_satisfying_point {
        return VerificationResult::Unknown {
            reason: "no tested input satisfied the preconditions; without a solver \
                     a real proof cannot be distinguished from a vacuous one"
                .to_string(),
        };
    }
    VerificationResult::Valid
}

// ---------------------------------------------------------------------------
// Registry of standard lowering rule proofs
// ---------------------------------------------------------------------------

/// Build the proof obligation for: `trust_ir::Iadd(I32, a, b) -> ADDWrr Wd, Wn, Wm`
pub fn proof_iadd_i32() -> ProofObligation {
    use crate::aarch64_semantics::encode_add_rr;
    use crate::trust_ir_semantics::encode_trust_ir_binop;
    use trust_cg_ir::cc::OperandSize;
    use trust_cg_lower::instructions::Opcode;
    use trust_cg_lower::types::Type;

    let a = SmtExpr::var("a", 32);
    let b = SmtExpr::var("b", 32);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "Iadd_I32 -> ADDWrr".to_string(),
        trust_ir_expr: encode_trust_ir_binop(&Opcode::Iadd, Type::I32, a.clone(), b.clone()),
        aarch64_expr: encode_add_rr(OperandSize::S32, a, b),
        inputs: vec![("a".to_string(), 32), ("b".to_string(), 32)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// Build the proof obligation for: `trust_ir::Iadd(I64, a, b) -> ADDXrr Xd, Xn, Xm`
pub fn proof_iadd_i64() -> ProofObligation {
    use crate::aarch64_semantics::encode_add_rr;
    use crate::trust_ir_semantics::encode_trust_ir_binop;
    use trust_cg_ir::cc::OperandSize;
    use trust_cg_lower::instructions::Opcode;
    use trust_cg_lower::types::Type;

    let a = SmtExpr::var("a", 64);
    let b = SmtExpr::var("b", 64);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "Iadd_I64 -> ADDXrr".to_string(),
        trust_ir_expr: encode_trust_ir_binop(&Opcode::Iadd, Type::I64, a.clone(), b.clone()),
        aarch64_expr: encode_add_rr(OperandSize::S64, a, b),
        inputs: vec![("a".to_string(), 64), ("b".to_string(), 64)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// Build the proof obligation for: `trust_ir::Isub(I32, a, b) -> SUBWrr Wd, Wn, Wm`
pub fn proof_isub_i32() -> ProofObligation {
    use crate::aarch64_semantics::encode_sub_rr;
    use crate::trust_ir_semantics::encode_trust_ir_binop;
    use trust_cg_ir::cc::OperandSize;
    use trust_cg_lower::instructions::Opcode;
    use trust_cg_lower::types::Type;

    let a = SmtExpr::var("a", 32);
    let b = SmtExpr::var("b", 32);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "Isub_I32 -> SUBWrr".to_string(),
        trust_ir_expr: encode_trust_ir_binop(&Opcode::Isub, Type::I32, a.clone(), b.clone()),
        aarch64_expr: encode_sub_rr(OperandSize::S32, a, b),
        inputs: vec![("a".to_string(), 32), ("b".to_string(), 32)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// Build the proof obligation for: `trust_ir::Imul(I32, a, b) -> MULWrrr Wd, Wn, Wm`
pub fn proof_imul_i32() -> ProofObligation {
    use crate::aarch64_semantics::encode_mul_rr;
    use crate::trust_ir_semantics::encode_trust_ir_binop;
    use trust_cg_ir::cc::OperandSize;
    use trust_cg_lower::instructions::Opcode;
    use trust_cg_lower::types::Type;

    let a = SmtExpr::var("a", 32);
    let b = SmtExpr::var("b", 32);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "Imul_I32 -> MULWrrr".to_string(),
        trust_ir_expr: encode_trust_ir_binop(&Opcode::Imul, Type::I32, a.clone(), b.clone()),
        aarch64_expr: encode_mul_rr(OperandSize::S32, a, b),
        inputs: vec![("a".to_string(), 32), ("b".to_string(), 32)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// Build the proof obligation for: `trust_ir::Neg(I32, a) -> NEG Wd, Wn`
///
/// NEG is `SUB Wd, WZR, Wn`, which is two's complement negation.
/// trust_ir Neg is encoded as `bvneg(a)`, AArch64 NEG is also `bvneg(a)`.
pub fn proof_neg_i32() -> ProofObligation {
    use crate::aarch64_semantics::encode_neg;
    use crate::trust_ir_semantics::encode_trust_ir_neg;
    use trust_cg_ir::cc::OperandSize;
    use trust_cg_lower::types::Type;

    let a = SmtExpr::var("a", 32);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "Neg_I32 -> NEG Wd".to_string(),
        trust_ir_expr: encode_trust_ir_neg(Type::I32, a.clone()),
        aarch64_expr: encode_neg(OperandSize::S32, a),
        inputs: vec![("a".to_string(), 32)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// Build a generic proof obligation for: `MADD Rd, Rn, Rm, Ra`.
///
/// This is an AArch64 instruction-semantics proof rather than a trust_ir lowering
/// rule: it proves the reusable encoder matches the architectural formula
/// `Ra + Rn * Rm` under wrapping bitvector arithmetic.
pub fn proof_aarch64_madd_rr_generic() -> ProofObligation {
    use crate::aarch64_semantics::encode_madd_rr;
    use trust_cg_ir::cc::OperandSize;

    let rn = SmtExpr::var("rn", 64);
    let rm = SmtExpr::var("rm", 64);
    let ra = SmtExpr::var("ra", 64);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "AArch64 MADD_RR generic".to_string(),
        trust_ir_expr: ra.clone().bvadd(rn.clone().bvmul(rm.clone())),
        aarch64_expr: encode_madd_rr(OperandSize::S64, rn, rm, ra),
        inputs: vec![
            ("rn".to_string(), 64),
            ("rm".to_string(), 64),
            ("ra".to_string(), 64),
        ],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// Build a generic proof obligation for: `MSUB Rd, Rn, Rm, Ra`.
///
/// This gives FunctionVerifier a direct single-instruction proof for `Msub`
/// instead of relying on remainder-lowering proofs that happen to contain an
/// MSUB instruction.
pub fn proof_aarch64_msub_rr_generic() -> ProofObligation {
    use crate::aarch64_semantics::encode_msub_rr;
    use trust_cg_ir::cc::OperandSize;

    let rn = SmtExpr::var("rn", 64);
    let rm = SmtExpr::var("rm", 64);
    let ra = SmtExpr::var("ra", 64);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "AArch64 MSUB_RR generic".to_string(),
        trust_ir_expr: ra.clone().bvsub(rn.clone().bvmul(rm.clone())),
        aarch64_expr: encode_msub_rr(OperandSize::S64, rn, rm, ra),
        inputs: vec![
            ("rn".to_string(), 64),
            ("rm".to_string(), 64),
            ("ra".to_string(), 64),
        ],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// Build the FAITHFUL widening-multiply obligation for:
/// `UMULL Xd, Wn, Wm` — `Xd == zext64(Wn) * zext64(Wm)`.
///
/// UMULL has EXACTLY ONE legal form (the UMADDL-with-XZR alias; sf=1 is
/// hardwired, the sources are always full W registers, the destination always
/// X), so a single obligation IS the complete per-opcode statement — the #62
/// unfaithful-inheritance hazard (one form's proof credited to another form)
/// cannot arise.
///
/// * SOURCE (trust_ir intent, the zext ring form the unsigned magic-division
///   isel path relies on): `Concat(0_32, a) * Concat(0_32, b)` — zext expressed
///   STRUCTURALLY as a concat with a zero upper word.
/// * MACHINE (encoder-faithful): [`encode_umull_rr`] — the UMADDL alias
///   `0 + ZeroExtend(a, 32) * ZeroExtend(b, 32)`, with the architectural XZR
///   addend and `ZeroExtend` nodes.
///
/// The two sides are STRUCTURALLY DISTINCT (`Concat`-zext vs `ZeroExtend`-zext
/// plus the XZR addend — `is_genuinely_proven`, not X==X) yet provably equal
/// over BV64. NON-DEGENERATE by control: a sign-extending machine side (the
/// SMULL confusion — this is exactly what distinguishes UMULL from SMULL) and
/// a truncating 32-bit MUL both REFUTE (see [`umull_wrong_controls`]).
pub fn proof_umull_rr() -> ProofObligation {
    use crate::aarch64_semantics::encode_umull_rr;

    let a = SmtExpr::var("a", 32);
    let b = SmtExpr::var("b", 32);
    let zero32 = SmtExpr::bv_const(0, 32);
    let source = zero32
        .clone()
        .concat(a.clone())
        .bvmul(zero32.concat(b.clone()));

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "Umull_RR -> UMULL Xd, Wn, Wm: Xd == zext64(Wn) * zext64(Wm)".to_string(),
        trust_ir_expr: source,
        aarch64_expr: encode_umull_rr(a, b),
        inputs: vec![("a".to_string(), 32), ("b".to_string(), 32)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// NEGATIVE CONTROLS for the UMULL obligation — each MUST refute (so the
/// positive is not vacuous):
///
/// 1. SEXT machine instead of ZEXT — the SMULL confusion. This is the control
///    that DISTINGUISHES UMULL from SMULL: a lowerer/encoder that produced the
///    signed widening multiply cannot inherit the unsigned proof.
/// 2. Truncating 32-bit MUL then zext — the plain `MUL Wd` confusion: the
///    product's high 32 bits are lost, diverging whenever it overflows 32 bits.
pub fn umull_wrong_controls() -> Vec<ProofObligation> {
    let a = SmtExpr::var("a", 32);
    let b = SmtExpr::var("b", 32);
    let zero32 = SmtExpr::bv_const(0, 32);
    let source = || {
        zero32
            .clone()
            .concat(a.clone())
            .bvmul(zero32.clone().concat(b.clone()))
    };
    let xzr = SmtExpr::bv_const(0, 64);

    vec![
        // (1) SMULL machine (sext64 * sext64) against the zext source.
        ProofObligation {
            machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
            name: "WRONG (umull_rr): SMULL machine (sext64*sext64) instead of zext must REFUTE"
                .to_string(),
            trust_ir_expr: source(),
            aarch64_expr: xzr
                .clone()
                .bvadd(a.clone().sign_ext(32).bvmul(b.clone().sign_ext(32))),
            inputs: vec![("a".to_string(), 32), ("b".to_string(), 32)],
            preconditions: vec![],
            fp_inputs: vec![],
            category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
        },
        // (2) Truncating 32-bit MUL then zext (plain MUL Wd confusion).
        ProofObligation {
            machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
            name: "WRONG (umull_rr): truncating 32-bit MUL then zext must REFUTE".to_string(),
            trust_ir_expr: source(),
            aarch64_expr: xzr.bvadd(a.clone().bvmul(b.clone()).zero_ext(32)),
            inputs: vec![("a".to_string(), 32), ("b".to_string(), 32)],
            preconditions: vec![],
            fp_inputs: vec![],
            category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
        },
    ]
}

// ---------------------------------------------------------------------------
// I8 arithmetic lowering proofs
// ---------------------------------------------------------------------------

/// Build the proof obligation for: `trust_ir::Iadd(I8, a, b) -> ADD (8-bit)`
///
/// On AArch64, 8-bit operations are performed in 32-bit W registers.
/// The proof verifies semantic equivalence at the 8-bit bitvector level.
pub fn proof_iadd_i8() -> ProofObligation {
    use crate::trust_ir_semantics::encode_trust_ir_binop;
    use trust_cg_lower::instructions::Opcode;
    use trust_cg_lower::types::Type;

    let a = SmtExpr::var("a", 8);
    let b = SmtExpr::var("b", 8);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "Iadd_I8 -> ADD (8-bit)".to_string(),
        trust_ir_expr: encode_trust_ir_binop(&Opcode::Iadd, Type::I8, a.clone(), b.clone()),
        aarch64_expr: a.bvadd(b),
        inputs: vec![("a".to_string(), 8), ("b".to_string(), 8)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// Build the proof obligation for: `trust_ir::Isub(I8, a, b) -> SUB (8-bit)`
pub fn proof_isub_i8() -> ProofObligation {
    use crate::trust_ir_semantics::encode_trust_ir_binop;
    use trust_cg_lower::instructions::Opcode;
    use trust_cg_lower::types::Type;

    let a = SmtExpr::var("a", 8);
    let b = SmtExpr::var("b", 8);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "Isub_I8 -> SUB (8-bit)".to_string(),
        trust_ir_expr: encode_trust_ir_binop(&Opcode::Isub, Type::I8, a.clone(), b.clone()),
        aarch64_expr: a.bvsub(b),
        inputs: vec![("a".to_string(), 8), ("b".to_string(), 8)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// Build the proof obligation for: `trust_ir::Imul(I8, a, b) -> MUL (8-bit)`
pub fn proof_imul_i8() -> ProofObligation {
    use crate::trust_ir_semantics::encode_trust_ir_binop;
    use trust_cg_lower::instructions::Opcode;
    use trust_cg_lower::types::Type;

    let a = SmtExpr::var("a", 8);
    let b = SmtExpr::var("b", 8);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "Imul_I8 -> MUL (8-bit)".to_string(),
        trust_ir_expr: encode_trust_ir_binop(&Opcode::Imul, Type::I8, a.clone(), b.clone()),
        aarch64_expr: a.bvmul(b),
        inputs: vec![("a".to_string(), 8), ("b".to_string(), 8)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// Build the proof obligation for: `trust_ir::Neg(I8, a) -> NEG (8-bit)`
pub fn proof_neg_i8() -> ProofObligation {
    use crate::trust_ir_semantics::encode_trust_ir_neg;
    use trust_cg_lower::types::Type;

    let a = SmtExpr::var("a", 8);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "Neg_I8 -> NEG (8-bit)".to_string(),
        trust_ir_expr: encode_trust_ir_neg(Type::I8, a.clone()),
        aarch64_expr: a.bvneg(),
        inputs: vec![("a".to_string(), 8)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

// ---------------------------------------------------------------------------
// I16 arithmetic lowering proofs
// ---------------------------------------------------------------------------

/// Build the proof obligation for: `trust_ir::Iadd(I16, a, b) -> ADD (16-bit)`
///
/// On AArch64, 16-bit operations are performed in 32-bit W registers.
/// The proof verifies semantic equivalence at the 16-bit bitvector level.
pub fn proof_iadd_i16() -> ProofObligation {
    use crate::trust_ir_semantics::encode_trust_ir_binop;
    use trust_cg_lower::instructions::Opcode;
    use trust_cg_lower::types::Type;

    let a = SmtExpr::var("a", 16);
    let b = SmtExpr::var("b", 16);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "Iadd_I16 -> ADD (16-bit)".to_string(),
        trust_ir_expr: encode_trust_ir_binop(&Opcode::Iadd, Type::I16, a.clone(), b.clone()),
        aarch64_expr: a.bvadd(b),
        inputs: vec![("a".to_string(), 16), ("b".to_string(), 16)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// Build the proof obligation for: `trust_ir::Isub(I16, a, b) -> SUB (16-bit)`
pub fn proof_isub_i16() -> ProofObligation {
    use crate::trust_ir_semantics::encode_trust_ir_binop;
    use trust_cg_lower::instructions::Opcode;
    use trust_cg_lower::types::Type;

    let a = SmtExpr::var("a", 16);
    let b = SmtExpr::var("b", 16);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "Isub_I16 -> SUB (16-bit)".to_string(),
        trust_ir_expr: encode_trust_ir_binop(&Opcode::Isub, Type::I16, a.clone(), b.clone()),
        aarch64_expr: a.bvsub(b),
        inputs: vec![("a".to_string(), 16), ("b".to_string(), 16)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// Build the proof obligation for: `trust_ir::Imul(I16, a, b) -> MUL (16-bit)`
pub fn proof_imul_i16() -> ProofObligation {
    use crate::trust_ir_semantics::encode_trust_ir_binop;
    use trust_cg_lower::instructions::Opcode;
    use trust_cg_lower::types::Type;

    let a = SmtExpr::var("a", 16);
    let b = SmtExpr::var("b", 16);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "Imul_I16 -> MUL (16-bit)".to_string(),
        trust_ir_expr: encode_trust_ir_binop(&Opcode::Imul, Type::I16, a.clone(), b.clone()),
        aarch64_expr: a.bvmul(b),
        inputs: vec![("a".to_string(), 16), ("b".to_string(), 16)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// Build the proof obligation for: `trust_ir::Neg(I16, a) -> NEG (16-bit)`
pub fn proof_neg_i16() -> ProofObligation {
    use crate::trust_ir_semantics::encode_trust_ir_neg;
    use trust_cg_lower::types::Type;

    let a = SmtExpr::var("a", 16);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "Neg_I16 -> NEG (16-bit)".to_string(),
        trust_ir_expr: encode_trust_ir_neg(Type::I16, a.clone()),
        aarch64_expr: a.bvneg(),
        inputs: vec![("a".to_string(), 16)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

// ---------------------------------------------------------------------------
// I64 arithmetic lowering proofs (sub, mul, neg — iadd_i64 already exists)
// ---------------------------------------------------------------------------

/// Build the proof obligation for: `trust_ir::Isub(I64, a, b) -> SUBXrr Xd, Xn, Xm`
pub fn proof_isub_i64() -> ProofObligation {
    use crate::aarch64_semantics::encode_sub_rr;
    use crate::trust_ir_semantics::encode_trust_ir_binop;
    use trust_cg_ir::cc::OperandSize;
    use trust_cg_lower::instructions::Opcode;
    use trust_cg_lower::types::Type;

    let a = SmtExpr::var("a", 64);
    let b = SmtExpr::var("b", 64);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "Isub_I64 -> SUBXrr".to_string(),
        trust_ir_expr: encode_trust_ir_binop(&Opcode::Isub, Type::I64, a.clone(), b.clone()),
        aarch64_expr: encode_sub_rr(OperandSize::S64, a, b),
        inputs: vec![("a".to_string(), 64), ("b".to_string(), 64)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// Build the proof obligation for: `trust_ir::Imul(I64, a, b) -> MULXrrr Xd, Xn, Xm`
pub fn proof_imul_i64() -> ProofObligation {
    use crate::aarch64_semantics::encode_mul_rr;
    use crate::trust_ir_semantics::encode_trust_ir_binop;
    use trust_cg_ir::cc::OperandSize;
    use trust_cg_lower::instructions::Opcode;
    use trust_cg_lower::types::Type;

    let a = SmtExpr::var("a", 64);
    let b = SmtExpr::var("b", 64);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "Imul_I64 -> MULXrrr".to_string(),
        trust_ir_expr: encode_trust_ir_binop(&Opcode::Imul, Type::I64, a.clone(), b.clone()),
        aarch64_expr: encode_mul_rr(OperandSize::S64, a, b),
        inputs: vec![("a".to_string(), 64), ("b".to_string(), 64)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// Build the proof obligation for: `trust_ir::Neg(I64, a) -> NEG Xd, Xn`
pub fn proof_neg_i64() -> ProofObligation {
    use crate::aarch64_semantics::encode_neg;
    use crate::trust_ir_semantics::encode_trust_ir_neg;
    use trust_cg_ir::cc::OperandSize;
    use trust_cg_lower::types::Type;

    let a = SmtExpr::var("a", 64);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "Neg_I64 -> NEG Xd".to_string(),
        trust_ir_expr: encode_trust_ir_neg(Type::I64, a.clone()),
        aarch64_expr: encode_neg(OperandSize::S64, a),
        inputs: vec![("a".to_string(), 64)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

// ---------------------------------------------------------------------------
// Division lowering proofs: trust_ir::Sdiv/Udiv -> AArch64 SDIV/UDIV
// ---------------------------------------------------------------------------

/// Build the proof obligation for: `trust_ir::Sdiv(I32, a, b) -> SDIV Wd, Wn, Wm`
///
/// Precondition: `b != 0` (NonZeroDivisor proof annotation).
///
/// AArch64 SDIV semantics: signed division with truncation toward zero.
/// Division by zero returns 0 on AArch64, but trust_ir treats it as UB --
/// we verify equivalence only when the precondition holds.
///
/// Edge case: `INT32_MIN / -1` = `INT32_MIN` on AArch64 (signed overflow
/// wraps). The SMT `bvsdiv` semantics match this behavior.
pub fn proof_sdiv_i32() -> ProofObligation {
    use crate::aarch64_semantics::encode_sdiv_rr;
    use crate::trust_ir_semantics::{encode_trust_ir_binop, precondition};
    use trust_cg_ir::cc::OperandSize;
    use trust_cg_lower::instructions::Opcode;
    use trust_cg_lower::types::Type;

    let a = SmtExpr::var("a", 32);
    let b = SmtExpr::var("b", 32);

    let mut preconditions = vec![];
    if let Some(pre) = precondition(&Opcode::Sdiv, Type::I32, &a, &b) {
        preconditions.push(pre);
    }

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "Sdiv_I32 -> SDIVWrr".to_string(),
        trust_ir_expr: encode_trust_ir_binop(&Opcode::Sdiv, Type::I32, a.clone(), b.clone()),
        aarch64_expr: encode_sdiv_rr(OperandSize::S32, a, b),
        inputs: vec![("a".to_string(), 32), ("b".to_string(), 32)],
        preconditions,
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// Build the proof obligation for: `trust_ir::Sdiv(I64, a, b) -> SDIV Xd, Xn, Xm`
///
/// Precondition: `b != 0`.
/// Edge case: `INT64_MIN / -1` = `INT64_MIN` (signed overflow wraps).
pub fn proof_sdiv_i64() -> ProofObligation {
    use crate::aarch64_semantics::encode_sdiv_rr;
    use crate::trust_ir_semantics::{encode_trust_ir_binop, precondition};
    use trust_cg_ir::cc::OperandSize;
    use trust_cg_lower::instructions::Opcode;
    use trust_cg_lower::types::Type;

    let a = SmtExpr::var("a", 64);
    let b = SmtExpr::var("b", 64);

    let mut preconditions = vec![];
    if let Some(pre) = precondition(&Opcode::Sdiv, Type::I64, &a, &b) {
        preconditions.push(pre);
    }

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "Sdiv_I64 -> SDIVXrr".to_string(),
        trust_ir_expr: encode_trust_ir_binop(&Opcode::Sdiv, Type::I64, a.clone(), b.clone()),
        aarch64_expr: encode_sdiv_rr(OperandSize::S64, a, b),
        inputs: vec![("a".to_string(), 64), ("b".to_string(), 64)],
        preconditions,
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// Build the proof obligation for: `trust_ir::Udiv(I32, a, b) -> UDIV Wd, Wn, Wm`
///
/// Precondition: `b != 0` (NonZeroDivisor proof annotation).
///
/// AArch64 UDIV semantics: unsigned division with truncation toward zero.
/// Division by zero returns 0 on AArch64, but trust_ir treats it as UB.
pub fn proof_udiv_i32() -> ProofObligation {
    use crate::aarch64_semantics::encode_udiv_rr;
    use crate::trust_ir_semantics::{encode_trust_ir_binop, precondition};
    use trust_cg_ir::cc::OperandSize;
    use trust_cg_lower::instructions::Opcode;
    use trust_cg_lower::types::Type;

    let a = SmtExpr::var("a", 32);
    let b = SmtExpr::var("b", 32);

    let mut preconditions = vec![];
    if let Some(pre) = precondition(&Opcode::Udiv, Type::I32, &a, &b) {
        preconditions.push(pre);
    }

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "Udiv_I32 -> UDIVWrr".to_string(),
        trust_ir_expr: encode_trust_ir_binop(&Opcode::Udiv, Type::I32, a.clone(), b.clone()),
        aarch64_expr: encode_udiv_rr(OperandSize::S32, a, b),
        inputs: vec![("a".to_string(), 32), ("b".to_string(), 32)],
        preconditions,
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// Build the proof obligation for: `trust_ir::Udiv(I64, a, b) -> UDIV Xd, Xn, Xm`
///
/// Precondition: `b != 0`.
pub fn proof_udiv_i64() -> ProofObligation {
    use crate::aarch64_semantics::encode_udiv_rr;
    use crate::trust_ir_semantics::{encode_trust_ir_binop, precondition};
    use trust_cg_ir::cc::OperandSize;
    use trust_cg_lower::instructions::Opcode;
    use trust_cg_lower::types::Type;

    let a = SmtExpr::var("a", 64);
    let b = SmtExpr::var("b", 64);

    let mut preconditions = vec![];
    if let Some(pre) = precondition(&Opcode::Udiv, Type::I64, &a, &b) {
        preconditions.push(pre);
    }

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "Udiv_I64 -> UDIVXrr".to_string(),
        trust_ir_expr: encode_trust_ir_binop(&Opcode::Udiv, Type::I64, a.clone(), b.clone()),
        aarch64_expr: encode_udiv_rr(OperandSize::S64, a, b),
        inputs: vec![("a".to_string(), 64), ("b".to_string(), 64)],
        preconditions,
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// Return all division lowering proofs.
pub fn all_division_proofs() -> Vec<ProofObligation> {
    vec![
        proof_sdiv_i32(),
        proof_sdiv_i64(),
        proof_udiv_i32(),
        proof_udiv_i64(),
    ]
}

// ---------------------------------------------------------------------------
// Remainder lowering proofs (issue #435)
// ---------------------------------------------------------------------------
//
// AArch64 has no dedicated remainder instruction. `Urem` / `Srem` lower to a
// two-instruction sequence:
//
//   q = UDIV/SDIV  Wn, Wm          ; quotient
//   r = MSUB       q,  Wm, Wn      ; r = Wn - q * Wm
//
// The proof encodes both the trust_ir `Urem`/`Srem` form (via `encode_trust_ir_binop`
// which composes `bvudiv`/`bvsdiv` + `bvmul` + `bvsub`) and the machine
// `MSUB(UDIV/SDIV(a, b), b, a)` form, then verifies they are equivalent
// under the division preconditions.
//
// Preconditions:
//   * `Urem`: `b != 0` (divisor nonzero).
//   * `Srem`: `b != 0` AND `not (a == INT_MIN && b == -1)` -- the second
//     conjunct avoids the signed-division overflow case where `bvsdiv` is
//     defined but some hardware manuals leave remainder-via-MSUB behavior
//     unspecified. In practice AArch64's SDIV of `INT_MIN / -1` returns
//     `INT_MIN` and the MSUB identity holds, but the trust_ir spec forbids this
//     input, so we add it as an explicit precondition for symmetry with
//     classical compilers (LLVM, rustc).

/// Build the proof obligation for: `trust_ir::Urem(I8, a, b) -> UDIV + MSUB (8-bit)`
///
/// Proves: `bvurem(a, b) == a - (a /u b) * b` for all 8-bit `a` and all
/// `b != 0`. Exhaustive at 8-bit (2^16 - 256 inputs with precondition filter).
pub fn proof_urem_i8() -> ProofObligation {
    use crate::aarch64_semantics::{encode_msub_rr, encode_udiv_rr_nonzero};
    use crate::trust_ir_semantics::{encode_trust_ir_binop, precondition};
    use trust_cg_ir::cc::OperandSize;
    use trust_cg_lower::instructions::Opcode;
    use trust_cg_lower::types::Type;

    let a = SmtExpr::var("a", 8);
    let b = SmtExpr::var("b", 8);

    let mut preconditions = vec![];
    if let Some(pre) = precondition(&Opcode::Urem, Type::I8, &a, &b) {
        preconditions.push(pre);
    }

    let quotient = encode_udiv_rr_nonzero(OperandSize::S32, a.clone(), b.clone());
    let machine = encode_msub_rr(OperandSize::S32, quotient, b.clone(), a.clone());

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "Urem_I8 -> UDIV+MSUB (8-bit)".to_string(),
        trust_ir_expr: encode_trust_ir_binop(&Opcode::Urem, Type::I8, a, b),
        aarch64_expr: machine,
        inputs: vec![("a".to_string(), 8), ("b".to_string(), 8)],
        preconditions,
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// Build the proof obligation for: `trust_ir::Srem(I8, a, b) -> SDIV + MSUB (8-bit)`
///
/// Proves: `bvsrem(a, b) == a - (a /s b) * b` under the preconditions
/// `b != 0` and `not (a == INT8_MIN && b == -1)`.
///
/// The second precondition guards the signed-division overflow case where
/// `INT_MIN / -1` is mathematically `|INT_MIN|` but does not fit in the
/// signed range. trust_ir treats this as UB; classical compilers add a runtime
/// check. Adding the precondition here mirrors that convention.
pub fn proof_srem_i8() -> ProofObligation {
    use crate::aarch64_semantics::{encode_msub_rr, encode_sdiv_rr_nonzero};
    use crate::trust_ir_semantics::{encode_trust_ir_binop, precondition};
    use trust_cg_ir::cc::OperandSize;
    use trust_cg_lower::instructions::Opcode;
    use trust_cg_lower::types::Type;

    let a = SmtExpr::var("a", 8);
    let b = SmtExpr::var("b", 8);

    let mut preconditions = vec![];
    if let Some(pre) = precondition(&Opcode::Srem, Type::I8, &a, &b) {
        preconditions.push(pre);
    }
    // Additional precondition: not (a == INT8_MIN && b == -1).
    // INT8_MIN = 0x80 = -128, -1 = 0xFF at 8 bits.
    let int8_min = SmtExpr::bv_const(0x80, 8);
    let neg_one = SmtExpr::bv_const(0xFF, 8);
    let overflow = a
        .clone()
        .eq_expr(int8_min)
        .and_expr(b.clone().eq_expr(neg_one));
    preconditions.push(overflow.not_expr());

    let quotient = encode_sdiv_rr_nonzero(OperandSize::S32, a.clone(), b.clone());
    let machine = encode_msub_rr(OperandSize::S32, quotient, b.clone(), a.clone());

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "Srem_I8 -> SDIV+MSUB (8-bit)".to_string(),
        trust_ir_expr: encode_trust_ir_binop(&Opcode::Srem, Type::I8, a, b),
        aarch64_expr: machine,
        inputs: vec![("a".to_string(), 8), ("b".to_string(), 8)],
        preconditions,
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// Build the proof obligation for: `trust_ir::Urem(I16, a, b) -> UDIV + MSUB (16-bit)`
///
/// Widening of [`proof_urem_i8`] to i16. The encoders (`encode_udiv_rr`,
/// `encode_msub_rr`) are width-polymorphic — they use the bitvector width
/// carried by the `SmtExpr`, so the 16-bit obligation is a direct copy of
/// the 8-bit proof with `SmtExpr::var("a", 16)` / `SmtExpr::var("b", 16)`.
/// `OperandSize::S32` is passed because 16-bit values are held in W
/// registers on AArch64, matching the i8 convention.
///
/// Under ay this runs symbolically (no enumeration), so wall-time is modest
/// despite the 2^32 joint input space. Smoke lane uses the tolerant
/// `assert_verified_or_timeout` helper (#435).
pub fn proof_urem_i16() -> ProofObligation {
    use crate::aarch64_semantics::{encode_msub_rr, encode_udiv_rr_nonzero};
    use crate::trust_ir_semantics::{encode_trust_ir_binop, precondition};
    use trust_cg_ir::cc::OperandSize;
    use trust_cg_lower::instructions::Opcode;
    use trust_cg_lower::types::Type;

    let a = SmtExpr::var("a", 16);
    let b = SmtExpr::var("b", 16);

    let mut preconditions = vec![];
    if let Some(pre) = precondition(&Opcode::Urem, Type::I16, &a, &b) {
        preconditions.push(pre);
    }

    let quotient = encode_udiv_rr_nonzero(OperandSize::S32, a.clone(), b.clone());
    let machine = encode_msub_rr(OperandSize::S32, quotient, b.clone(), a.clone());

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "Urem_I16 -> UDIV+MSUB (16-bit)".to_string(),
        trust_ir_expr: encode_trust_ir_binop(&Opcode::Urem, Type::I16, a, b),
        aarch64_expr: machine,
        inputs: vec![("a".to_string(), 16), ("b".to_string(), 16)],
        preconditions,
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// Build the proof obligation for: `trust_ir::Srem(I16, a, b) -> SDIV + MSUB (16-bit)`
///
/// Widening of [`proof_srem_i8`] to i16. Preconditions mirror the i8 case:
/// `b != 0` AND `not (a == INT16_MIN && b == -1)`. `INT16_MIN = 0x8000`,
/// `-1 @ 16 bits = 0xFFFF`.
pub fn proof_srem_i16() -> ProofObligation {
    use crate::aarch64_semantics::{encode_msub_rr, encode_sdiv_rr_nonzero};
    use crate::trust_ir_semantics::{encode_trust_ir_binop, precondition};
    use trust_cg_ir::cc::OperandSize;
    use trust_cg_lower::instructions::Opcode;
    use trust_cg_lower::types::Type;

    let a = SmtExpr::var("a", 16);
    let b = SmtExpr::var("b", 16);

    let mut preconditions = vec![];
    if let Some(pre) = precondition(&Opcode::Srem, Type::I16, &a, &b) {
        preconditions.push(pre);
    }
    // Additional precondition: not (a == INT16_MIN && b == -1).
    // INT16_MIN = 0x8000 = -32768, -1 = 0xFFFF at 16 bits.
    let int16_min = SmtExpr::bv_const(0x8000, 16);
    let neg_one = SmtExpr::bv_const(0xFFFF, 16);
    let overflow = a
        .clone()
        .eq_expr(int16_min)
        .and_expr(b.clone().eq_expr(neg_one));
    preconditions.push(overflow.not_expr());

    let quotient = encode_sdiv_rr_nonzero(OperandSize::S32, a.clone(), b.clone());
    let machine = encode_msub_rr(OperandSize::S32, quotient, b.clone(), a.clone());

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "Srem_I16 -> SDIV+MSUB (16-bit)".to_string(),
        trust_ir_expr: encode_trust_ir_binop(&Opcode::Srem, Type::I16, a, b),
        aarch64_expr: machine,
        inputs: vec![("a".to_string(), 16), ("b".to_string(), 16)],
        preconditions,
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// Build the proof obligation for: `trust_ir::Urem(I32, a, b) -> UDIV + MSUB (32-bit)`.
///
/// Widening of [`proof_urem_i16`] to the native W-register width.
/// Precondition: `b != 0`.
pub fn proof_urem_i32() -> ProofObligation {
    use crate::aarch64_semantics::{encode_msub_rr, encode_udiv_rr_nonzero};
    use crate::trust_ir_semantics::{encode_trust_ir_binop, precondition};
    use trust_cg_ir::cc::OperandSize;
    use trust_cg_lower::instructions::Opcode;
    use trust_cg_lower::types::Type;

    let a = SmtExpr::var("a", 32);
    let b = SmtExpr::var("b", 32);

    let mut preconditions = vec![];
    if let Some(pre) = precondition(&Opcode::Urem, Type::I32, &a, &b) {
        preconditions.push(pre);
    }

    let quotient = encode_udiv_rr_nonzero(OperandSize::S32, a.clone(), b.clone());
    let machine = encode_msub_rr(OperandSize::S32, quotient, b.clone(), a.clone());

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "Urem_I32 -> UDIV+MSUB (32-bit)".to_string(),
        trust_ir_expr: encode_trust_ir_binop(&Opcode::Urem, Type::I32, a, b),
        aarch64_expr: machine,
        inputs: vec![("a".to_string(), 32), ("b".to_string(), 32)],
        preconditions,
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// Build the proof obligation for: `trust_ir::Srem(I32, a, b) -> SDIV + MSUB (32-bit)`.
///
/// Widening of [`proof_srem_i16`] to the native W-register width.
/// Preconditions: `b != 0` AND `not (a == INT32_MIN && b == -1)`.
pub fn proof_srem_i32() -> ProofObligation {
    use crate::aarch64_semantics::{encode_msub_rr, encode_sdiv_rr_nonzero};
    use crate::trust_ir_semantics::{encode_trust_ir_binop, precondition};
    use trust_cg_ir::cc::OperandSize;
    use trust_cg_lower::instructions::Opcode;
    use trust_cg_lower::types::Type;

    let a = SmtExpr::var("a", 32);
    let b = SmtExpr::var("b", 32);

    let mut preconditions = vec![];
    if let Some(pre) = precondition(&Opcode::Srem, Type::I32, &a, &b) {
        preconditions.push(pre);
    }
    let int32_min = SmtExpr::bv_const(0x8000_0000, 32);
    let neg_one = SmtExpr::bv_const(0xFFFF_FFFF, 32);
    let overflow = a
        .clone()
        .eq_expr(int32_min)
        .and_expr(b.clone().eq_expr(neg_one));
    preconditions.push(overflow.not_expr());

    let quotient = encode_sdiv_rr_nonzero(OperandSize::S32, a.clone(), b.clone());
    let machine = encode_msub_rr(OperandSize::S32, quotient, b.clone(), a.clone());

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "Srem_I32 -> SDIV+MSUB (32-bit)".to_string(),
        trust_ir_expr: encode_trust_ir_binop(&Opcode::Srem, Type::I32, a, b),
        aarch64_expr: machine,
        inputs: vec![("a".to_string(), 32), ("b".to_string(), 32)],
        preconditions,
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// Build the proof obligation for: `trust_ir::Urem(I64, a, b) -> UDIV + MSUB (64-bit)`.
///
/// Widening of [`proof_urem_i32`] to the native X-register width.
/// Precondition: `b != 0`.
pub fn proof_urem_i64() -> ProofObligation {
    use crate::aarch64_semantics::{encode_msub_rr, encode_udiv_rr_nonzero};
    use crate::trust_ir_semantics::{encode_trust_ir_binop, precondition};
    use trust_cg_ir::cc::OperandSize;
    use trust_cg_lower::instructions::Opcode;
    use trust_cg_lower::types::Type;

    let a = SmtExpr::var("a", 64);
    let b = SmtExpr::var("b", 64);

    let mut preconditions = vec![];
    if let Some(pre) = precondition(&Opcode::Urem, Type::I64, &a, &b) {
        preconditions.push(pre);
    }

    let quotient = encode_udiv_rr_nonzero(OperandSize::S64, a.clone(), b.clone());
    let machine = encode_msub_rr(OperandSize::S64, quotient, b.clone(), a.clone());

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "Urem_I64 -> UDIV+MSUB (64-bit)".to_string(),
        trust_ir_expr: encode_trust_ir_binop(&Opcode::Urem, Type::I64, a, b),
        aarch64_expr: machine,
        inputs: vec![("a".to_string(), 64), ("b".to_string(), 64)],
        preconditions,
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// Build the proof obligation for: `trust_ir::Srem(I64, a, b) -> SDIV + MSUB (64-bit)`.
///
/// Widening of [`proof_srem_i32`] to the native X-register width.
/// Preconditions: `b != 0` AND `not (a == INT64_MIN && b == -1)`.
pub fn proof_srem_i64() -> ProofObligation {
    use crate::aarch64_semantics::{encode_msub_rr, encode_sdiv_rr_nonzero};
    use crate::trust_ir_semantics::{encode_trust_ir_binop, precondition};
    use trust_cg_ir::cc::OperandSize;
    use trust_cg_lower::instructions::Opcode;
    use trust_cg_lower::types::Type;

    let a = SmtExpr::var("a", 64);
    let b = SmtExpr::var("b", 64);

    let mut preconditions = vec![];
    if let Some(pre) = precondition(&Opcode::Srem, Type::I64, &a, &b) {
        preconditions.push(pre);
    }
    let int64_min = SmtExpr::bv_const(0x8000_0000_0000_0000, 64);
    let neg_one = SmtExpr::bv_const(u64::MAX, 64);
    let overflow = a
        .clone()
        .eq_expr(int64_min)
        .and_expr(b.clone().eq_expr(neg_one));
    preconditions.push(overflow.not_expr());

    let quotient = encode_sdiv_rr_nonzero(OperandSize::S64, a.clone(), b.clone());
    let machine = encode_msub_rr(OperandSize::S64, quotient, b.clone(), a.clone());

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "Srem_I64 -> SDIV+MSUB (64-bit)".to_string(),
        trust_ir_expr: encode_trust_ir_binop(&Opcode::Srem, Type::I64, a, b),
        aarch64_expr: machine,
        inputs: vec![("a".to_string(), 64), ("b".to_string(), 64)],
        preconditions,
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// Return all remainder lowering proofs (issue #435).
pub fn all_remainder_proofs() -> Vec<ProofObligation> {
    vec![
        proof_urem_i8(),
        proof_srem_i8(),
        proof_urem_i16(),
        proof_srem_i16(),
        proof_urem_i32(),
        proof_srem_i32(),
        proof_urem_i64(),
        proof_srem_i64(),
    ]
}

// ---------------------------------------------------------------------------
// Bitcast lowering proof (issue #435)
// ---------------------------------------------------------------------------
//
// `trust_ir::Bitcast { to_ty }` reinterprets the bit pattern of `operand` as a
// different type of the same width. It is pure type-punning with no runtime
// cost: on AArch64 it lowers to `MOV` (GPR<->GPR), `FMOV` register-register
// (FPR<->FPR), or `FMOV` general (GPR<->FPR / FPR<->GPR). All three machine
// forms reduce to the bitvector identity.
//
// The proof below uses `i8` as a representative width; the equivalence is
// trivial (`x == x`) but the obligation exercises the full proof pipeline
// (precondition-free, ay-compatible) and locks in the semantics so that
// future changes to `encode_trust_ir_bitcast` or `encode_mov_rr` are caught.

/// Build the proof obligation for: `trust_ir::Bitcast(I8 -> I8, a) -> MOV (8-bit)`
///
/// Verifies that a same-width bitcast is the identity at the bit level.
/// Representative of the full family of same-width bitcasts:
/// `i32<->f32`, `i64<->f64`, pointer casts, etc.
pub fn proof_bitcast_i8() -> ProofObligation {
    use crate::aarch64_semantics::encode_mov_rr;
    use crate::trust_ir_semantics::encode_trust_ir_bitcast;
    use trust_cg_ir::cc::OperandSize;
    use trust_cg_lower::types::Type;

    let a = SmtExpr::var("a", 8);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "Bitcast_I8_I8 -> MOV (8-bit)".to_string(),
        trust_ir_expr: encode_trust_ir_bitcast(Type::I8, Type::I8, a.clone()),
        aarch64_expr: encode_mov_rr(OperandSize::S32, a),
        inputs: vec![("a".to_string(), 8)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// Build the proof obligation for: `trust_ir::Bitcast(I16 -> I16, a) -> MOV (16-bit)`
///
/// Widening of [`proof_bitcast_i8`] to i16. `encode_trust_ir_bitcast` and
/// `encode_mov_rr` are width-agnostic (pure identity on the input
/// bitvector), so the obligation is the BV identity `x == x` at width 16.
pub fn proof_bitcast_i16() -> ProofObligation {
    use crate::aarch64_semantics::encode_mov_rr;
    use crate::trust_ir_semantics::encode_trust_ir_bitcast;
    use trust_cg_ir::cc::OperandSize;
    use trust_cg_lower::types::Type;

    let a = SmtExpr::var("a", 16);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "Bitcast_I16_I16 -> MOV (16-bit)".to_string(),
        trust_ir_expr: encode_trust_ir_bitcast(Type::I16, Type::I16, a.clone()),
        aarch64_expr: encode_mov_rr(OperandSize::S32, a),
        inputs: vec![("a".to_string(), 16)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// Build the proof obligation for: `trust_ir::Bitcast(I32 -> I32, a) -> MOV (32-bit)`
///
/// Widening of [`proof_bitcast_i8`] to i32. Covers the i32<->f32 bit
/// reinterpretation case at the BV level. Pure identity.
pub fn proof_bitcast_i32() -> ProofObligation {
    use crate::aarch64_semantics::encode_mov_rr;
    use crate::trust_ir_semantics::encode_trust_ir_bitcast;
    use trust_cg_ir::cc::OperandSize;
    use trust_cg_lower::types::Type;

    let a = SmtExpr::var("a", 32);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "Bitcast_I32_I32 -> MOV (32-bit)".to_string(),
        trust_ir_expr: encode_trust_ir_bitcast(Type::I32, Type::I32, a.clone()),
        aarch64_expr: encode_mov_rr(OperandSize::S32, a),
        inputs: vec![("a".to_string(), 32)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// Build the proof obligation for: `trust_ir::Bitcast(I64 -> I64, a) -> MOV (64-bit)`
///
/// Widening of [`proof_bitcast_i8`] to i64. Covers the i64<->f64 and
/// pointer bitcast families at the BV level. Pure identity.
pub fn proof_bitcast_i64() -> ProofObligation {
    use crate::aarch64_semantics::encode_mov_rr;
    use crate::trust_ir_semantics::encode_trust_ir_bitcast;
    use trust_cg_ir::cc::OperandSize;
    use trust_cg_lower::types::Type;

    let a = SmtExpr::var("a", 64);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "Bitcast_I64_I64 -> MOV (64-bit)".to_string(),
        trust_ir_expr: encode_trust_ir_bitcast(Type::I64, Type::I64, a.clone()),
        aarch64_expr: encode_mov_rr(OperandSize::S64, a),
        inputs: vec![("a".to_string(), 64)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// Return all bitcast lowering proofs (issue #435).
pub fn all_bitcast_proofs() -> Vec<ProofObligation> {
    vec![
        proof_bitcast_i8(),
        proof_bitcast_i16(),
        proof_bitcast_i32(),
        proof_bitcast_i64(),
    ]
}

// ---------------------------------------------------------------------------
// Bitfield lowering proofs (issue #452, epic #435)
// ---------------------------------------------------------------------------
//
// trust_ir has three bitfield opcodes that have no dedicated 1:1 AArch64
// instruction mnemonic but compose from UBFM / SBFM / BFM:
//
//   ExtractBits { lsb, width }   ->  UBFM Wd, Wn, #lsb, #(lsb + width - 1)
//   SextractBits { lsb, width }  ->  SBFM Wd, Wn, #lsb, #(lsb + width - 1)
//   InsertBits { lsb, width }    ->  BFM  Wd, Wn, #((reg_size - lsb) % reg_size),
//                                          #(width - 1)
//                                   (preceded by a COPY of the `dst` operand
//                                    into the result register -- see
//                                    `trust-cg-lower/src/isel.rs::select_bitfield_insert`)
//
// All three machine instructions are pure QF_BV operations -- no flags, no
// memory, no preconditions beyond the immediate-field range enforced by the
// trust_ir type system and the encoder (`lsb + width <= reg_size`, `width >= 1`).
// The proofs below verify that the trust_ir semantic encoding matches the
// AArch64 semantic encoding for representative (lsb, width) pairs at
// i8/i16/i32/i64.
//
// # Representative (lsb, width) choice
//
// We pick middle-ish slices that exercise both non-zero lsb and multi-bit
// masks: i8 `(2,4)`, i16 `(3,7)`, i32 `(7,13)`, and i64 `(11,23)`. In each
// `SextractBits` proof, the top bit of the slice can be either value
// depending on the input, so the sign-extension arm is actually exercised
// both with and without sign bits set.
//
// Exhaustive i8 evaluation covers all 2^8 = 256 inputs for ExtractBits /
// SextractBits and all 2^16 = 65,536 (dst, src) pairs for InsertBits.
//
// References:
// - ARM DDI 0487, C6.2.335 UBFM (C6.2.334 UBFX alias)
// - ARM DDI 0487, C6.2.266 SBFM (C6.2.264 SBFX alias)
// - ARM DDI 0487, C6.2.46 BFM (C6.2.45 BFI alias)

fn proof_extract_bits_for_width(
    ty: trust_cg_lower::types::Type,
    ty_name: &str,
    bits: u32,
    lsb: u8,
    width: u8,
) -> ProofObligation {
    use crate::aarch64_semantics::encode_ubfm_extract;
    use crate::trust_ir_semantics::encode_trust_ir_extract_bits;

    let x = SmtExpr::var("x", bits);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: format!(
            "ExtractBits{{lsb={},width={}}}_{} -> UBFM ({}-bit)",
            lsb, width, ty_name, bits
        ),
        trust_ir_expr: encode_trust_ir_extract_bits(ty, lsb, width, x.clone()),
        aarch64_expr: encode_ubfm_extract(x, lsb as u32, width as u32, bits),
        inputs: vec![("x".to_string(), bits)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

fn proof_sextract_bits_for_width(
    ty: trust_cg_lower::types::Type,
    ty_name: &str,
    bits: u32,
    lsb: u8,
    width: u8,
) -> ProofObligation {
    use crate::aarch64_semantics::encode_sbfm_extract;
    use crate::trust_ir_semantics::encode_trust_ir_sextract_bits;

    let x = SmtExpr::var("x", bits);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: format!(
            "SextractBits{{lsb={},width={}}}_{} -> SBFM ({}-bit)",
            lsb, width, ty_name, bits
        ),
        trust_ir_expr: encode_trust_ir_sextract_bits(ty, lsb, width, x.clone()),
        aarch64_expr: encode_sbfm_extract(x, lsb as u32, width as u32, bits),
        inputs: vec![("x".to_string(), bits)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

fn proof_insert_bits_for_width(
    ty: trust_cg_lower::types::Type,
    ty_name: &str,
    bits: u32,
    lsb: u8,
    width: u8,
) -> ProofObligation {
    use crate::aarch64_semantics::encode_bfm_insert;
    use crate::trust_ir_semantics::encode_trust_ir_insert_bits;

    let x = SmtExpr::var("x", bits);
    let y = SmtExpr::var("y", bits);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: format!(
            "InsertBits{{lsb={},width={}}}_{} -> BFM ({}-bit)",
            lsb, width, ty_name, bits
        ),
        trust_ir_expr: encode_trust_ir_insert_bits(ty, lsb, width, x.clone(), y.clone()),
        aarch64_expr: encode_bfm_insert(x, y, lsb as u32, width as u32, bits),
        inputs: vec![("x".to_string(), bits), ("y".to_string(), bits)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// Build the proof obligation for:
/// `trust_ir::ExtractBits{lsb=2, width=4}(I8, x) -> UBFM Wd, Wn, #2, #5 (8-bit)`.
///
/// Proves: `bv_extract(lsb, width, x) == (x lsr lsb) & mask(width)` for all
/// 8-bit `x`. No preconditions.
pub fn proof_extract_bits_i8() -> ProofObligation {
    use trust_cg_lower::types::Type;

    proof_extract_bits_for_width(Type::I8, "I8", 8, 2, 4)
}

/// Build the proof obligation for:
/// `trust_ir::ExtractBits{lsb=3, width=7}(I16, x) -> UBFM Wd, Wn, #3, #9 (16-bit)`.
pub fn proof_extract_bits_i16() -> ProofObligation {
    use trust_cg_lower::types::Type;

    proof_extract_bits_for_width(Type::I16, "I16", 16, 3, 7)
}

/// Build the proof obligation for:
/// `trust_ir::ExtractBits{lsb=7, width=13}(I32, x) -> UBFM Wd, Wn, #7, #19 (32-bit)`.
pub fn proof_extract_bits_i32() -> ProofObligation {
    use trust_cg_lower::types::Type;

    proof_extract_bits_for_width(Type::I32, "I32", 32, 7, 13)
}

/// Build the proof obligation for:
/// `trust_ir::ExtractBits{lsb=11, width=23}(I64, x) -> UBFM Xd, Xn, #11, #33 (64-bit)`.
pub fn proof_extract_bits_i64() -> ProofObligation {
    use trust_cg_lower::types::Type;

    proof_extract_bits_for_width(Type::I64, "I64", 64, 11, 23)
}

/// Build the proof obligation for:
/// `trust_ir::SextractBits{lsb=2, width=4}(I8, x) -> SBFM Wd, Wn, #2, #5 (8-bit)`.
///
/// Proves: `sign_extend(x[lsb+width-1:lsb]) == SBFM-machine-semantics` for
/// all 8-bit `x`. No preconditions.
///
/// SBFM's machine encoding ties to `sign_extend(extract(lsb, width, x))`:
/// the 4-bit slice `x[5:2]` is pulled out and sign-extended to 8 bits by
/// replicating bit 3 of the slice (= bit 5 of `x`) across the upper 4 bits.
pub fn proof_sextract_bits_i8() -> ProofObligation {
    use trust_cg_lower::types::Type;

    proof_sextract_bits_for_width(Type::I8, "I8", 8, 2, 4)
}

/// Build the proof obligation for:
/// `trust_ir::SextractBits{lsb=3, width=7}(I16, x) -> SBFM Wd, Wn, #3, #9 (16-bit)`.
pub fn proof_sextract_bits_i16() -> ProofObligation {
    use trust_cg_lower::types::Type;

    proof_sextract_bits_for_width(Type::I16, "I16", 16, 3, 7)
}

/// Build the proof obligation for:
/// `trust_ir::SextractBits{lsb=7, width=13}(I32, x) -> SBFM Wd, Wn, #7, #19 (32-bit)`.
pub fn proof_sextract_bits_i32() -> ProofObligation {
    use trust_cg_lower::types::Type;

    proof_sextract_bits_for_width(Type::I32, "I32", 32, 7, 13)
}

/// Build the proof obligation for:
/// `trust_ir::SextractBits{lsb=11, width=23}(I64, x) -> SBFM Xd, Xn, #11, #33 (64-bit)`.
pub fn proof_sextract_bits_i64() -> ProofObligation {
    use trust_cg_lower::types::Type;

    proof_sextract_bits_for_width(Type::I64, "I64", 64, 11, 23)
}

/// Build the proof obligation for:
/// `trust_ir::InsertBits{lsb=2, width=4}(I8, x, y) -> BFM Wd, Ws (8-bit)`.
///
/// Proves: `result == (x & ~mask_shifted) | ((y & mask(width)) shl lsb)`
/// for all 8-bit `(x, y)`, where `mask_shifted = mask(width) << lsb`.
/// No preconditions.
///
/// `x` is the destination (old value, preserved outside the slice).
/// `y` supplies the new bits for `[lsb + width - 1 : lsb]`.
pub fn proof_insert_bits_i8() -> ProofObligation {
    use trust_cg_lower::types::Type;

    proof_insert_bits_for_width(Type::I8, "I8", 8, 2, 4)
}

/// Build the proof obligation for:
/// `trust_ir::InsertBits{lsb=3, width=7}(I16, x, y) -> BFM Wd, Ws (16-bit)`.
pub fn proof_insert_bits_i16() -> ProofObligation {
    use trust_cg_lower::types::Type;

    proof_insert_bits_for_width(Type::I16, "I16", 16, 3, 7)
}

/// Build the proof obligation for:
/// `trust_ir::InsertBits{lsb=7, width=13}(I32, x, y) -> BFM Wd, Ws (32-bit)`.
pub fn proof_insert_bits_i32() -> ProofObligation {
    use trust_cg_lower::types::Type;

    proof_insert_bits_for_width(Type::I32, "I32", 32, 7, 13)
}

/// Build the proof obligation for:
/// `trust_ir::InsertBits{lsb=11, width=23}(I64, x, y) -> BFM Xd, Xs (64-bit)`.
pub fn proof_insert_bits_i64() -> ProofObligation {
    use trust_cg_lower::types::Type;

    proof_insert_bits_for_width(Type::I64, "I64", 64, 11, 23)
}

/// Return all bitfield lowering proofs (issue #452, widened by #435).
pub fn all_bitfield_proofs() -> Vec<ProofObligation> {
    vec![
        proof_extract_bits_i8(),
        proof_sextract_bits_i8(),
        proof_insert_bits_i8(),
        proof_extract_bits_i16(),
        proof_sextract_bits_i16(),
        proof_insert_bits_i16(),
        proof_extract_bits_i32(),
        proof_sextract_bits_i32(),
        proof_insert_bits_i32(),
        proof_extract_bits_i64(),
        proof_sextract_bits_i64(),
        proof_insert_bits_i64(),
    ]
}

// ---------------------------------------------------------------------------
// I128 multi-register arithmetic lowering proofs (issue #324)
// ---------------------------------------------------------------------------
//
// i128 values are held in a register pair (lo:hi) of two 64-bit GPRs. Add /
// sub are lowered to two machine instructions — a flag-setting low-half op
// followed by a carry/borrow-propagating high-half op:
//
//   i128 ADD: `ADDS dst_lo, a_lo, b_lo`  then  `ADC dst_hi, a_hi, b_hi`
//   i128 SUB: `SUBS dst_lo, a_lo, b_lo`  then  `SBC dst_hi, a_hi, b_hi`
//
// The default evaluator's `bvadd`/`bvsub`/`bvmul` eval paths truncate to u64
// (see `SmtExpr::BvAdd` in `smt.rs`), so we cannot model the 128-bit spec as
// a single 128-bit `bvadd`/`bvsub` and get meaningful coverage. Instead, the
// proof obligations below are split across the two 64-bit limbs — one
// obligation for each — with a concrete SMT-level carry / borrow expression
// that matches the AArch64 NZCV semantics:
//
//   ADC carry  : C = 1 iff a_lo + b_lo overflows 2^64 ≡ `bvult(lo_sum, a_lo)`
//   SBC borrow : C = 1 iff a_lo >= b_lo (AArch64 sets C=!borrow) ≡
//                !bvult(a_lo, b_lo) ≡ `bvuge(a_lo, b_lo)`
//
// Both sides of each obligation (trust_ir spec, aarch64 machine form) are
// constructed using the same SMT primitives, so evaluation-based
// verification acts as a regression lock on the carry/borrow encoding. A
// future ay formal proof can compare against `concat(hi, lo).bvadd/bvsub`
// directly once the evaluator grows native 128-bit add/sub.

/// Build the proof obligation for the low 64 bits of i128 ADD.
///
/// `dst_lo = (a_lo + b_lo) mod 2^64` on both sides. This is the trivial
/// half of the ADDS+ADC lowering; the hi-half proof below carries the
/// ADC-specific carry identity.
pub fn proof_iadd_i128_lo() -> ProofObligation {
    let a_lo = SmtExpr::var("a_lo", 64);
    let b_lo = SmtExpr::var("b_lo", 64);

    // trust_ir spec: low 64 bits of `a + b` are `(a_lo + b_lo) mod 2^64`.
    let trust_ir = a_lo.clone().bvadd(b_lo.clone());
    // AArch64 ADDS writes `a_lo + b_lo` into dst_lo.
    let aarch64 = a_lo.bvadd(b_lo);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "Iadd_I128 lo -> ADDS Xlo,Xa_lo,Xb_lo".to_string(),
        trust_ir_expr: trust_ir,
        aarch64_expr: aarch64,
        inputs: vec![("a_lo".to_string(), 64), ("b_lo".to_string(), 64)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// Build the proof obligation for the high 64 bits of i128 ADD.
///
/// `dst_hi = (a_hi + b_hi + carry) mod 2^64` where
/// `carry = 1 iff (a_lo + b_lo) wraps past 2^64`. Both sides use the same
/// carry formula drawn from AArch64's ADDS NZCV flag semantics.
pub fn proof_iadd_i128_hi() -> ProofObligation {
    let a_lo = SmtExpr::var("a_lo", 64);
    let b_lo = SmtExpr::var("b_lo", 64);
    let a_hi = SmtExpr::var("a_hi", 64);
    let b_hi = SmtExpr::var("b_hi", 64);

    // carry = 1 iff a_lo + b_lo overflowed the 64-bit word.
    let lo_sum = a_lo.clone().bvadd(b_lo);
    let carry_bool = lo_sum.bvult(a_lo);
    let carry_bv = SmtExpr::ite(
        carry_bool,
        SmtExpr::bv_const(1, 64),
        SmtExpr::bv_const(0, 64),
    );

    // trust_ir spec: high 64 bits of `a + b` = a_hi + b_hi + carry (mod 2^64).
    let trust_ir = a_hi.clone().bvadd(b_hi.clone()).bvadd(carry_bv.clone());
    // AArch64 ADC: dst_hi = a_hi + b_hi + C (where C came from ADDS above).
    let aarch64 = a_hi.bvadd(b_hi).bvadd(carry_bv);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "Iadd_I128 hi -> ADC Xhi,Xa_hi,Xb_hi".to_string(),
        trust_ir_expr: trust_ir,
        aarch64_expr: aarch64,
        inputs: vec![
            ("a_lo".to_string(), 64),
            ("b_lo".to_string(), 64),
            ("a_hi".to_string(), 64),
            ("b_hi".to_string(), 64),
        ],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// Build the proof obligation for the low 64 bits of i128 SUB.
///
/// `dst_lo = (a_lo - b_lo) mod 2^64` via AArch64 SUBS.
pub fn proof_isub_i128_lo() -> ProofObligation {
    let a_lo = SmtExpr::var("a_lo", 64);
    let b_lo = SmtExpr::var("b_lo", 64);

    let trust_ir = a_lo.clone().bvsub(b_lo.clone());
    let aarch64 = a_lo.bvsub(b_lo);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "Isub_I128 lo -> SUBS Xlo,Xa_lo,Xb_lo".to_string(),
        trust_ir_expr: trust_ir,
        aarch64_expr: aarch64,
        inputs: vec![("a_lo".to_string(), 64), ("b_lo".to_string(), 64)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// Build the proof obligation for the high 64 bits of i128 SUB.
///
/// AArch64 SBC computes `a_hi + NOT(b_hi) + C` where `C = !borrow`, i.e.
/// `dst_hi = a_hi - b_hi - borrow (mod 2^64)`. The borrow from the low
/// half is `1 iff a_lo < b_lo` (unsigned), so `C = 1 iff a_lo >= b_lo`.
/// The trust_ir spec for the high limb of `a - b` is the same.
pub fn proof_isub_i128_hi() -> ProofObligation {
    let a_lo = SmtExpr::var("a_lo", 64);
    let b_lo = SmtExpr::var("b_lo", 64);
    let a_hi = SmtExpr::var("a_hi", 64);
    let b_hi = SmtExpr::var("b_hi", 64);

    // borrow = 1 iff a_lo < b_lo (unsigned).
    let borrow_bool = a_lo.bvult(b_lo);
    let borrow_bv = SmtExpr::ite(
        borrow_bool,
        SmtExpr::bv_const(1, 64),
        SmtExpr::bv_const(0, 64),
    );

    // trust_ir spec: high 64 bits of `a - b` = a_hi - b_hi - borrow (mod 2^64).
    let trust_ir = a_hi.clone().bvsub(b_hi.clone()).bvsub(borrow_bv.clone());
    // AArch64 SBC: dst_hi = a_hi - b_hi - borrow, reading C from SUBS.
    let aarch64 = a_hi.bvsub(b_hi).bvsub(borrow_bv);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "Isub_I128 hi -> SBC Xhi,Xa_hi,Xb_hi".to_string(),
        trust_ir_expr: trust_ir,
        aarch64_expr: aarch64,
        inputs: vec![
            ("a_lo".to_string(), 64),
            ("b_lo".to_string(), 64),
            ("a_hi".to_string(), 64),
            ("b_hi".to_string(), 64),
        ],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// FAITHFUL whole-chain i128 ADD: `ADDS lo; ADC hi` reconstructs the native
/// 128-bit sum. STRUCTURALLY DISTINCT from the spec side — `trust_ir_expr` is a
/// native 128-bit `BvAdd` at the root, `aarch64_expr` is `Concat{hi: carry-add,
/// lo: add}` — so it is NOT a degenerate X==X (unlike `proof_iadd_i128_lo`/`_hi`
/// above, which credit nothing). A dropped carry-in or wrong limb order REFUTES
/// (cf. the x86 negative control `test_x86_64_iadd_i128_dropped_carry_is_refuted`).
/// Reuses the TARGET-INDEPENDENT carry-chain encoder shared with the landed x86
/// i128 proof (`proof_x86_iadd_i128_add_adc`).
pub fn proof_iadd_i128_whole_chain() -> ProofObligation {
    use crate::trust_ir_semantics::encode_trust_ir_binop;
    use crate::x86_64_semantics::encode_add_adc_i128;
    use trust_cg_lower::instructions::Opcode;
    use trust_cg_lower::types::Type;
    let a_lo = SmtExpr::var("a_lo", 64);
    let a_hi = SmtExpr::var("a_hi", 64);
    let b_lo = SmtExpr::var("b_lo", 64);
    let b_hi = SmtExpr::var("b_hi", 64);
    let a128 = a_hi.clone().concat(a_lo.clone());
    let b128 = b_hi.clone().concat(b_lo.clone());
    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "AArch64: Iadd_I128 whole-chain -> ADDS lo; ADC hi".to_string(),
        trust_ir_expr: encode_trust_ir_binop(&Opcode::Iadd, Type::I128, a128, b128),
        aarch64_expr: encode_add_adc_i128(a_lo, a_hi, b_lo, b_hi),
        inputs: vec![
            ("a_lo".to_string(), 64),
            ("a_hi".to_string(), 64),
            ("b_lo".to_string(), 64),
            ("b_hi".to_string(), 64),
        ],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// FAITHFUL whole-chain i128 SUB: `SUBS lo; SBC hi` reconstructs the native
/// 128-bit difference. Mirror of [`proof_iadd_i128_whole_chain`] (Isub + borrow,
/// `encode_sub_sbb_i128`); a flipped borrow polarity REFUTES (cf. the x86 SBB
/// negative control). Also credits the i128-NEG `SUBS;SBC` (the `a == 0` instance
/// the generic symbolic obligation subsumes).
pub fn proof_isub_i128_whole_chain() -> ProofObligation {
    use crate::trust_ir_semantics::encode_trust_ir_binop;
    use crate::x86_64_semantics::encode_sub_sbb_i128;
    use trust_cg_lower::instructions::Opcode;
    use trust_cg_lower::types::Type;
    let a_lo = SmtExpr::var("a_lo", 64);
    let a_hi = SmtExpr::var("a_hi", 64);
    let b_lo = SmtExpr::var("b_lo", 64);
    let b_hi = SmtExpr::var("b_hi", 64);
    let a128 = a_hi.clone().concat(a_lo.clone());
    let b128 = b_hi.clone().concat(b_lo.clone());
    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "AArch64: Isub_I128 whole-chain -> SUBS lo; SBC hi".to_string(),
        trust_ir_expr: encode_trust_ir_binop(&Opcode::Isub, Type::I128, a128, b128),
        aarch64_expr: encode_sub_sbb_i128(a_lo, a_hi, b_lo, b_hi),
        inputs: vec![
            ("a_lo".to_string(), 64),
            ("a_hi".to_string(), 64),
            ("b_lo".to_string(), 64),
            ("b_hi".to_string(), 64),
        ],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// FAITHFUL per-compile **encoding** proof for the AArch64 `UBFM` unsigned
/// bitfield-EXTRACT form at register width `w` (∈ {32, 64}).
///
/// SOUNDNESS — this verifies the ISEL ENCODING, NOT a tautology. The naive
/// "reconstruct BOTH sides from the same recovered `(lsb, width)`" obligation is
/// UNSOUND: [`crate::aarch64_semantics::encode_ubfm_extract`] and
/// [`crate::trust_ir_semantics::encode_trust_ir_extract_bits`] are STRUCTURALLY
/// IDENTICAL `(rn lsr lsb) & mask(width)`, so that obligation is a degenerate
/// X==X that no wrong `immr`/`imms` could ever refute (it would NOT catch a
/// miscompiled UBFM). Instead we model the ENCODING and compare to the intended
/// extract:
///
///   * MACHINE side = the ARM hardware UBFM/UBFX DECODE
///     `(rn lsr immr) & mask(imms − immr + 1)` applied to the **isel encoding
///     formula** `immr = lsb`, `imms = lsb + width − 1` (the exact mapping in
///     `trust-cg-lower/src/isel.rs::select_bitfield_extract`, isel.rs:8045-8046).
///   * SOURCE side = the intended trust_ir `ExtractBits` semantics
///     `(rn lsr lsb) & ((1 << width) − 1)` — the symbolic generalization of
///     `encode_trust_ir_extract_bits`.
///
/// The two sides are STRUCTURALLY DISTINCT (`is_genuinely_proven`, NOT X==X):
/// the source mask width is the symbol `width`; the machine mask width is the
/// arithmetic tree `(imms − immr) + 1` over `imms = lsb + width − 1`. They are
/// EQUAL iff the isel `imms` formula is correct — a wrong `imms` (e.g.
/// `lsb + width`, an off-by-one) decodes to `mask(width + 1)` and REFUTES on any
/// `rn` whose bit `lsb + width` is set; a wrong `immr` shifts by the wrong
/// amount and REFUTES likewise.
///
/// `lsb`/`width` are SMALL (`idxw`-bit) symbolic vars so the no-solver
/// statistical sampler lands a large fraction (~1/8) of draws inside the
/// precondition `0 < width ∧ lsb + width ≤ W` (a full-`W` var would leave every
/// random draw precondition-unmet ⇒ a sweep that compares nothing: the
/// vacuous-sample `Unknown`, with no power to refute).
/// `idxw` is the smallest width that still represents the full-register endpoint
/// (`width = W`, `lsb = 0`). They are zero-extended to `w` for use as the
/// shift/mask amounts. Reference: ARM DDI 0487, C6.2.335 UBFM / C6.2.334 UBFX.
fn proof_ubfm_extract_at_width(w: u32) -> ProofObligation {
    let idxw = if w <= 32 { 6 } else { 7 };
    let rn = SmtExpr::var("rn", w);
    let one = SmtExpr::bv_const(1, w);
    let zero = SmtExpr::bv_const(0, w);
    let wbits = SmtExpr::bv_const(w as u64, w);
    let lsb_w = SmtExpr::var("lsb", idxw).zero_ext(w - idxw);
    let width_w = SmtExpr::var("width", idxw).zero_ext(w - idxw);

    // SOURCE: trust_ir ExtractBits == (rn lsr lsb) & ((1 << width) - 1).
    let source = rn
        .clone()
        .bvlshr(lsb_w.clone())
        .bvand(one.clone().bvshl(width_w.clone()).bvsub(one.clone()));

    // MACHINE: hardware UBFM/UBFX decode of the isel encoding immr=lsb,
    // imms=lsb+width-1 == (rn lsr immr) & mask((imms - immr) + 1).
    let immr = lsb_w.clone();
    let imms = lsb_w.clone().bvadd(width_w.clone()).bvsub(one.clone());
    let field_w = imms.bvsub(immr.clone()).bvadd(one.clone());
    let machine = rn
        .bvlshr(immr)
        .bvand(one.clone().bvshl(field_w).bvsub(one.clone()));

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: format!(
            "AArch64: UBFM extract w{w} ENCODING (immr=lsb, imms=lsb+width-1) == ExtractBits"
        ),
        trust_ir_expr: source,
        aarch64_expr: machine,
        inputs: vec![
            ("rn".to_string(), w),
            ("lsb".to_string(), idxw),
            ("width".to_string(), idxw),
        ],
        // 0 < width  AND  lsb + width <= W.
        preconditions: vec![
            zero.bvult(width_w.clone()),
            lsb_w.bvadd(width_w).bvule(wbits),
        ],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// FAITHFUL per-compile UBFM extract-ENCODING proof at register width 32.
pub fn proof_ubfm_extract_w32() -> ProofObligation {
    proof_ubfm_extract_at_width(32)
}

/// FAITHFUL per-compile UBFM extract-ENCODING proof at register width 64.
pub fn proof_ubfm_extract_w64() -> ProofObligation {
    proof_ubfm_extract_at_width(64)
}

/// FAITHFUL per-compile **encoding** proof for the AArch64 `SBFM` signed
/// bitfield-EXTRACT form at register width `w` (∈ {32, 64}). Mirror of
/// [`proof_ubfm_extract_at_width`] for the SIGNED extract (same soundness
/// argument: encoding-verifying, NOT the degenerate X==X that reusing
/// `encode_sbfm_extract`/`encode_trust_ir_sextract_bits` — which are
/// structurally identical `extract`+`sign_extend` — would produce).
///
/// The signed extract is realized as the classic shift-left / arithmetic-shift-
/// right sign-extract so that BOTH sides stay symbolic in `(lsb, width)` (the
/// SMT `(sign_extend)` node needs a CONCRETE width, so it cannot carry a
/// symbolic field width):
///
///   * SOURCE = trust_ir `SextractBits`:
///     `(rn << (W − lsb − width)) >>a (W − width)`.
///   * MACHINE = hardware SBFM/SBFX decode of the isel encoding `immr = lsb`,
///     `imms = lsb + width − 1`, sign-extending bits `[imms : immr]` (field width
///     `imms − immr + 1`):
///     `(rn << ((W − 1) − imms)) >>a (W − (imms − immr + 1))`.
///
/// STRUCTURALLY DISTINCT: the machine shift amounts are arithmetic trees over
/// `imms = lsb + width − 1`; the source's are over `lsb`/`width` directly. They
/// are EQUAL iff the isel encoding is correct — a wrong `imms` misaligns the
/// field (replicates the WRONG sign bit) and REFUTES. Same small-var,
/// precondition-respecting sampling discipline as the unsigned form.
/// Reference: ARM DDI 0487, C6.2.266 SBFM / C6.2.264 SBFX.
fn proof_sbfm_extract_at_width(w: u32) -> ProofObligation {
    let idxw = if w <= 32 { 6 } else { 7 };
    let rn = SmtExpr::var("rn", w);
    let one = SmtExpr::bv_const(1, w);
    let zero = SmtExpr::bv_const(0, w);
    let wbits = SmtExpr::bv_const(w as u64, w);
    let lsb_w = SmtExpr::var("lsb", idxw).zero_ext(w - idxw);
    let width_w = SmtExpr::var("width", idxw).zero_ext(w - idxw);

    // SOURCE: trust_ir SextractBits via shift-left then arithmetic-shift-right.
    let src_left = wbits.clone().bvsub(lsb_w.clone()).bvsub(width_w.clone()); // W - lsb - width
    let src_right = wbits.clone().bvsub(width_w.clone()); // W - width
    let source = rn.clone().bvshl(src_left).bvashr(src_right);

    // MACHINE: hardware SBFM/SBFX decode of the isel encoding immr=lsb,
    // imms=lsb+width-1, sign-extending bits [imms:immr].
    let immr = lsb_w.clone();
    let imms = lsb_w.clone().bvadd(width_w.clone()).bvsub(one.clone()); // lsb + width - 1
    let field_w = imms.clone().bvsub(immr).bvadd(one.clone()); // (imms - immr) + 1
    let mach_left = wbits.clone().bvsub(one).bvsub(imms); // (W - 1) - imms
    let mach_right = wbits.clone().bvsub(field_w); // W - field_w
    let machine = rn.bvshl(mach_left).bvashr(mach_right);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: format!(
            "AArch64: SBFM extract w{w} ENCODING (immr=lsb, imms=lsb+width-1) == SextractBits"
        ),
        trust_ir_expr: source,
        aarch64_expr: machine,
        inputs: vec![
            ("rn".to_string(), w),
            ("lsb".to_string(), idxw),
            ("width".to_string(), idxw),
        ],
        // 0 < width  AND  lsb + width <= W.
        preconditions: vec![
            zero.bvult(width_w.clone()),
            lsb_w.bvadd(width_w).bvule(wbits),
        ],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// FAITHFUL per-compile SBFM extract-ENCODING proof at register width 32.
pub fn proof_sbfm_extract_w32() -> ProofObligation {
    proof_sbfm_extract_at_width(32)
}

/// FAITHFUL per-compile SBFM extract-ENCODING proof at register width 64.
pub fn proof_sbfm_extract_w64() -> ProofObligation {
    proof_sbfm_extract_at_width(64)
}

/// Build the proof obligation for the low 64 bits of i128 MUL.
///
/// ```text
/// dst_lo = MUL a_lo, b_lo
/// ```
/// i.e. `dst_lo = (a_lo * b_lo) mod 2^64`. The i128 product spec reduces to
/// the same expression for its low 64 bits because multiplication is
/// commutative/associative under mod 2^64 and only the cross terms
/// `a_lo*b_hi`, `a_hi*b_lo`, `a_hi*b_hi` contribute to bits >= 64.
pub fn proof_imul_i128_lo() -> ProofObligation {
    let a_lo = SmtExpr::var("a_lo", 64);
    let b_lo = SmtExpr::var("b_lo", 64);

    // trust_ir spec: low 64 bits of `a * b` are `(a_lo * b_lo) mod 2^64`.
    let trust_ir = a_lo.clone().bvmul(b_lo.clone());
    // AArch64 MUL writes `a_lo * b_lo` into dst_lo.
    let aarch64 = a_lo.bvmul(b_lo);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "Imul_I128 lo -> MUL Xlo,Xa_lo,Xb_lo".to_string(),
        trust_ir_expr: trust_ir,
        aarch64_expr: aarch64,
        inputs: vec![("a_lo".to_string(), 64), ("b_lo".to_string(), 64)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// Build the proof obligation for the high 64 bits of i128 MUL.
///
/// The AArch64 lowering emits:
/// ```text
/// dst_lo = MUL   a_lo, b_lo
/// t0     = UMULH a_lo, b_lo                 // upper 64 bits of a_lo*b_lo
/// t1     = MADD  a_lo, b_hi, t0             // t0 + a_lo * b_hi
/// dst_hi = MADD  a_hi, b_lo, t1             // t1 + a_hi * b_lo
/// ```
/// So `dst_hi = UMULH(a_lo, b_lo) + a_lo*b_hi + a_hi*b_lo (mod 2^64)`.
///
/// `UMULH` has no native 64-bit encoding and the SMT evaluator truncates
/// `bvmul` to 64 bits, so we cannot compute the true high-half product
/// inside the evaluator. We model `UMULH(a_lo, b_lo)` as a free 64-bit
/// variable `umulh_ab_lo` that appears identically on the trust_ir spec side
/// and the AArch64 machine side. The proof then verifies that the MADD
/// chain correctly accumulates the cross terms on top of the UMULH
/// contribution — this is the part of the lowering that could realistically
/// be miscoded (operand order, missed addend, wrong base). The correctness
/// of `UMULH` itself is covered by `aarch64_semantics` encoding tests.
///
/// A future ay-native proof can replace `umulh_ab_lo` with the true
/// `(zero_extend(a_lo, 64).bvmul(zero_extend(b_lo, 64))).extract(127, 64)`
/// expression once the evaluator supports 128-bit `bvmul`.
pub fn proof_imul_i128_hi() -> ProofObligation {
    let a_lo = SmtExpr::var("a_lo", 64);
    let b_lo = SmtExpr::var("b_lo", 64);
    let a_hi = SmtExpr::var("a_hi", 64);
    let b_hi = SmtExpr::var("b_hi", 64);
    // Symbolic stand-in for UMULH(a_lo, b_lo). The same variable appears on
    // both sides so the evaluator sees a well-defined value; any lowering
    // bug in the MADD chain around it will still surface as a mismatch.
    let umulh = SmtExpr::var("umulh_ab_lo", 64);

    // trust_ir spec: `dst_hi = umulh(a_lo,b_lo) + a_lo*b_hi + a_hi*b_lo (mod 2^64)`.
    let cross_ab = a_lo.clone().bvmul(b_hi.clone());
    let cross_ba = a_hi.clone().bvmul(b_lo.clone());
    let trust_ir = umulh
        .clone()
        .bvadd(cross_ab.clone())
        .bvadd(cross_ba.clone());

    // AArch64 form: t1 = MADD(a_lo, b_hi, t0) = a_lo*b_hi + umulh
    //               dst_hi = MADD(a_hi, b_lo, t1) = a_hi*b_lo + t1
    let t1 = cross_ab.bvadd(umulh);
    let aarch64 = cross_ba.bvadd(t1);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "Imul_I128 hi -> MUL+UMULH+MADD+MADD".to_string(),
        trust_ir_expr: trust_ir,
        aarch64_expr: aarch64,
        inputs: vec![
            ("a_lo".to_string(), 64),
            ("b_lo".to_string(), 64),
            ("a_hi".to_string(), 64),
            ("b_hi".to_string(), 64),
            ("umulh_ab_lo".to_string(), 64),
        ],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

fn zext_i128_shift_to_64(shift: SmtExpr) -> SmtExpr {
    SmtExpr::bv_const(0, 57).concat(shift)
}

fn zext_i128_shift_to_128(shift: SmtExpr) -> SmtExpr {
    SmtExpr::bv_const(0, 121).concat(shift)
}

fn aarch64_shift_amount_mod64(amount: SmtExpr) -> SmtExpr {
    amount.bvand(SmtExpr::bv_const(63, 64))
}

fn aarch64_lslv64(value: SmtExpr, amount: SmtExpr) -> SmtExpr {
    value.bvshl(aarch64_shift_amount_mod64(amount))
}

fn aarch64_lsrv64(value: SmtExpr, amount: SmtExpr) -> SmtExpr {
    value.bvlshr(aarch64_shift_amount_mod64(amount))
}

fn aarch64_asrv64(value: SmtExpr, amount: SmtExpr) -> SmtExpr {
    value.bvashr(aarch64_shift_amount_mod64(amount))
}

/// Build the proof obligation for i128 left shift.
///
/// The trust_ir side shifts the full 128-bit concatenation by a valid i128 shift
/// amount in `[0, 127]`. The AArch64 side models the multi-register lowering:
/// limb shifts use LSLV/LSRV modulo-64 shift amounts, with an explicit CSEL
/// guard that zeros the spill contribution when `shift == 0`.
///
/// EXPLICIT DOMAIN CONTRACT (adversarial audit, #94-class): the 7-BIT `shift`
/// variable quantifies this proof over `[0, 127]` ONLY — it says nothing about
/// a runtime count `>= 128`, where the 128-bit ISel decompositions genuinely
/// DIVERGE from a masked shift (`select_i128_shl` declares such counts UB and
/// does not reduce them). The producer is responsible for establishing the
/// domain: the rustc bridge now emits an explicit `And(count, 127)` before
/// every 128-bit shift (matching MIR `Shl`/`Shr` masked semantics), so the
/// precondition this quantification encodes is established by construction.
/// Treat a "Verified" verdict for the i128 shift family as conditional on that
/// mask — it is NOT a statement about unmasked out-of-range counts.
pub fn proof_ishl_i128() -> ProofObligation {
    use crate::trust_ir_semantics::encode_trust_ir_shift;
    use trust_cg_lower::instructions::Opcode;
    use trust_cg_lower::types::Type;

    let a_lo = SmtExpr::var("a_lo", 64);
    let a_hi = SmtExpr::var("a_hi", 64);
    let shift = SmtExpr::var("shift", 7);

    let trust_ir = encode_trust_ir_shift(
        &Opcode::Ishl,
        Type::I128,
        a_hi.clone().concat(a_lo.clone()),
        zext_i128_shift_to_128(shift.clone()),
    );

    let shift64 = zext_i128_shift_to_64(shift);
    let zero = SmtExpr::bv_const(0, 64);
    let c64 = SmtExpr::bv_const(64, 64);

    let neg_shift = c64.clone().bvsub(shift64.clone());
    let lo_spill_raw = aarch64_lsrv64(a_lo.clone(), neg_shift);
    let lo_spill = SmtExpr::ite(
        shift64.clone().eq_expr(zero.clone()),
        zero.clone(),
        lo_spill_raw,
    );
    let hi_shifted = aarch64_lslv64(a_hi, shift64.clone());
    let hi_normal = hi_shifted.bvor(lo_spill);
    let lo_normal = aarch64_lslv64(a_lo.clone(), shift64.clone());
    let big_shift = shift64.clone().bvsub(c64.clone());
    let hi_big = aarch64_lslv64(a_lo, big_shift);
    let is_big = shift64.bvuge(c64);
    let dst_lo = SmtExpr::ite(is_big.clone(), zero, lo_normal);
    let dst_hi = SmtExpr::ite(is_big, hi_big, hi_normal);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "Ishl_I128 -> LSLV/LSRV/ORR/CSEL pair".to_string(),
        trust_ir_expr: trust_ir,
        aarch64_expr: dst_hi.concat(dst_lo),
        inputs: vec![
            ("a_lo".to_string(), 64),
            ("a_hi".to_string(), 64),
            ("shift".to_string(), 7),
        ],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// Build the proof obligation for i128 logical right shift.
///
/// This mirrors [`proof_ishl_i128`], including the `shift == 0` spill guard
/// needed because AArch64 register shifts mask limb shift amounts modulo 64.
pub fn proof_ushr_i128() -> ProofObligation {
    use crate::trust_ir_semantics::encode_trust_ir_shift;
    use trust_cg_lower::instructions::Opcode;
    use trust_cg_lower::types::Type;

    let a_lo = SmtExpr::var("a_lo", 64);
    let a_hi = SmtExpr::var("a_hi", 64);
    let shift = SmtExpr::var("shift", 7);

    let trust_ir = encode_trust_ir_shift(
        &Opcode::Ushr,
        Type::I128,
        a_hi.clone().concat(a_lo.clone()),
        zext_i128_shift_to_128(shift.clone()),
    );

    let shift64 = zext_i128_shift_to_64(shift);
    let zero = SmtExpr::bv_const(0, 64);
    let c64 = SmtExpr::bv_const(64, 64);

    let neg_shift = c64.clone().bvsub(shift64.clone());
    let hi_spill_raw = aarch64_lslv64(a_hi.clone(), neg_shift);
    let hi_spill = SmtExpr::ite(
        shift64.clone().eq_expr(zero.clone()),
        zero.clone(),
        hi_spill_raw,
    );
    let lo_shifted = aarch64_lsrv64(a_lo, shift64.clone());
    let lo_normal = lo_shifted.bvor(hi_spill);
    let hi_normal = aarch64_lsrv64(a_hi.clone(), shift64.clone());
    let big_shift = shift64.clone().bvsub(c64.clone());
    let lo_big = aarch64_lsrv64(a_hi, big_shift);
    let is_big = shift64.bvuge(c64);
    let dst_hi = SmtExpr::ite(is_big.clone(), zero, hi_normal);
    let dst_lo = SmtExpr::ite(is_big, lo_big, lo_normal);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "Ushr_I128 -> LSRV/LSLV/ORR/CSEL pair".to_string(),
        trust_ir_expr: trust_ir,
        aarch64_expr: dst_hi.concat(dst_lo),
        inputs: vec![
            ("a_lo".to_string(), 64),
            ("a_hi".to_string(), 64),
            ("shift".to_string(), 7),
        ],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// Build the proof obligation for i128 arithmetic right shift.
///
/// The high half uses ASRV for sign-extending limb shifts; the `shift >= 64`
/// case selects `src_hi >>s (shift - 64)` for the low half and `src_hi >>s 63`
/// for the sign-filled high half.
pub fn proof_sshr_i128() -> ProofObligation {
    use crate::trust_ir_semantics::encode_trust_ir_shift;
    use trust_cg_lower::instructions::Opcode;
    use trust_cg_lower::types::Type;

    let a_lo = SmtExpr::var("a_lo", 64);
    let a_hi = SmtExpr::var("a_hi", 64);
    let shift = SmtExpr::var("shift", 7);

    let trust_ir = encode_trust_ir_shift(
        &Opcode::Sshr,
        Type::I128,
        a_hi.clone().concat(a_lo.clone()),
        zext_i128_shift_to_128(shift.clone()),
    );

    let shift64 = zext_i128_shift_to_64(shift);
    let zero = SmtExpr::bv_const(0, 64);
    let c63 = SmtExpr::bv_const(63, 64);
    let c64 = SmtExpr::bv_const(64, 64);

    let neg_shift = c64.clone().bvsub(shift64.clone());
    let hi_spill_raw = aarch64_lslv64(a_hi.clone(), neg_shift);
    let hi_spill = SmtExpr::ite(shift64.clone().eq_expr(zero.clone()), zero, hi_spill_raw);
    let lo_shifted = aarch64_lsrv64(a_lo, shift64.clone());
    let lo_normal = lo_shifted.bvor(hi_spill);
    let hi_normal = aarch64_asrv64(a_hi.clone(), shift64.clone());
    let big_shift = shift64.clone().bvsub(c64.clone());
    let lo_big = aarch64_asrv64(a_hi.clone(), big_shift);
    let hi_sign = aarch64_asrv64(a_hi, c63);
    let is_big = shift64.bvuge(c64);
    let dst_hi = SmtExpr::ite(is_big.clone(), hi_sign, hi_normal);
    let dst_lo = SmtExpr::ite(is_big, lo_big, lo_normal);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "Sshr_I128 -> ASRV/LSRV/LSLV/ORR/CSEL pair".to_string(),
        trust_ir_expr: trust_ir,
        aarch64_expr: dst_hi.concat(dst_lo),
        inputs: vec![
            ("a_lo".to_string(), 64),
            ("a_hi".to_string(), 64),
            ("shift".to_string(), 7),
        ],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// Return all standard arithmetic lowering rule proofs.
pub fn all_arithmetic_proofs() -> Vec<ProofObligation> {
    vec![
        // I8 (exhaustive verification — all 2^16 or 2^8 input combos tested)
        proof_iadd_i8(),
        proof_isub_i8(),
        proof_imul_i8(),
        proof_neg_i8(),
        // I16 (statistical verification — edge cases + random sampling)
        proof_iadd_i16(),
        proof_isub_i16(),
        proof_imul_i16(),
        proof_neg_i16(),
        // I32 (statistical verification)
        proof_iadd_i32(),
        proof_isub_i32(),
        proof_imul_i32(),
        proof_neg_i32(),
        // I64 (statistical verification)
        proof_iadd_i64(),
        proof_isub_i64(),
        proof_imul_i64(),
        proof_neg_i64(),
        // Generic AArch64 multiply-add/subtract instruction semantics.
        proof_aarch64_madd_rr_generic(),
        proof_aarch64_msub_rr_generic(),
        // Division (statistical verification, with NonZeroDivisor precondition)
        proof_sdiv_i32(),
        proof_sdiv_i64(),
        proof_udiv_i32(),
        proof_udiv_i64(),
        // I128 multi-register (statistical verification on 64-bit limbs and
        // full 128-bit shift concatenations; see #324).
        proof_iadd_i128_lo(),
        proof_iadd_i128_hi(),
        proof_isub_i128_lo(),
        proof_isub_i128_hi(),
        proof_imul_i128_lo(),
        proof_imul_i128_hi(),
        proof_ishl_i128(),
        proof_ushr_i128(),
        proof_sshr_i128(),
    ]
}

// ---------------------------------------------------------------------------
// Floating-point lowering proofs
// ---------------------------------------------------------------------------

/// Build the proof obligation for: `trust_ir::Fadd(F32, a, b) -> FADD Sd, Sn, Sm`
///
/// Verifies that the trust_ir FP add semantics (`fp.add(RNE, a, b)`) match
/// the AArch64 FADD instruction semantics for single-precision.
pub fn proof_fadd_f32() -> ProofObligation {
    use crate::aarch64_semantics::{FPSize, encode_fadd_rr};
    use crate::trust_ir_semantics::encode_trust_ir_fp_binop;
    use trust_cg_lower::instructions::Opcode;
    use trust_cg_lower::types::Type;

    let a = SmtExpr::bv_bits_to_fp(SmtExpr::var("fp_a_bits", 32), 8, 24);
    let b = SmtExpr::bv_bits_to_fp(SmtExpr::var("fp_b_bits", 32), 8, 24);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "Fadd_F32 -> FADD Sd".to_string(),
        trust_ir_expr: encode_trust_ir_fp_binop(&Opcode::Fadd, Type::F32, a.clone(), b.clone()),
        aarch64_expr: encode_fadd_rr(FPSize::Single, a, b),
        inputs: vec![("fp_a_bits".to_string(), 32), ("fp_b_bits".to_string(), 32)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// Build the proof obligation for: `trust_ir::Fadd(F64, a, b) -> FADD Dd, Dn, Dm`
pub fn proof_fadd_f64() -> ProofObligation {
    use crate::aarch64_semantics::{FPSize, encode_fadd_rr};
    use crate::trust_ir_semantics::encode_trust_ir_fp_binop;
    use trust_cg_lower::instructions::Opcode;
    use trust_cg_lower::types::Type;

    let a = SmtExpr::bv_bits_to_fp(SmtExpr::var("fp_a_bits", 64), 11, 53);
    let b = SmtExpr::bv_bits_to_fp(SmtExpr::var("fp_b_bits", 64), 11, 53);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "Fadd_F64 -> FADD Dd".to_string(),
        trust_ir_expr: encode_trust_ir_fp_binop(&Opcode::Fadd, Type::F64, a.clone(), b.clone()),
        aarch64_expr: encode_fadd_rr(FPSize::Double, a, b),
        inputs: vec![("fp_a_bits".to_string(), 64), ("fp_b_bits".to_string(), 64)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// Build the proof obligation for: `trust_ir::Fsub(F32, a, b) -> FSUB Sd, Sn, Sm`
pub fn proof_fsub_f32() -> ProofObligation {
    use crate::aarch64_semantics::{FPSize, encode_fsub_rr};
    use crate::trust_ir_semantics::encode_trust_ir_fp_binop;
    use trust_cg_lower::instructions::Opcode;
    use trust_cg_lower::types::Type;

    let a = SmtExpr::bv_bits_to_fp(SmtExpr::var("fp_a_bits", 32), 8, 24);
    let b = SmtExpr::bv_bits_to_fp(SmtExpr::var("fp_b_bits", 32), 8, 24);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "Fsub_F32 -> FSUB Sd".to_string(),
        trust_ir_expr: encode_trust_ir_fp_binop(&Opcode::Fsub, Type::F32, a.clone(), b.clone()),
        aarch64_expr: encode_fsub_rr(FPSize::Single, a, b),
        inputs: vec![("fp_a_bits".to_string(), 32), ("fp_b_bits".to_string(), 32)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// Build the proof obligation for: `trust_ir::Fsub(F64, a, b) -> FSUB Dd, Dn, Dm`
pub fn proof_fsub_f64() -> ProofObligation {
    use crate::aarch64_semantics::{FPSize, encode_fsub_rr};
    use crate::trust_ir_semantics::encode_trust_ir_fp_binop;
    use trust_cg_lower::instructions::Opcode;
    use trust_cg_lower::types::Type;

    let a = SmtExpr::bv_bits_to_fp(SmtExpr::var("fp_a_bits", 64), 11, 53);
    let b = SmtExpr::bv_bits_to_fp(SmtExpr::var("fp_b_bits", 64), 11, 53);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "Fsub_F64 -> FSUB Dd".to_string(),
        trust_ir_expr: encode_trust_ir_fp_binop(&Opcode::Fsub, Type::F64, a.clone(), b.clone()),
        aarch64_expr: encode_fsub_rr(FPSize::Double, a, b),
        inputs: vec![("fp_a_bits".to_string(), 64), ("fp_b_bits".to_string(), 64)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// Build the proof obligation for: `trust_ir::Fmul(F32, a, b) -> FMUL Sd, Sn, Sm`
pub fn proof_fmul_f32() -> ProofObligation {
    use crate::aarch64_semantics::{FPSize, encode_fmul_rr};
    use crate::trust_ir_semantics::encode_trust_ir_fp_binop;
    use trust_cg_lower::instructions::Opcode;
    use trust_cg_lower::types::Type;

    let a = SmtExpr::bv_bits_to_fp(SmtExpr::var("fp_a_bits", 32), 8, 24);
    let b = SmtExpr::bv_bits_to_fp(SmtExpr::var("fp_b_bits", 32), 8, 24);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "Fmul_F32 -> FMUL Sd".to_string(),
        trust_ir_expr: encode_trust_ir_fp_binop(&Opcode::Fmul, Type::F32, a.clone(), b.clone()),
        aarch64_expr: encode_fmul_rr(FPSize::Single, a, b),
        inputs: vec![("fp_a_bits".to_string(), 32), ("fp_b_bits".to_string(), 32)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// Build the proof obligation for: `trust_ir::Fmul(F64, a, b) -> FMUL Dd, Dn, Dm`
pub fn proof_fmul_f64() -> ProofObligation {
    use crate::aarch64_semantics::{FPSize, encode_fmul_rr};
    use crate::trust_ir_semantics::encode_trust_ir_fp_binop;
    use trust_cg_lower::instructions::Opcode;
    use trust_cg_lower::types::Type;

    let a = SmtExpr::bv_bits_to_fp(SmtExpr::var("fp_a_bits", 64), 11, 53);
    let b = SmtExpr::bv_bits_to_fp(SmtExpr::var("fp_b_bits", 64), 11, 53);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "Fmul_F64 -> FMUL Dd".to_string(),
        trust_ir_expr: encode_trust_ir_fp_binop(&Opcode::Fmul, Type::F64, a.clone(), b.clone()),
        aarch64_expr: encode_fmul_rr(FPSize::Double, a, b),
        inputs: vec![("fp_a_bits".to_string(), 64), ("fp_b_bits".to_string(), 64)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// Build the proof obligation for: `trust_ir::Fneg(F32, a) -> FNEG Sd, Sn`
pub fn proof_fneg_f32() -> ProofObligation {
    use crate::aarch64_semantics::{FPSize, encode_fneg};
    use crate::trust_ir_semantics::encode_trust_ir_fneg;
    use trust_cg_lower::types::Type;

    let a = SmtExpr::bv_bits_to_fp(SmtExpr::var("fp_a_bits", 32), 8, 24);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "Fneg_F32 -> FNEG Sd".to_string(),
        trust_ir_expr: encode_trust_ir_fneg(Type::F32, a.clone()),
        aarch64_expr: encode_fneg(FPSize::Single, a),
        inputs: vec![("fp_a_bits".to_string(), 32)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// Build the proof obligation for: `trust_ir::Fneg(F64, a) -> FNEG Dd, Dn`
pub fn proof_fneg_f64() -> ProofObligation {
    use crate::aarch64_semantics::{FPSize, encode_fneg};
    use crate::trust_ir_semantics::encode_trust_ir_fneg;
    use trust_cg_lower::types::Type;

    let a = SmtExpr::bv_bits_to_fp(SmtExpr::var("fp_a_bits", 64), 11, 53);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "Fneg_F64 -> FNEG Dd".to_string(),
        trust_ir_expr: encode_trust_ir_fneg(Type::F64, a.clone()),
        aarch64_expr: encode_fneg(FPSize::Double, a),
        inputs: vec![("fp_a_bits".to_string(), 64)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// `trust_ir::Ffloor(F32, a) -> FRINTM Sd, Sn` (round to integral toward -inf).
pub fn proof_ffloor_f32() -> ProofObligation {
    use crate::aarch64_semantics::{FPSize, encode_frintm};
    use crate::trust_ir_semantics::encode_trust_ir_ffloor;
    use trust_cg_lower::types::Type;
    let a = SmtExpr::bv_bits_to_fp(SmtExpr::var("fp_a_bits", 32), 8, 24);
    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "Ffloor_F32 -> FRINTM Sd".to_string(),
        trust_ir_expr: encode_trust_ir_ffloor(Type::F32, a.clone()),
        aarch64_expr: encode_frintm(FPSize::Single, a),
        inputs: vec![("fp_a_bits".to_string(), 32)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// `trust_ir::Ffloor(F64, a) -> FRINTM Dd, Dn`.
pub fn proof_ffloor_f64() -> ProofObligation {
    use crate::aarch64_semantics::{FPSize, encode_frintm};
    use crate::trust_ir_semantics::encode_trust_ir_ffloor;
    use trust_cg_lower::types::Type;
    let a = SmtExpr::bv_bits_to_fp(SmtExpr::var("fp_a_bits", 64), 11, 53);
    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "Ffloor_F64 -> FRINTM Dd".to_string(),
        trust_ir_expr: encode_trust_ir_ffloor(Type::F64, a.clone()),
        aarch64_expr: encode_frintm(FPSize::Double, a),
        inputs: vec![("fp_a_bits".to_string(), 64)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// `trust_ir::Fceil(F32, a) -> FRINTP Sd, Sn` (round to integral toward +inf).
pub fn proof_fceil_f32() -> ProofObligation {
    use crate::aarch64_semantics::{FPSize, encode_frintp};
    use crate::trust_ir_semantics::encode_trust_ir_fceil;
    use trust_cg_lower::types::Type;
    let a = SmtExpr::bv_bits_to_fp(SmtExpr::var("fp_a_bits", 32), 8, 24);
    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "Fceil_F32 -> FRINTP Sd".to_string(),
        trust_ir_expr: encode_trust_ir_fceil(Type::F32, a.clone()),
        aarch64_expr: encode_frintp(FPSize::Single, a),
        inputs: vec![("fp_a_bits".to_string(), 32)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// `trust_ir::Fceil(F64, a) -> FRINTP Dd, Dn`.
pub fn proof_fceil_f64() -> ProofObligation {
    use crate::aarch64_semantics::{FPSize, encode_frintp};
    use crate::trust_ir_semantics::encode_trust_ir_fceil;
    use trust_cg_lower::types::Type;
    let a = SmtExpr::bv_bits_to_fp(SmtExpr::var("fp_a_bits", 64), 11, 53);
    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "Fceil_F64 -> FRINTP Dd".to_string(),
        trust_ir_expr: encode_trust_ir_fceil(Type::F64, a.clone()),
        aarch64_expr: encode_frintp(FPSize::Double, a),
        inputs: vec![("fp_a_bits".to_string(), 64)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// `trust_ir::Ftrunc(F32, a) -> FRINTZ Sd, Sn` (round to integral toward zero).
pub fn proof_ftrunc_f32() -> ProofObligation {
    use crate::aarch64_semantics::{FPSize, encode_frintz};
    use crate::trust_ir_semantics::encode_trust_ir_ftrunc;
    use trust_cg_lower::types::Type;
    let a = SmtExpr::bv_bits_to_fp(SmtExpr::var("fp_a_bits", 32), 8, 24);
    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "Ftrunc_F32 -> FRINTZ Sd".to_string(),
        trust_ir_expr: encode_trust_ir_ftrunc(Type::F32, a.clone()),
        aarch64_expr: encode_frintz(FPSize::Single, a),
        inputs: vec![("fp_a_bits".to_string(), 32)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// `trust_ir::Ftrunc(F64, a) -> FRINTZ Dd, Dn`.
pub fn proof_ftrunc_f64() -> ProofObligation {
    use crate::aarch64_semantics::{FPSize, encode_frintz};
    use crate::trust_ir_semantics::encode_trust_ir_ftrunc;
    use trust_cg_lower::types::Type;
    let a = SmtExpr::bv_bits_to_fp(SmtExpr::var("fp_a_bits", 64), 11, 53);
    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "Ftrunc_F64 -> FRINTZ Dd".to_string(),
        trust_ir_expr: encode_trust_ir_ftrunc(Type::F64, a.clone()),
        aarch64_expr: encode_frintz(FPSize::Double, a),
        inputs: vec![("fp_a_bits".to_string(), 64)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// Build the proof obligation for: `trust_ir::Fdiv(F32, a, b) -> FDIV Sd, Sn, Sm`
///
/// Reference: ARM DDI 0487, C7.2.77 FDIV (scalar).
pub fn proof_fdiv_f32() -> ProofObligation {
    use crate::aarch64_semantics::{FPSize, encode_fdiv_rr};
    use crate::trust_ir_semantics::encode_trust_ir_fp_binop;
    use trust_cg_lower::instructions::Opcode;
    use trust_cg_lower::types::Type;

    let a = SmtExpr::bv_bits_to_fp(SmtExpr::var("fp_a_bits", 32), 8, 24);
    let b = SmtExpr::bv_bits_to_fp(SmtExpr::var("fp_b_bits", 32), 8, 24);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "Fdiv_F32 -> FDIV Sd".to_string(),
        trust_ir_expr: encode_trust_ir_fp_binop(&Opcode::Fdiv, Type::F32, a.clone(), b.clone()),
        aarch64_expr: encode_fdiv_rr(FPSize::Single, a, b),
        inputs: vec![("fp_a_bits".to_string(), 32), ("fp_b_bits".to_string(), 32)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// Build the proof obligation for: `trust_ir::Fdiv(F64, a, b) -> FDIV Dd, Dn, Dm`
///
/// Reference: ARM DDI 0487, C7.2.77 FDIV (scalar).
pub fn proof_fdiv_f64() -> ProofObligation {
    use crate::aarch64_semantics::{FPSize, encode_fdiv_rr};
    use crate::trust_ir_semantics::encode_trust_ir_fp_binop;
    use trust_cg_lower::instructions::Opcode;
    use trust_cg_lower::types::Type;

    let a = SmtExpr::bv_bits_to_fp(SmtExpr::var("fp_a_bits", 64), 11, 53);
    let b = SmtExpr::bv_bits_to_fp(SmtExpr::var("fp_b_bits", 64), 11, 53);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "Fdiv_F64 -> FDIV Dd".to_string(),
        trust_ir_expr: encode_trust_ir_fp_binop(&Opcode::Fdiv, Type::F64, a.clone(), b.clone()),
        aarch64_expr: encode_fdiv_rr(FPSize::Double, a, b),
        inputs: vec![("fp_a_bits".to_string(), 64), ("fp_b_bits".to_string(), 64)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

// ---------------------------------------------------------------------------
// Floating-point absolute value and square root lowering proofs
// ---------------------------------------------------------------------------

/// Build the proof obligation for: `trust_ir::Fabs(F32, a) -> FABS Sd, Sn`
///
/// Reference: ARM DDI 0487, C7.2.73 FABS (scalar).
pub fn proof_fabs_f32() -> ProofObligation {
    proof_fabs_bits(32, "Fabs_F32 -> FABS Sd")
}

/// Build the proof obligation for: `trust_ir::Fabs(F64, a) -> FABS Dd, Dn`
///
/// Reference: ARM DDI 0487, C7.2.73 FABS (scalar).
pub fn proof_fabs_f64() -> ProofObligation {
    proof_fabs_bits(64, "Fabs_F64 -> FABS Dd")
}

/// Full raw-bit FABS obligation. TrustIR's `UnOp::FAbs` contract clears
/// the sign bit; the source mask retains every exponent and fraction bit.
/// The machine model independently concatenates zero with bits N-2 through 0,
/// matching FABS's register bit operation, including signed zero and NaN payloads.
/// These symbolic operands replace the legacy constant-zero FP placeholders.
fn proof_fabs_bits(width: u32, name: &str) -> ProofObligation {
    let input = SmtExpr::var("a", width);
    let magnitude_mask = (1u64 << (width - 1)) - 1;
    ProofObligation {
        machine_side_provenance: MachineSideProvenance::StaticDb,
        name: name.to_string(),
        trust_ir_expr: input
            .clone()
            .bvand(SmtExpr::bv_const(magnitude_mask, width)),
        aarch64_expr: SmtExpr::bv_const(0, 1).concat(input.extract(width - 2, 0)),
        inputs: vec![("a".to_string(), width)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(TransvalCheckKind::InstructionLowering),
    }
}

/// Build the proof obligation for: `trust_ir::Fsqrt(F32, a) -> FSQRT Sd, Sn`
///
/// Reference: ARM DDI 0487, C7.2.160 FSQRT (scalar).
pub fn proof_fsqrt_f32() -> ProofObligation {
    use crate::aarch64_semantics::{FPSize, encode_fsqrt};
    use crate::trust_ir_semantics::encode_trust_ir_fsqrt;
    use trust_cg_lower::types::Type;

    let a = SmtExpr::bv_bits_to_fp(SmtExpr::var("fp_a_bits", 32), 8, 24);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "Fsqrt_F32 -> FSQRT Sd".to_string(),
        trust_ir_expr: encode_trust_ir_fsqrt(Type::F32, a.clone()),
        aarch64_expr: encode_fsqrt(FPSize::Single, a),
        inputs: vec![("fp_a_bits".to_string(), 32)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// Build the proof obligation for: `trust_ir::Fsqrt(F64, a) -> FSQRT Dd, Dn`
///
/// Reference: ARM DDI 0487, C7.2.160 FSQRT (scalar).
pub fn proof_fsqrt_f64() -> ProofObligation {
    use crate::aarch64_semantics::{FPSize, encode_fsqrt};
    use crate::trust_ir_semantics::encode_trust_ir_fsqrt;
    use trust_cg_lower::types::Type;

    let a = SmtExpr::bv_bits_to_fp(SmtExpr::var("fp_a_bits", 64), 11, 53);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "Fsqrt_F64 -> FSQRT Dd".to_string(),
        trust_ir_expr: encode_trust_ir_fsqrt(Type::F64, a.clone()),
        aarch64_expr: encode_fsqrt(FPSize::Double, a),
        inputs: vec![("fp_a_bits".to_string(), 64)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

// ---------------------------------------------------------------------------
// Floating-point comparison lowering proofs: trust_ir::Fcmp -> FCMP + CSET
// ---------------------------------------------------------------------------

/// Generic FCMP proof builder. Builds a proof that
/// `trust_ir::Fcmp(cond, ty, a, b)` produces the same BV1 result as the
/// AArch64 `FCMP + CSET` sequence encoded by `encode_fcmp`.
///
/// Reference: ARM DDI 0487, C7.2.76 FCMP.
fn proof_fcmp_generic(
    cond: trust_cg_lower::instructions::FloatCC,
    is_f32: bool,
    name: &str,
) -> ProofObligation {
    use crate::aarch64_semantics::{FPSize, encode_fcmp};
    use crate::trust_ir_semantics::encode_trust_ir_fcmp;
    use trust_cg_lower::types::Type;

    let (ty, fp_size, eb, sb) = if is_f32 {
        (Type::F32, FPSize::Single, 8u32, 24u32)
    } else {
        (Type::F64, FPSize::Double, 11u32, 53u32)
    };

    let width = eb + sb;
    let a = SmtExpr::bv_bits_to_fp(SmtExpr::var("a_bits", width), eb, sb);
    let b = SmtExpr::bv_bits_to_fp(SmtExpr::var("b_bits", width), eb, sb);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: name.to_string(),
        trust_ir_expr: encode_trust_ir_fcmp(&cond, ty, a.clone(), b.clone()),
        aarch64_expr: encode_fcmp(fp_size, a, b, &cond),
        inputs: vec![("a_bits".into(), width), ("b_bits".into(), width)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// Proof: trust_ir::Fcmp(Equal, F32) -> FCMP Sn, Sm + CSET (EQ)
pub fn proof_fcmp_eq_f32() -> ProofObligation {
    use trust_cg_lower::instructions::FloatCC;
    proof_fcmp_generic(FloatCC::Equal, true, "Fcmp_Eq_F32 -> FCMP+CSET")
}

/// Proof: trust_ir::Fcmp(Equal, F64) -> FCMP Dn, Dm + CSET (EQ)
pub fn proof_fcmp_eq_f64() -> ProofObligation {
    use trust_cg_lower::instructions::FloatCC;
    proof_fcmp_generic(FloatCC::Equal, false, "Fcmp_Eq_F64 -> FCMP+CSET")
}

/// Proof: trust_ir::Fcmp(NotEqual, F32) -> FCMP + CSET (NE)
pub fn proof_fcmp_ne_f32() -> ProofObligation {
    use trust_cg_lower::instructions::FloatCC;
    proof_fcmp_generic(FloatCC::NotEqual, true, "Fcmp_NE_F32 -> FCMP+CSET")
}

/// Proof: trust_ir::Fcmp(NotEqual, F64) -> FCMP + CSET (NE)
pub fn proof_fcmp_ne_f64() -> ProofObligation {
    use trust_cg_lower::instructions::FloatCC;
    proof_fcmp_generic(FloatCC::NotEqual, false, "Fcmp_NE_F64 -> FCMP+CSET")
}

/// Proof: trust_ir::Fcmp(LessThan, F32) -> FCMP + CSET (LT)
pub fn proof_fcmp_lt_f32() -> ProofObligation {
    use trust_cg_lower::instructions::FloatCC;
    proof_fcmp_generic(FloatCC::LessThan, true, "Fcmp_LT_F32 -> FCMP+CSET")
}

/// Proof: trust_ir::Fcmp(LessThan, F64) -> FCMP + CSET (LT)
pub fn proof_fcmp_lt_f64() -> ProofObligation {
    use trust_cg_lower::instructions::FloatCC;
    proof_fcmp_generic(FloatCC::LessThan, false, "Fcmp_LT_F64 -> FCMP+CSET")
}

/// Proof: trust_ir::Fcmp(LessThanOrEqual, F32) -> FCMP + CSET (LE)
pub fn proof_fcmp_le_f32() -> ProofObligation {
    use trust_cg_lower::instructions::FloatCC;
    proof_fcmp_generic(FloatCC::LessThanOrEqual, true, "Fcmp_LE_F32 -> FCMP+CSET")
}

/// Proof: trust_ir::Fcmp(LessThanOrEqual, F64) -> FCMP + CSET (LE)
pub fn proof_fcmp_le_f64() -> ProofObligation {
    use trust_cg_lower::instructions::FloatCC;
    proof_fcmp_generic(FloatCC::LessThanOrEqual, false, "Fcmp_LE_F64 -> FCMP+CSET")
}

/// Proof: trust_ir::Fcmp(GreaterThan, F32) -> FCMP + CSET (GT)
pub fn proof_fcmp_gt_f32() -> ProofObligation {
    use trust_cg_lower::instructions::FloatCC;
    proof_fcmp_generic(FloatCC::GreaterThan, true, "Fcmp_GT_F32 -> FCMP+CSET")
}

/// Proof: trust_ir::Fcmp(GreaterThan, F64) -> FCMP + CSET (GT)
pub fn proof_fcmp_gt_f64() -> ProofObligation {
    use trust_cg_lower::instructions::FloatCC;
    proof_fcmp_generic(FloatCC::GreaterThan, false, "Fcmp_GT_F64 -> FCMP+CSET")
}

/// Proof: trust_ir::Fcmp(GreaterThanOrEqual, F32) -> FCMP + CSET (GE)
pub fn proof_fcmp_ge_f32() -> ProofObligation {
    use trust_cg_lower::instructions::FloatCC;
    proof_fcmp_generic(
        FloatCC::GreaterThanOrEqual,
        true,
        "Fcmp_GE_F32 -> FCMP+CSET",
    )
}

/// Proof: trust_ir::Fcmp(GreaterThanOrEqual, F64) -> FCMP + CSET (GE)
pub fn proof_fcmp_ge_f64() -> ProofObligation {
    use trust_cg_lower::instructions::FloatCC;
    proof_fcmp_generic(
        FloatCC::GreaterThanOrEqual,
        false,
        "Fcmp_GE_F64 -> FCMP+CSET",
    )
}

/// Proof: trust_ir::Fcmp(Ordered, F32) -> FCMP + CSET (ORD)
pub fn proof_fcmp_ord_f32() -> ProofObligation {
    use trust_cg_lower::instructions::FloatCC;
    proof_fcmp_generic(FloatCC::Ordered, true, "Fcmp_Ord_F32 -> FCMP+CSET")
}

/// Proof: trust_ir::Fcmp(Ordered, F64) -> FCMP + CSET (ORD)
pub fn proof_fcmp_ord_f64() -> ProofObligation {
    use trust_cg_lower::instructions::FloatCC;
    proof_fcmp_generic(FloatCC::Ordered, false, "Fcmp_Ord_F64 -> FCMP+CSET")
}

/// Proof: trust_ir::Fcmp(Unordered, F32) -> FCMP + CSET (UNO)
pub fn proof_fcmp_uno_f32() -> ProofObligation {
    use trust_cg_lower::instructions::FloatCC;
    proof_fcmp_generic(FloatCC::Unordered, true, "Fcmp_Uno_F32 -> FCMP+CSET")
}

/// Proof: trust_ir::Fcmp(Unordered, F64) -> FCMP + CSET (UNO)
pub fn proof_fcmp_uno_f64() -> ProofObligation {
    use trust_cg_lower::instructions::FloatCC;
    proof_fcmp_generic(FloatCC::Unordered, false, "Fcmp_Uno_F64 -> FCMP+CSET")
}

/// Proof: trust_ir::Fcmp(UnorderedEqual, F32) -> FCMP + CSET (UEQ)
pub fn proof_fcmp_ueq_f32() -> ProofObligation {
    use trust_cg_lower::instructions::FloatCC;
    proof_fcmp_generic(FloatCC::UnorderedEqual, true, "Fcmp_UEQ_F32 -> FCMP+CSET")
}

/// Proof: trust_ir::Fcmp(UnorderedEqual, F64) -> FCMP + CSET (UEQ)
pub fn proof_fcmp_ueq_f64() -> ProofObligation {
    use trust_cg_lower::instructions::FloatCC;
    proof_fcmp_generic(FloatCC::UnorderedEqual, false, "Fcmp_UEQ_F64 -> FCMP+CSET")
}

/// Proof: trust_ir::Fcmp(UnorderedNotEqual, F32) -> FCMP + CSET (UNE)
pub fn proof_fcmp_une_f32() -> ProofObligation {
    use trust_cg_lower::instructions::FloatCC;
    proof_fcmp_generic(
        FloatCC::UnorderedNotEqual,
        true,
        "Fcmp_UNE_F32 -> FCMP+CSET",
    )
}

/// Proof: trust_ir::Fcmp(UnorderedNotEqual, F64) -> FCMP + CSET (UNE)
pub fn proof_fcmp_une_f64() -> ProofObligation {
    use trust_cg_lower::instructions::FloatCC;
    proof_fcmp_generic(
        FloatCC::UnorderedNotEqual,
        false,
        "Fcmp_UNE_F64 -> FCMP+CSET",
    )
}

/// Proof: trust_ir::Fcmp(UnorderedLessThan, F32) -> FCMP + CSET (ULT)
pub fn proof_fcmp_ult_f32() -> ProofObligation {
    use trust_cg_lower::instructions::FloatCC;
    proof_fcmp_generic(
        FloatCC::UnorderedLessThan,
        true,
        "Fcmp_ULT_F32 -> FCMP+CSET",
    )
}

/// Proof: trust_ir::Fcmp(UnorderedLessThan, F64) -> FCMP + CSET (ULT)
pub fn proof_fcmp_ult_f64() -> ProofObligation {
    use trust_cg_lower::instructions::FloatCC;
    proof_fcmp_generic(
        FloatCC::UnorderedLessThan,
        false,
        "Fcmp_ULT_F64 -> FCMP+CSET",
    )
}

/// Proof: trust_ir::Fcmp(UnorderedLessThanOrEqual, F32) -> FCMP + CSET (ULE)
pub fn proof_fcmp_ule_f32() -> ProofObligation {
    use trust_cg_lower::instructions::FloatCC;
    proof_fcmp_generic(
        FloatCC::UnorderedLessThanOrEqual,
        true,
        "Fcmp_ULE_F32 -> FCMP+CSET",
    )
}

/// Proof: trust_ir::Fcmp(UnorderedLessThanOrEqual, F64) -> FCMP + CSET (ULE)
pub fn proof_fcmp_ule_f64() -> ProofObligation {
    use trust_cg_lower::instructions::FloatCC;
    proof_fcmp_generic(
        FloatCC::UnorderedLessThanOrEqual,
        false,
        "Fcmp_ULE_F64 -> FCMP+CSET",
    )
}

/// Proof: trust_ir::Fcmp(UnorderedGreaterThan, F32) -> FCMP + CSET (UGT)
pub fn proof_fcmp_ugt_f32() -> ProofObligation {
    use trust_cg_lower::instructions::FloatCC;
    proof_fcmp_generic(
        FloatCC::UnorderedGreaterThan,
        true,
        "Fcmp_UGT_F32 -> FCMP+CSET",
    )
}

/// Proof: trust_ir::Fcmp(UnorderedGreaterThan, F64) -> FCMP + CSET (UGT)
pub fn proof_fcmp_ugt_f64() -> ProofObligation {
    use trust_cg_lower::instructions::FloatCC;
    proof_fcmp_generic(
        FloatCC::UnorderedGreaterThan,
        false,
        "Fcmp_UGT_F64 -> FCMP+CSET",
    )
}

/// Proof: trust_ir::Fcmp(UnorderedGreaterThanOrEqual, F32) -> FCMP + CSET (UGE)
pub fn proof_fcmp_uge_f32() -> ProofObligation {
    use trust_cg_lower::instructions::FloatCC;
    proof_fcmp_generic(
        FloatCC::UnorderedGreaterThanOrEqual,
        true,
        "Fcmp_UGE_F32 -> FCMP+CSET",
    )
}

/// Proof: trust_ir::Fcmp(UnorderedGreaterThanOrEqual, F64) -> FCMP + CSET (UGE)
pub fn proof_fcmp_uge_f64() -> ProofObligation {
    use trust_cg_lower::instructions::FloatCC;
    proof_fcmp_generic(
        FloatCC::UnorderedGreaterThanOrEqual,
        false,
        "Fcmp_UGE_F64 -> FCMP+CSET",
    )
}

/// Return all floating-point lowering rule proofs.
pub fn all_fp_lowering_proofs() -> Vec<ProofObligation> {
    vec![
        proof_fadd_f32(),
        proof_fadd_f64(),
        proof_fsub_f32(),
        proof_fsub_f64(),
        proof_fmul_f32(),
        proof_fmul_f64(),
        proof_fneg_f32(),
        proof_fneg_f64(),
        proof_fdiv_f32(),
        proof_fdiv_f64(),
        // FABS: absolute value (F32 + F64)
        proof_fabs_f32(),
        proof_fabs_f64(),
        // FRINTM/FRINTP/FRINTZ: round to integral floor/ceil/trunc (F32 + F64)
        proof_ffloor_f32(),
        proof_ffloor_f64(),
        proof_fceil_f32(),
        proof_fceil_f64(),
        proof_ftrunc_f32(),
        proof_ftrunc_f64(),
        // FSQRT: square root (F32 + F64)
        proof_fsqrt_f32(),
        proof_fsqrt_f64(),
        // FCMP: ordered comparisons (F32 + F64)
        proof_fcmp_eq_f32(),
        proof_fcmp_eq_f64(),
        proof_fcmp_ne_f32(),
        proof_fcmp_ne_f64(),
        proof_fcmp_lt_f32(),
        proof_fcmp_lt_f64(),
        proof_fcmp_le_f32(),
        proof_fcmp_le_f64(),
        proof_fcmp_gt_f32(),
        proof_fcmp_gt_f64(),
        proof_fcmp_ge_f32(),
        proof_fcmp_ge_f64(),
        // FCMP: ordering predicates (F32 + F64)
        proof_fcmp_ord_f32(),
        proof_fcmp_ord_f64(),
        proof_fcmp_uno_f32(),
        proof_fcmp_uno_f64(),
        // FCMP: unordered comparisons (F32 + F64)
        proof_fcmp_ueq_f32(),
        proof_fcmp_ueq_f64(),
        proof_fcmp_une_f32(),
        proof_fcmp_une_f64(),
        proof_fcmp_ult_f32(),
        proof_fcmp_ult_f64(),
        proof_fcmp_ule_f32(),
        proof_fcmp_ule_f64(),
        proof_fcmp_ugt_f32(),
        proof_fcmp_ugt_f64(),
        proof_fcmp_uge_f32(),
        proof_fcmp_uge_f64(),
    ]
}

// ---------------------------------------------------------------------------
// FCSEL (scalar FP conditional select) lowering proofs
// ---------------------------------------------------------------------------
//
// The AArch64 FP-`Select` isel path lowers a trust_ir `Select { cond }` over
// f32/f64 operands as `CMP sel, #0` then `FCSEL(dst, tval, fval,
// from_intcc(cond))` — replacing the old FMOV(FPR->GPR)x2 + CMP + integer CSEL +
// FMOV(GPR->FPR) cross-bank sequence. These obligations prove that whole
// sequence realizes the frontend select as a BIT-PRESERVING mux over the raw FP
// register bits.
//
// FAITHFULNESS / NON-DEGENERACY: each obligation ties two STRUCTURALLY DISTINCT
// SMT expressions that are provably equal:
//   * SOURCE  = `ite(icmp(cond, sel, 0), a, b)` — the frontend select, the
//               condition expressed DIRECTLY on the operands
//               (`encode_trust_ir_icmp`), and
//   * MACHINE = `ite(eval_condition(from_intcc(cond), encode_cmp(sel, 0)), a, b)`
//               — the FCSEL data path (`aarch64_semantics::encode_fcsel`) over
//               the NZCV flags a symbolic `CMP sel, #0` sets.
// The two condition predicates are structurally different (a direct integer
// compare vs a subtraction-derived NZCV flag read) yet provably equal, so
// `trust_ir_expr != aarch64_expr` (genuine, not X==X). The FP register bits
// `a`/`b` appear IDENTICALLY on both sides and are NEVER interpreted as floats —
// bit-preserving by construction, so NaN payloads (incl. signaling NaNs), signed
// zeros and denormals are safe with no FP reasoning at all. Two NEGATIVE controls
// (`fcsel_wrong_controls`) each perturb the MACHINE side and REFUTE:
//   (1) INVERTED-COND — `from_intcc(cond).invert()` selects the wrong branch,
//   (2) OPERAND-SWAP  — `ite(cond, b, a)` wires the true/false sources backwards.

/// One FCSEL obligation at FP data width `fp_width` (32 = S/f32, 64 = D/f64) and
/// trust_ir integer condition `cond` (applied to the i1 selector vs #0). SOURCE =
/// frontend `Select { cond }`, MACHINE = `CMP sel,#0` + `FCSEL cc`. Positive: the
/// two are provably equal, and the FP bits pass through bit-for-bit.
pub fn proof_fcsel(fp_width: u32, cond: trust_cg_lower::instructions::IntCC) -> ProofObligation {
    use crate::aarch64_semantics::encode_fcsel;
    use trust_cg_lower::isel::AArch64CC;
    use trust_cg_lower::types::Type;

    debug_assert!(fp_width == 32 || fp_width == 64);
    // The i1 selector is materialized/compared in a 32-bit GPR (`CMP Wn, #0`).
    let sel_width = 32u32;
    let sel = SmtExpr::var("sel", sel_width);
    let a = SmtExpr::var("a", fp_width);
    let b = SmtExpr::var("b", fp_width);
    let zero = SmtExpr::bv_const(0, sel_width);

    // SOURCE: trust_ir `Select { cond }` — the condition is the trust_ir
    // comparison `icmp(cond, sel, 0)` (a `B1` bitvector) being TRUE, i.e. its
    // low bit set (`== 1`); the select is then a pure mux over the raw FP bits a
    // (true) / b (false). The `== 1` truthiness test keeps the ite condition a
    // proper Bool (an `ite` over a bare `B1` is malformed SMT).
    let src_bit = crate::trust_ir_semantics::encode_trust_ir_icmp(
        &cond,
        Type::I32,
        sel.clone(),
        zero.clone(),
    );
    let src_pred = src_bit.eq_expr(SmtExpr::bv_const(1, 1));
    let source = SmtExpr::ite(src_pred, a.clone(), b.clone());

    // MACHINE: `CMP sel, #0` sets NZCV; `FCSEL(dst, a, b, from_intcc(cond))`.
    let flags = crate::nzcv::encode_cmp(sel, zero, sel_width);
    let machine = encode_fcsel(AArch64CC::from_intcc(cond), &flags, a, b);

    let (ty_tag, dst) = if fp_width == 32 {
        ("F32", "S")
    } else {
        ("F64", "D")
    };
    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: format!(
            "Fcsel_{ty_tag} {cond:?} -> CMP+FCSEL ({dst}): trust_ir Select == \
             bit-preserving FPR mux"
        ),
        trust_ir_expr: source,
        aarch64_expr: machine,
        inputs: vec![
            ("sel".to_string(), sel_width),
            ("a".to_string(), fp_width),
            ("b".to_string(), fp_width),
        ],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// The FAITHFUL FCSEL obligations across a spread of condition codes (Z-based,
/// N/V-based, C/Z-based) at both the S (f32) and D (f64) forms. Registered under
/// FloatingPoint (via [`all_fcsel_proofs`]); the coverage gate binds `FcselRR` to
/// the `fcsel_f32` / `fcsel_f64` names (both forms must discharge).
pub fn all_fcsel_proofs() -> Vec<ProofObligation> {
    use trust_cg_lower::instructions::IntCC;
    // A spread exercising the distinct NZCV flag reads: EQ/NE (Z), LT/GE
    // (N vs V), GT (Z & N==V), and HI (C & !Z ≡ unsigned != 0). Each is a
    // non-trivial condition against #0.
    const CONDS: [IntCC; 6] = [
        IntCC::Equal,
        IntCC::NotEqual,
        IntCC::SignedLessThan,
        IntCC::SignedGreaterThanOrEqual,
        IntCC::SignedGreaterThan,
        IntCC::UnsignedGreaterThan,
    ];
    let mut proofs = Vec::with_capacity(CONDS.len() * 2);
    for &cond in &CONDS {
        proofs.push(proof_fcsel(32, cond));
        proofs.push(proof_fcsel(64, cond));
    }
    proofs
}

/// NEGATIVE CONTROLS for the FCSEL obligations — each MUST refute (a wrong FCSEL
/// encoding must be caught, so the positives are not vacuous). Built at both S
/// and D over two representative conditions (NotEqual, SignedLessThan, whose
/// discriminating inputs are ~half of the input space): inverted-condition and
/// operand-swap.
pub fn fcsel_wrong_controls() -> Vec<ProofObligation> {
    use crate::aarch64_semantics::encode_fcsel;
    use trust_cg_lower::instructions::IntCC;
    use trust_cg_lower::isel::AArch64CC;
    use trust_cg_lower::types::Type;

    let mut controls = Vec::new();
    for fp_width in [32u32, 64u32] {
        let (ty_tag, dst) = if fp_width == 32 {
            ("F32", "S")
        } else {
            ("F64", "D")
        };
        for cond in [IntCC::NotEqual, IntCC::SignedLessThan] {
            let sel_width = 32u32;
            let zero = SmtExpr::bv_const(0, sel_width);
            let build_source = || {
                let sel = SmtExpr::var("sel", sel_width);
                let a = SmtExpr::var("a", fp_width);
                let b = SmtExpr::var("b", fp_width);
                let bit = crate::trust_ir_semantics::encode_trust_ir_icmp(
                    &cond,
                    Type::I32,
                    sel,
                    zero.clone(),
                );
                let pred = bit.eq_expr(SmtExpr::bv_const(1, 1));
                SmtExpr::ite(pred, a, b)
            };
            let flags = || {
                let sel = SmtExpr::var("sel", sel_width);
                crate::nzcv::encode_cmp(sel, zero.clone(), sel_width)
            };
            let inputs = vec![
                ("sel".to_string(), sel_width),
                ("a".to_string(), fp_width),
                ("b".to_string(), fp_width),
            ];

            // (1) INVERTED-COND: MACHINE selects on from_intcc(cond).invert() —
            // it takes the WRONG branch, so it diverges from the source select.
            controls.push(ProofObligation {
                machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
                name: format!(
                    "WRONG (fcsel_{}): inverted condition {cond:?} ({dst}) must REFUTE",
                    ty_tag.to_lowercase()
                ),
                trust_ir_expr: build_source(),
                aarch64_expr: encode_fcsel(
                    AArch64CC::from_intcc(cond).invert(),
                    &flags(),
                    SmtExpr::var("a", fp_width),
                    SmtExpr::var("b", fp_width),
                ),
                inputs: inputs.clone(),
                preconditions: vec![],
                fp_inputs: vec![],
                category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
            });

            // (2) OPERAND-SWAP: MACHINE wires the true/false sources backwards
            // (`ite(cond, b, a)`) — the FCSEL data path is asymmetric.
            controls.push(ProofObligation {
                machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
                name: format!(
                    "WRONG (fcsel_{}): operand-swap {cond:?} ({dst}) must REFUTE",
                    ty_tag.to_lowercase()
                ),
                trust_ir_expr: build_source(),
                aarch64_expr: encode_fcsel(
                    AArch64CC::from_intcc(cond),
                    &flags(),
                    SmtExpr::var("b", fp_width),
                    SmtExpr::var("a", fp_width),
                ),
                inputs: inputs.clone(),
                preconditions: vec![],
                fp_inputs: vec![],
                category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
            });
        }
    }
    controls
}

/// Detect whether a proof obligation is an FP comparison (FCMP).
///
/// FCMP proofs produce `ITE(comparison_bool, BV1(1), BV1(0))` at the top
/// level, whereas arithmetic proofs (FADD/FSUB/FMUL/FDIV) have FPAdd/FPSub/
/// FPMul/FPDiv at the top. FNEG has FPNeg. FABS has FPAbs. FSQRT has FPSqrt.
fn is_fp_cmp_obligation(obligation: &ProofObligation) -> bool {
    matches!(&obligation.trust_ir_expr, SmtExpr::Ite { .. })
}

/// Classify a binary FP min/max / compare-to-mask lowering obligation by name.
///
/// These obligations (MINSD/MAXSD/MINSS/MAXSS and the CMPSD/CMPSS UNORD mask)
/// have `Ite`-rooted trust_ir specs just like FCMP, so they must be detected
/// and routed BEFORE `is_fp_cmp_obligation` (which would otherwise misparse the
/// name as a FloatCC and panic). We evaluate them by calling the spec/machine
/// encoders directly with concrete operands (like the FCMP path), because the
/// `Ite` trees carry multiple FPConst placeholders that structural substitution
/// cannot reliably distinguish.
#[derive(Clone, Copy, PartialEq, Eq)]
enum FpMinMaxKind {
    Min,
    Max,
    CmpUnordMask,
}

fn minmax_obligation_kind(name: &str) -> Option<FpMinMaxKind> {
    if name.contains("MINSD") || name.contains("MINSS") {
        Some(FpMinMaxKind::Min)
    } else if name.contains("MAXSD") || name.contains("MAXSS") {
        Some(FpMinMaxKind::Max)
    } else if name.contains("CMPSD_UNORD") || name.contains("CMPSS_UNORD") {
        Some(FpMinMaxKind::CmpUnordMask)
    } else {
        None
    }
}

/// Parse a `FloatCC` condition from an FCMP proof obligation name.
///
/// Proof names follow the convention `Fcmp_{CondCode}_{Size} -> FCMP+CSET`.
/// This function extracts the condition code and maps it to the corresponding
/// `FloatCC` variant.
/// This is a test-only naming-inventory helper. Production evaluation never
/// reconstructs a comparison condition or expression from an obligation name.
/// Two spellings exist in the registry: the aarch64/x86 `Fcmp_<CC>_...`
/// (`Eq NE LT LE GT GE Ord Uno UEQ UNE ULT ULE UGT UGE`) and the wasm
/// `FCmp_<cc>_...` (`OEq ONe OLt OLe OGt OGe UEq UNe ULt ULe UGt UGe`).
#[cfg(test)]
fn parse_float_cc_from_name(name: &str) -> Option<trust_cg_lower::instructions::FloatCC> {
    use trust_cg_lower::instructions::FloatCC;
    let rest = name
        .strip_prefix("Fcmp_")
        .or_else(|| name.strip_prefix("FCmp_"))?;
    let cond_str = rest.split('_').next().unwrap_or("");
    Some(match cond_str {
        "Eq" | "OEq" => FloatCC::Equal,
        "NE" | "ONe" | "Ne" => FloatCC::NotEqual,
        "LT" | "OLt" | "Lt" => FloatCC::LessThan,
        "LE" | "OLe" | "Le" => FloatCC::LessThanOrEqual,
        "GT" | "OGt" | "Gt" => FloatCC::GreaterThan,
        "GE" | "OGe" | "Ge" => FloatCC::GreaterThanOrEqual,
        "Ord" => FloatCC::Ordered,
        "Uno" | "Unord" => FloatCC::Unordered,
        "UEQ" | "UEq" => FloatCC::UnorderedEqual,
        "UNE" | "UNe" => FloatCC::UnorderedNotEqual,
        "ULT" | "ULt" => FloatCC::UnorderedLessThan,
        "ULE" | "ULe" => FloatCC::UnorderedLessThanOrEqual,
        "UGT" | "UGt" => FloatCC::UnorderedGreaterThan,
        "UGE" | "UGe" => FloatCC::UnorderedGreaterThanOrEqual,
        _ => return None,
    })
}

/// Verify a floating-point proof obligation by concrete evaluation with
/// representative FP values.
///
/// Unlike integer proofs which use symbolic bitvector variables and exhaustive/
/// random sampling, FP proofs work with concrete floating-point constants.
/// Both trust_ir and AArch64 sides are evaluated with the same FP inputs, and
/// results are compared for bitwise equality.
///
/// # Test vectors
///
/// For binary FP operations (FADD, FSUB, FMUL, FDIV): tests all combinations
/// of edge cases including zero, one, negative values, small/large magnitudes,
/// denormals, and infinity.
///
/// For unary FP operations (FNEG, FABS, FSQRT): tests each edge case value individually.
///
/// For bound scalar FP comparisons (FCMP): validates raw-input declarations
/// and recursive sorts, evaluates the stored trees/preconditions over IEEE
/// edges and the default random workload, and compares BV1 results (or the
/// exactly validated Wasm BV1-to-i32 / i32 0-or-1 materialization pair). Unknown
/// means malformed/unsupported binding, an evaluation error, or no applicable
/// sampled point. The other legacy FP families retain their edge-only path.
///
/// # Verification strength
///
/// This is **statistical** verification using native f64 arithmetic, matching
/// the mock evaluation approach used for integer proofs at larger bit-widths.
/// For formal FP proofs, use the ay QF_FP theory via [`crate::ay_bridge`].
pub fn verify_fp_by_evaluation(obligation: &ProofObligation) -> VerificationResult {
    // Raw-bit scalar comparisons evaluate the actual stored trees, including
    // preconditions, IEEE edges and the full default random workload. Other
    // legacy FP families below retain their separate edge-only behavior.
    if uses_checked_scalar_fp_evaluation(obligation) {
        return verify_by_evaluation_with_config(obligation, &VerificationConfig::default());
    }
    // Raw-bit FP operations (including FABS) must evaluate their stored trees.
    // The legacy FP path substitutes constant operands and cannot bind these
    // bitvector variables. The primary evaluator only calls back here when
    // fp_inputs is nonempty, so this dispatch cannot recurse.
    if obligation.fp_inputs.is_empty()
        && matches!(
            obligation.trust_ir_expr.sort(),
            crate::smt::SmtSort::BitVec(_)
        )
        && matches!(
            obligation.aarch64_expr.sort(),
            crate::smt::SmtSort::BitVec(_)
        )
    {
        return verify_by_evaluation(obligation);
    }
    let empty_env = HashMap::new();

    // FP test vectors: representative values covering IEEE 754 edge cases.
    // NaN is included for FCMP proofs (critical for ordered/unordered semantics).
    let f64_test_values: Vec<f64> = vec![
        0.0,
        -0.0,
        1.0,
        -1.0,
        0.5,
        -0.5,
        2.0,
        -2.0,
        0.1,
        -0.1,
        1e10,
        -1e10,
        1e-10,
        -1e-10,
        f64::INFINITY,
        f64::NEG_INFINITY,
        f64::MIN_POSITIVE,
        -f64::MIN_POSITIVE,
        f64::MAX,
        f64::MIN,
        std::f64::consts::PI,
        -std::f64::consts::PI,
        1.0 / 3.0,
        -1.0 / 3.0,
        42.0,
        -42.0,
        100.0,
        -100.0,
        0.000001,
        -0.000001,
        f64::NAN,
    ];

    let f32_test_values: Vec<f32> = vec![
        0.0f32,
        -0.0f32,
        1.0f32,
        -1.0f32,
        0.5f32,
        -0.5f32,
        2.0f32,
        -2.0f32,
        0.1f32,
        -0.1f32,
        1e10f32,
        -1e10f32,
        1e-10f32,
        -1e-10f32,
        f32::INFINITY,
        f32::NEG_INFINITY,
        f32::MIN_POSITIVE,
        -f32::MIN_POSITIVE,
        f32::MAX,
        f32::MIN,
        std::f32::consts::PI,
        -std::f32::consts::PI,
        42.0f32,
        -42.0f32,
        100.0f32,
        -100.0f32,
        0.000001f32,
        -0.000001f32,
        f32::NAN,
    ];

    let is_unary = obligation.fp_inputs.len() == 1;
    let is_f32 = obligation
        .fp_inputs
        .first()
        .map(|(_, eb, _)| *eb == 8)
        .unwrap_or(false);
    // Detect MINSD/MAXSD/MINSS/MAXSS + CMPSD/CMPSS UNORD mask FIRST: their
    // trust_ir specs are `Ite`-rooted (like FCMP) but are NOT FloatCC compares.
    let minmax_kind = minmax_obligation_kind(&obligation.name);
    let is_cmp = minmax_kind.is_none() && is_fp_cmp_obligation(obligation);

    if let Some(kind) = minmax_kind {
        // Binary FP min/max / compare-to-mask: evaluate by calling the
        // spec (trust_ir) and machine (x86) encoders directly with concrete
        // operands, exhaustively over the IEEE edge-case battery (incl. NaN,
        // +/-0.0, +/-Inf). This is the faithful, non-vacuous check the gap
        // requires: every (a,b) pair drives the real lowering semantics.
        use crate::trust_ir_semantics::{
            encode_trust_ir_cmp_unord_mask, encode_trust_ir_fmaxsd_hw, encode_trust_ir_fminsd_hw,
        };
        use crate::x86_64_semantics::{encode_fp_cmp_unord_mask, encode_fp_maxsd, encode_fp_minsd};
        use trust_cg_lower::types::Type;

        let width = if is_f32 { 32u32 } else { 64u32 };
        let ty = if is_f32 { Type::F32 } else { Type::F64 };

        let mk = |a_val: f64, b_val: f64| -> (SmtExpr, SmtExpr) {
            let (a, b) = if is_f32 {
                (
                    SmtExpr::fp32_const(a_val as f32),
                    SmtExpr::fp32_const(b_val as f32),
                )
            } else {
                (SmtExpr::fp64_const(a_val), SmtExpr::fp64_const(b_val))
            };
            match kind {
                FpMinMaxKind::Min => (
                    encode_trust_ir_fminsd_hw(ty.clone(), a.clone(), b.clone()),
                    encode_fp_minsd(a, b),
                ),
                FpMinMaxKind::Max => (
                    encode_trust_ir_fmaxsd_hw(ty.clone(), a.clone(), b.clone()),
                    encode_fp_maxsd(a, b),
                ),
                FpMinMaxKind::CmpUnordMask => (
                    encode_trust_ir_cmp_unord_mask(width, a.clone(), b.clone()),
                    encode_fp_cmp_unord_mask(width, a, b),
                ),
            }
        };

        let values_f64 = &f64_test_values;
        let values_f32 = &f32_test_values;
        let n = if is_f32 {
            values_f32.len()
        } else {
            values_f64.len()
        };
        for i in 0..n {
            for j in 0..n {
                let (a_val, b_val) = if is_f32 {
                    (values_f32[i] as f64, values_f32[j] as f64)
                } else {
                    (values_f64[i], values_f64[j])
                };
                let (trust_ir_expr, machine_expr) = mk(a_val, b_val);
                let trust_ir_result = trust_ir_expr.try_eval(&empty_env);
                let machine_result = machine_expr.try_eval(&empty_env);
                if let Some(result) = check_fp_evaluation_results(
                    &trust_ir_result,
                    &machine_result,
                    format!("a={a_val}, b={b_val}"),
                ) {
                    return result;
                }
            }
        }
        return VerificationResult::Valid;
    }

    if is_unary {
        // Unary FP operation (FNEG, FABS, FSQRT)
        if is_f32 {
            for &a_val in &f32_test_values {
                let trust_ir_expr =
                    build_fp_unary_expr(&obligation.trust_ir_expr, a_val as f64, is_f32);
                let aarch64_expr =
                    build_fp_unary_expr(&obligation.aarch64_expr, a_val as f64, is_f32);
                let trust_ir_result = trust_ir_expr.try_eval(&empty_env);
                let aarch64_result = aarch64_expr.try_eval(&empty_env);
                if let Some(result) = check_fp_evaluation_results(
                    &trust_ir_result,
                    &aarch64_result,
                    format!("a={a_val}"),
                ) {
                    return result;
                }
            }
        } else {
            for &a_val in &f64_test_values {
                let trust_ir_expr = build_fp_unary_expr(&obligation.trust_ir_expr, a_val, is_f32);
                let aarch64_expr = build_fp_unary_expr(&obligation.aarch64_expr, a_val, is_f32);
                let trust_ir_result = trust_ir_expr.try_eval(&empty_env);
                let aarch64_result = aarch64_expr.try_eval(&empty_env);
                if let Some(result) = check_fp_evaluation_results(
                    &trust_ir_result,
                    &aarch64_result,
                    format!("a={a_val}"),
                ) {
                    return result;
                }
            }
        }
    } else if is_cmp {
        // Never reconstruct a comparison from its name. A comparison outside
        // the checked raw-input contract cannot obtain finite Valid here.
        return VerificationResult::Unknown {
            reason: "FP comparison lacks checked raw-input binding".into(),
        };
    } else {
        // Binary FP operation (FADD, FSUB, FMUL, FDIV)
        if is_f32 {
            for &a_val in &f32_test_values {
                for &b_val in &f32_test_values {
                    let trust_ir_expr = build_fp_binary_expr(
                        &obligation.trust_ir_expr,
                        a_val as f64,
                        b_val as f64,
                        is_f32,
                    );
                    let aarch64_expr = build_fp_binary_expr(
                        &obligation.aarch64_expr,
                        a_val as f64,
                        b_val as f64,
                        is_f32,
                    );
                    let trust_ir_result = trust_ir_expr.try_eval(&empty_env);
                    let aarch64_result = aarch64_expr.try_eval(&empty_env);
                    if let Some(result) = check_fp_evaluation_results(
                        &trust_ir_result,
                        &aarch64_result,
                        format!("a={a_val}, b={b_val}"),
                    ) {
                        return result;
                    }
                }
            }
        } else {
            for &a_val in &f64_test_values {
                for &b_val in &f64_test_values {
                    let trust_ir_expr =
                        build_fp_binary_expr(&obligation.trust_ir_expr, a_val, b_val, is_f32);
                    let aarch64_expr =
                        build_fp_binary_expr(&obligation.aarch64_expr, a_val, b_val, is_f32);
                    let trust_ir_result = trust_ir_expr.try_eval(&empty_env);
                    let aarch64_result = aarch64_expr.try_eval(&empty_env);
                    if let Some(result) = check_fp_evaluation_results(
                        &trust_ir_result,
                        &aarch64_result,
                        format!("a={a_val}, b={b_val}"),
                    ) {
                        return result;
                    }
                }
            }
        }
    }

    VerificationResult::Valid
}

/// A sample only agrees when both evaluators produced comparable values.
/// Missing bindings and unsupported semantics refuse the obligation, even if
/// both sides fail in the same way; failed samples are never positive evidence.
fn check_fp_evaluation_results(
    source: &Result<crate::smt::EvalResult, crate::smt::SmtError>,
    machine: &Result<crate::smt::EvalResult, crate::smt::SmtError>,
    sample: String,
) -> Option<VerificationResult> {
    match (source, machine) {
        (Ok(source), Ok(machine)) if fp_results_equal(source, machine) => None,
        (Ok(source), Ok(machine)) => Some(VerificationResult::Invalid {
            counterexample: format!("{sample}, trust_ir={source:?}, machine={machine:?}"),
        }),
        (Err(error), _) => Some(VerificationResult::Unknown {
            reason: format!("FP source evaluation failed at {sample}: {error}"),
        }),
        (_, Err(error)) => Some(VerificationResult::Unknown {
            reason: format!("FP machine evaluation failed at {sample}: {error}"),
        }),
    }
}

/// Build a concrete FP binary expression by substituting concrete values.
///
/// The proof obligation's trust_ir_expr / aarch64_expr use placeholder FPConst(0.0)
/// nodes. This function rebuilds the expression tree with concrete values.
fn build_fp_binary_expr(template: &SmtExpr, a_val: f64, b_val: f64, is_f32: bool) -> SmtExpr {
    let a = if is_f32 {
        SmtExpr::fp32_const(a_val as f32)
    } else {
        SmtExpr::fp64_const(a_val)
    };
    let b = if is_f32 {
        SmtExpr::fp32_const(b_val as f32)
    } else {
        SmtExpr::fp64_const(b_val)
    };

    match template {
        SmtExpr::FPAdd { rm, .. } => SmtExpr::fp_add(*rm, a, b),
        SmtExpr::FPSub { rm, .. } => SmtExpr::fp_sub(*rm, a, b),
        SmtExpr::FPMul { rm, .. } => SmtExpr::fp_mul(*rm, a, b),
        SmtExpr::FPDiv { rm, .. } => SmtExpr::fp_div(*rm, a, b),
        _ => template.clone(),
    }
}

/// Build a concrete FP unary expression by substituting a concrete value.
fn build_fp_unary_expr(template: &SmtExpr, a_val: f64, is_f32: bool) -> SmtExpr {
    let a = if is_f32 {
        SmtExpr::fp32_const(a_val as f32)
    } else {
        SmtExpr::fp64_const(a_val)
    };

    match template {
        SmtExpr::FPNeg { .. } => a.fp_neg(),
        SmtExpr::FPAbs { .. } => a.fp_abs(),
        SmtExpr::FPSqrt { rm, .. } => SmtExpr::fp_sqrt(*rm, a),
        // Round-to-integral (FFloor/FCeil/FTrunc spec side AND the ROUNDSD/
        // ROUNDSS machine side both use this node): substitute the concrete FP
        // value so the test battery genuinely exercises each rounding mode
        // rather than evaluating the `fp_const(0.0)` placeholder.
        SmtExpr::FPRoundToIntegral { rm, .. } => SmtExpr::fp_round_to_integral(*rm, a),
        // FP conversion templates (x86-64 CVTSD2SI/CVTSS2SI/CVTTSD2SI/...,
        // CVTSD2SS/CVTSS2SD). Substituting the concrete FP value here lets the
        // FP test battery genuinely exercise the conversion rather than
        // evaluating the placeholder `fp_const(0.0)`.
        SmtExpr::FPToSBv {
            rm, width, mode, ..
        } => SmtExpr::fp_to_sbv_mode(*rm, a, *width, *mode),
        SmtExpr::FPToUBv { rm, width, .. } => SmtExpr::fp_to_ubv(*rm, a, *width),
        SmtExpr::FPToFP { rm, eb, sb, .. } => SmtExpr::fp_to_fp(*rm, a, *eb, *sb),
        _ => template.clone(),
    }
}

/// Verify a RECONSTRUCTED FP obligation by concrete evaluation, PRESERVING
/// operand wiring (task: FP/div/madd reconstruction extension).
///
/// Unlike [`verify_fp_by_evaluation`], which rebuilds only the root node with a
/// canonical (a, b) operand order, this evaluator substitutes a concrete FP
/// value for each NAMED leaf (`recon_a` / `recon_b`) THROUGHOUT both expression
/// trees. The operand identity is therefore retained, so:
///
///   * a WRONG OPCODE (e.g. source `fp.add` vs machine `fp.sub`) diverges as
///     before (different op), and
///   * a WRONG WIRING of a NON-COMMUTATIVE op (machine `fp.sub(b, a)` while the
///     source is `fp.sub(a, b)`) genuinely diverges for asymmetric inputs ⇒
///     REFUTE. The canonical-order static evaluator would have MISSED this.
///
/// Operand widths come from `fp_inputs`. Binary (two `fp_inputs`) and unary (one
/// `fp_input`) FP value ops are handled; FCVTZS/FCVTZU are unary FP→BV ops whose
/// single operand is an FP leaf (`recon_a`) and whose result is a bitvector —
/// `fp_results_equal` falls through to `==` on the `Bv` results in that case.
fn verify_fp_reconstructed_by_evaluation(obligation: &ProofObligation) -> VerificationResult {
    let empty_env = HashMap::new();

    let is_f32 = obligation
        .fp_inputs
        .first()
        .map(|(_, eb, _)| *eb == 8)
        .unwrap_or(false);
    let is_unary = obligation.fp_inputs.len() == 1;
    let is_ternary = obligation.fp_inputs.len() == 3;

    let mk_fp = |v: f64| -> SmtExpr {
        if is_f32 {
            SmtExpr::fp32_const(v as f32)
        } else {
            SmtExpr::fp64_const(v)
        }
    };

    // Reuse the same IEEE-754 edge-case battery the static FP evaluator uses;
    // build it inline so this evaluator is self-contained.
    let f64_values: &[f64] = &[
        0.0,
        -0.0,
        1.0,
        -1.0,
        0.5,
        -0.5,
        // Round-mode discriminators: a non-integral TIE / fractional input where
        // RTZ (truncate) and RNE (round-ties-even) DISAGREE — this is what makes an
        // RNE-for-RTZ FP->int lowering bug REFUTE. 1.5 -> RTZ 1, RNE 2; 2.5 -> RTZ
        // 2, RNE 2 (already even); 0.5 -> 0 under both. Without one of these in the
        // battery a wrong rounding mode would pass vacuously.
        1.5,
        -1.5,
        2.5,
        -2.5,
        2.0,
        -2.0,
        0.1,
        -0.1,
        3.0,
        -3.0,
        1e10,
        -1e10,
        1e-10,
        -1e-10,
        f64::INFINITY,
        f64::NEG_INFINITY,
        f64::MIN_POSITIVE,
        f64::MAX,
        std::f64::consts::PI,
        42.0,
        -42.0,
        100.0,
        -100.0,
        0.000001,
        f64::NAN,
    ];

    let check = |a_val: f64, b_val: f64| -> Option<VerificationResult> {
        let a = mk_fp(a_val);
        let b = mk_fp(b_val);
        let t = subst_fp_recon_leaves(&obligation.trust_ir_expr, &a, &b);
        let m = subst_fp_recon_leaves(&obligation.aarch64_expr, &a, &b);
        check_fp_evaluation_results(
            &t.try_eval(&empty_env),
            &m.try_eval(&empty_env),
            format!("a={a_val}, b={b_val}"),
        )
    };

    // Ternary (FMADD) check: substitute all three named leaves and compare the
    // single-rounding fused result on both sides over a triple battery. The
    // battery includes the round-once-vs-twice DIVERGENT triple below so a
    // round-TWICE machine model (were it ever substituted) would be caught.
    let check3 = |a_val: f64, b_val: f64, c_val: f64| -> Option<VerificationResult> {
        let a = mk_fp(a_val);
        let b = mk_fp(b_val);
        let c = mk_fp(c_val);
        let t = subst_fp_recon_leaves3(&obligation.trust_ir_expr, &a, &b, &c);
        let m = subst_fp_recon_leaves3(&obligation.aarch64_expr, &a, &b, &c);
        check_fp_evaluation_results(
            &t.try_eval(&empty_env),
            &m.try_eval(&empty_env),
            format!("a={a_val}, b={b_val}, c={c_val}"),
        )
    };

    if is_unary {
        for &a_val in f64_values {
            if let Some(r) = check(a_val, 0.0) {
                return r;
            }
        }
    } else if is_ternary {
        // A triple where the SINGLE-ROUNDING fused a*b+c differs from the unfused
        // round(round(a*b)+c) in the last ULP (round-once-vs-twice discriminator).
        // Width-specific: the f64 witness (`1+2^-30`) rounds to 1.0 in f32, so use
        // a genuine f32 witness there (both verified to diverge fused-vs-unfused).
        let (da, db) = if is_f32 {
            (1.000_000_48_f64, 1.000_000_48_f64)
        } else {
            (1.000_000_000_1_f64, 1.000_000_000_1_f64)
        };
        if let Some(r) = check3(da, db, -1.0) {
            return r;
        }
        for &a_val in f64_values {
            for &b_val in f64_values {
                for &c_val in f64_values {
                    if let Some(r) = check3(a_val, b_val, c_val) {
                        return r;
                    }
                }
                // also probe the divergent addend against each (a,b): c = -(a*b)
                // maximizes cancellation, exposing any dropped product bits.
                if let Some(r) = check3(a_val, b_val, -(a_val * b_val)) {
                    return r;
                }
            }
        }
    } else {
        for &a_val in f64_values {
            for &b_val in f64_values {
                if let Some(r) = check(a_val, b_val) {
                    return r;
                }
            }
        }
    }
    VerificationResult::Valid
}

/// Substitute concrete FP values for the named reconstruction leaves
/// (`recon_a` / `recon_b`) throughout an SMT expression tree.
///
/// The reconstruction FP encoders build their operand leaves as
/// `SmtExpr::var("recon_a"/"recon_b", width)`; `try_eval` cannot evaluate an FP
/// `Var` directly (its env is bitvector-only), so this rewrite replaces those
/// leaves with concrete `FPConst` values BEFORE evaluation. Crucially it
/// preserves WHICH operand sits WHERE in each subtree, so a swapped
/// non-commutative wiring stays observable.
fn subst_fp_recon_leaves(expr: &SmtExpr, a: &SmtExpr, b: &SmtExpr) -> SmtExpr {
    match expr {
        SmtExpr::Var { name, .. } if name == "recon_a" => a.clone(),
        SmtExpr::Var { name, .. } if name == "recon_b" => b.clone(),
        SmtExpr::FPAdd { rm, lhs, rhs } => SmtExpr::fp_add(
            *rm,
            subst_fp_recon_leaves(lhs, a, b),
            subst_fp_recon_leaves(rhs, a, b),
        ),
        SmtExpr::FPSub { rm, lhs, rhs } => SmtExpr::fp_sub(
            *rm,
            subst_fp_recon_leaves(lhs, a, b),
            subst_fp_recon_leaves(rhs, a, b),
        ),
        SmtExpr::FPMul { rm, lhs, rhs } => SmtExpr::fp_mul(
            *rm,
            subst_fp_recon_leaves(lhs, a, b),
            subst_fp_recon_leaves(rhs, a, b),
        ),
        SmtExpr::FPDiv { rm, lhs, rhs } => SmtExpr::fp_div(
            *rm,
            subst_fp_recon_leaves(lhs, a, b),
            subst_fp_recon_leaves(rhs, a, b),
        ),
        SmtExpr::FPNeg { operand } => subst_fp_recon_leaves(operand, a, b).fp_neg(),
        SmtExpr::FPAbs { operand } => subst_fp_recon_leaves(operand, a, b).fp_abs(),
        SmtExpr::FPSqrt { rm, operand } => {
            SmtExpr::fp_sqrt(*rm, subst_fp_recon_leaves(operand, a, b))
        }
        // ROUND-TO-INTEGRAL (SSE4.1 ROUNDSD/ROUNDSS): recurse into the FP operand
        // so a `recon_a` leaf inside an `FPRoundToIntegral` is substituted. The
        // rounding mode `rm` (RTN/RTP/RTZ = floor/ceil/trunc) is PRESERVED, so a
        // wrong rounding mode (floor-for-ceil) stays observable on a non-integral
        // input ⇒ REFUTE. Without this the leaf would survive un-substituted,
        // `try_eval` would error, and the obligation would be VACUOUSLY "Valid".
        SmtExpr::FPRoundToIntegral { rm, operand } => {
            SmtExpr::fp_round_to_integral(*rm, subst_fp_recon_leaves(operand, a, b))
        }
        SmtExpr::FPToSBv {
            rm,
            operand,
            width,
            mode,
        } => SmtExpr::fp_to_sbv_mode(*rm, subst_fp_recon_leaves(operand, a, b), *width, *mode),
        SmtExpr::FPToUBv { rm, operand, width } => {
            SmtExpr::fp_to_ubv(*rm, subst_fp_recon_leaves(operand, a, b), *width)
        }
        // FP-FORMAT conversion (FCVT widen/narrow): recurse into the FP operand so
        // a `recon_a` leaf inside an `FPToFP` (e.g. FcvtSD/FcvtDS) is substituted.
        // The destination format `(eb, sb)` is preserved, so a wrong-direction
        // cast (different dest format) stays observable ⇒ REFUTE.
        SmtExpr::FPToFP {
            rm,
            operand,
            eb,
            sb,
        } => SmtExpr::fp_to_fp(*rm, subst_fp_recon_leaves(operand, a, b), *eb, *sb),
        // FP COMPARISONS / predicate / conditional / boolean glue — needed for the
        // x86 scalar MIN/MAX (hardware `dest < src ? dest : src`), the UNORD
        // compare-to-mask (`isNaN(a) OR isNaN(b)`), and the complementary trust_ir
        // specs that formulate these with `fp.ge`/`fp.le` and self-`fp.eq` NaN
        // tests. Without recursing through these the `recon_a`/`recon_b` leaves
        // nested inside an ITE/compare would survive un-substituted, `try_eval`
        // would error, and the obligation would be VACUOUSLY "Valid" — a wrong
        // wiring would NOT refute. Recursing here makes the min/max/cmp
        // obligations genuinely checkable (a swapped MIN/MAX wiring refutes).
        SmtExpr::Ite {
            cond,
            then_expr,
            else_expr,
        } => SmtExpr::ite(
            subst_fp_recon_leaves(cond, a, b),
            subst_fp_recon_leaves(then_expr, a, b),
            subst_fp_recon_leaves(else_expr, a, b),
        ),
        SmtExpr::FPEq { lhs, rhs } => {
            subst_fp_recon_leaves(lhs, a, b).fp_eq(subst_fp_recon_leaves(rhs, a, b))
        }
        SmtExpr::FPLt { lhs, rhs } => {
            subst_fp_recon_leaves(lhs, a, b).fp_lt(subst_fp_recon_leaves(rhs, a, b))
        }
        SmtExpr::FPLe { lhs, rhs } => {
            subst_fp_recon_leaves(lhs, a, b).fp_le(subst_fp_recon_leaves(rhs, a, b))
        }
        SmtExpr::FPGt { lhs, rhs } => {
            subst_fp_recon_leaves(lhs, a, b).fp_gt(subst_fp_recon_leaves(rhs, a, b))
        }
        SmtExpr::FPGe { lhs, rhs } => {
            subst_fp_recon_leaves(lhs, a, b).fp_ge(subst_fp_recon_leaves(rhs, a, b))
        }
        SmtExpr::FPIsNaN { operand } => subst_fp_recon_leaves(operand, a, b).fp_is_nan(),
        // BV WRAPPERS over an FP->int result — needed for the float<->int CONVERSION
        // family (saturating trunc_sat / convert), where the int result of an
        // `FPToSBv`/`FPToUBv` (or the int source of a `BvToFP`) may be wrapped in an
        // Extract / Zero/SignExtend / Concat (e.g. a WRAPPING `trunc -> low 32 bits`
        // machine vs the SATURATING source). Without recursing here the `recon_a`
        // leaf nested under the Extract would survive un-substituted, `try_eval`
        // would error, and the obligation would be VACUOUSLY "Valid" — a wrong
        // saturation/width would NOT refute. Recursing makes those genuinely
        // checkable.
        SmtExpr::Extract {
            high, low, operand, ..
        } => subst_fp_recon_leaves(operand, a, b).extract(*high, *low),
        SmtExpr::ZeroExtend {
            operand,
            extra_bits,
            width,
        } => SmtExpr::ZeroExtend {
            operand: Arc::new(subst_fp_recon_leaves(operand, a, b)),
            extra_bits: *extra_bits,
            width: *width,
        },
        SmtExpr::SignExtend {
            operand,
            extra_bits,
            width,
        } => SmtExpr::SignExtend {
            operand: Arc::new(subst_fp_recon_leaves(operand, a, b)),
            extra_bits: *extra_bits,
            width: *width,
        },
        SmtExpr::Not { operand } => subst_fp_recon_leaves(operand, a, b).not_expr(),
        SmtExpr::And { lhs, rhs } => {
            subst_fp_recon_leaves(lhs, a, b).and_expr(subst_fp_recon_leaves(rhs, a, b))
        }
        SmtExpr::Or { lhs, rhs } => {
            subst_fp_recon_leaves(lhs, a, b).or_expr(subst_fp_recon_leaves(rhs, a, b))
        }
        // Leaves / unsupported nodes pass through unchanged.
        other => other.clone(),
    }
}

/// Substitute concrete FP values for the TERNARY reconstruction leaves
/// (`recon_a`/`recon_b`/`recon_c`) throughout an SMT expression tree — the FMA
/// (`FMADD`) analogue of [`subst_fp_recon_leaves`]. Recurses through `FPFma`
/// (the FUSED node) AND the unfused `FPAdd`/`FPMul`/`FPSub`/`FPDiv`/`FPNeg`/
/// `FPAbs` shapes used by the round-once-vs-twice and sign refute controls, so a
/// `recon_*` leaf nested inside any of them is substituted (NOT silently left as
/// an unevaluable FP `Var`, which would make the obligation VACUOUSLY Valid).
/// WHICH operand sits WHERE is preserved, so a swapped wiring stays observable.
fn subst_fp_recon_leaves3(expr: &SmtExpr, a: &SmtExpr, b: &SmtExpr, c: &SmtExpr) -> SmtExpr {
    match expr {
        SmtExpr::Var { name, .. } if name == "recon_a" => a.clone(),
        SmtExpr::Var { name, .. } if name == "recon_b" => b.clone(),
        SmtExpr::Var { name, .. } if name == "recon_c" => c.clone(),
        SmtExpr::FPFma {
            rm,
            a: fa,
            b: fb,
            c: fc,
        } => SmtExpr::fp_fma(
            *rm,
            subst_fp_recon_leaves3(fa, a, b, c),
            subst_fp_recon_leaves3(fb, a, b, c),
            subst_fp_recon_leaves3(fc, a, b, c),
        ),
        SmtExpr::FPAdd { rm, lhs, rhs } => SmtExpr::fp_add(
            *rm,
            subst_fp_recon_leaves3(lhs, a, b, c),
            subst_fp_recon_leaves3(rhs, a, b, c),
        ),
        SmtExpr::FPSub { rm, lhs, rhs } => SmtExpr::fp_sub(
            *rm,
            subst_fp_recon_leaves3(lhs, a, b, c),
            subst_fp_recon_leaves3(rhs, a, b, c),
        ),
        SmtExpr::FPMul { rm, lhs, rhs } => SmtExpr::fp_mul(
            *rm,
            subst_fp_recon_leaves3(lhs, a, b, c),
            subst_fp_recon_leaves3(rhs, a, b, c),
        ),
        SmtExpr::FPDiv { rm, lhs, rhs } => SmtExpr::fp_div(
            *rm,
            subst_fp_recon_leaves3(lhs, a, b, c),
            subst_fp_recon_leaves3(rhs, a, b, c),
        ),
        SmtExpr::FPNeg { operand } => subst_fp_recon_leaves3(operand, a, b, c).fp_neg(),
        SmtExpr::FPAbs { operand } => subst_fp_recon_leaves3(operand, a, b, c).fp_abs(),
        // Leaves / unsupported nodes pass through unchanged.
        other => other.clone(),
    }
}

/// Compare two FP evaluation results, handling NaN correctly.
///
/// IEEE 754: NaN != NaN, but for verification we consider two NaN results
/// as equal (both sides produced NaN, which is the correct behavior).
fn fp_results_equal(a: &crate::smt::EvalResult, b: &crate::smt::EvalResult) -> bool {
    use crate::smt::EvalResult;
    match (a, b) {
        (EvalResult::Float(fa), EvalResult::Float(fb)) => {
            if fa.is_nan() && fb.is_nan() {
                true // Both NaN = correct
            } else {
                fa.to_bits() == fb.to_bits() // Bitwise comparison (handles -0.0 vs +0.0)
            }
        }
        _ => a == b,
    }
}

// ---------------------------------------------------------------------------
// Comparison lowering proofs: trust_ir::Icmp -> CMP + CSET
// ---------------------------------------------------------------------------

/// Generic comparison lowering proof builder.
///
/// Builds a proof that `trust_ir::Icmp(cond, a, b)` produces the same 1-bit
/// result as the AArch64 sequence `CMP Rn, Rm ; CSET Rd, cc`.
fn proof_icmp_generic(
    intcc: trust_cg_lower::instructions::IntCC,
    aarch64cc: trust_cg_lower::isel::AArch64CC,
    width: u32,
    name: &str,
) -> ProofObligation {
    use crate::nzcv::encode_cmp_cset;
    use crate::trust_ir_semantics::encode_trust_ir_icmp;
    use trust_cg_lower::types::Type;

    let ty = if width == 32 { Type::I32 } else { Type::I64 };
    let a = SmtExpr::var("a", width);
    let b = SmtExpr::var("b", width);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: name.to_string(),
        trust_ir_expr: encode_trust_ir_icmp(&intcc, ty, a.clone(), b.clone()),
        aarch64_expr: encode_cmp_cset(a, b, width, aarch64cc),
        inputs: vec![("a".to_string(), width), ("b".to_string(), width)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// Proof: trust_ir::Icmp(Equal, I32) -> CMP Wn, Wm ; CSET Wd, EQ
pub fn proof_icmp_eq_i32() -> ProofObligation {
    use trust_cg_lower::instructions::IntCC;
    use trust_cg_lower::isel::AArch64CC;
    proof_icmp_generic(
        IntCC::Equal,
        AArch64CC::EQ,
        32,
        "Icmp_Eq_I32 -> CMP+CSET_EQ",
    )
}

/// Proof: trust_ir::Icmp(NotEqual, I32) -> CMP Wn, Wm ; CSET Wd, NE
pub fn proof_icmp_ne_i32() -> ProofObligation {
    use trust_cg_lower::instructions::IntCC;
    use trust_cg_lower::isel::AArch64CC;
    proof_icmp_generic(
        IntCC::NotEqual,
        AArch64CC::NE,
        32,
        "Icmp_NE_I32 -> CMP+CSET_NE",
    )
}

/// Proof: trust_ir::Icmp(SignedLessThan, I32) -> CMP Wn, Wm ; CSET Wd, LT
pub fn proof_icmp_slt_i32() -> ProofObligation {
    use trust_cg_lower::instructions::IntCC;
    use trust_cg_lower::isel::AArch64CC;
    proof_icmp_generic(
        IntCC::SignedLessThan,
        AArch64CC::LT,
        32,
        "Icmp_SLT_I32 -> CMP+CSET_LT",
    )
}

/// Proof: trust_ir::Icmp(SignedGreaterThanOrEqual, I32) -> CMP + CSET GE
pub fn proof_icmp_sge_i32() -> ProofObligation {
    use trust_cg_lower::instructions::IntCC;
    use trust_cg_lower::isel::AArch64CC;
    proof_icmp_generic(
        IntCC::SignedGreaterThanOrEqual,
        AArch64CC::GE,
        32,
        "Icmp_SGE_I32 -> CMP+CSET_GE",
    )
}

/// Proof: trust_ir::Icmp(SignedGreaterThan, I32) -> CMP + CSET GT
pub fn proof_icmp_sgt_i32() -> ProofObligation {
    use trust_cg_lower::instructions::IntCC;
    use trust_cg_lower::isel::AArch64CC;
    proof_icmp_generic(
        IntCC::SignedGreaterThan,
        AArch64CC::GT,
        32,
        "Icmp_SGT_I32 -> CMP+CSET_GT",
    )
}

/// Proof: trust_ir::Icmp(SignedLessThanOrEqual, I32) -> CMP + CSET LE
pub fn proof_icmp_sle_i32() -> ProofObligation {
    use trust_cg_lower::instructions::IntCC;
    use trust_cg_lower::isel::AArch64CC;
    proof_icmp_generic(
        IntCC::SignedLessThanOrEqual,
        AArch64CC::LE,
        32,
        "Icmp_SLE_I32 -> CMP+CSET_LE",
    )
}

/// Proof: trust_ir::Icmp(UnsignedLessThan, I32) -> CMP + CSET LO
pub fn proof_icmp_ult_i32() -> ProofObligation {
    use trust_cg_lower::instructions::IntCC;
    use trust_cg_lower::isel::AArch64CC;
    proof_icmp_generic(
        IntCC::UnsignedLessThan,
        AArch64CC::LO,
        32,
        "Icmp_ULT_I32 -> CMP+CSET_LO",
    )
}

/// Proof: trust_ir::Icmp(UnsignedGreaterThanOrEqual, I32) -> CMP + CSET HS
pub fn proof_icmp_uge_i32() -> ProofObligation {
    use trust_cg_lower::instructions::IntCC;
    use trust_cg_lower::isel::AArch64CC;
    proof_icmp_generic(
        IntCC::UnsignedGreaterThanOrEqual,
        AArch64CC::HS,
        32,
        "Icmp_UGE_I32 -> CMP+CSET_HS",
    )
}

/// Proof: trust_ir::Icmp(UnsignedGreaterThan, I32) -> CMP + CSET HI
pub fn proof_icmp_ugt_i32() -> ProofObligation {
    use trust_cg_lower::instructions::IntCC;
    use trust_cg_lower::isel::AArch64CC;
    proof_icmp_generic(
        IntCC::UnsignedGreaterThan,
        AArch64CC::HI,
        32,
        "Icmp_UGT_I32 -> CMP+CSET_HI",
    )
}

/// Proof: trust_ir::Icmp(UnsignedLessThanOrEqual, I32) -> CMP + CSET LS
pub fn proof_icmp_ule_i32() -> ProofObligation {
    use trust_cg_lower::instructions::IntCC;
    use trust_cg_lower::isel::AArch64CC;
    proof_icmp_generic(
        IntCC::UnsignedLessThanOrEqual,
        AArch64CC::LS,
        32,
        "Icmp_ULE_I32 -> CMP+CSET_LS",
    )
}

/// Return all 10 comparison lowering proofs (32-bit).
pub fn all_comparison_proofs_i32() -> Vec<ProofObligation> {
    vec![
        proof_icmp_eq_i32(),
        proof_icmp_ne_i32(),
        proof_icmp_slt_i32(),
        proof_icmp_sge_i32(),
        proof_icmp_sgt_i32(),
        proof_icmp_sle_i32(),
        proof_icmp_ult_i32(),
        // #62 (group b) retracted Icmp_UGE_I32 -> CMP+CSET_HS as degenerate while
        // the model spelled C as `bvuge(Rn, Rm)`. C is now the adder carry-out
        // (nzcv.rs), so the obligation is a genuine theorem; pinned non-degenerate
        // by `uge_proofs_are_no_longer_degenerate`.
        proof_icmp_uge_i32(),
        proof_icmp_ugt_i32(),
        proof_icmp_ule_i32(),
    ]
}

// ---------------------------------------------------------------------------
// 64-bit comparison proofs
// ---------------------------------------------------------------------------

/// Proof: trust_ir::Icmp(Equal, I64) -> CMP Xn, Xm ; CSET Xd, EQ
pub fn proof_icmp_eq_i64() -> ProofObligation {
    use trust_cg_lower::instructions::IntCC;
    use trust_cg_lower::isel::AArch64CC;
    proof_icmp_generic(
        IntCC::Equal,
        AArch64CC::EQ,
        64,
        "Icmp_Eq_I64 -> CMP+CSET_EQ",
    )
}

/// Proof: trust_ir::Icmp(SignedLessThan, I64) -> CMP + CSET LT (64-bit)
pub fn proof_icmp_slt_i64() -> ProofObligation {
    use trust_cg_lower::instructions::IntCC;
    use trust_cg_lower::isel::AArch64CC;
    proof_icmp_generic(
        IntCC::SignedLessThan,
        AArch64CC::LT,
        64,
        "Icmp_SLT_I64 -> CMP+CSET_LT",
    )
}

/// Proof: trust_ir::Icmp(UnsignedLessThan, I64) -> CMP + CSET LO (64-bit)
pub fn proof_icmp_ult_i64() -> ProofObligation {
    use trust_cg_lower::instructions::IntCC;
    use trust_cg_lower::isel::AArch64CC;
    proof_icmp_generic(
        IntCC::UnsignedLessThan,
        AArch64CC::LO,
        64,
        "Icmp_ULT_I64 -> CMP+CSET_LO",
    )
}

/// Proof: trust_ir::Icmp(NotEqual, I64) -> CMP Xn, Xm ; CSET Xd, NE
pub fn proof_icmp_ne_i64() -> ProofObligation {
    use trust_cg_lower::instructions::IntCC;
    use trust_cg_lower::isel::AArch64CC;
    proof_icmp_generic(
        IntCC::NotEqual,
        AArch64CC::NE,
        64,
        "Icmp_NE_I64 -> CMP+CSET_NE",
    )
}

/// Proof: trust_ir::Icmp(SignedGreaterThanOrEqual, I64) -> CMP + CSET GE (64-bit)
pub fn proof_icmp_sge_i64() -> ProofObligation {
    use trust_cg_lower::instructions::IntCC;
    use trust_cg_lower::isel::AArch64CC;
    proof_icmp_generic(
        IntCC::SignedGreaterThanOrEqual,
        AArch64CC::GE,
        64,
        "Icmp_SGE_I64 -> CMP+CSET_GE",
    )
}

/// Proof: trust_ir::Icmp(SignedGreaterThan, I64) -> CMP + CSET GT (64-bit)
pub fn proof_icmp_sgt_i64() -> ProofObligation {
    use trust_cg_lower::instructions::IntCC;
    use trust_cg_lower::isel::AArch64CC;
    proof_icmp_generic(
        IntCC::SignedGreaterThan,
        AArch64CC::GT,
        64,
        "Icmp_SGT_I64 -> CMP+CSET_GT",
    )
}

/// Proof: trust_ir::Icmp(SignedLessThanOrEqual, I64) -> CMP + CSET LE (64-bit)
pub fn proof_icmp_sle_i64() -> ProofObligation {
    use trust_cg_lower::instructions::IntCC;
    use trust_cg_lower::isel::AArch64CC;
    proof_icmp_generic(
        IntCC::SignedLessThanOrEqual,
        AArch64CC::LE,
        64,
        "Icmp_SLE_I64 -> CMP+CSET_LE",
    )
}

/// Proof: trust_ir::Icmp(UnsignedGreaterThanOrEqual, I64) -> CMP + CSET HS (64-bit)
pub fn proof_icmp_uge_i64() -> ProofObligation {
    use trust_cg_lower::instructions::IntCC;
    use trust_cg_lower::isel::AArch64CC;
    proof_icmp_generic(
        IntCC::UnsignedGreaterThanOrEqual,
        AArch64CC::HS,
        64,
        "Icmp_UGE_I64 -> CMP+CSET_HS",
    )
}

/// Proof: trust_ir::Icmp(UnsignedGreaterThan, I64) -> CMP + CSET HI (64-bit)
pub fn proof_icmp_ugt_i64() -> ProofObligation {
    use trust_cg_lower::instructions::IntCC;
    use trust_cg_lower::isel::AArch64CC;
    proof_icmp_generic(
        IntCC::UnsignedGreaterThan,
        AArch64CC::HI,
        64,
        "Icmp_UGT_I64 -> CMP+CSET_HI",
    )
}

/// Proof: trust_ir::Icmp(UnsignedLessThanOrEqual, I64) -> CMP + CSET LS (64-bit)
pub fn proof_icmp_ule_i64() -> ProofObligation {
    use trust_cg_lower::instructions::IntCC;
    use trust_cg_lower::isel::AArch64CC;
    proof_icmp_generic(
        IntCC::UnsignedLessThanOrEqual,
        AArch64CC::LS,
        64,
        "Icmp_ULE_I64 -> CMP+CSET_LS",
    )
}

/// Return all 10 comparison lowering proofs (64-bit).
pub fn all_comparison_proofs_i64() -> Vec<ProofObligation> {
    vec![
        proof_icmp_eq_i64(),
        proof_icmp_ne_i64(),
        proof_icmp_slt_i64(),
        proof_icmp_sge_i64(),
        proof_icmp_sgt_i64(),
        proof_icmp_sle_i64(),
        proof_icmp_ult_i64(),
        // #62 retraction lifted (see i32): C is the adder carry-out now.
        proof_icmp_uge_i64(),
        proof_icmp_ugt_i64(),
        proof_icmp_ule_i64(),
    ]
}

// ---------------------------------------------------------------------------
// Branch lowering proofs: trust_ir::CondBr(Icmp) -> CMP + B.cond
// ---------------------------------------------------------------------------

/// Build a proof that conditional branch lowering preserves semantics.
///
/// `trust_ir::CondBr(Icmp(cond, a, b))` branches if the comparison is true.
/// AArch64 lowers this to `CMP Rn, Rm ; B.cc target`.
///
/// The proof obligation: the branch is taken (condition evaluates to true)
/// iff the trust_ir comparison evaluates to true.
fn proof_condbr_generic(
    intcc: trust_cg_lower::instructions::IntCC,
    aarch64cc: trust_cg_lower::isel::AArch64CC,
    width: u32,
    name: &str,
) -> ProofObligation {
    use crate::nzcv::{encode_cmp, eval_condition};
    use crate::trust_ir_semantics::encode_trust_ir_icmp;
    use trust_cg_lower::types::Type;

    let ty = if width == 32 { Type::I32 } else { Type::I64 };
    let a = SmtExpr::var("a", width);
    let b = SmtExpr::var("b", width);

    // trust_ir side: Icmp produces B1. Branch is taken if result == 1.
    let trust_ir_cmp = encode_trust_ir_icmp(&intcc, ty, a.clone(), b.clone());
    // This is already a BV1 (0 or 1). Branch taken iff == 1.
    // We use it directly for comparison.

    // AArch64 side: CMP sets flags, B.cond evaluates condition.
    // eval_condition returns a Bool. Convert to BV1 for comparison.
    let flags = encode_cmp(a, b, width);
    let cond_bool = eval_condition(aarch64cc, &flags);
    let aarch64_branch_taken =
        SmtExpr::ite(cond_bool, SmtExpr::bv_const(1, 1), SmtExpr::bv_const(0, 1));

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: name.to_string(),
        trust_ir_expr: trust_ir_cmp,
        aarch64_expr: aarch64_branch_taken,
        inputs: vec![("a".to_string(), width), ("b".to_string(), width)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// Proof: trust_ir::CondBr(Icmp(Equal)) -> CMP + B.EQ
pub fn proof_condbr_eq_i32() -> ProofObligation {
    use trust_cg_lower::instructions::IntCC;
    use trust_cg_lower::isel::AArch64CC;
    proof_condbr_generic(IntCC::Equal, AArch64CC::EQ, 32, "CondBr_Eq_I32 -> CMP+B.EQ")
}

/// Proof: trust_ir::CondBr(Icmp(NotEqual)) -> CMP + B.NE
pub fn proof_condbr_ne_i32() -> ProofObligation {
    use trust_cg_lower::instructions::IntCC;
    use trust_cg_lower::isel::AArch64CC;
    proof_condbr_generic(
        IntCC::NotEqual,
        AArch64CC::NE,
        32,
        "CondBr_NE_I32 -> CMP+B.NE",
    )
}

/// Proof: trust_ir::CondBr(Icmp(SignedLessThan)) -> CMP + B.LT
pub fn proof_condbr_slt_i32() -> ProofObligation {
    use trust_cg_lower::instructions::IntCC;
    use trust_cg_lower::isel::AArch64CC;
    proof_condbr_generic(
        IntCC::SignedLessThan,
        AArch64CC::LT,
        32,
        "CondBr_SLT_I32 -> CMP+B.LT",
    )
}

/// Proof: trust_ir::CondBr(Icmp(UnsignedLessThan)) -> CMP + B.LO
pub fn proof_condbr_ult_i32() -> ProofObligation {
    use trust_cg_lower::instructions::IntCC;
    use trust_cg_lower::isel::AArch64CC;
    proof_condbr_generic(
        IntCC::UnsignedLessThan,
        AArch64CC::LO,
        32,
        "CondBr_ULT_I32 -> CMP+B.LO",
    )
}

/// Proof: trust_ir::CondBr(Icmp(SignedGreaterThanOrEqual)) -> CMP + B.GE
pub fn proof_condbr_sge_i32() -> ProofObligation {
    use trust_cg_lower::instructions::IntCC;
    use trust_cg_lower::isel::AArch64CC;
    proof_condbr_generic(
        IntCC::SignedGreaterThanOrEqual,
        AArch64CC::GE,
        32,
        "CondBr_SGE_I32 -> CMP+B.GE",
    )
}

/// Proof: trust_ir::CondBr(Icmp(SignedGreaterThan)) -> CMP + B.GT
pub fn proof_condbr_sgt_i32() -> ProofObligation {
    use trust_cg_lower::instructions::IntCC;
    use trust_cg_lower::isel::AArch64CC;
    proof_condbr_generic(
        IntCC::SignedGreaterThan,
        AArch64CC::GT,
        32,
        "CondBr_SGT_I32 -> CMP+B.GT",
    )
}

/// Proof: trust_ir::CondBr(Icmp(SignedLessThanOrEqual)) -> CMP + B.LE
pub fn proof_condbr_sle_i32() -> ProofObligation {
    use trust_cg_lower::instructions::IntCC;
    use trust_cg_lower::isel::AArch64CC;
    proof_condbr_generic(
        IntCC::SignedLessThanOrEqual,
        AArch64CC::LE,
        32,
        "CondBr_SLE_I32 -> CMP+B.LE",
    )
}

/// Proof: trust_ir::CondBr(Icmp(UnsignedGreaterThanOrEqual)) -> CMP + B.HS
pub fn proof_condbr_uge_i32() -> ProofObligation {
    use trust_cg_lower::instructions::IntCC;
    use trust_cg_lower::isel::AArch64CC;
    proof_condbr_generic(
        IntCC::UnsignedGreaterThanOrEqual,
        AArch64CC::HS,
        32,
        "CondBr_UGE_I32 -> CMP+B.HS",
    )
}

/// Proof: trust_ir::CondBr(Icmp(UnsignedGreaterThan)) -> CMP + B.HI
pub fn proof_condbr_ugt_i32() -> ProofObligation {
    use trust_cg_lower::instructions::IntCC;
    use trust_cg_lower::isel::AArch64CC;
    proof_condbr_generic(
        IntCC::UnsignedGreaterThan,
        AArch64CC::HI,
        32,
        "CondBr_UGT_I32 -> CMP+B.HI",
    )
}

/// Proof: trust_ir::CondBr(Icmp(UnsignedLessThanOrEqual)) -> CMP + B.LS
pub fn proof_condbr_ule_i32() -> ProofObligation {
    use trust_cg_lower::instructions::IntCC;
    use trust_cg_lower::isel::AArch64CC;
    proof_condbr_generic(
        IntCC::UnsignedLessThanOrEqual,
        AArch64CC::LS,
        32,
        "CondBr_ULE_I32 -> CMP+B.LS",
    )
}

/// Return all 10 branch lowering proofs (32-bit).
pub fn all_branch_proofs_i32() -> Vec<ProofObligation> {
    vec![
        proof_condbr_eq_i32(),
        proof_condbr_ne_i32(),
        proof_condbr_slt_i32(),
        proof_condbr_sge_i32(),
        proof_condbr_sgt_i32(),
        proof_condbr_sle_i32(),
        proof_condbr_ult_i32(),
        // #62 (group b) retracted CondBr_UGE_I32 -> CMP+B.HS as degenerate while C
        // was spelled `bvuge`; lifted with the adder carry-out model (nzcv.rs).
        proof_condbr_uge_i32(),
        proof_condbr_ugt_i32(),
        proof_condbr_ule_i32(),
    ]
}

// ---------------------------------------------------------------------------
// 64-bit branch lowering proofs: trust_ir::CondBr(Icmp, I64) -> CMP + B.cond
// ---------------------------------------------------------------------------

/// Proof: trust_ir::CondBr(Icmp(Equal, I64)) -> CMP + B.EQ (64-bit)
pub fn proof_condbr_eq_i64() -> ProofObligation {
    use trust_cg_lower::instructions::IntCC;
    use trust_cg_lower::isel::AArch64CC;
    proof_condbr_generic(IntCC::Equal, AArch64CC::EQ, 64, "CondBr_Eq_I64 -> CMP+B.EQ")
}

/// Proof: trust_ir::CondBr(Icmp(NotEqual, I64)) -> CMP + B.NE (64-bit)
pub fn proof_condbr_ne_i64() -> ProofObligation {
    use trust_cg_lower::instructions::IntCC;
    use trust_cg_lower::isel::AArch64CC;
    proof_condbr_generic(
        IntCC::NotEqual,
        AArch64CC::NE,
        64,
        "CondBr_NE_I64 -> CMP+B.NE",
    )
}

/// Proof: trust_ir::CondBr(Icmp(SignedLessThan, I64)) -> CMP + B.LT (64-bit)
pub fn proof_condbr_slt_i64() -> ProofObligation {
    use trust_cg_lower::instructions::IntCC;
    use trust_cg_lower::isel::AArch64CC;
    proof_condbr_generic(
        IntCC::SignedLessThan,
        AArch64CC::LT,
        64,
        "CondBr_SLT_I64 -> CMP+B.LT",
    )
}

/// Proof: trust_ir::CondBr(Icmp(SignedGreaterThanOrEqual, I64)) -> CMP + B.GE (64-bit)
pub fn proof_condbr_sge_i64() -> ProofObligation {
    use trust_cg_lower::instructions::IntCC;
    use trust_cg_lower::isel::AArch64CC;
    proof_condbr_generic(
        IntCC::SignedGreaterThanOrEqual,
        AArch64CC::GE,
        64,
        "CondBr_SGE_I64 -> CMP+B.GE",
    )
}

/// Proof: trust_ir::CondBr(Icmp(SignedGreaterThan, I64)) -> CMP + B.GT (64-bit)
pub fn proof_condbr_sgt_i64() -> ProofObligation {
    use trust_cg_lower::instructions::IntCC;
    use trust_cg_lower::isel::AArch64CC;
    proof_condbr_generic(
        IntCC::SignedGreaterThan,
        AArch64CC::GT,
        64,
        "CondBr_SGT_I64 -> CMP+B.GT",
    )
}

/// Proof: trust_ir::CondBr(Icmp(SignedLessThanOrEqual, I64)) -> CMP + B.LE (64-bit)
pub fn proof_condbr_sle_i64() -> ProofObligation {
    use trust_cg_lower::instructions::IntCC;
    use trust_cg_lower::isel::AArch64CC;
    proof_condbr_generic(
        IntCC::SignedLessThanOrEqual,
        AArch64CC::LE,
        64,
        "CondBr_SLE_I64 -> CMP+B.LE",
    )
}

/// Proof: trust_ir::CondBr(Icmp(UnsignedLessThan, I64)) -> CMP + B.LO (64-bit)
pub fn proof_condbr_ult_i64() -> ProofObligation {
    use trust_cg_lower::instructions::IntCC;
    use trust_cg_lower::isel::AArch64CC;
    proof_condbr_generic(
        IntCC::UnsignedLessThan,
        AArch64CC::LO,
        64,
        "CondBr_ULT_I64 -> CMP+B.LO",
    )
}

/// Proof: trust_ir::CondBr(Icmp(UnsignedGreaterThanOrEqual, I64)) -> CMP + B.HS (64-bit)
pub fn proof_condbr_uge_i64() -> ProofObligation {
    use trust_cg_lower::instructions::IntCC;
    use trust_cg_lower::isel::AArch64CC;
    proof_condbr_generic(
        IntCC::UnsignedGreaterThanOrEqual,
        AArch64CC::HS,
        64,
        "CondBr_UGE_I64 -> CMP+B.HS",
    )
}

/// Proof: trust_ir::CondBr(Icmp(UnsignedGreaterThan, I64)) -> CMP + B.HI (64-bit)
pub fn proof_condbr_ugt_i64() -> ProofObligation {
    use trust_cg_lower::instructions::IntCC;
    use trust_cg_lower::isel::AArch64CC;
    proof_condbr_generic(
        IntCC::UnsignedGreaterThan,
        AArch64CC::HI,
        64,
        "CondBr_UGT_I64 -> CMP+B.HI",
    )
}

/// Proof: trust_ir::CondBr(Icmp(UnsignedLessThanOrEqual, I64)) -> CMP + B.LS (64-bit)
pub fn proof_condbr_ule_i64() -> ProofObligation {
    use trust_cg_lower::instructions::IntCC;
    use trust_cg_lower::isel::AArch64CC;
    proof_condbr_generic(
        IntCC::UnsignedLessThanOrEqual,
        AArch64CC::LS,
        64,
        "CondBr_ULE_I64 -> CMP+B.LS",
    )
}

/// Return all 10 branch lowering proofs (64-bit).
pub fn all_branch_proofs_i64() -> Vec<ProofObligation> {
    vec![
        proof_condbr_eq_i64(),
        proof_condbr_ne_i64(),
        proof_condbr_slt_i64(),
        proof_condbr_sge_i64(),
        proof_condbr_sgt_i64(),
        proof_condbr_sle_i64(),
        proof_condbr_ult_i64(),
        // #62 retraction lifted (see i32): C is the adder carry-out now.
        proof_condbr_uge_i64(),
        proof_condbr_ugt_i64(),
        proof_condbr_ule_i64(),
    ]
}

/// Return all branch lowering proofs (both 32-bit and 64-bit).
pub fn all_branch_proofs() -> Vec<ProofObligation> {
    let mut proofs = all_branch_proofs_i32();
    proofs.extend(all_branch_proofs_i64());
    proofs
}

/// Return all NZCV-related proofs (flags + comparisons + branches).
pub fn all_nzcv_proofs() -> Vec<ProofObligation> {
    let mut proofs = Vec::new();
    proofs.extend(all_comparison_proofs_i32());
    proofs.extend(all_comparison_proofs_i64());
    proofs.extend(all_branch_proofs());
    proofs
}

// ---------------------------------------------------------------------------
// Load/Store lowering proofs
// ---------------------------------------------------------------------------
//
// Proofs that trust_ir Load/Store operations are correctly lowered to
// AArch64 LDR/STR instructions. These use the symbolic SMT array theory
// (Array(BV64, BV8)) to model byte-addressable memory.
//
// The proof structure for each load lowering:
//   forall base: BV64, mem_default: BV8 .
//     let mem = ConstArray(BV64, mem_default)
//     encode_trust_ir_load(mem, base, 0, size) == encode_aarch64_ldr_imm(mem, base, 0, size)
//
// The proof structure for each store lowering:
//   forall base: BV64, value: BV(size*8), mem_default: BV8 .
//     let mem = ConstArray(BV64, mem_default)
//     let trust_ir_mem = encode_trust_ir_store(mem, base, 0, value, size)
//     let aarch64_mem = encode_aarch64_str_imm(mem, base, 0, value, size)
//     load(trust_ir_mem, base, size) == load(aarch64_mem, base, size)
//
// These delegate to the symbolic encoders in memory_proofs.rs which build
// the actual SMT array expressions.
//
// Reference: ARM DDI 0487, C6.2.131-132 (LDRB/LDR), C6.2.134 (LDRH),
//            C6.2.257-258 (STR/STRB/STRH).

/// Proof: `trust_ir::Load(I32, addr)` == `LDRWui [Xn, #0]` (32-bit load, zero offset).
///
/// Verifies that loading 4 bytes from base address produces the same
/// result via trust_ir semantics and AArch64 LDRWui with zero scaled offset.
///
/// Both sides read from the same symbolic ConstArray memory, so the proof
/// holds for all possible initial memory contents.
pub fn proof_load_i32_lowering() -> ProofObligation {
    crate::memory_proofs::proof_load_i32()
}

/// Proof: `trust_ir::Load(I64, addr)` == `LDRXui [Xn, #0]` (64-bit load, zero offset).
pub fn proof_load_i64_lowering() -> ProofObligation {
    crate::memory_proofs::proof_load_i64()
}

/// Proof: `trust_ir::Store(I32, val, addr)` == `STRWui [Xn, #0]` (32-bit store, zero offset).
///
/// Verifies that storing a 32-bit value via trust_ir and AArch64 STRWui produces
/// identical memory states. Checked by storing, then loading back from both
/// memories and comparing the results.
pub fn proof_store_i32_lowering() -> ProofObligation {
    crate::memory_proofs::proof_store_i32()
}

/// Proof: `trust_ir::Store(I64, val, addr)` == `STRXui [Xn, #0]` (64-bit store, zero offset).
pub fn proof_store_i64_lowering() -> ProofObligation {
    crate::memory_proofs::proof_store_i64()
}

/// Proof: `trust_ir::Load(I8, addr)` == `LDRB Wt, [Xn, #0]` (8-bit load, zero offset).
///
/// On AArch64, LDRB loads a single byte and zero-extends it to 32 bits
/// in the destination W register. The trust_ir side loads 1 byte.
///
/// Reference: ARM DDI 0487, C6.2.131.
pub fn proof_load_i8_lowering() -> ProofObligation {
    crate::memory_proofs::proof_load_i8()
}

/// Proof: `trust_ir::Load(I16, addr)` == `LDRH Wt, [Xn, #0]` (16-bit load, zero offset).
///
/// LDRH loads a 16-bit halfword in little-endian order and zero-extends
/// it to 32 bits. The trust_ir side loads 2 bytes.
///
/// Reference: ARM DDI 0487, C6.2.134.
pub fn proof_load_i16_lowering() -> ProofObligation {
    crate::memory_proofs::proof_load_i16()
}

/// Proof: `trust_ir::Store(I8, val, addr)` == `STRB Wt, [Xn, #0]` (8-bit store, zero offset).
///
/// STRB stores the least significant byte of the W register to memory.
///
/// Reference: ARM DDI 0487, C6.2.258.
pub fn proof_store_i8_lowering() -> ProofObligation {
    crate::memory_proofs::proof_store_i8()
}

/// Proof: `trust_ir::Store(I16, val, addr)` == `STRH Wt, [Xn, #0]` (16-bit store, zero offset).
///
/// STRH stores the least significant halfword of the W register to memory
/// in little-endian byte order.
///
/// Reference: ARM DDI 0487, C6.2.259.
pub fn proof_store_i16_lowering() -> ProofObligation {
    crate::memory_proofs::proof_store_i16()
}

/// Proof: store then load at same address returns stored value (32-bit).
///
/// ```text
/// forall base: BV64, value: BV32, mem_default: BV8 .
///   let mem = ConstArray(BV64, mem_default)
///   let mem' = store(mem, base, value, 4)
///   load(mem', base, 4) == value
/// ```
///
/// This is the fundamental store-load coherence property: memory behaves as
/// a reliable array. Critical for compiler correctness -- if this fails,
/// no program that uses memory can be verified.
pub fn proof_load_store_roundtrip_i32() -> ProofObligation {
    crate::memory_proofs::proof_roundtrip_i32()
}

/// Proof: store then load at same address returns stored value (64-bit).
///
/// The 64-bit version exercises the full 8-byte little-endian decomposition
/// and reassembly path through the SMT array model.
pub fn proof_load_store_roundtrip_i64() -> ProofObligation {
    crate::memory_proofs::proof_roundtrip_i64()
}

/// Return all load/store lowering proofs (10 total).
///
/// Covers:
/// - Load equivalence: I8, I16, I32, I64 (trust_ir Load == AArch64 LDR/LDRB/LDRH)
/// - Store equivalence: I8, I16, I32, I64 (trust_ir Store == AArch64 STR/STRB/STRH)
/// - Store-load roundtrip: I32, I64 (store then load returns same value)
pub fn all_load_store_proofs() -> Vec<ProofObligation> {
    // #62 retraction: the per-width "Load_I* -> LDR*ui [Xn,#0]" / "Store_I* ->
    // STR*ui [Xn,#0]" obligations were degenerate X==X (the trust_ir memory
    // expression and the machine side are the SAME constructed expression; no
    // independent address-mode encoder, a wrong [Xn,#imm] could not refute). They
    // are RETRACTED. The GENUINE store-then-load roundtrip proofs (which carry the
    // real load/store coverage via the memory-model array theory) remain.
    vec![
        proof_load_store_roundtrip_i32(),
        proof_load_store_roundtrip_i64(),
    ]
}

// ---------------------------------------------------------------------------
// I8 bitwise/shift lowering proofs (exhaustive — all 2^16 or 2^8 combos)
// ---------------------------------------------------------------------------

/// Build the proof obligation for: `trust_ir::Band(I8, a, b) -> AND (8-bit)`
///
/// On AArch64, 8-bit operations are performed in 32-bit W registers.
/// The proof verifies semantic equivalence at the 8-bit bitvector level.
pub fn proof_band_i8() -> ProofObligation {
    use crate::trust_ir_semantics::encode_trust_ir_bitwise_binop;
    use trust_cg_lower::instructions::Opcode;
    use trust_cg_lower::types::Type;

    let a = SmtExpr::var("a", 8);
    let b = SmtExpr::var("b", 8);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "Band_I8 -> AND (8-bit)".to_string(),
        trust_ir_expr: encode_trust_ir_bitwise_binop(&Opcode::Band, Type::I8, a.clone(), b.clone()),
        aarch64_expr: a.bvand(b),
        inputs: vec![("a".to_string(), 8), ("b".to_string(), 8)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// Build the proof obligation for: `trust_ir::Bor(I8, a, b) -> OR (8-bit)`
pub fn proof_bor_i8() -> ProofObligation {
    use crate::trust_ir_semantics::encode_trust_ir_bitwise_binop;
    use trust_cg_lower::instructions::Opcode;
    use trust_cg_lower::types::Type;

    let a = SmtExpr::var("a", 8);
    let b = SmtExpr::var("b", 8);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "Bor_I8 -> OR (8-bit)".to_string(),
        trust_ir_expr: encode_trust_ir_bitwise_binop(&Opcode::Bor, Type::I8, a.clone(), b.clone()),
        aarch64_expr: a.bvor(b),
        inputs: vec![("a".to_string(), 8), ("b".to_string(), 8)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// Build the proof obligation for: `trust_ir::Bxor(I8, a, b) -> XOR (8-bit)`
pub fn proof_bxor_i8() -> ProofObligation {
    use crate::trust_ir_semantics::encode_trust_ir_bitwise_binop;
    use trust_cg_lower::instructions::Opcode;
    use trust_cg_lower::types::Type;

    let a = SmtExpr::var("a", 8);
    let b = SmtExpr::var("b", 8);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "Bxor_I8 -> XOR (8-bit)".to_string(),
        trust_ir_expr: encode_trust_ir_bitwise_binop(&Opcode::Bxor, Type::I8, a.clone(), b.clone()),
        aarch64_expr: a.bvxor(b),
        inputs: vec![("a".to_string(), 8), ("b".to_string(), 8)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// Build the proof obligation for: `trust_ir::Bnot(I8, a) -> NOT (8-bit)`
///
/// MVN on AArch64 is `ORN Rd, XZR, Rm` = bitwise complement.
pub fn proof_bnot_i8() -> ProofObligation {
    use crate::trust_ir_semantics::encode_trust_ir_bnot;
    use trust_cg_lower::types::Type;

    let a = SmtExpr::var("a", 8);
    let all_ones = SmtExpr::bv_const(mask(u64::MAX, 8), 8);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "Bnot_I8 -> NOT (8-bit)".to_string(),
        trust_ir_expr: encode_trust_ir_bnot(Type::I8, a.clone()),
        aarch64_expr: a.bvxor(all_ones),
        inputs: vec![("a".to_string(), 8)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// Build the proof obligation for: `trust_ir::Ishl(I8, a, b) -> SHL (8-bit)`
pub fn proof_ishl_i8() -> ProofObligation {
    use crate::trust_ir_semantics::encode_trust_ir_shift;
    use trust_cg_lower::instructions::Opcode;
    use trust_cg_lower::types::Type;

    let a = SmtExpr::var("a", 8);
    let b = SmtExpr::var("b", 8);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "Ishl_I8 -> SHL (8-bit)".to_string(),
        trust_ir_expr: encode_trust_ir_shift(&Opcode::Ishl, Type::I8, a.clone(), b.clone()),
        aarch64_expr: a.clone().bvshl(b.clone()),
        inputs: vec![("a".to_string(), 8), ("b".to_string(), 8)],
        preconditions: vec![shift_in_range_precondition(b, 8)],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// Build the proof obligation for: `trust_ir::Ushr(I8, a, b) -> LSR (8-bit)`
pub fn proof_ushr_i8() -> ProofObligation {
    use crate::trust_ir_semantics::encode_trust_ir_shift;
    use trust_cg_lower::instructions::Opcode;
    use trust_cg_lower::types::Type;

    let a = SmtExpr::var("a", 8);
    let b = SmtExpr::var("b", 8);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "Ushr_I8 -> LSR (8-bit)".to_string(),
        trust_ir_expr: encode_trust_ir_shift(&Opcode::Ushr, Type::I8, a.clone(), b.clone()),
        aarch64_expr: a.clone().bvlshr(b.clone()),
        inputs: vec![("a".to_string(), 8), ("b".to_string(), 8)],
        preconditions: vec![shift_in_range_precondition(b, 8)],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// Build the proof obligation for: `trust_ir::Sshr(I8, a, b) -> ASR (8-bit)`
pub fn proof_sshr_i8() -> ProofObligation {
    use crate::trust_ir_semantics::encode_trust_ir_shift;
    use trust_cg_lower::instructions::Opcode;
    use trust_cg_lower::types::Type;

    let a = SmtExpr::var("a", 8);
    let b = SmtExpr::var("b", 8);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "Sshr_I8 -> ASR (8-bit)".to_string(),
        trust_ir_expr: encode_trust_ir_shift(&Opcode::Sshr, Type::I8, a.clone(), b.clone()),
        aarch64_expr: a.clone().bvashr(b.clone()),
        inputs: vec![("a".to_string(), 8), ("b".to_string(), 8)],
        preconditions: vec![shift_in_range_precondition(b, 8)],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// Build the proof obligation for: `trust_ir::BandNot(I8, a, b) -> BIC (8-bit)`
///
/// BIC (bit clear) on AArch64: `Rd = Rn & ~Rm`.
/// trust_ir `BandNot` has identical semantics; issue #425 wires the default-on
/// lowering proof.
pub fn proof_bic_i8() -> ProofObligation {
    use crate::aarch64_semantics::encode_bic_rr;
    use crate::trust_ir_semantics::encode_trust_ir_bitwise_binop;
    use trust_cg_ir::cc::OperandSize;
    use trust_cg_lower::instructions::Opcode;
    use trust_cg_lower::types::Type;

    let a = SmtExpr::var("a", 8);
    let b = SmtExpr::var("b", 8);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "BandNot_I8 -> BIC (8-bit)".to_string(),
        trust_ir_expr: encode_trust_ir_bitwise_binop(
            &Opcode::BandNot,
            Type::I8,
            a.clone(),
            b.clone(),
        ),
        aarch64_expr: encode_bic_rr(OperandSize::S32, a, b),
        inputs: vec![("a".to_string(), 8), ("b".to_string(), 8)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// Build the proof obligation for: `trust_ir::BorNot(I8, a, b) -> ORN (8-bit)`
///
/// ORN on AArch64: `Rd = Rn | ~Rm`. trust_ir `BorNot` has identical semantics;
/// issue #425 wires the default-on lowering proof.
pub fn proof_orn_i8() -> ProofObligation {
    use crate::aarch64_semantics::encode_orn_rr;
    use crate::trust_ir_semantics::encode_trust_ir_bitwise_binop;
    use trust_cg_ir::cc::OperandSize;
    use trust_cg_lower::instructions::Opcode;
    use trust_cg_lower::types::Type;

    let a = SmtExpr::var("a", 8);
    let b = SmtExpr::var("b", 8);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "BorNot_I8 -> ORN (8-bit)".to_string(),
        trust_ir_expr: encode_trust_ir_bitwise_binop(
            &Opcode::BorNot,
            Type::I8,
            a.clone(),
            b.clone(),
        ),
        aarch64_expr: encode_orn_rr(OperandSize::S32, a, b),
        inputs: vec![("a".to_string(), 8), ("b".to_string(), 8)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

// ---------------------------------------------------------------------------
// I16 bitwise/shift lowering proofs (statistical — edge cases + random sampling)
// ---------------------------------------------------------------------------

/// Build the proof obligation for: `trust_ir::Band(I16, a, b) -> AND (16-bit)`
///
/// On AArch64, 16-bit operations are performed in 32-bit W registers.
/// The proof verifies semantic equivalence at the 16-bit bitvector level.
pub fn proof_band_i16() -> ProofObligation {
    use crate::trust_ir_semantics::encode_trust_ir_bitwise_binop;
    use trust_cg_lower::instructions::Opcode;
    use trust_cg_lower::types::Type;

    let a = SmtExpr::var("a", 16);
    let b = SmtExpr::var("b", 16);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "Band_I16 -> AND (16-bit)".to_string(),
        trust_ir_expr: encode_trust_ir_bitwise_binop(
            &Opcode::Band,
            Type::I16,
            a.clone(),
            b.clone(),
        ),
        aarch64_expr: a.bvand(b),
        inputs: vec![("a".to_string(), 16), ("b".to_string(), 16)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// Build the proof obligation for: `trust_ir::Bor(I16, a, b) -> OR (16-bit)`
pub fn proof_bor_i16() -> ProofObligation {
    use crate::trust_ir_semantics::encode_trust_ir_bitwise_binop;
    use trust_cg_lower::instructions::Opcode;
    use trust_cg_lower::types::Type;

    let a = SmtExpr::var("a", 16);
    let b = SmtExpr::var("b", 16);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "Bor_I16 -> OR (16-bit)".to_string(),
        trust_ir_expr: encode_trust_ir_bitwise_binop(&Opcode::Bor, Type::I16, a.clone(), b.clone()),
        aarch64_expr: a.bvor(b),
        inputs: vec![("a".to_string(), 16), ("b".to_string(), 16)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// Build the proof obligation for: `trust_ir::Bxor(I16, a, b) -> XOR (16-bit)`
pub fn proof_bxor_i16() -> ProofObligation {
    use crate::trust_ir_semantics::encode_trust_ir_bitwise_binop;
    use trust_cg_lower::instructions::Opcode;
    use trust_cg_lower::types::Type;

    let a = SmtExpr::var("a", 16);
    let b = SmtExpr::var("b", 16);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "Bxor_I16 -> XOR (16-bit)".to_string(),
        trust_ir_expr: encode_trust_ir_bitwise_binop(
            &Opcode::Bxor,
            Type::I16,
            a.clone(),
            b.clone(),
        ),
        aarch64_expr: a.bvxor(b),
        inputs: vec![("a".to_string(), 16), ("b".to_string(), 16)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// Build the proof obligation for: `trust_ir::Bnot(I16, a) -> NOT (16-bit)`
pub fn proof_bnot_i16() -> ProofObligation {
    use crate::trust_ir_semantics::encode_trust_ir_bnot;
    use trust_cg_lower::types::Type;

    let a = SmtExpr::var("a", 16);
    let all_ones = SmtExpr::bv_const(mask(u64::MAX, 16), 16);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "Bnot_I16 -> NOT (16-bit)".to_string(),
        trust_ir_expr: encode_trust_ir_bnot(Type::I16, a.clone()),
        aarch64_expr: a.bvxor(all_ones),
        inputs: vec![("a".to_string(), 16)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// Build the proof obligation for: `trust_ir::Ishl(I16, a, b) -> SHL (16-bit)`
pub fn proof_ishl_i16() -> ProofObligation {
    use crate::trust_ir_semantics::encode_trust_ir_shift;
    use trust_cg_lower::instructions::Opcode;
    use trust_cg_lower::types::Type;

    let a = SmtExpr::var("a", 16);
    let b = SmtExpr::var("b", 16);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "Ishl_I16 -> SHL (16-bit)".to_string(),
        trust_ir_expr: encode_trust_ir_shift(&Opcode::Ishl, Type::I16, a.clone(), b.clone()),
        aarch64_expr: a.clone().bvshl(b.clone()),
        inputs: vec![("a".to_string(), 16), ("b".to_string(), 16)],
        preconditions: vec![shift_in_range_precondition(b, 16)],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// Build the proof obligation for: `trust_ir::Ushr(I16, a, b) -> LSR (16-bit)`
pub fn proof_ushr_i16() -> ProofObligation {
    use crate::trust_ir_semantics::encode_trust_ir_shift;
    use trust_cg_lower::instructions::Opcode;
    use trust_cg_lower::types::Type;

    let a = SmtExpr::var("a", 16);
    let b = SmtExpr::var("b", 16);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "Ushr_I16 -> LSR (16-bit)".to_string(),
        trust_ir_expr: encode_trust_ir_shift(&Opcode::Ushr, Type::I16, a.clone(), b.clone()),
        aarch64_expr: a.clone().bvlshr(b.clone()),
        inputs: vec![("a".to_string(), 16), ("b".to_string(), 16)],
        preconditions: vec![shift_in_range_precondition(b, 16)],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// Build the proof obligation for: `trust_ir::Sshr(I16, a, b) -> ASR (16-bit)`
pub fn proof_sshr_i16() -> ProofObligation {
    use crate::trust_ir_semantics::encode_trust_ir_shift;
    use trust_cg_lower::instructions::Opcode;
    use trust_cg_lower::types::Type;

    let a = SmtExpr::var("a", 16);
    let b = SmtExpr::var("b", 16);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "Sshr_I16 -> ASR (16-bit)".to_string(),
        trust_ir_expr: encode_trust_ir_shift(&Opcode::Sshr, Type::I16, a.clone(), b.clone()),
        aarch64_expr: a.clone().bvashr(b.clone()),
        inputs: vec![("a".to_string(), 16), ("b".to_string(), 16)],
        preconditions: vec![shift_in_range_precondition(b, 16)],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// Build the proof obligation for: `trust_ir::BandNot(I16, a, b) -> BIC (16-bit)`
///
/// BIC (bit clear) on AArch64: `Rd = Rn & ~Rm`. On AArch64, 16-bit operations
/// are performed in 32-bit W registers; `encode_bic_rr` derives complement
/// width from the operand's bitvector sort so the I16 proof composes
/// correctly. I16 sibling of `proof_bic_i8` (issue #425), widened for
/// the #407 ay smoke rollout.
pub fn proof_bic_i16() -> ProofObligation {
    use crate::aarch64_semantics::encode_bic_rr;
    use crate::trust_ir_semantics::encode_trust_ir_bitwise_binop;
    use trust_cg_ir::cc::OperandSize;
    use trust_cg_lower::instructions::Opcode;
    use trust_cg_lower::types::Type;

    let a = SmtExpr::var("a", 16);
    let b = SmtExpr::var("b", 16);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "BandNot_I16 -> BIC (16-bit)".to_string(),
        trust_ir_expr: encode_trust_ir_bitwise_binop(
            &Opcode::BandNot,
            Type::I16,
            a.clone(),
            b.clone(),
        ),
        aarch64_expr: encode_bic_rr(OperandSize::S32, a, b),
        inputs: vec![("a".to_string(), 16), ("b".to_string(), 16)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// Build the proof obligation for: `trust_ir::BorNot(I16, a, b) -> ORN (16-bit)`
///
/// ORN on AArch64: `Rd = Rn | ~Rm`. I16 sibling of `proof_orn_i8`
/// (issue #425), widened for the #407 ay smoke rollout.
pub fn proof_orn_i16() -> ProofObligation {
    use crate::aarch64_semantics::encode_orn_rr;
    use crate::trust_ir_semantics::encode_trust_ir_bitwise_binop;
    use trust_cg_ir::cc::OperandSize;
    use trust_cg_lower::instructions::Opcode;
    use trust_cg_lower::types::Type;

    let a = SmtExpr::var("a", 16);
    let b = SmtExpr::var("b", 16);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "BorNot_I16 -> ORN (16-bit)".to_string(),
        trust_ir_expr: encode_trust_ir_bitwise_binop(
            &Opcode::BorNot,
            Type::I16,
            a.clone(),
            b.clone(),
        ),
        aarch64_expr: encode_orn_rr(OperandSize::S32, a, b),
        inputs: vec![("a".to_string(), 16), ("b".to_string(), 16)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

// ---------------------------------------------------------------------------
// I32 bitwise/shift lowering proofs (statistical -- 100K random samples)
// ---------------------------------------------------------------------------
//
// Issue #449, epic #407 (Task 3): widen ay smoke to i32/i64. StableHasher
// caching (#420) made wider-width SMT proofs tractable.

/// Build the proof obligation for: `trust_ir::Band(I32, a, b) -> AND (32-bit)`.
pub fn proof_band_i32() -> ProofObligation {
    use crate::trust_ir_semantics::encode_trust_ir_bitwise_binop;
    use trust_cg_lower::instructions::Opcode;
    use trust_cg_lower::types::Type;

    let a = SmtExpr::var("a", 32);
    let b = SmtExpr::var("b", 32);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "Band_I32 -> AND (32-bit)".to_string(),
        trust_ir_expr: encode_trust_ir_bitwise_binop(
            &Opcode::Band,
            Type::I32,
            a.clone(),
            b.clone(),
        ),
        aarch64_expr: a.bvand(b),
        inputs: vec![("a".to_string(), 32), ("b".to_string(), 32)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// Build the proof obligation for: `trust_ir::Bor(I32, a, b) -> OR (32-bit)`.
pub fn proof_bor_i32() -> ProofObligation {
    use crate::trust_ir_semantics::encode_trust_ir_bitwise_binop;
    use trust_cg_lower::instructions::Opcode;
    use trust_cg_lower::types::Type;

    let a = SmtExpr::var("a", 32);
    let b = SmtExpr::var("b", 32);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "Bor_I32 -> OR (32-bit)".to_string(),
        trust_ir_expr: encode_trust_ir_bitwise_binop(&Opcode::Bor, Type::I32, a.clone(), b.clone()),
        aarch64_expr: a.bvor(b),
        inputs: vec![("a".to_string(), 32), ("b".to_string(), 32)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// Build the proof obligation for: `trust_ir::Bxor(I32, a, b) -> XOR (32-bit)`.
pub fn proof_bxor_i32() -> ProofObligation {
    use crate::trust_ir_semantics::encode_trust_ir_bitwise_binop;
    use trust_cg_lower::instructions::Opcode;
    use trust_cg_lower::types::Type;

    let a = SmtExpr::var("a", 32);
    let b = SmtExpr::var("b", 32);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "Bxor_I32 -> XOR (32-bit)".to_string(),
        trust_ir_expr: encode_trust_ir_bitwise_binop(
            &Opcode::Bxor,
            Type::I32,
            a.clone(),
            b.clone(),
        ),
        aarch64_expr: a.bvxor(b),
        inputs: vec![("a".to_string(), 32), ("b".to_string(), 32)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// Build the proof obligation for: `trust_ir::Ishl(I32, a, b) -> LSL (32-bit)`.
pub fn proof_ishl_i32() -> ProofObligation {
    use crate::trust_ir_semantics::encode_trust_ir_shift;
    use trust_cg_lower::instructions::Opcode;
    use trust_cg_lower::types::Type;

    let a = SmtExpr::var("a", 32);
    let b = SmtExpr::var("b", 32);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "Ishl_I32 -> LSL (32-bit)".to_string(),
        trust_ir_expr: encode_trust_ir_shift(&Opcode::Ishl, Type::I32, a.clone(), b.clone()),
        aarch64_expr: a.clone().bvshl(b.clone()),
        inputs: vec![("a".to_string(), 32), ("b".to_string(), 32)],
        preconditions: vec![shift_in_range_precondition(b, 32)],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// Build the proof obligation for: `trust_ir::Ushr(I32, a, b) -> LSR (32-bit)`.
pub fn proof_ushr_i32() -> ProofObligation {
    use crate::trust_ir_semantics::encode_trust_ir_shift;
    use trust_cg_lower::instructions::Opcode;
    use trust_cg_lower::types::Type;

    let a = SmtExpr::var("a", 32);
    let b = SmtExpr::var("b", 32);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "Ushr_I32 -> LSR (32-bit)".to_string(),
        trust_ir_expr: encode_trust_ir_shift(&Opcode::Ushr, Type::I32, a.clone(), b.clone()),
        aarch64_expr: a.clone().bvlshr(b.clone()),
        inputs: vec![("a".to_string(), 32), ("b".to_string(), 32)],
        preconditions: vec![shift_in_range_precondition(b, 32)],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// Build the proof obligation for: `trust_ir::Sshr(I32, a, b) -> ASR (32-bit)`.
pub fn proof_sshr_i32() -> ProofObligation {
    use crate::trust_ir_semantics::encode_trust_ir_shift;
    use trust_cg_lower::instructions::Opcode;
    use trust_cg_lower::types::Type;

    let a = SmtExpr::var("a", 32);
    let b = SmtExpr::var("b", 32);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "Sshr_I32 -> ASR (32-bit)".to_string(),
        trust_ir_expr: encode_trust_ir_shift(&Opcode::Sshr, Type::I32, a.clone(), b.clone()),
        aarch64_expr: a.clone().bvashr(b.clone()),
        inputs: vec![("a".to_string(), 32), ("b".to_string(), 32)],
        preconditions: vec![shift_in_range_precondition(b, 32)],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// Build the proof obligation for: `trust_ir::BandNot(I32, a, b) -> BIC (32-bit)`.
pub fn proof_bic_i32() -> ProofObligation {
    use crate::aarch64_semantics::encode_bic_rr;
    use crate::trust_ir_semantics::encode_trust_ir_bitwise_binop;
    use trust_cg_ir::cc::OperandSize;
    use trust_cg_lower::instructions::Opcode;
    use trust_cg_lower::types::Type;

    let a = SmtExpr::var("a", 32);
    let b = SmtExpr::var("b", 32);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "BandNot_I32 -> BIC (32-bit)".to_string(),
        trust_ir_expr: encode_trust_ir_bitwise_binop(
            &Opcode::BandNot,
            Type::I32,
            a.clone(),
            b.clone(),
        ),
        aarch64_expr: encode_bic_rr(OperandSize::S32, a, b),
        inputs: vec![("a".to_string(), 32), ("b".to_string(), 32)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// Build the proof obligation for: `trust_ir::BorNot(I32, a, b) -> ORN (32-bit)`.
pub fn proof_orn_i32() -> ProofObligation {
    use crate::aarch64_semantics::encode_orn_rr;
    use crate::trust_ir_semantics::encode_trust_ir_bitwise_binop;
    use trust_cg_ir::cc::OperandSize;
    use trust_cg_lower::instructions::Opcode;
    use trust_cg_lower::types::Type;

    let a = SmtExpr::var("a", 32);
    let b = SmtExpr::var("b", 32);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "BorNot_I32 -> ORN (32-bit)".to_string(),
        trust_ir_expr: encode_trust_ir_bitwise_binop(
            &Opcode::BorNot,
            Type::I32,
            a.clone(),
            b.clone(),
        ),
        aarch64_expr: encode_orn_rr(OperandSize::S32, a, b),
        inputs: vec![("a".to_string(), 32), ("b".to_string(), 32)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

// ---------------------------------------------------------------------------
// I64 bitwise/shift lowering proofs (statistical -- 100K random samples)
// ---------------------------------------------------------------------------

/// Build the proof obligation for: `trust_ir::Band(I64, a, b) -> AND (64-bit)`.
pub fn proof_band_i64() -> ProofObligation {
    use crate::trust_ir_semantics::encode_trust_ir_bitwise_binop;
    use trust_cg_lower::instructions::Opcode;
    use trust_cg_lower::types::Type;

    let a = SmtExpr::var("a", 64);
    let b = SmtExpr::var("b", 64);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "Band_I64 -> AND (64-bit)".to_string(),
        trust_ir_expr: encode_trust_ir_bitwise_binop(
            &Opcode::Band,
            Type::I64,
            a.clone(),
            b.clone(),
        ),
        aarch64_expr: a.bvand(b),
        inputs: vec![("a".to_string(), 64), ("b".to_string(), 64)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// Build the proof obligation for: `trust_ir::Bor(I64, a, b) -> OR (64-bit)`.
pub fn proof_bor_i64() -> ProofObligation {
    use crate::trust_ir_semantics::encode_trust_ir_bitwise_binop;
    use trust_cg_lower::instructions::Opcode;
    use trust_cg_lower::types::Type;

    let a = SmtExpr::var("a", 64);
    let b = SmtExpr::var("b", 64);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "Bor_I64 -> OR (64-bit)".to_string(),
        trust_ir_expr: encode_trust_ir_bitwise_binop(&Opcode::Bor, Type::I64, a.clone(), b.clone()),
        aarch64_expr: a.bvor(b),
        inputs: vec![("a".to_string(), 64), ("b".to_string(), 64)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// Build the proof obligation for: `trust_ir::Bxor(I64, a, b) -> XOR (64-bit)`.
pub fn proof_bxor_i64() -> ProofObligation {
    use crate::trust_ir_semantics::encode_trust_ir_bitwise_binop;
    use trust_cg_lower::instructions::Opcode;
    use trust_cg_lower::types::Type;

    let a = SmtExpr::var("a", 64);
    let b = SmtExpr::var("b", 64);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "Bxor_I64 -> XOR (64-bit)".to_string(),
        trust_ir_expr: encode_trust_ir_bitwise_binop(
            &Opcode::Bxor,
            Type::I64,
            a.clone(),
            b.clone(),
        ),
        aarch64_expr: a.bvxor(b),
        inputs: vec![("a".to_string(), 64), ("b".to_string(), 64)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

// ---------------------------------------------------------------------------
// EOR with ROR-shifted source (rotate-fusion peephole) lowering proofs
// ---------------------------------------------------------------------------
//
// The rotate-fusion peephole (`trust_cg_opt::eor_rotate_fuse`) collapses the
// frontend `x ^= ROTL(v, r)` idiom — after `rotate_idiom` turns
// `(v<<r)|(v>>(w-r))` into `RorRI(v, k)` with `k = w - r` — from
//     t = RorRI(s, k); d = EorRR(x, t)
// into the single shifted-register instruction
//     d = EorRRShift(x, s, k)   ==   EOR d, x, s, ROR #k .
//
// FAITHFULNESS / NON-DEGENERACY: the obligation ties two STRUCTURALLY DISTINCT
// SMT expressions that are provably equal:
//   * SOURCE  = the FRONTEND ROTL-XOR idiom  `a ^ ((b << r) | (b >>u (w-r)))`
//               (`encode_eor_rotl_source`, r = w - k), and
//   * MACHINE = the shifted-register EOR-ROR  `a ^ ((b >>u k) | (b << (w-k)))`
//               (`encode_eor_shifted_reg(.., Ror, k)`).
// With r = w - k the two shifted halves are IDENTICAL but appear in the OPPOSITE
// OR order, so `trust_ir_expr != aarch64_expr` (genuine, not X==X) while the
// values coincide (OR commutes). The three NEGATIVE controls
// (`eor_ror_shift_wrong_controls`) each perturb the MACHINE side and REFUTE:
//   (1) WRONG-AMOUNT     — ROR #(k+1) instead of #k,
//   (2) WRONG-SHIFT-KIND — LSR #k (shift field 0b01) instead of ROR (0b11),
//   (3) OPERAND-SWAP     — `b ^ ror(a, k)` instead of `a ^ ror(b, k)`.

/// One EOR-ROR obligation at register `size`, rotate amount `k` (the ROR amount,
/// in `[1, width)`). SOURCE = frontend ROTL-XOR (`r = width - k`); MACHINE =
/// the shifted-register EOR-ROR. Positive: the two are provably equal.
pub fn proof_eor_ror_shift(size: trust_cg_ir::cc::OperandSize, k: u32) -> ProofObligation {
    use crate::aarch64_semantics::{RegShiftKind, encode_eor_rotl_source, encode_eor_shifted_reg};
    let width = crate::aarch64_semantics::operand_size_bits(size);
    debug_assert!(k >= 1 && k < width);
    let a = SmtExpr::var("a", width);
    let b = SmtExpr::var("b", width);
    let source = encode_eor_rotl_source(size, a.clone(), b.clone(), width - k);
    let machine = encode_eor_shifted_reg(size, a, b, RegShiftKind::Ror, k);
    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: format!(
            "Eor_Ror_Shift_I{width} k={k} -> EOR (shifted ROR, {width}-bit): \
             frontend ROTL-XOR == shifted-register EOR-ROR"
        ),
        trust_ir_expr: source,
        aarch64_expr: machine,
        inputs: vec![("a".to_string(), width), ("b".to_string(), width)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// The FAITHFUL EOR-ROR obligations across representative amounts at W and X.
/// Registered into the proof DB (via [`all_bitwise_shift_proofs`]); the coverage
/// gate binds `EorRRShift` to the `eor_ror_shift_i32` / `eor_ror_shift_i64`
/// names (both the W and X forms must discharge). Boundary amounts (1, w-1) and
/// salsa20's own `ror #25` / mid-range are all covered.
pub fn all_eor_ror_shift_proofs() -> Vec<ProofObligation> {
    use trust_cg_ir::cc::OperandSize;
    let mut proofs = Vec::new();
    for k in [1u32, 7, 16, 25, 31] {
        proofs.push(proof_eor_ror_shift(OperandSize::S32, k));
    }
    for k in [1u32, 24, 32, 40, 63] {
        proofs.push(proof_eor_ror_shift(OperandSize::S64, k));
    }
    proofs
}

/// NEGATIVE CONTROLS for the EOR-ROR obligations — each MUST refute (a wrong
/// encoding of the shifted-register EOR must be caught, so the positives are not
/// vacuous). Built at both W and X: wrong-amount, wrong-shift-kind (ROR-vs-LSR),
/// and operand-swap.
pub fn eor_ror_shift_wrong_controls() -> Vec<ProofObligation> {
    use crate::aarch64_semantics::{RegShiftKind, encode_eor_rotl_source, encode_eor_shifted_reg};
    use trust_cg_ir::cc::OperandSize;

    let mut controls = Vec::new();
    for size in [OperandSize::S32, OperandSize::S64] {
        let width = crate::aarch64_semantics::operand_size_bits(size);
        let k = 25u32.min(width - 1); // salsa20's amount at W; in-range at X too
        let r = width - k;
        let a = SmtExpr::var("a", width);
        let b = SmtExpr::var("b", width);
        let source = || encode_eor_rotl_source(size, a.clone(), b.clone(), r);

        // (1) WRONG-AMOUNT: MACHINE rotates by k+1 (still in range) — the halves
        // misalign, so it diverges from the ROR-by-k source.
        controls.push(ProofObligation {
            machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
            name: format!(
                "WRONG (eor_ror_shift_i{width}): ROR #{} instead of #{k} must REFUTE",
                k + 1
            ),
            trust_ir_expr: source(),
            aarch64_expr: encode_eor_shifted_reg(
                size,
                a.clone(),
                b.clone(),
                RegShiftKind::Ror,
                k + 1,
            ),
            inputs: vec![("a".to_string(), width), ("b".to_string(), width)],
            preconditions: vec![],
            fp_inputs: vec![],
            category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
        });

        // (2) WRONG-SHIFT-KIND: MACHINE uses LSR (shift field 0b01) not ROR
        // (0b11) — a plain logical shift drops the wrapped high bits.
        controls.push(ProofObligation {
            machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
            name: format!(
                "WRONG (eor_ror_shift_i{width}): shift kind LSR instead of ROR must REFUTE"
            ),
            trust_ir_expr: source(),
            aarch64_expr: encode_eor_shifted_reg(size, a.clone(), b.clone(), RegShiftKind::Lsr, k),
            inputs: vec![("a".to_string(), width), ("b".to_string(), width)],
            preconditions: vec![],
            fp_inputs: vec![],
            category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
        });

        // (3) OPERAND-SWAP: MACHINE rotates the WRONG source — `b ^ ror(a, k)`
        // instead of `a ^ ror(b, k)` (the shifted-register EOR is asymmetric).
        controls.push(ProofObligation {
            machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
            name: format!(
                "WRONG (eor_ror_shift_i{width}): operand-swap (b ^ ror(a,k)) must REFUTE"
            ),
            trust_ir_expr: source(),
            aarch64_expr: encode_eor_shifted_reg(size, b.clone(), a.clone(), RegShiftKind::Ror, k),
            inputs: vec![("a".to_string(), width), ("b".to_string(), width)],
            preconditions: vec![],
            fp_inputs: vec![],
            category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
        });
    }
    controls
}

// ---------------------------------------------------------------------------
// Standalone ROR-immediate (rotate recognizer) lowering proofs
// ---------------------------------------------------------------------------
//
// `rotate_idiom` folds the frontend rotate blend `(v << r) | (v >>u (w-r))`
// into the single `RorRI(v, k)` with `k = w - r`. When the following EOR does
// not fold (the xorshift state update on b1_mispredict / m1_call_chain feeds a
// non-EOR consumer), the RorRI ships STANDALONE — the EorRRShift family only
// constrains the fused form — so it needs its own value obligations.
//
// FAITHFULNESS / NON-DEGENERACY: the same mechanism as the EOR-ROR family.
//   * SOURCE  = the frontend ROTL blend (`encode_rotl_source`, r = w - k,
//               shl half first), and
//   * MACHINE = the ROR shifted operand (`shifted_reg_operand` Ror #k,
//               lshr half first).
// With r = w - k the two shifted halves are IDENTICAL but appear in the
// OPPOSITE OR order, so `trust_ir_expr != aarch64_expr` (genuine, not X==X)
// while the values coincide (OR commutes). The three NEGATIVE controls
// (`ror_immediate_wrong_controls`) each perturb the MACHINE side and REFUTE:
//   (1) WRONG-AMOUNT — ROR #(k+1) instead of #k,
//   (2) WRONG-KIND   — LSR #k (drops the wrapped-around high half),
//   (3) WRONG-DIRECTION — ROL #k (rotate-left instead of rotate-right).

/// One standalone ROR-immediate obligation at register `size`, rotate amount
/// `k` (the ROR amount, in `[1, width)`). SOURCE = frontend ROTL blend
/// (`r = width - k`); MACHINE = the ROR shifted operand. Positive: the two are
/// provably equal.
pub fn proof_ror_immediate(size: trust_cg_ir::cc::OperandSize, k: u32) -> ProofObligation {
    use crate::aarch64_semantics::{RegShiftKind, encode_rotl_source, shifted_reg_operand};
    let width = crate::aarch64_semantics::operand_size_bits(size);
    debug_assert!(k >= 1 && k < width);
    let v = SmtExpr::var("v", width);
    let source = encode_rotl_source(size, v.clone(), width - k);
    let machine = shifted_reg_operand(RegShiftKind::Ror, v, k, width);
    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: format!(
            "RorRI_I{width} k={k} -> ROR #{k} ({width}-bit): \
             frontend rotate blend == ROR shifted operand"
        ),
        trust_ir_expr: source,
        aarch64_expr: machine,
        inputs: vec![("v".to_string(), width)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// The FAITHFUL standalone ROR-immediate obligations across representative
/// amounts at W and X (boundaries 1 and w-1, the xorshift amounts, mid-range).
/// Registered into the proof DB (via [`all_bitwise_shift_proofs`]); the
/// function verifier binds a concrete `RorRI` per destination width to the
/// `rorri_i32` / `rorri_i64` names, and the coverage gate demands BOTH widths
/// discharge (see `aarch64_width_polymorphic_proofs`).
pub fn all_ror_immediate_proofs() -> Vec<ProofObligation> {
    use trust_cg_ir::cc::OperandSize;
    let mut proofs = Vec::new();
    for k in [1u32, 7, 16, 25, 31] {
        proofs.push(proof_ror_immediate(OperandSize::S32, k));
    }
    for k in [1u32, 13, 32, 51, 63] {
        proofs.push(proof_ror_immediate(OperandSize::S64, k));
    }
    proofs
}

/// NEGATIVE CONTROLS for the standalone ROR-immediate obligations — each MUST
/// refute (a wrong rotate encoding must be caught, so the positives are not
/// vacuous). Built at both W and X: wrong-amount, wrong-kind (ROR-vs-LSR), and
/// wrong-direction (ROR-vs-ROL).
pub fn ror_immediate_wrong_controls() -> Vec<ProofObligation> {
    use crate::aarch64_semantics::{RegShiftKind, encode_rotl_source, shifted_reg_operand};
    use trust_cg_ir::cc::OperandSize;

    let mut controls = Vec::new();
    for size in [OperandSize::S32, OperandSize::S64] {
        let width = crate::aarch64_semantics::operand_size_bits(size);
        let k = 25u32.min(width - 1);
        let v = SmtExpr::var("v", width);
        let source = || encode_rotl_source(size, v.clone(), width - k);
        let control = |name: String, machine: SmtExpr| ProofObligation {
            machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
            name,
            trust_ir_expr: source(),
            aarch64_expr: machine,
            inputs: vec![("v".to_string(), width)],
            preconditions: vec![],
            fp_inputs: vec![],
            category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
        };

        // (1) WRONG-AMOUNT: MACHINE rotates by k+1 (still in range) — the
        // halves misalign, so it diverges from the ROR-by-k source.
        controls.push(control(
            format!(
                "WRONG (rorri_i{width}): ROR #{} instead of #{k} must REFUTE",
                k + 1
            ),
            shifted_reg_operand(RegShiftKind::Ror, v.clone(), k + 1, width),
        ));

        // (2) WRONG-KIND: MACHINE uses LSR #k — a plain logical shift drops
        // the wrapped-around high half.
        controls.push(control(
            format!("WRONG (rorri_i{width}): shift kind LSR instead of ROR must REFUTE"),
            shifted_reg_operand(RegShiftKind::Lsr, v.clone(), k, width),
        ));

        // (3) WRONG-DIRECTION: MACHINE rotates LEFT by k (ROR by w-k) — the
        // classic k vs w-k confusion the recognizer's `k = w - r` derivation
        // could get backwards.
        controls.push(control(
            format!("WRONG (rorri_i{width}): rotate-left #{k} instead of rotate-right must REFUTE"),
            shifted_reg_operand(RegShiftKind::Ror, v.clone(), width - k, width),
        ));
    }
    controls
}

// ---------------------------------------------------------------------------
// ADD/SUB with an LSL-shifted source (shift-add/sub fusion peephole) proofs
// ---------------------------------------------------------------------------
//
// The shift-ALU fusion peephole (`trust_cg_opt::shift_alu_fuse`) collapses the
// two-instruction `t = LslRI(s, k); d = AddRR(x, t)` (and the SUB form) — as
// emitted for an explicit `y + (x << k)` or produced by the mul-by-constant
// strength reduction (`mul_shift_reduce`: LslRI + AddRR) — into the single
// shifted-register instruction
//     d = AddRRShift(x, s, k)   ==   ADD d, x, s, LSL #k , and
//     d = SubRRShift(x, s, k)   ==   SUB d, x, s, LSL #k .
//
// FAITHFULNESS / NON-DEGENERACY: the obligation ties two STRUCTURALLY DISTINCT
// SMT expressions that are provably equal over Z/2^W:
//   * SOURCE  = the ring form  `base +/- src * 2^k`   (a bvMUL by the BAKED
//               power-of-two constant `2^k`), and
//   * MACHINE = the shifted-register form  `base +/- (src << k)`  (a bvSHL by
//               `k` via the LSL shifted-register operand).
// `src * 2^k == src << k` is an EXACT modular identity, so the values coincide
// while `bvmul != bvshl` structurally (`is_genuinely_proven`, not X==X). This is
// the exact bvmul-vs-bvshl shape of `proof_ldrsw_ro_scaled_addr` (`base + 4*index`
// == `base + (index<<2)`), which is registered and discharges Valid via the
// in-house evaluator (the multiply is by a baked constant — NOT solver-hard).
// The negative controls (`add_sub_lsl_shift_wrong_controls`) each perturb the
// MACHINE side and REFUTE: wrong-amount (LSL #(k+1)), wrong-op (ADD source vs
// SUB machine), and — for SUB, whose subtrahend-only shift is non-commutative —
// an operand-swap `(src<<k) - base` instead of `base - (src<<k)`.

/// One ADD-LSL obligation at register `size`, shift amount `k` in `[1, width)`.
/// SOURCE = `base + src*2^k` (bvmul); MACHINE = `base + (src<<k)` (bvshl).
/// Positive: the two are provably equal.
pub fn proof_add_lsl_shift(size: trust_cg_ir::cc::OperandSize, k: u32) -> ProofObligation {
    use crate::aarch64_semantics::{RegShiftKind, encode_add_rr, encode_add_shifted_reg};
    let width = crate::aarch64_semantics::operand_size_bits(size);
    debug_assert!(k >= 1 && k < width);
    let base = SmtExpr::var("base", width);
    let src = SmtExpr::var("src", width);
    let two_k = SmtExpr::bv_const(1u64 << k, width);
    let source = encode_add_rr(size, base.clone(), src.clone().bvmul(two_k));
    let machine = encode_add_shifted_reg(size, base, src, RegShiftKind::Lsl, k);
    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: format!(
            "Add_Lsl_Shift_I{width} k={k} -> ADD (shifted LSL, {width}-bit): \
             base + src*2^k == base + (src<<k)"
        ),
        trust_ir_expr: source,
        aarch64_expr: machine,
        inputs: vec![("base".to_string(), width), ("src".to_string(), width)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// One SUB-LSL obligation at register `size`, shift amount `k` in `[1, width)`.
/// SOURCE = `base - src*2^k` (bvmul); MACHINE = `base - (src<<k)` (bvshl).
/// Positive: the two are provably equal. The shift binds to the subtrahend only.
pub fn proof_sub_lsl_shift(size: trust_cg_ir::cc::OperandSize, k: u32) -> ProofObligation {
    use crate::aarch64_semantics::{RegShiftKind, encode_sub_rr, encode_sub_shifted_reg};
    let width = crate::aarch64_semantics::operand_size_bits(size);
    debug_assert!(k >= 1 && k < width);
    let base = SmtExpr::var("base", width);
    let src = SmtExpr::var("src", width);
    let two_k = SmtExpr::bv_const(1u64 << k, width);
    let source = encode_sub_rr(size, base.clone(), src.clone().bvmul(two_k));
    let machine = encode_sub_shifted_reg(size, base, src, RegShiftKind::Lsl, k);
    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: format!(
            "Sub_Lsl_Shift_I{width} k={k} -> SUB (shifted LSL, {width}-bit): \
             base - src*2^k == base - (src<<k)"
        ),
        trust_ir_expr: source,
        aarch64_expr: machine,
        inputs: vec![("base".to_string(), width), ("src".to_string(), width)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// The FAITHFUL ADD/SUB-LSL obligations across representative amounts at W and X:
/// 10 ADD (5 amounts x {W,X}) + 10 SUB = 20. Registered into the proof DB (via
/// [`all_bitwise_shift_proofs`]); the coverage gate binds `AddRRShift` to
/// `add_lsl_shift_i32`/`add_lsl_shift_i64` and `SubRRShift` to
/// `sub_lsl_shift_i32`/`sub_lsl_shift_i64` (BOTH widths of each must discharge).
/// Boundary amounts (1, w-1) and the collatz `*3` shift (#1) are covered.
pub fn all_add_sub_lsl_shift_proofs() -> Vec<ProofObligation> {
    use trust_cg_ir::cc::OperandSize;
    let mut proofs = Vec::new();
    for k in [1u32, 7, 16, 25, 31] {
        proofs.push(proof_add_lsl_shift(OperandSize::S32, k));
    }
    for k in [1u32, 24, 32, 40, 63] {
        proofs.push(proof_add_lsl_shift(OperandSize::S64, k));
    }
    for k in [1u32, 7, 16, 25, 31] {
        proofs.push(proof_sub_lsl_shift(OperandSize::S32, k));
    }
    for k in [1u32, 24, 32, 40, 63] {
        proofs.push(proof_sub_lsl_shift(OperandSize::S64, k));
    }
    proofs
}

/// NEGATIVE CONTROLS for the ADD/SUB-LSL obligations — each MUST refute (so the
/// positives are not vacuous). Built at both W and X: ADD wrong-amount, ADD
/// wrong-op (ADD source vs SUB machine), SUB wrong-amount, and SUB operand-swap
/// (`(src<<k) - base`, exercising the subtrahend-only non-commutativity).
pub fn add_sub_lsl_shift_wrong_controls() -> Vec<ProofObligation> {
    use crate::aarch64_semantics::{
        RegShiftKind, encode_add_rr, encode_add_shifted_reg, encode_sub_rr, encode_sub_shifted_reg,
        shifted_reg_operand,
    };
    use trust_cg_ir::cc::OperandSize;

    let mut controls = Vec::new();
    for size in [OperandSize::S32, OperandSize::S64] {
        let width = crate::aarch64_semantics::operand_size_bits(size);
        let k = 7u32.min(width - 2); // in range at both W and X, k+1 < width too
        let base = SmtExpr::var("base", width);
        let src = SmtExpr::var("src", width);
        let two_k = SmtExpr::bv_const(1u64 << k, width);
        let add_source = || encode_add_rr(size, base.clone(), src.clone().bvmul(two_k.clone()));
        let sub_source = || encode_sub_rr(size, base.clone(), src.clone().bvmul(two_k.clone()));

        // (1) ADD WRONG-AMOUNT: MACHINE shifts by k+1 — `base + (src<<(k+1))`
        // diverges from the `+ src*2^k` source.
        controls.push(ProofObligation {
            machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
            name: format!(
                "WRONG (add_lsl_shift_i{width}): LSL #{} instead of #{k} must REFUTE",
                k + 1
            ),
            trust_ir_expr: add_source(),
            aarch64_expr: encode_add_shifted_reg(
                size,
                base.clone(),
                src.clone(),
                RegShiftKind::Lsl,
                k + 1,
            ),
            inputs: vec![("base".to_string(), width), ("src".to_string(), width)],
            preconditions: vec![],
            fp_inputs: vec![],
            category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
        });

        // (2) ADD WRONG-OP: MACHINE subtracts — `base - (src<<k)` instead of
        // the `base + …` the ADD source computes.
        controls.push(ProofObligation {
            machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
            name: format!("WRONG (add_lsl_shift_i{width}): SUB machine instead of ADD must REFUTE"),
            trust_ir_expr: add_source(),
            aarch64_expr: encode_sub_shifted_reg(
                size,
                base.clone(),
                src.clone(),
                RegShiftKind::Lsl,
                k,
            ),
            inputs: vec![("base".to_string(), width), ("src".to_string(), width)],
            preconditions: vec![],
            fp_inputs: vec![],
            category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
        });

        // (3) SUB WRONG-AMOUNT: MACHINE subtracts a k+1 shift.
        controls.push(ProofObligation {
            machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
            name: format!(
                "WRONG (sub_lsl_shift_i{width}): LSL #{} instead of #{k} must REFUTE",
                k + 1
            ),
            trust_ir_expr: sub_source(),
            aarch64_expr: encode_sub_shifted_reg(
                size,
                base.clone(),
                src.clone(),
                RegShiftKind::Lsl,
                k + 1,
            ),
            inputs: vec![("base".to_string(), width), ("src".to_string(), width)],
            preconditions: vec![],
            fp_inputs: vec![],
            category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
        });

        // (4) SUB OPERAND-SWAP: the load-bearing non-commutativity. MACHINE
        // computes `(src<<k) - base` instead of `base - (src<<k)` — swapping the
        // minuend and subtrahend, which SUB (unlike ADD) does NOT tolerate.
        let swapped =
            shifted_reg_operand(RegShiftKind::Lsl, src.clone(), k, width).bvsub(base.clone());
        controls.push(ProofObligation {
            machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
            name: format!(
                "WRONG (sub_lsl_shift_i{width}): operand-swap ((src<<k)-base) must REFUTE"
            ),
            trust_ir_expr: sub_source(),
            aarch64_expr: swapped,
            inputs: vec![("base".to_string(), width), ("src".to_string(), width)],
            preconditions: vec![],
            fp_inputs: vec![],
            category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
        });
    }
    controls
}

// ---------------------------------------------------------------------------
// ADD with an LSR-shifted source (shift-add fusion peephole, LSR sibling) proofs
// ---------------------------------------------------------------------------
//
// The shift-ALU fusion peephole (`trust_cg_opt::shift_alu_fuse`) also collapses
// the two-instruction `t = LsrRI(s, k); d = AddRR(x, t)` — the srem/sdiv-by-
// constant magic sign-bit correction (`lsr t, x, #31; add r, r, t`) and the
// udiv magic add-back (`lsr t, sub, #1; add r, mh, t`) — into the single
// shifted-register instruction
//     d = AddRRShiftLsr(x, s, k)   ==   ADD d, x, s, LSR #k .
//
// FAITHFULNESS / NON-DEGENERACY: the obligation ties two STRUCTURALLY DISTINCT
// SMT expressions that are provably equal over Z/2^W:
//   * SOURCE  = the ring form  `base + src / 2^k`  (a bvUDIV by the BAKED
//               power-of-two constant `2^k` — unsigned division truncates,
//               which for a power-of-two divisor IS the zero-fill right shift),
//   * MACHINE = the shifted-register form `base + (src >>u k)` (a bvLSHR by `k`
//               via the LSR shifted-register operand).
// `udiv(src, 2^k) == src >>u k` is an EXACT identity for every unsigned `src`
// and `k` in `[1, width)`, so the values coincide while `bvudiv != bvlshr`
// structurally (`is_genuinely_proven`, not X==X) — the LSR analogue of the
// bvmul-vs-bvshl shape of `proof_add_lsl_shift`. The negative controls
// (`add_lsr_shift_wrong_controls`) each perturb the MACHINE side and REFUTE:
// wrong-amount (LSR #(k+1)), wrong-shift-kind ASR-not-LSR (the exact srem
// sign-correction bug class — sign-fill diverges for negative `src`),
// wrong-shift-kind LSL-not-LSR, and wrong-op (SUB machine instead of ADD).

/// One ADD-LSR obligation at register `size`, shift amount `k` in `[1, width)`.
/// SOURCE = `base + src/2^k` (bvudiv, unsigned); MACHINE = `base + (src>>u k)`
/// (bvlshr). Positive: the two are provably equal.
pub fn proof_add_lsr_shift(size: trust_cg_ir::cc::OperandSize, k: u32) -> ProofObligation {
    use crate::aarch64_semantics::{RegShiftKind, encode_add_rr, encode_add_shifted_reg};
    let width = crate::aarch64_semantics::operand_size_bits(size);
    debug_assert!(k >= 1 && k < width);
    let base = SmtExpr::var("base", width);
    let src = SmtExpr::var("src", width);
    let two_k = SmtExpr::bv_const(1u64 << k, width);
    let source = encode_add_rr(size, base.clone(), src.clone().bvudiv(two_k));
    let machine = encode_add_shifted_reg(size, base, src, RegShiftKind::Lsr, k);
    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: format!(
            "Add_Lsr_Shift_I{width} k={k} -> ADD (shifted LSR, {width}-bit): \
             base + src/2^k == base + (src>>u k)"
        ),
        trust_ir_expr: source,
        aarch64_expr: machine,
        inputs: vec![("base".to_string(), width), ("src".to_string(), width)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// The FAITHFUL ADD-LSR obligations across representative amounts at W and X:
/// 5 amounts x {W,X} = 10. Registered into the proof DB (via
/// [`all_bitwise_shift_proofs`]); the coverage gate binds `AddRRShiftLsr` to
/// `add_lsr_shift_i32`/`add_lsr_shift_i64` (BOTH widths must discharge).
/// Boundary amounts (1, w-1) are covered — `#31`/`#63` ARE the srem/sdiv magic
/// sign-bit correction, `#1` the udiv magic add-back.
pub fn all_add_lsr_shift_proofs() -> Vec<ProofObligation> {
    use trust_cg_ir::cc::OperandSize;
    let mut proofs = Vec::new();
    for k in [1u32, 7, 16, 25, 31] {
        proofs.push(proof_add_lsr_shift(OperandSize::S32, k));
    }
    for k in [1u32, 24, 32, 40, 63] {
        proofs.push(proof_add_lsr_shift(OperandSize::S64, k));
    }
    proofs
}

/// NEGATIVE CONTROLS for the ADD-LSR obligations — each MUST refute (so the
/// positives are not vacuous). Built at both W and X: wrong-amount, ASR-not-LSR
/// (sign-fill vs zero-fill — the srem sign-correction bug class), LSL-not-LSR,
/// and wrong-op (SUB machine instead of ADD).
pub fn add_lsr_shift_wrong_controls() -> Vec<ProofObligation> {
    use crate::aarch64_semantics::{
        RegShiftKind, encode_add_rr, encode_add_shifted_reg, encode_sub_shifted_reg,
    };
    use trust_cg_ir::cc::OperandSize;

    let mut controls = Vec::new();
    for size in [OperandSize::S32, OperandSize::S64] {
        let width = crate::aarch64_semantics::operand_size_bits(size);
        let k = 7u32.min(width - 2); // in range at both W and X, k+1 < width too
        let base = SmtExpr::var("base", width);
        let src = SmtExpr::var("src", width);
        let two_k = SmtExpr::bv_const(1u64 << k, width);
        let add_source = || encode_add_rr(size, base.clone(), src.clone().bvudiv(two_k.clone()));

        // The four wrong MACHINE sides: wrong amount, wrong shift kind (ASR /
        // LSL instead of LSR), and wrong op (SUB instead of ADD).
        let wrongs: [(String, SmtExpr); 4] = [
            (
                format!(
                    "WRONG (add_lsr_shift_i{width}): LSR #{} instead of #{k} must REFUTE",
                    k + 1
                ),
                encode_add_shifted_reg(size, base.clone(), src.clone(), RegShiftKind::Lsr, k + 1),
            ),
            (
                format!("WRONG (add_lsr_shift_i{width}): ASR instead of LSR must REFUTE"),
                encode_add_shifted_reg(size, base.clone(), src.clone(), RegShiftKind::Asr, k),
            ),
            (
                format!("WRONG (add_lsr_shift_i{width}): LSL instead of LSR must REFUTE"),
                encode_add_shifted_reg(size, base.clone(), src.clone(), RegShiftKind::Lsl, k),
            ),
            (
                format!("WRONG (add_lsr_shift_i{width}): SUB machine instead of ADD must REFUTE"),
                encode_sub_shifted_reg(size, base.clone(), src.clone(), RegShiftKind::Lsr, k),
            ),
        ];
        for (name, machine) in wrongs {
            controls.push(ProofObligation {
                machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
                name,
                trust_ir_expr: add_source(),
                aarch64_expr: machine,
                inputs: vec![("base".to_string(), width), ("src".to_string(), width)],
                preconditions: vec![],
                fp_inputs: vec![],
                category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
            });
        }
    }
    controls
}

/// Build the proof obligation for: `trust_ir::Ishl(I64, a, b) -> LSL (64-bit)`.
pub fn proof_ishl_i64() -> ProofObligation {
    use crate::trust_ir_semantics::encode_trust_ir_shift;
    use trust_cg_lower::instructions::Opcode;
    use trust_cg_lower::types::Type;

    let a = SmtExpr::var("a", 64);
    let b = SmtExpr::var("b", 64);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "Ishl_I64 -> LSL (64-bit)".to_string(),
        trust_ir_expr: encode_trust_ir_shift(&Opcode::Ishl, Type::I64, a.clone(), b.clone()),
        aarch64_expr: a.clone().bvshl(b.clone()),
        inputs: vec![("a".to_string(), 64), ("b".to_string(), 64)],
        preconditions: vec![shift_in_range_precondition(b, 64)],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// Build the proof obligation for: `trust_ir::Ushr(I64, a, b) -> LSR (64-bit)`.
pub fn proof_ushr_i64() -> ProofObligation {
    use crate::trust_ir_semantics::encode_trust_ir_shift;
    use trust_cg_lower::instructions::Opcode;
    use trust_cg_lower::types::Type;

    let a = SmtExpr::var("a", 64);
    let b = SmtExpr::var("b", 64);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "Ushr_I64 -> LSR (64-bit)".to_string(),
        trust_ir_expr: encode_trust_ir_shift(&Opcode::Ushr, Type::I64, a.clone(), b.clone()),
        aarch64_expr: a.clone().bvlshr(b.clone()),
        inputs: vec![("a".to_string(), 64), ("b".to_string(), 64)],
        preconditions: vec![shift_in_range_precondition(b, 64)],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// Build the proof obligation for: `trust_ir::Sshr(I64, a, b) -> ASR (64-bit)`.
pub fn proof_sshr_i64() -> ProofObligation {
    use crate::trust_ir_semantics::encode_trust_ir_shift;
    use trust_cg_lower::instructions::Opcode;
    use trust_cg_lower::types::Type;

    let a = SmtExpr::var("a", 64);
    let b = SmtExpr::var("b", 64);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "Sshr_I64 -> ASR (64-bit)".to_string(),
        trust_ir_expr: encode_trust_ir_shift(&Opcode::Sshr, Type::I64, a.clone(), b.clone()),
        aarch64_expr: a.clone().bvashr(b.clone()),
        inputs: vec![("a".to_string(), 64), ("b".to_string(), 64)],
        preconditions: vec![shift_in_range_precondition(b, 64)],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// Build the proof obligation for: `trust_ir::BandNot(I64, a, b) -> BIC (64-bit)`.
pub fn proof_bic_i64() -> ProofObligation {
    use crate::aarch64_semantics::encode_bic_rr;
    use crate::trust_ir_semantics::encode_trust_ir_bitwise_binop;
    use trust_cg_ir::cc::OperandSize;
    use trust_cg_lower::instructions::Opcode;
    use trust_cg_lower::types::Type;

    let a = SmtExpr::var("a", 64);
    let b = SmtExpr::var("b", 64);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "BandNot_I64 -> BIC (64-bit)".to_string(),
        trust_ir_expr: encode_trust_ir_bitwise_binop(
            &Opcode::BandNot,
            Type::I64,
            a.clone(),
            b.clone(),
        ),
        aarch64_expr: encode_bic_rr(OperandSize::S64, a, b),
        inputs: vec![("a".to_string(), 64), ("b".to_string(), 64)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// Build the proof obligation for: `trust_ir::BorNot(I64, a, b) -> ORN (64-bit)`.
pub fn proof_orn_i64() -> ProofObligation {
    use crate::aarch64_semantics::encode_orn_rr;
    use crate::trust_ir_semantics::encode_trust_ir_bitwise_binop;
    use trust_cg_ir::cc::OperandSize;
    use trust_cg_lower::instructions::Opcode;
    use trust_cg_lower::types::Type;

    let a = SmtExpr::var("a", 64);
    let b = SmtExpr::var("b", 64);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "BorNot_I64 -> ORN (64-bit)".to_string(),
        trust_ir_expr: encode_trust_ir_bitwise_binop(
            &Opcode::BorNot,
            Type::I64,
            a.clone(),
            b.clone(),
        ),
        aarch64_expr: encode_orn_rr(OperandSize::S64, a, b),
        inputs: vec![("a".to_string(), 64), ("b".to_string(), 64)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// Return all bitwise and shift lowering proofs (I8 + I16 + I32 + I64).
///
/// Covers: AND, OR, XOR, NOT, SHL, LSR, ASR at I8 (exhaustive) and
/// I16/I32/I64 (statistical) widths, plus BIC/ORN at all four widths.
/// I32/I64 BIC/ORN/BAND/BOR/BXOR/SHL/LSR/ASR widened by issue #449 for the
/// epic #407 Task 3 ay smoke rollout (enabled by StableHasher caching in
/// #420). I8/I16 BIC/ORN added by issue #425.
pub fn all_bitwise_shift_proofs() -> Vec<ProofObligation> {
    vec![
        // I8 (exhaustive verification -- all 2^16 or 2^8 input combos tested)
        proof_band_i8(),
        proof_bor_i8(),
        proof_bxor_i8(),
        proof_bnot_i8(),
        proof_ishl_i8(),
        proof_ushr_i8(),
        proof_sshr_i8(),
        // I8 BIC/ORN (issue #425) -- BandNot/BorNot lowering proofs
        proof_bic_i8(),
        proof_orn_i8(),
        // I16 (statistical verification -- edge cases + random sampling)
        proof_band_i16(),
        proof_bor_i16(),
        proof_bxor_i16(),
        proof_bnot_i16(),
        proof_ishl_i16(),
        proof_ushr_i16(),
        proof_sshr_i16(),
        // I16 BIC/ORN -- widened for epic #407 ay smoke rollout
        proof_bic_i16(),
        proof_orn_i16(),
        // I32 bitwise/shift/BIC/ORN (issue #449) -- statistical sampling;
        // ay can discharge most symbolically, imul-free so bvshl/bvlshr/bvashr
        // close in seconds on a warm solver.
        proof_band_i32(),
        proof_bor_i32(),
        proof_bxor_i32(),
        proof_ishl_i32(),
        proof_ushr_i32(),
        proof_sshr_i32(),
        proof_bic_i32(),
        proof_orn_i32(),
        // I64 bitwise/shift/BIC/ORN (issue #449).
        proof_band_i64(),
        proof_bor_i64(),
        proof_bxor_i64(),
        proof_ishl_i64(),
        proof_ushr_i64(),
        proof_sshr_i64(),
        proof_bic_i64(),
        proof_orn_i64(),
    ]
    .into_iter()
    // EOR with ROR-shifted source (rotate-fusion peephole): the FAITHFUL
    // rotate-XOR obligations, W+X, several amounts. STRUCTURALLY DISTINCT
    // (source = ROTL-XOR idiom, machine = shifted-register EOR-ROR) so they are
    // genuine (not X==X); the coverage gate credits `EorRRShift` through the
    // `eor_ror_shift_i32` / `eor_ror_shift_i64` names.
    .chain(all_eor_ror_shift_proofs())
    // Standalone ROR-immediate (the rotate recognizer's unfused form): the
    // FAITHFUL rotate obligations, W+X, several amounts. Same opposite-OR-order
    // non-degeneracy mechanism as the EOR-ROR family above; the function
    // verifier binds `RorRI` per destination width through the `rorri_i32` /
    // `rorri_i64` names and the coverage gate demands both widths.
    .chain(all_ror_immediate_proofs())
    // ADD/SUB with an LSL-shifted source (shift-add/sub fusion peephole): the
    // FAITHFUL ring obligations, W+X, several amounts (10 ADD + 10 SUB = 20).
    // STRUCTURALLY DISTINCT (source = base +/- src*2^k via bvmul, machine =
    // base +/- (src<<k) via bvshl) so they are genuine (not X==X) — the exact
    // bvmul-vs-bvshl shape of proof_ldrsw_ro_scaled_addr; the coverage gate
    // credits `AddRRShift`/`SubRRShift` through the `add_lsl_shift_i{32,64}` /
    // `sub_lsl_shift_i{32,64}` names.
    .chain(all_add_sub_lsl_shift_proofs())
    // ADD with an LSR-shifted source (shift-add fusion peephole, LSR sibling):
    // the FAITHFUL obligations, W+X, several amounts (10 ADD). STRUCTURALLY
    // DISTINCT (source = base + src/2^k via bvudiv, machine = base + (src>>u k)
    // via bvlshr) so they are genuine (not X==X) — the LSR analogue of the
    // bvmul-vs-bvshl ring shape above; the coverage gate credits `AddRRShiftLsr`
    // through the `add_lsr_shift_i{32,64}` names.
    .chain(all_add_lsr_shift_proofs())
    // #62 retraction (group b): the scalar shift lowerings (Ishl->SHL/LSL,
    // Ushr->LSR, Sshr->ASR, I8..I64) were degenerate X==X — the trust_ir side
    // (encode_trust_ir_shift) and the machine side built the SAME bv shift op,
    // and the #57 in-range precondition was added IDENTICALLY to both sides
    // (cosmetic). The Lsl/Lsr/Asr opcodes are now CREDITED via operand
    // reconstruction with the FAITHFUL hardware-amount-masked machine encoder
    // under a LOAD-BEARING `amount < width` precondition (#57) — that is the
    // genuine coverage that SUPERSEDES these static proofs. The bitwise AND/OR/
    // XOR/NOT/BIC/ORN identities (on GENUINE_IDENTITY_ALLOWLIST) remain.
    .filter(|p| !SCALAR_SHIFT_RETRACTED_DEGENERATE.contains(&p.name.as_str()))
    .collect()
}

const SCALAR_SHIFT_RETRACTED_DEGENERATE: &[&str] = &[
    "Ishl_I8 -> SHL (8-bit)",
    "Ishl_I16 -> SHL (16-bit)",
    "Ishl_I32 -> LSL (32-bit)",
    "Ishl_I64 -> LSL (64-bit)",
    "Ushr_I8 -> LSR (8-bit)",
    "Ushr_I16 -> LSR (16-bit)",
    "Ushr_I32 -> LSR (32-bit)",
    "Ushr_I64 -> LSR (64-bit)",
    "Sshr_I8 -> ASR (8-bit)",
    "Sshr_I16 -> ASR (16-bit)",
    "Sshr_I32 -> ASR (32-bit)",
    "Sshr_I64 -> ASR (64-bit)",
];

#[cfg(test)]
mod tests {
    use super::*;

    /// E0.5: the formal-on-miss upgrade route is deleted, not bounded. Under
    /// the compiler's proof-promotion policy a registry obligation with no
    /// portable certificate and no tier-0 row is discharged by evaluation at
    /// its honest Statistical strength, and a real counted solver process is
    /// never entered. Before the deletion this configuration spent a live AY
    /// attempt per call (bounded at two per key by f992f4fc).
    #[cfg(unix)]
    #[test]
    fn registry_miss_never_enters_a_live_solver_under_promotion_policy() {
        use crate::smt::SmtExpr;
        use std::os::unix::fs::PermissionsExt;

        let _serial = crate::ay_bridge::formal_solver_test_lock();
        let dir = tempfile::tempdir().unwrap();
        // Counts every real query, whatever it answers. The AY identity rule
        // starts an admitted fixture from its private copy, so the script names
        // its own path literally (bind_self) for the counter to land where this
        // test reads it, and its digest is declared below: without that
        // admission every query stopped at TCG-AY-IDENTITY-MISMATCH and
        // `calls() == 0` held whatever the code did (measured: a restored live
        // route on a registry miss passed this test).
        let solver = dir.path().join("ay-counting");
        std::fs::write(
            &solver,
            crate::ay_identity::test_fixtures::bind_self(
                &solver,
                "#!/bin/sh\n\
                 if test \"$1\" = --version; then printf 'ay fixture\\n'; exit 0; fi\n\
                 printf 'q\\n' >> \"$0.calls\"\n\
                 printf 'unsat\\n'\n",
            ),
        )
        .unwrap();
        std::fs::set_permissions(&solver, std::fs::Permissions::from_mode(0o700)).unwrap();
        let calls = || {
            std::fs::read_to_string(solver.with_extension("calls"))
                .unwrap_or_default()
                .lines()
                .count()
        };
        // Unique content, so no portable certificate or memo cell can answer it.
        let input = format!("e05_registry_miss_{}", std::process::id());
        let x = SmtExpr::var(&input, 32);
        let obligation = ProofObligation {
            machine_side_provenance: MachineSideProvenance::StaticDb,
            name: format!("E0.5 registry miss {}", dir.path().display()),
            trust_ir_expr: x.clone().bvadd(SmtExpr::bv_const(0, 32)),
            aarch64_expr: x,
            inputs: vec![(input, 32)],
            preconditions: vec![],
            fp_inputs: vec![],
            category: None,
        };
        let declaration = crate::ay_identity::test_fixtures::declare(&[solver.as_path()]);
        crate::env_lock::with_env_edits(|env| {
            env.set("AY_SOLVER_PATH", &solver);
            env.set(
                crate::ay_identity::test_fixtures::FIXTURE_DIGESTS_ENV,
                &declaration,
            );
            env.set("TCG_NO_VERDICT_DB", "1");
            env.set("TCG_NO_SOLVER_SERVER", "1");
            env.set("TCG_NO_CERT_STORE", "1");
            env.set("TCG_REFINE_SOLVER", "1");
            env.remove("TCG_NO_PROOF_CACHE");
            let promotion = VerificationConfig::for_proof_promotion();
            assert!(!crate::verdict_db::portable_cert_verified_obligation(
                &obligation
            ));
            for _ in 0..3 {
                let (result, strength) = discharge_registry_obligation(&obligation, &promotion);
                assert!(matches!(result, VerificationResult::Valid), "{result:?}");
                assert!(
                    matches!(
                        strength,
                        crate::verify::VerificationStrength::Statistical { .. }
                    ),
                    "no live route may upgrade a registry miss: {strength:?}"
                );
            }
        });
        assert_eq!(calls(), 0, "a registry miss must never reach the solver");
    }

    #[test]
    fn portable_registry_proofs_promote_but_reconstruction_needs_source_binding() {
        use trust_cg_ir::regs::VReg;
        use trust_cg_ir::{AArch64Opcode, MachInst, MachOperand, RegClass};

        crate::env_lock::with_env_edits(|env| {
            // Prove the registry path does not inherit authority from either
            // tier-0 or a live AY process. The portable checker is its sole
            // route. A reconstructed theorem remains independently replayable
            // below, but cannot promote an instruction without source binding.
            env.set("TCG_NO_VERDICT_DB", "1");
            env.set("TCG_REFINE_SOLVER", "0");
            env.remove("TCG_NO_PROOF_CACHE");
            env.remove("TCG_CANARY_NO_CACHE");

            let promotion = VerificationConfig::for_proof_promotion();
            let (icmp_result, icmp_strength) =
                discharge_registry_obligation(&proof_icmp_eq_i32(), &promotion);
            assert!(matches!(icmp_result, VerificationResult::Valid));
            assert_eq!(
                icmp_strength,
                crate::verify::VerificationStrength::Formal,
                "an independently replayed registry proof must not require tier-0 or AY"
            );

            let r = |id| MachOperand::VReg(VReg::new(id, RegClass::Gpr64));
            let inst = MachInst::new(AArch64Opcode::LsrRI, vec![r(0), r(1), MachOperand::Imm(17)]);
            let instance = crate::function_verifier::reconstruct_alu_obligation(&inst)
                .expect("LsrRI instance reconstruction");
            let canonical = crate::function_verifier::canonical_reconstruct_obligation(&inst)
                .expect("LsrRI canonical reconstruction");
            assert_ne!(
                crate::verdict_db::db_obligation_smt2(&instance),
                crate::verdict_db::db_obligation_smt2(&canonical),
                "the regression needs a baked instance distinct from its parametric proof"
            );
            assert!(
                crate::verdict_db::portable_cert_verified_obligation(&canonical),
                "the canonical Ushr64 query must have portable proof authority"
            );
            assert!(
                !crate::verdict_db::portable_cert_verified_obligation(&instance),
                "the baked instance must not accidentally carry the canonical query key"
            );

            let (recon_result, recon_strength) =
                discharge_reconstructed_obligation(&instance, &canonical, &promotion);
            assert!(matches!(recon_result, VerificationResult::Valid));
            assert_eq!(
                recon_strength,
                crate::verify::VerificationStrength::Statistical {
                    sample_count: promotion.sample_count,
                },
                "a target-derived canonical proof cannot confer source-lowering authority"
            );
        });
    }

    #[test]
    fn random_fallback_i128_edge_samples_do_not_shift_u64_out_of_range() {
        let x = SmtExpr::var("x", 128);
        let obligation = ProofObligation {
            name: "i128 random fallback edge sampling".to_string(),
            trust_ir_expr: x.clone(),
            aarch64_expr: x,
            inputs: vec![("x".to_string(), 128)],
            preconditions: vec![],
            fp_inputs: vec![],
            category: Some(TransvalCheckKind::InstructionLowering),
            machine_side_provenance: MachineSideProvenance::StaticDb,
        };

        assert!(matches!(
            verify_random(&obligation, None, 128, 1),
            VerificationResult::Valid
        ));
    }

    /// Build an obligation in the RECONSTRUCTED-obligation shape used by the
    /// PROOF-2 memo-key tests below: the NAME omits the baked immediates
    /// (mirroring `x86_64_function_verifier::reconstruct_alu_obligation`,
    /// whose names are e.g. `"RECONSTRUCTED x86_64 Iadd_32 -> AddRI
    /// (real-operand)"`) while the immediates live only in the expression
    /// trees.
    fn proof2_obligation(name: &str, source_imm: u64, machine_imm: u64) -> ProofObligation {
        let x = || SmtExpr::var("recon_src1", 32);
        ProofObligation {
            name: name.to_string(),
            trust_ir_expr: x().bvadd(SmtExpr::bv_const(source_imm, 32)),
            aarch64_expr: x().bvadd(SmtExpr::bv_const(machine_imm, 32)),
            inputs: vec![("recon_src1".to_string(), 32)],
            preconditions: vec![],
            fp_inputs: vec![],
            category: Some(TransvalCheckKind::InstructionLowering),
            machine_side_provenance: MachineSideProvenance::Reconstructed {
                from_opcode: "AddRI".to_string(),
                arity: 2,
            },
        }
    }

    /// VERDICT-IDENTITY gate for the structural-identity short-circuit (proof-
    /// lane floor). This is the WHOLE game: the short-circuit must return the
    /// SAME `VerificationResult` variant the full 100k-sample sweep would, in
    /// every direction — Valid where identical trap-free sides sweep to Valid,
    /// and NOT short-circuited (so the refuting/vacuous sweep still runs) for
    /// distinct-sided OR trap-capable obligations, or for identical-sided ones
    /// whose preconditions no edge point satisfies. A divergence here would be
    /// a silent proof-system miscompile (crediting Valid where the sweep
    /// refutes, or where it compared nothing).
    #[test]
    fn test_structural_identity_short_circuit_is_verdict_identical() {
        use crate::verify::VerificationStrength;

        // Reference: `verify_by_evaluation_with_config` with the short-circuit
        // DISABLED — an exact copy of its statistical/exhaustive dispatch minus
        // the early-out block. This is the verdict the full sweep produces.
        fn full_sweep(
            obligation: &ProofObligation,
            config: &VerificationConfig,
        ) -> VerificationResult {
            let width = obligation.inputs.first().map(|(_, w)| *w).unwrap_or(32);
            let compiled = CompiledObligation::try_new(obligation);
            let compiled = compiled.as_ref();
            if let Some(count) = exhaustive_input_count(obligation, config) {
                verify_exhaustive(obligation, compiled, count)
            } else if needs_multi_input_sampling(obligation) {
                verify_random_multi(obligation, compiled, config.sample_count)
            } else {
                verify_random(obligation, compiled, width, config.sample_count)
            }
        }

        // `VerificationResult` is not `PartialEq` (the `Invalid` counterexample
        // string differs run-to-run by which sampled point refuted first), so
        // compare by VARIANT — that is the verdict.
        fn tag(r: &VerificationResult) -> u8 {
            match r {
                VerificationResult::Valid => 0,
                VerificationResult::Invalid { .. } => 1,
                VerificationResult::Unknown { .. } => 2,
            }
        }

        // Build a RECONSTRUCTED-provenance obligation (the hot family the
        // short-circuit targets) at 64-bit width so the STATISTICAL dispatch is
        // taken (64 > exhaustive_threshold 8).
        fn oblig(
            name: &str,
            trust_ir: SmtExpr,
            aarch64: SmtExpr,
            inputs: Vec<(String, u32)>,
            preconditions: Vec<SmtExpr>,
        ) -> ProofObligation {
            ProofObligation {
                name: name.to_string(),
                trust_ir_expr: trust_ir,
                aarch64_expr: aarch64,
                inputs,
                preconditions,
                fp_inputs: vec![],
                category: Some(TransvalCheckKind::InstructionLowering),
                machine_side_provenance: MachineSideProvenance::Reconstructed {
                    from_opcode: "recon".to_string(),
                    arity: 2,
                },
            }
        }
        let a = || SmtExpr::var("a", 64);
        let b = || SmtExpr::var("b", 64);
        let ab = || vec![("a".to_string(), 64), ("b".to_string(), 64)];
        let a_only = || vec![("a".to_string(), 64)];
        let cfg = VerificationConfig::default();

        // -- (1) IDENTICAL-SIDED, TRAP-FREE: the commutative/immediate/LEA ALU
        //    surface. Short-circuit MUST fire and return Valid; the full sweep
        //    ALSO returns Valid. Verdict-identical.
        let identical_trap_free = vec![
            // AddRR: bvadd(a,b) == bvadd(a,b)
            oblig("id-add-rr", a().bvadd(b()), a().bvadd(b()), ab(), vec![]),
            // SubRR (correctly wired): bvsub(a,b) == bvsub(a,b)
            oblig("id-sub-rr", a().bvsub(b()), a().bvsub(b()), ab(), vec![]),
            // AndRR: bvand(a,b) == bvand(a,b)
            oblig("id-and-rr", a().bvand(b()), a().bvand(b()), ab(), vec![]),
            // ImulRR: bvmul(a,b) == bvmul(a,b)
            oblig("id-imul-rr", a().bvmul(b()), a().bvmul(b()), ab(), vec![]),
            // AddRI (immediate baked identically): bvadd(a,5) == bvadd(a,5)
            oblig(
                "id-add-ri",
                a().bvadd(SmtExpr::bv_const(5, 64)),
                a().bvadd(SmtExpr::bv_const(5, 64)),
                a_only(),
                vec![],
            ),
            // LEA (base + index + disp), same both sides.
            oblig(
                "id-lea",
                a().bvadd(b()).bvadd(SmtExpr::bv_const(16, 64)),
                a().bvadd(b()).bvadd(SmtExpr::bv_const(16, 64)),
                ab(),
                vec![],
            ),
        ];
        for o in &identical_trap_free {
            // Precondition of the intended path: sides structurally equal AND
            // trap-free, so the short-circuit predicate genuinely fires here.
            assert!(
                o.trust_ir_expr == o.aarch64_expr,
                "{}: sides not identical",
                o.name
            );
            assert!(
                crate::smt::collect_trap_poison_decls(&o.trust_ir_expr).is_empty(),
                "{}: unexpected trap node",
                o.name
            );
            let sc = verify_by_evaluation_with_config(o, &cfg);
            let sweep = full_sweep(o, &cfg);
            let memo = memoized_verify_by_evaluation(o, &cfg);
            assert_eq!(
                tag(&sc),
                0,
                "{}: short-circuit not Valid ({:?})",
                o.name,
                sc
            );
            assert_eq!(
                tag(&sweep),
                0,
                "{}: full sweep not Valid ({:?})",
                o.name,
                sweep
            );
            assert_eq!(tag(&sc), tag(&sweep), "{}: short-circuit != sweep", o.name);
            assert_eq!(tag(&memo), tag(&sweep), "{}: memo != sweep", o.name);
            // Strength label is computed SEPARATELY and is untouched by the
            // short-circuit: still Statistical{100000} => byte-identical certs.
            assert!(
                matches!(
                    VerificationStrength::for_obligation_with_config(o, &cfg),
                    VerificationStrength::Statistical {
                        sample_count: 100_000
                    }
                ),
                "{}: strength label changed",
                o.name
            );
        }

        // -- (2) IDENTICAL-SIDED WITH A TRAP (no guarding precondition): the
        //    shared tree can evaluate to Poison at guard==0, and
        //    semantically_equal(Poison, Poison) == false, so the sweep REFUTES.
        //    The trap-free guard MUST exclude this from the short-circuit, and
        //    both paths must return the SAME (Invalid) verdict.
        //    trust == aarch64 == trap_if_zero(a udiv b, guard=b).
        let trapped = a().bvudiv(b()).trap_if_zero(b());
        let with_trap = oblig("id-trap-udiv", trapped.clone(), trapped, ab(), vec![]);
        assert!(
            with_trap.trust_ir_expr == with_trap.aarch64_expr,
            "trap sides not identical"
        );
        assert!(
            !crate::smt::collect_trap_poison_decls(&with_trap.trust_ir_expr).is_empty(),
            "trap obligation should contain a TrapIfZero"
        );
        let sc_trap = verify_by_evaluation_with_config(&with_trap, &cfg);
        let sweep_trap = full_sweep(&with_trap, &cfg);
        let memo_trap = memoized_verify_by_evaluation(&with_trap, &cfg);
        assert_eq!(
            tag(&sweep_trap),
            1,
            "trap obligation full sweep should REFUTE (Poison vs Poison), got {:?}",
            sweep_trap
        );
        assert_eq!(
            tag(&sc_trap),
            tag(&sweep_trap),
            "trap obligation: short-circuit diverged from sweep ({:?} vs {:?}) — the trap guard failed",
            sc_trap,
            sweep_trap
        );
        assert_eq!(
            tag(&memo_trap),
            tag(&sweep_trap),
            "trap obligation: memo diverged from sweep"
        );

        // -- (3) DISTINCT-SIDED (mis-lowered): sides structurally differ, so the
        //    short-circuit MUST NOT fire and the full REFUTING sweep runs. Both
        //    paths must return the SAME (Invalid) verdict — refutation preserved.
        let distinct = vec![
            // Wrong opcode: source add, machine sub.
            oblig("wrong-opcode", a().bvadd(b()), a().bvsub(b()), ab(), vec![]),
            // Swapped non-commutative operands: a-b vs b-a.
            oblig("swapped-sub", a().bvsub(b()), b().bvsub(a()), ab(), vec![]),
            // Wrong baked immediate: a+5 vs a+7.
            oblig(
                "wrong-immediate",
                a().bvadd(SmtExpr::bv_const(5, 64)),
                a().bvadd(SmtExpr::bv_const(7, 64)),
                a_only(),
                vec![],
            ),
        ];
        for o in &distinct {
            assert!(
                o.trust_ir_expr != o.aarch64_expr,
                "{}: sides unexpectedly identical",
                o.name
            );
            let sc = verify_by_evaluation_with_config(o, &cfg);
            let sweep = full_sweep(o, &cfg);
            let memo = memoized_verify_by_evaluation(o, &cfg);
            assert_eq!(
                tag(&sweep),
                1,
                "{}: full sweep should REFUTE a mis-lowered obligation, got {:?}",
                o.name,
                sweep
            );
            assert_eq!(
                tag(&sc),
                tag(&sweep),
                "{}: short-circuit diverged from refuting sweep ({:?} vs {:?})",
                o.name,
                sc,
                sweep
            );
            assert_eq!(
                tag(&memo),
                tag(&sweep),
                "{}: memo diverged from refuting sweep",
                o.name
            );
        }

        // -- (4) IDENTICAL-SIDED, TRAP-FREE, WITH PRECONDITIONS: the sweep is
        //    `Valid` only when some sampled point satisfies them and the
        //    vacuous-sample `Unknown` otherwise, so the short-circuit may fire
        //    only with a witness in hand. Edge-witnessed and random-witnessed
        //    obligations sweep Valid; an obligation no point satisfies sweeps
        //    Unknown — and the short-circuit and memo must agree in every case.
        let a_is = |value: u64| a().eq_expr(SmtExpr::bv_const(value, 64));
        let not_an_edge: Vec<SmtExpr> = [0, 1, u64::MAX, u64::MAX - 1, 1 << 63, (1 << 63) - 1]
            .into_iter()
            .map(|edge| a_is(edge).not_expr())
            .collect();
        let with_preconditions = [
            (
                oblig(
                    "id-add-rr edge-witnessed",
                    a().bvadd(b()),
                    a().bvadd(b()),
                    ab(),
                    vec![a_is(0)],
                ),
                0,
            ),
            (
                oblig(
                    "id-add-rr random-witnessed",
                    a().bvadd(b()),
                    a().bvadd(b()),
                    ab(),
                    not_an_edge,
                ),
                0,
            ),
            (
                oblig(
                    "id-add-rr never satisfied",
                    a().bvadd(b()),
                    a().bvadd(b()),
                    ab(),
                    vec![a_is(0).and_expr(a_is(1))],
                ),
                2,
            ),
        ];
        for (o, expected) in &with_preconditions {
            let sc = verify_by_evaluation_with_config(o, &cfg);
            let sweep = full_sweep(o, &cfg);
            let memo = memoized_verify_by_evaluation(o, &cfg);
            assert_eq!(tag(&sweep), *expected, "{}: full sweep {:?}", o.name, sweep);
            assert_eq!(
                tag(&sc),
                tag(&sweep),
                "{}: short-circuit diverged from sweep ({:?} vs {:?})",
                o.name,
                sc,
                sweep
            );
            assert_eq!(
                tag(&memo),
                tag(&sweep),
                "{}: memo diverged from sweep ({:?} vs {:?})",
                o.name,
                memo,
                sweep
            );
        }
    }

    /// PROOF-2 adversarial REFUTATION test (roadmap 2026-07-01, WORKSTREAM
    /// PROOF): two obligations IDENTICAL except for a baked operand immediate
    /// must NOT share a cached verdict.
    ///
    /// OLD-KEY BEHAVIOR (demonstrated by construction): the retired
    /// process-wide memo (`x86_64_function_verifier::
    /// memoized_verify_by_evaluation`, pre-PROOF-2) was keyed by
    /// `(obligation.name, config.sample_count, config.exhaustive_threshold)`.
    /// Both obligations below produce the IDENTICAL old key
    /// `("PROOF2-ADVERSARIAL …", 100_000, 8)` — the old map would have
    /// returned the first (Valid) entry for the second obligation WITHOUT
    /// evaluating it, replaying `Valid` for a lowering whose machine side
    /// baked the WRONG immediate (7 where the source intends 5, false at
    /// every input). That replay is exactly the latent unsound
    /// verdict-replay class this fix closes; under the content-complete key
    /// the second obligation is evaluated on its own and REFUTES.
    #[test]
    fn memo_never_replays_verdict_across_different_baked_immediates() {
        let name = "PROOF2-ADVERSARIAL x86_64 Iadd_32 -> AddRI (real-operand)";
        let config = VerificationConfig::default();

        // Obligation A: source `x + 5`, machine `x + 5` — a CORRECT lowering
        // with immediate 5 baked into both sides. Must discharge Valid.
        let correct = proof2_obligation(name, 5, 5);
        assert!(
            matches!(
                memoized_verify_by_evaluation(&correct, &config),
                VerificationResult::Valid
            ),
            "correct same-immediate obligation must discharge Valid"
        );

        // Obligation B: SAME NAME, but the machine side baked a DIFFERENT
        // immediate (7 vs the intended 5) — the wrong-immediate miscompile
        // the old name-keyed memo would have masked by replaying A's Valid.
        let wrong_imm = proof2_obligation(name, 5, 7);
        assert!(
            matches!(
                memoized_verify_by_evaluation(&wrong_imm, &config),
                VerificationResult::Invalid { .. }
            ),
            "same-name obligation with a different baked immediate must REFUTE, \
             not replay the cached Valid verdict"
        );

        // The two verdicts are DISTINCT under distinct keys (the old key
        // admitted only ONE entry for this name+config, which is what caused
        // the replay). Obligation A is IDENTICAL-SIDED (`x + 5 == x + 5`) and
        // trap-free, so it is served by the structural-identity short-circuit
        // in `memoized_verify_by_evaluation` (returns Valid WITHOUT touching the
        // memo — a counterexample is structurally impossible), hence it is NOT
        // memoized. Obligation B is DISTINCT-SIDED (`x + 5` vs `x + 7`), so it
        // bypasses the short-circuit and is genuinely evaluated + memoized under
        // ITS OWN content-complete key. The anti-replay property is preserved a
        // fortiori: A never populates the memo, and B is computed on its own key
        // and REFUTES rather than replaying A's Valid.
        assert!(!eval_memo_contains(&correct, &config));
        assert!(eval_memo_contains(&wrong_imm, &config));
        // …and the refutation did not clobber or coarsen the correct entry.
        assert!(
            matches!(
                memoized_verify_by_evaluation(&correct, &config),
                VerificationResult::Valid
            ),
            "re-query of the correct obligation must still be Valid"
        );
    }

    /// PROOF-2 shift-count variant (the roadmap's ShlRI example): the shift
    /// COUNT is a semantically load-bearing baked immediate. A correct
    /// `x << 1` obligation must not lend its Valid verdict to a same-name
    /// obligation whose machine side shifts by a different count.
    #[test]
    fn memo_separates_same_name_shift_obligations_with_different_counts() {
        let name = "PROOF2-ADVERSARIAL x86_64 Ishl_32 -> ShlRI (real-operand)";
        let config = VerificationConfig::default();
        let x = || SmtExpr::var("recon_src1", 32);
        let shl = |count: u64| SmtExpr::BvShl {
            lhs: Arc::new(x()),
            rhs: Arc::new(SmtExpr::bv_const(count, 32)),
            width: 32,
        };
        let mk = |machine_count: u64| ProofObligation {
            name: name.to_string(),
            trust_ir_expr: shl(1),
            aarch64_expr: shl(machine_count),
            inputs: vec![("recon_src1".to_string(), 32)],
            // In-range count precondition, as the real ShlRI reconstruction
            // emits (#57).
            preconditions: vec![shift_in_range_precondition(SmtExpr::bv_const(1, 32), 32)],
            fp_inputs: vec![],
            category: Some(TransvalCheckKind::InstructionLowering),
            machine_side_provenance: MachineSideProvenance::Reconstructed {
                from_opcode: "ShlRI".to_string(),
                arity: 2,
            },
        };

        // Correct count (1 == 1): Valid.
        assert!(matches!(
            memoized_verify_by_evaluation(&mk(1), &config),
            VerificationResult::Valid
        ));
        // SAME name, machine side shifts by 2 instead of 1: refutes at x=1
        // (2 vs 4). The old (name, config) key replayed Valid here.
        assert!(
            matches!(
                memoized_verify_by_evaluation(&mk(2), &config),
                VerificationResult::Invalid { .. }
            ),
            "same-name shift obligation with a different baked count must REFUTE"
        );
    }

    /// SOUNDNESS GATE for the compiled fast path: for EVERY obligation in the
    /// full proof database that `CompiledObligation::try_new` accepts, the
    /// compiled [`FlatProg`] tape must agree with the interpreter `SmtExpr::eval`
    /// — bit-for-bit, on `trust_ir`, `aarch64`, and every precondition — across a
    /// battery of edge-case and random inputs. If this passes, the fast path can
    /// only ever compute the SAME verdict the interpreter would, just faster (a
    /// divergence here is the one way the fast path could change a verdict). It
    /// also asserts the fast path is actually exercised (compiled_count > 0).
    ///
    /// Because `FlatProg` (unlike the earlier `CExpr`) covers the division/
    /// remainder subset, this now also cross-checks any `bvsdiv`/`bvudiv`/`bvurem`
    /// DB proofs the interpreter previously handled alone; the 128-bit / trap /
    /// overflow division arms are additionally covered by
    /// `smt::tests::flatprog_matches_interpreter_differential_fuzz`.
    #[test]
    fn compiled_fast_path_matches_interpreter_on_full_db() {
        use crate::proof_database::ProofDatabase;
        let db = ProofDatabase::new();
        let total = db.all().len();
        let mut compiled_count = 0usize;
        let mut div_count = 0usize;
        let mut scratch: Vec<SVal> = Vec::new();
        for cp in db.all() {
            let ob = &cp.obligation;
            let Some(co) = CompiledObligation::try_new(ob) else {
                continue;
            };
            compiled_count += 1;
            if crate::smt::expr_contains_division(&ob.trust_ir_expr)
                || crate::smt::expr_contains_division(&ob.aarch64_expr)
            {
                div_count += 1;
            }

            let mut rng: u64 = 0x9E37_79B9_7F4A_7C15
                ^ ob.name.bytes().fold(0u64, |h, b| {
                    h.wrapping_mul(1099511628211).wrapping_add(u64::from(b))
                });
            for trial in 0..256u64 {
                let mut env = EvalEnv::default();
                for (name, width) in &ob.inputs {
                    rng = rng
                        .wrapping_mul(6364136223846793005)
                        .wrapping_add(1442695040888963407);
                    let mask_val = mask(u64::MAX, *width);
                    let raw = match trial {
                        0 => 0,
                        1 => 1,
                        2 => mask_val,
                        3 => mask_val.wrapping_sub(1),
                        4 => 1u64 << width.saturating_sub(1),
                        5 => (1u64 << width.saturating_sub(1)).wrapping_sub(1),
                        6 => !rng,
                        _ => rng,
                    };
                    env.insert(name.clone(), mask(raw, *width));
                }

                assert_eq!(
                    co.trust_ir.eval(&env, &mut scratch),
                    ob.trust_ir_expr.eval(&env),
                    "compiled vs interpreted trust_ir diverged for `{}` at trial {trial}",
                    ob.name
                );
                assert_eq!(
                    co.aarch64.eval(&env, &mut scratch),
                    ob.aarch64_expr.eval(&env),
                    "compiled vs interpreted aarch64 diverged for `{}` at trial {trial}",
                    ob.name
                );
                for (cpre, spre) in co.preconds.iter().zip(&ob.preconditions) {
                    assert_eq!(
                        cpre.eval(&env, &mut scratch),
                        spre.eval(&env),
                        "compiled vs interpreted precondition diverged for `{}` at trial {trial}",
                        ob.name
                    );
                }
            }
        }
        assert!(
            compiled_count > 0,
            "compiled fast path was never exercised — 0 of {total} obligations compiled"
        );
        eprintln!(
            "compiled fast path cross-checked {compiled_count} / {total} obligations \
             ({div_count} contain division/remainder)"
        );
    }

    /// Helper: verify a proof obligation using the mock evaluator and assert Valid.
    fn assert_valid(obligation: &ProofObligation) {
        let result = verify_by_evaluation(obligation);
        match &result {
            VerificationResult::Valid => {} // expected
            VerificationResult::Invalid { counterexample } => {
                panic!(
                    "Proof '{}' FAILED with counterexample: {}",
                    obligation.name, counterexample
                );
            }
            VerificationResult::Unknown { reason } => {
                panic!("Proof '{}' returned Unknown: {}", obligation.name, reason);
            }
        }
    }

    // -----------------------------------------------------------------------
    // I8 arithmetic proofs (exhaustive — all 2^16 or 2^8 input combos)
    // -----------------------------------------------------------------------

    #[test]
    fn test_proof_iadd_i8() {
        assert_valid(&proof_iadd_i8());
    }

    #[test]
    fn test_proof_isub_i8() {
        assert_valid(&proof_isub_i8());
    }

    #[test]
    fn test_proof_imul_i8() {
        assert_valid(&proof_imul_i8());
    }

    #[test]
    fn test_proof_neg_i8() {
        assert_valid(&proof_neg_i8());
    }

    // -----------------------------------------------------------------------
    // I16 arithmetic proofs (statistical — edge cases + random sampling)
    // -----------------------------------------------------------------------

    #[test]
    fn test_proof_iadd_i16() {
        assert_valid(&proof_iadd_i16());
    }

    #[test]
    fn test_proof_isub_i16() {
        assert_valid(&proof_isub_i16());
    }

    #[test]
    fn test_proof_imul_i16() {
        assert_valid(&proof_imul_i16());
    }

    #[test]
    fn test_proof_neg_i16() {
        assert_valid(&proof_neg_i16());
    }

    // -----------------------------------------------------------------------
    // I32 arithmetic proofs (statistical)
    // -----------------------------------------------------------------------

    #[test]
    fn test_proof_iadd_i32() {
        assert_valid(&proof_iadd_i32());
    }

    #[test]
    fn test_proof_isub_i32() {
        assert_valid(&proof_isub_i32());
    }

    #[test]
    fn test_proof_imul_i32() {
        assert_valid(&proof_imul_i32());
    }

    #[test]
    fn test_proof_neg_i32() {
        assert_valid(&proof_neg_i32());
    }

    // -----------------------------------------------------------------------
    // I64 arithmetic proofs (statistical)
    // -----------------------------------------------------------------------

    #[test]
    fn test_proof_iadd_i64() {
        assert_valid(&proof_iadd_i64());
    }

    #[test]
    fn test_proof_isub_i64() {
        assert_valid(&proof_isub_i64());
    }

    #[test]
    fn test_proof_imul_i64() {
        assert_valid(&proof_imul_i64());
    }

    #[test]
    fn test_proof_neg_i64() {
        assert_valid(&proof_neg_i64());
    }

    #[test]
    fn test_proof_aarch64_madd_rr_generic() {
        assert_valid(&proof_aarch64_madd_rr_generic());
    }

    #[test]
    fn test_proof_aarch64_msub_rr_generic() {
        assert_valid(&proof_aarch64_msub_rr_generic());
    }

    /// The FAITHFUL UMULL widening obligation: genuine (structurally distinct,
    /// Concat-zext source vs ZeroExtend-plus-XZR-addend machine, NOT X==X) and
    /// discharges Valid under the in-house evaluator.
    #[test]
    fn test_proof_umull_rr_valid_and_genuine() {
        let obligation = proof_umull_rr();
        assert!(
            obligation.is_genuinely_proven(),
            "UMULL proof '{}' is DEGENERATE (X==X)",
            obligation.name
        );
        assert_valid(&obligation);
    }

    /// NON-VACUITY: the SMULL (sext) confusion — the exact control that
    /// distinguishes UMULL from SMULL — and the truncating-MUL confusion must
    /// both REFUTE under the in-house evaluator.
    #[test]
    fn test_umull_wrong_controls_refute() {
        let controls = umull_wrong_controls();
        assert_eq!(controls.len(), 2, "SMULL-sext + truncating-MUL controls");
        for obligation in &controls {
            assert!(
                obligation.is_genuinely_proven(),
                "UMULL control '{}' is degenerate",
                obligation.name
            );
            let result = verify_by_evaluation(obligation);
            assert!(
                !matches!(result, VerificationResult::Valid),
                "UMULL NEGATIVE control '{}' was VALID — a wrong widening-multiply \
                 machine side must refute, so the positive obligation is vacuous",
                obligation.name
            );
        }
    }

    // -----------------------------------------------------------------------
    // Aggregate arithmetic proof test
    // -----------------------------------------------------------------------

    #[test]
    fn test_all_arithmetic_proofs() {
        for obligation in all_arithmetic_proofs() {
            assert_valid(&obligation);
        }
    }

    // -----------------------------------------------------------------------
    // Division lowering proof tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_proof_sdiv_i32() {
        assert_valid(&proof_sdiv_i32());
    }

    #[test]
    fn test_proof_sdiv_i64() {
        assert_valid(&proof_sdiv_i64());
    }

    #[test]
    fn test_proof_udiv_i32() {
        assert_valid(&proof_udiv_i32());
    }

    #[test]
    fn test_proof_udiv_i64() {
        assert_valid(&proof_udiv_i64());
    }

    #[test]
    fn test_all_division_proofs() {
        for obligation in all_division_proofs() {
            assert_valid(&obligation);
        }
    }

    // -----------------------------------------------------------------------
    // Remainder lowering proof tests (issue #435)
    // -----------------------------------------------------------------------

    #[test]
    fn test_proof_urem_i8() {
        assert_valid(&proof_urem_i8());
    }

    #[test]
    fn test_proof_srem_i8() {
        assert_valid(&proof_srem_i8());
    }

    #[test]
    fn test_proof_urem_i32() {
        assert_valid(&proof_urem_i32());
    }

    #[test]
    fn test_proof_srem_i32() {
        assert_valid(&proof_srem_i32());
    }

    #[test]
    fn test_proof_urem_i64() {
        assert_valid(&proof_urem_i64());
    }

    #[test]
    fn test_proof_srem_i64() {
        assert_valid(&proof_srem_i64());
    }

    #[test]
    fn test_all_remainder_proofs() {
        for obligation in all_remainder_proofs() {
            assert_valid(&obligation);
        }
    }

    /// Precondition sanity: Urem obligation must have exactly the `b != 0`
    /// precondition (matching Udiv).
    #[test]
    fn test_proof_urem_i8_precondition_count() {
        let urem = proof_urem_i8();
        assert_eq!(
            urem.preconditions.len(),
            1,
            "Urem I8 must have NonZeroDivisor precondition"
        );
    }

    /// Precondition sanity: Srem obligation must have *two* preconditions --
    /// `b != 0` AND `not (a == INT8_MIN && b == -1)`.
    #[test]
    fn test_proof_srem_i8_precondition_count() {
        let srem = proof_srem_i8();
        assert_eq!(
            srem.preconditions.len(),
            2,
            "Srem I8 must have NonZeroDivisor + INT_MIN/-1 overflow preconditions"
        );
    }

    #[test]
    fn test_remainder_proofs_cover_i8_i16_i32_i64() {
        let names: Vec<_> = all_remainder_proofs().into_iter().map(|p| p.name).collect();
        assert_eq!(names.len(), 8, "expected urem/srem at four widths");
        for expected in [
            "Urem_I8", "Srem_I8", "Urem_I16", "Srem_I16", "Urem_I32", "Srem_I32", "Urem_I64",
            "Srem_I64",
        ] {
            assert!(
                names.iter().any(|name| name.starts_with(expected)),
                "missing remainder proof for {expected}"
            );
        }
    }

    // -----------------------------------------------------------------------
    // Bitcast lowering proof tests (issue #435)
    // -----------------------------------------------------------------------

    #[test]
    fn test_proof_bitcast_i8() {
        assert_valid(&proof_bitcast_i8());
    }

    #[test]
    fn test_all_bitcast_proofs() {
        for obligation in all_bitcast_proofs() {
            assert_valid(&obligation);
        }
    }

    // -----------------------------------------------------------------------
    // Bitfield lowering proof tests (issue #452/#435)
    // -----------------------------------------------------------------------

    #[test]
    fn test_proof_extract_bits_i8() {
        assert_valid(&proof_extract_bits_i8());
    }

    #[test]
    fn test_proof_sextract_bits_i8() {
        assert_valid(&proof_sextract_bits_i8());
    }

    #[test]
    fn test_proof_insert_bits_i8() {
        assert_valid(&proof_insert_bits_i8());
    }

    #[test]
    fn test_all_bitfield_proofs() {
        for obligation in all_bitfield_proofs() {
            assert_valid(&obligation);
        }
    }

    #[test]
    fn test_bitfield_proofs_cover_i8_i16_i32_i64() {
        let names: Vec<_> = all_bitfield_proofs().into_iter().map(|p| p.name).collect();
        assert_eq!(names.len(), 12, "expected 3 bitfield ops at four widths");
        for expected in [
            "ExtractBits{lsb=2,width=4}_I8",
            "SextractBits{lsb=2,width=4}_I8",
            "InsertBits{lsb=2,width=4}_I8",
            "ExtractBits{lsb=3,width=7}_I16",
            "SextractBits{lsb=3,width=7}_I16",
            "InsertBits{lsb=3,width=7}_I16",
            "ExtractBits{lsb=7,width=13}_I32",
            "SextractBits{lsb=7,width=13}_I32",
            "InsertBits{lsb=7,width=13}_I32",
            "ExtractBits{lsb=11,width=23}_I64",
            "SextractBits{lsb=11,width=23}_I64",
            "InsertBits{lsb=11,width=23}_I64",
        ] {
            assert!(
                names.iter().any(|name| name.starts_with(expected)),
                "missing bitfield proof for {expected}"
            );
        }
    }

    /// Sanity: none of the bitfield obligations has a precondition -- they
    /// are pure QF_BV identities at the bitvector level.
    #[test]
    fn test_bitfield_proofs_have_no_preconditions() {
        for obligation in all_bitfield_proofs() {
            assert!(
                obligation.preconditions.is_empty(),
                "bitfield proof '{}' must have no preconditions",
                obligation.name
            );
        }
    }

    // -----------------------------------------------------------------------
    // I128 multi-register lowering proof tests (issue #324)
    // -----------------------------------------------------------------------

    #[test]
    fn test_proof_iadd_i128_lo() {
        assert_valid(&proof_iadd_i128_lo());
    }

    #[test]
    fn test_proof_iadd_i128_hi() {
        assert_valid(&proof_iadd_i128_hi());
    }

    #[test]
    fn test_proof_isub_i128_lo() {
        assert_valid(&proof_isub_i128_lo());
    }

    #[test]
    fn test_proof_isub_i128_hi() {
        assert_valid(&proof_isub_i128_hi());
    }

    /// Sanity check that the ADC carry expression in `proof_iadd_i128_hi`
    /// actually flags wraparound for a concrete overflowing case.
    #[test]
    fn test_iadd_i128_carry_semantics_overflow() {
        use std::collections::HashMap;
        let obligation = proof_iadd_i128_hi();

        // a_lo = b_lo = 0xFFFF_FFFF_FFFF_FFFF, a_hi = b_hi = 0
        // lo_sum wraps to 0xFFFF_FFFF_FFFF_FFFE, carry = 1
        // expected dst_hi = 0 + 0 + 1 = 1
        let mut env = HashMap::new();
        env.insert("a_lo".to_string(), u64::MAX);
        env.insert("b_lo".to_string(), u64::MAX);
        env.insert("a_hi".to_string(), 0u64);
        env.insert("b_hi".to_string(), 0u64);

        let trust_ir_val = obligation.trust_ir_expr.eval(&env).as_u64();
        let mach_val = obligation.aarch64_expr.eval(&env).as_u64();
        assert_eq!(
            trust_ir_val, 1,
            "overflow case should give dst_hi = 1, got {}",
            trust_ir_val
        );
        assert_eq!(trust_ir_val, mach_val);
    }

    /// Complementary sanity check: non-overflowing low-limb addition must
    /// leave the high limb untouched (carry=0).
    #[test]
    fn test_iadd_i128_carry_semantics_no_overflow() {
        use std::collections::HashMap;
        let obligation = proof_iadd_i128_hi();

        // a_lo=1, b_lo=2 → lo_sum=3, no carry. a_hi=5, b_hi=7 → dst_hi=12.
        let mut env = HashMap::new();
        env.insert("a_lo".to_string(), 1u64);
        env.insert("b_lo".to_string(), 2u64);
        env.insert("a_hi".to_string(), 5u64);
        env.insert("b_hi".to_string(), 7u64);

        let trust_ir_val = obligation.trust_ir_expr.eval(&env).as_u64();
        let mach_val = obligation.aarch64_expr.eval(&env).as_u64();
        assert_eq!(
            trust_ir_val, 12,
            "no-carry case should give dst_hi = 12, got {}",
            trust_ir_val
        );
        assert_eq!(trust_ir_val, mach_val);
    }

    /// Sanity check that the SBC borrow expression in `proof_isub_i128_hi`
    /// flags borrow-out when a_lo < b_lo.
    #[test]
    fn test_isub_i128_borrow_semantics() {
        use std::collections::HashMap;
        let obligation = proof_isub_i128_hi();

        // a_lo=0, b_lo=1 → borrow=1. a_hi=5, b_hi=2 → dst_hi = 5 - 2 - 1 = 2.
        let mut env = HashMap::new();
        env.insert("a_lo".to_string(), 0u64);
        env.insert("b_lo".to_string(), 1u64);
        env.insert("a_hi".to_string(), 5u64);
        env.insert("b_hi".to_string(), 2u64);

        let trust_ir_val = obligation.trust_ir_expr.eval(&env).as_u64();
        let mach_val = obligation.aarch64_expr.eval(&env).as_u64();
        assert_eq!(
            trust_ir_val, 2,
            "borrow case should give dst_hi = 2, got {}",
            trust_ir_val
        );
        assert_eq!(trust_ir_val, mach_val);

        // Non-borrow: a_lo >= b_lo, dst_hi = a_hi - b_hi.
        env.insert("a_lo".to_string(), 10u64);
        env.insert("b_lo".to_string(), 3u64);
        let trust_ir_val = obligation.trust_ir_expr.eval(&env).as_u64();
        assert_eq!(
            trust_ir_val, 3,
            "no-borrow case should give dst_hi = 3, got {}",
            trust_ir_val
        );
    }

    #[test]
    fn test_proof_imul_i128_lo() {
        assert_valid(&proof_imul_i128_lo());
    }

    #[test]
    fn test_proof_imul_i128_hi() {
        assert_valid(&proof_imul_i128_hi());
    }

    /// Concrete sanity: for a = 2^64, b = 3 ->
    ///   a = (a_hi=1, a_lo=0), b = (b_hi=0, b_lo=3)
    ///   a*b = 3 * 2^64 = (hi=3, lo=0)
    ///   UMULH(a_lo=0, b_lo=3) = 0
    ///   MADD chain: t1 = 0*0 + 0 = 0, dst_hi = 1*3 + 0 = 3. PASS.
    #[test]
    fn test_imul_i128_cross_term_2pow64_times_3() {
        use std::collections::HashMap;
        let obligation = proof_imul_i128_hi();

        let mut env = HashMap::new();
        env.insert("a_lo".to_string(), 0u64);
        env.insert("a_hi".to_string(), 1u64);
        env.insert("b_lo".to_string(), 3u64);
        env.insert("b_hi".to_string(), 0u64);
        env.insert("umulh_ab_lo".to_string(), 0u64); // UMULH(0, 3) = 0

        let trust_ir_val = obligation.trust_ir_expr.eval(&env).as_u64();
        let mach_val = obligation.aarch64_expr.eval(&env).as_u64();
        assert_eq!(
            trust_ir_val, 3,
            "dst_hi for 2^64 * 3 should be 3, got {}",
            trust_ir_val
        );
        assert_eq!(trust_ir_val, mach_val);
    }

    /// Concrete sanity exercising the UMULH carry-in:
    ///   a = (a_hi=0, a_lo=u64::MAX), b = (b_hi=0, b_lo=u64::MAX)
    ///   a*b = (2^64 - 1)^2 = 2^128 - 2^65 + 1
    ///         = (hi = 2^64 - 2, lo = 1)  [i.e. hi = u64::MAX - 1]
    ///   UMULH(u64::MAX, u64::MAX) = u64::MAX - 1
    ///   MADD chain: t1 = u64::MAX*0 + (u64::MAX-1) = u64::MAX-1
    ///               dst_hi = 0*u64::MAX + (u64::MAX-1) = u64::MAX-1
    #[test]
    fn test_imul_i128_umulh_carry() {
        use std::collections::HashMap;
        let obligation = proof_imul_i128_hi();

        let mut env = HashMap::new();
        env.insert("a_lo".to_string(), u64::MAX);
        env.insert("a_hi".to_string(), 0u64);
        env.insert("b_lo".to_string(), u64::MAX);
        env.insert("b_hi".to_string(), 0u64);
        env.insert("umulh_ab_lo".to_string(), u64::MAX - 1);

        let trust_ir_val = obligation.trust_ir_expr.eval(&env).as_u64();
        let mach_val = obligation.aarch64_expr.eval(&env).as_u64();
        assert_eq!(
            trust_ir_val,
            u64::MAX - 1,
            "dst_hi for u64::MAX^2 should carry UMULH = u64::MAX-1, got {}",
            trust_ir_val
        );
        assert_eq!(trust_ir_val, mach_val);
    }

    #[test]
    fn test_proof_ishl_i128() {
        assert_valid(&proof_ishl_i128());
    }

    #[test]
    fn test_proof_ushr_i128() {
        assert_valid(&proof_ushr_i128());
    }

    #[test]
    fn test_proof_sshr_i128() {
        assert_valid(&proof_sshr_i128());
    }

    /// Concrete regression for the AArch64 modulo-64 shift boundary: without
    /// the explicit spill guard, shift-by-zero would OR an unshifted spill
    /// into the opposite limb.
    #[test]
    fn test_i128_shift_zero_is_identity() {
        use std::collections::HashMap;

        let mut env = HashMap::new();
        env.insert("a_lo".to_string(), 0x0123_4567_89AB_CDEFu64);
        env.insert("a_hi".to_string(), 0xFEDC_BA98_7654_3210u64);
        env.insert("shift".to_string(), 0u64);
        let expected = (0xFEDC_BA98_7654_3210u128 << 64) | 0x0123_4567_89AB_CDEFu128;

        for obligation in [proof_ishl_i128(), proof_ushr_i128(), proof_sshr_i128()] {
            let trust_ir_val = obligation.trust_ir_expr.eval(&env).as_u128();
            let mach_val = obligation.aarch64_expr.eval(&env).as_u128();
            assert_eq!(
                trust_ir_val, expected,
                "{} shift-by-zero trust_ir result must be identity",
                obligation.name
            );
            assert_eq!(
                mach_val, expected,
                "{} shift-by-zero lowering result must be identity",
                obligation.name
            );
        }
    }

    #[test]
    fn test_i128_shift_64_crosses_limb_boundary() {
        use std::collections::HashMap;

        let mut env = HashMap::new();
        env.insert("a_lo".to_string(), 0x0123_4567_89AB_CDEFu64);
        env.insert("a_hi".to_string(), 0x8000_0000_0000_0000u64);
        env.insert("shift".to_string(), 64u64);

        let shl = proof_ishl_i128();
        let shl_val = shl.aarch64_expr.eval(&env).as_u128();
        assert_eq!(shl_val, 0x0123_4567_89AB_CDEFu128 << 64);

        let ushr = proof_ushr_i128();
        let ushr_val = ushr.aarch64_expr.eval(&env).as_u128();
        assert_eq!(ushr_val, 0x8000_0000_0000_0000u128);

        let sshr = proof_sshr_i128();
        let sshr_val = sshr.aarch64_expr.eval(&env).as_u128();
        assert_eq!(sshr_val, 0xFFFF_FFFF_FFFF_FFFF_8000_0000_0000_0000u128);
    }

    /// Verify division proof obligations include the NonZeroDivisor precondition.
    #[test]
    fn test_division_proofs_have_preconditions() {
        let sdiv32 = proof_sdiv_i32();
        assert_eq!(
            sdiv32.preconditions.len(),
            1,
            "SDIV I32 must have NonZeroDivisor precondition"
        );

        let sdiv64 = proof_sdiv_i64();
        assert_eq!(
            sdiv64.preconditions.len(),
            1,
            "SDIV I64 must have NonZeroDivisor precondition"
        );

        let udiv32 = proof_udiv_i32();
        assert_eq!(
            udiv32.preconditions.len(),
            1,
            "UDIV I32 must have NonZeroDivisor precondition"
        );

        let udiv64 = proof_udiv_i64();
        assert_eq!(
            udiv64.preconditions.len(),
            1,
            "UDIV I64 must have NonZeroDivisor precondition"
        );
    }

    /// Verify that the precondition rejects b=0 and accepts b!=0.
    #[test]
    fn test_division_precondition_semantics() {
        use std::collections::HashMap;

        let obligation = proof_sdiv_i32();
        let pre = &obligation.preconditions[0];

        // b=0 should fail precondition
        let mut env_zero = HashMap::new();
        env_zero.insert("a".to_string(), 42u64);
        env_zero.insert("b".to_string(), 0u64);
        assert!(
            !pre.eval(&env_zero).as_bool(),
            "Precondition must reject b=0"
        );

        // b=1 should pass precondition
        let mut env_one = HashMap::new();
        env_one.insert("a".to_string(), 42u64);
        env_one.insert("b".to_string(), 1u64);
        assert!(pre.eval(&env_one).as_bool(), "Precondition must accept b=1");

        // b=0xFFFFFFFF (-1 in 32-bit signed) should pass precondition
        let mut env_neg1 = HashMap::new();
        env_neg1.insert("a".to_string(), 42u64);
        env_neg1.insert("b".to_string(), 0xFFFF_FFFFu64);
        assert!(
            pre.eval(&env_neg1).as_bool(),
            "Precondition must accept b=-1"
        );
    }

    /// Edge case: SDIV with dividend=1, divisor=1 -- basic sanity.
    #[test]
    fn test_sdiv_i32_div_by_one() {
        use crate::aarch64_semantics::encode_sdiv_rr;
        use crate::trust_ir_semantics::encode_trust_ir_binop;
        use std::collections::HashMap;
        use trust_cg_ir::cc::OperandSize;
        use trust_cg_lower::instructions::Opcode;
        use trust_cg_lower::types::Type;

        let a = SmtExpr::var("a", 32);
        let b = SmtExpr::var("b", 32);

        let trust_ir = encode_trust_ir_binop(&Opcode::Sdiv, Type::I32, a.clone(), b.clone());
        let aarch64 = encode_sdiv_rr(OperandSize::S32, a, b);

        let mut env = HashMap::new();
        env.insert("a".to_string(), 42u64);
        env.insert("b".to_string(), 1u64);

        assert_eq!(trust_ir.eval(&env), aarch64.eval(&env));
    }

    /// Edge case: SDIV INT_MIN / -1 = INT_MIN (signed overflow wraps).
    /// On AArch64, SDIV 0x80000000 / 0xFFFFFFFF = 0x80000000.
    #[test]
    fn test_sdiv_i32_int_min_div_neg1() {
        use crate::aarch64_semantics::encode_sdiv_rr;
        use crate::smt::EvalResult;
        use crate::trust_ir_semantics::encode_trust_ir_binop;
        use std::collections::HashMap;
        use trust_cg_ir::cc::OperandSize;
        use trust_cg_lower::instructions::Opcode;
        use trust_cg_lower::types::Type;

        let a = SmtExpr::var("a", 32);
        let b = SmtExpr::var("b", 32);

        let trust_ir = encode_trust_ir_binop(&Opcode::Sdiv, Type::I32, a.clone(), b.clone());
        let aarch64 = encode_sdiv_rr(OperandSize::S32, a, b);

        let mut env = HashMap::new();
        env.insert("a".to_string(), 0x8000_0000u64); // INT32_MIN
        env.insert("b".to_string(), 0xFFFF_FFFFu64); // -1

        let trust_ir_result = trust_ir.eval(&env);
        let aarch64_result = aarch64.eval(&env);
        assert_eq!(trust_ir_result, aarch64_result);
        // INT_MIN / -1 overflows to INT_MIN
        assert_eq!(trust_ir_result, EvalResult::Bv(0x8000_0000));
    }

    /// Edge case: SDIV negative values.
    #[test]
    fn test_sdiv_i32_negative_values() {
        use crate::aarch64_semantics::encode_sdiv_rr;
        use crate::smt::EvalResult;
        use crate::trust_ir_semantics::encode_trust_ir_binop;
        use std::collections::HashMap;
        use trust_cg_ir::cc::OperandSize;
        use trust_cg_lower::instructions::Opcode;
        use trust_cg_lower::types::Type;

        let a = SmtExpr::var("a", 32);
        let b = SmtExpr::var("b", 32);

        let trust_ir = encode_trust_ir_binop(&Opcode::Sdiv, Type::I32, a.clone(), b.clone());
        let aarch64 = encode_sdiv_rr(OperandSize::S32, a, b);

        // -10 / 3 = -3 (truncated toward zero)
        let mut env = HashMap::new();
        let neg10 = ((-10i32) as u32) as u64;
        env.insert("a".to_string(), neg10);
        env.insert("b".to_string(), 3u64);

        let trust_ir_result = trust_ir.eval(&env);
        let aarch64_result = aarch64.eval(&env);
        assert_eq!(trust_ir_result, aarch64_result);
        // -3 in 32-bit
        let neg3 = ((-3i32) as u32) as u64;
        assert_eq!(trust_ir_result, EvalResult::Bv(neg3));
    }

    /// Edge case: UDIV max value.
    #[test]
    fn test_udiv_i32_max_values() {
        use crate::aarch64_semantics::encode_udiv_rr;
        use crate::smt::EvalResult;
        use crate::trust_ir_semantics::encode_trust_ir_binop;
        use std::collections::HashMap;
        use trust_cg_ir::cc::OperandSize;
        use trust_cg_lower::instructions::Opcode;
        use trust_cg_lower::types::Type;

        let a = SmtExpr::var("a", 32);
        let b = SmtExpr::var("b", 32);

        let trust_ir = encode_trust_ir_binop(&Opcode::Udiv, Type::I32, a.clone(), b.clone());
        let aarch64 = encode_udiv_rr(OperandSize::S32, a, b);

        // UINT32_MAX / 1 = UINT32_MAX
        let mut env = HashMap::new();
        env.insert("a".to_string(), 0xFFFF_FFFFu64);
        env.insert("b".to_string(), 1u64);

        let trust_ir_result = trust_ir.eval(&env);
        let aarch64_result = aarch64.eval(&env);
        assert_eq!(trust_ir_result, aarch64_result);
        assert_eq!(trust_ir_result, EvalResult::Bv(0xFFFF_FFFF));

        // UINT32_MAX / UINT32_MAX = 1
        env.insert("b".to_string(), 0xFFFF_FFFFu64);
        let trust_ir_result2 = encode_trust_ir_binop(
            &Opcode::Udiv,
            Type::I32,
            SmtExpr::var("a", 32),
            SmtExpr::var("b", 32),
        )
        .eval(&env);
        let aarch64_result2 = encode_udiv_rr(
            OperandSize::S32,
            SmtExpr::var("a", 32),
            SmtExpr::var("b", 32),
        )
        .eval(&env);
        assert_eq!(trust_ir_result2, aarch64_result2);
        assert_eq!(trust_ir_result2, EvalResult::Bv(1));
    }

    /// Verify SMT2 output for division includes preconditions.
    #[test]
    fn test_sdiv_smt2_has_precondition() {
        let obligation = proof_sdiv_i32();
        let smt2 = obligation.to_smt2();
        assert!(smt2.contains("(set-logic"), "SMT2 should have set-logic");
        assert!(
            smt2.contains("(declare-const a (_ BitVec 32))"),
            "SMT2 should declare a"
        );
        assert!(
            smt2.contains("(declare-const b (_ BitVec 32))"),
            "SMT2 should declare b"
        );
        assert!(smt2.contains("(check-sat)"), "SMT2 should have check-sat");
        // The precondition (b != 0) should be ANDed into the formula
        assert!(smt2.contains("(assert"), "SMT2 should have assert");
    }

    /// Negative test: SDIV without precondition should fail (div-by-zero mismatch).
    /// trust_ir and AArch64 both return sentinel 0 for div-by-zero in the evaluator,
    /// so this tests that WITH precondition the proofs are valid but the
    /// precondition correctly skips div-by-zero inputs.
    #[test]
    fn test_division_precondition_skips_zero_divisor() {
        use std::collections::HashMap;

        let obligation = proof_sdiv_i32();

        // Manually test that b=0 is skipped by check_single_point
        let mut env = HashMap::new();
        env.insert("a".to_string(), 42u64);
        env.insert("b".to_string(), 0u64);

        // The precondition should evaluate to false for b=0
        let pre_result = obligation.preconditions[0].eval(&env);
        assert!(
            !pre_result.as_bool(),
            "Precondition should be false for b=0"
        );
    }

    #[test]
    fn test_smt2_output() {
        let obligation = proof_iadd_i32();
        let smt2 = obligation.to_smt2();
        assert!(smt2.contains("(set-logic QF_BV)"));
        assert!(smt2.contains("(declare-const a (_ BitVec 32))"));
        assert!(smt2.contains("(declare-const b (_ BitVec 32))"));
        assert!(smt2.contains("(check-sat)"));
        assert!(smt2.contains("(assert"));
    }

    /// Negative test: verify that a deliberately wrong rule is detected.
    #[test]
    fn test_wrong_rule_detected() {
        // Claim add = sub — should find a counterexample.
        let a = SmtExpr::var("a", 8);
        let b = SmtExpr::var("b", 8);

        let obligation = ProofObligation {
            machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
            name: "WRONG: Iadd -> SUBWrr".to_string(),
            trust_ir_expr: a.clone().bvadd(b.clone()), // add
            aarch64_expr: a.bvsub(b),                  // sub (wrong!)
            inputs: vec![("a".to_string(), 8), ("b".to_string(), 8)],
            preconditions: vec![],
            fp_inputs: vec![],
            category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
        };

        let result = verify_by_evaluation(&obligation);
        match result {
            VerificationResult::Invalid { .. } => {} // expected
            other => panic!("Expected Invalid for wrong rule, got {:?}", other),
        }
    }

    // -----------------------------------------------------------------------
    // Comparison lowering proof tests (32-bit, all 10 conditions)
    // -----------------------------------------------------------------------

    #[test]
    fn test_proof_icmp_eq_i32() {
        assert_valid(&proof_icmp_eq_i32());
    }

    #[test]
    fn test_proof_icmp_ne_i32() {
        assert_valid(&proof_icmp_ne_i32());
    }

    #[test]
    fn test_proof_icmp_slt_i32() {
        assert_valid(&proof_icmp_slt_i32());
    }

    #[test]
    fn test_proof_icmp_sge_i32() {
        assert_valid(&proof_icmp_sge_i32());
    }

    #[test]
    fn test_proof_icmp_sgt_i32() {
        assert_valid(&proof_icmp_sgt_i32());
    }

    #[test]
    fn test_proof_icmp_sle_i32() {
        assert_valid(&proof_icmp_sle_i32());
    }

    #[test]
    fn test_proof_icmp_ult_i32() {
        assert_valid(&proof_icmp_ult_i32());
    }

    #[test]
    fn test_proof_icmp_uge_i32() {
        assert_valid(&proof_icmp_uge_i32());
    }

    /// The four UGE obligations retracted by #62 are back in the registry, and
    /// they are theorems, not `X == X`: the machine side never spells the spec
    /// predicate (`bvuge`/`bvult`), and the two sides are structurally different.
    #[test]
    fn uge_proofs_are_no_longer_degenerate() {
        for ob in [
            proof_icmp_uge_i32(),
            proof_icmp_uge_i64(),
            proof_condbr_uge_i32(),
            proof_condbr_uge_i64(),
        ] {
            let machine = format!("{:?}", ob.aarch64_expr);
            assert!(
                !machine.contains("BvUge") && !machine.contains("BvUlt"),
                "{}: machine side spells the spec predicate: {machine}",
                ob.name
            );
            assert_ne!(ob.trust_ir_expr, ob.aarch64_expr, "{}: X == X", ob.name);
            assert!(
                crate::proof_database::ProofDatabase::new()
                    .all()
                    .iter()
                    .any(|p| p.obligation.name == ob.name),
                "{} is not registered",
                ob.name
            );
        }
    }

    #[test]
    fn test_proof_icmp_ugt_i32() {
        assert_valid(&proof_icmp_ugt_i32());
    }

    #[test]
    fn test_proof_icmp_ule_i32() {
        assert_valid(&proof_icmp_ule_i32());
    }

    #[test]
    fn test_all_comparison_proofs_i32() {
        for obligation in all_comparison_proofs_i32() {
            assert_valid(&obligation);
        }
    }

    // -----------------------------------------------------------------------
    // 64-bit comparison proofs (all 10 conditions)
    // -----------------------------------------------------------------------

    #[test]
    fn test_proof_icmp_eq_i64() {
        assert_valid(&proof_icmp_eq_i64());
    }

    #[test]
    fn test_proof_icmp_ne_i64() {
        assert_valid(&proof_icmp_ne_i64());
    }

    #[test]
    fn test_proof_icmp_slt_i64() {
        assert_valid(&proof_icmp_slt_i64());
    }

    #[test]
    fn test_proof_icmp_sge_i64() {
        assert_valid(&proof_icmp_sge_i64());
    }

    #[test]
    fn test_proof_icmp_sgt_i64() {
        assert_valid(&proof_icmp_sgt_i64());
    }

    #[test]
    fn test_proof_icmp_sle_i64() {
        assert_valid(&proof_icmp_sle_i64());
    }

    #[test]
    fn test_proof_icmp_ult_i64() {
        assert_valid(&proof_icmp_ult_i64());
    }

    #[test]
    fn test_proof_icmp_uge_i64() {
        assert_valid(&proof_icmp_uge_i64());
    }

    #[test]
    fn test_proof_icmp_ugt_i64() {
        assert_valid(&proof_icmp_ugt_i64());
    }

    #[test]
    fn test_proof_icmp_ule_i64() {
        assert_valid(&proof_icmp_ule_i64());
    }

    #[test]
    fn test_all_comparison_proofs_i64() {
        for obligation in all_comparison_proofs_i64() {
            assert_valid(&obligation);
        }
    }

    // -----------------------------------------------------------------------
    // Branch lowering proof tests (32-bit, all 10 conditions)
    // -----------------------------------------------------------------------

    #[test]
    fn test_proof_condbr_eq_i32() {
        assert_valid(&proof_condbr_eq_i32());
    }

    #[test]
    fn test_proof_condbr_ne_i32() {
        assert_valid(&proof_condbr_ne_i32());
    }

    #[test]
    fn test_proof_condbr_slt_i32() {
        assert_valid(&proof_condbr_slt_i32());
    }

    #[test]
    fn test_proof_condbr_sge_i32() {
        assert_valid(&proof_condbr_sge_i32());
    }

    #[test]
    fn test_proof_condbr_sgt_i32() {
        assert_valid(&proof_condbr_sgt_i32());
    }

    #[test]
    fn test_proof_condbr_sle_i32() {
        assert_valid(&proof_condbr_sle_i32());
    }

    #[test]
    fn test_proof_condbr_ult_i32() {
        assert_valid(&proof_condbr_ult_i32());
    }

    #[test]
    fn test_proof_condbr_uge_i32() {
        assert_valid(&proof_condbr_uge_i32());
    }

    #[test]
    fn test_proof_condbr_ugt_i32() {
        assert_valid(&proof_condbr_ugt_i32());
    }

    #[test]
    fn test_proof_condbr_ule_i32() {
        assert_valid(&proof_condbr_ule_i32());
    }

    #[test]
    fn test_all_branch_proofs_i32() {
        for obligation in all_branch_proofs_i32() {
            assert_valid(&obligation);
        }
    }

    // -----------------------------------------------------------------------
    // Branch lowering proof tests (64-bit, all 10 conditions)
    // -----------------------------------------------------------------------

    #[test]
    fn test_proof_condbr_eq_i64() {
        assert_valid(&proof_condbr_eq_i64());
    }

    #[test]
    fn test_proof_condbr_ne_i64() {
        assert_valid(&proof_condbr_ne_i64());
    }

    #[test]
    fn test_proof_condbr_slt_i64() {
        assert_valid(&proof_condbr_slt_i64());
    }

    #[test]
    fn test_proof_condbr_sge_i64() {
        assert_valid(&proof_condbr_sge_i64());
    }

    #[test]
    fn test_proof_condbr_sgt_i64() {
        assert_valid(&proof_condbr_sgt_i64());
    }

    #[test]
    fn test_proof_condbr_sle_i64() {
        assert_valid(&proof_condbr_sle_i64());
    }

    #[test]
    fn test_proof_condbr_ult_i64() {
        assert_valid(&proof_condbr_ult_i64());
    }

    #[test]
    fn test_proof_condbr_uge_i64() {
        assert_valid(&proof_condbr_uge_i64());
    }

    #[test]
    fn test_proof_condbr_ugt_i64() {
        assert_valid(&proof_condbr_ugt_i64());
    }

    #[test]
    fn test_proof_condbr_ule_i64() {
        assert_valid(&proof_condbr_ule_i64());
    }

    #[test]
    fn test_all_branch_proofs_i64() {
        for obligation in all_branch_proofs_i64() {
            assert_valid(&obligation);
        }
    }

    #[test]
    fn test_all_branch_proofs() {
        for obligation in all_branch_proofs() {
            assert_valid(&obligation);
        }
    }

    #[test]
    fn test_all_nzcv_proofs() {
        for obligation in all_nzcv_proofs() {
            assert_valid(&obligation);
        }
    }

    // -----------------------------------------------------------------------
    // Negative test: verify wrong comparison mapping is detected
    // -----------------------------------------------------------------------

    #[test]
    fn test_wrong_comparison_detected() {
        // Map Eq to LT -- should find a counterexample
        use crate::nzcv::encode_cmp_cset;
        use crate::trust_ir_semantics::encode_trust_ir_icmp;
        use trust_cg_lower::instructions::IntCC;
        use trust_cg_lower::isel::AArch64CC;
        use trust_cg_lower::types::Type;

        let a = SmtExpr::var("a", 8);
        let b = SmtExpr::var("b", 8);

        let obligation = ProofObligation {
            machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
            name: "WRONG: Icmp_Eq -> CMP+CSET_LT".to_string(),
            trust_ir_expr: encode_trust_ir_icmp(&IntCC::Equal, Type::I8, a.clone(), b.clone()),
            aarch64_expr: encode_cmp_cset(a, b, 8, AArch64CC::LT),
            inputs: vec![("a".to_string(), 8), ("b".to_string(), 8)],
            preconditions: vec![],
            fp_inputs: vec![],
            category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
        };

        let result = verify_by_evaluation(&obligation);
        match result {
            VerificationResult::Invalid { .. } => {} // expected
            other => panic!(
                "Expected Invalid for wrong comparison mapping, got {:?}",
                other
            ),
        }
    }

    /// Test that exhaustive verification catches all 8-bit values.
    #[test]
    fn test_exhaustive_8bit_add() {
        let a = SmtExpr::var("a", 8);
        let b = SmtExpr::var("b", 8);

        let obligation = ProofObligation {
            machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
            name: "Iadd_I8 -> ADD (8-bit exhaustive)".to_string(),
            trust_ir_expr: a.clone().bvadd(b.clone()),
            aarch64_expr: a.bvadd(b),
            inputs: vec![("a".to_string(), 8), ("b".to_string(), 8)],
            preconditions: vec![],
            fp_inputs: vec![],
            category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
        };

        let result = verify_by_evaluation(&obligation);
        assert!(matches!(result, VerificationResult::Valid));
    }

    // -----------------------------------------------------------------------
    // VerificationConfig tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_default_config_values() {
        let config = VerificationConfig::default();
        assert_eq!(config.sample_count, DEFAULT_SAMPLE_COUNT);
        assert_eq!(config.sample_count, 100_000);
        assert_eq!(config.exhaustive_threshold, EXHAUSTIVE_WIDTH_THRESHOLD);
        assert_eq!(config.exhaustive_threshold, 8);
    }

    #[test]
    fn test_config_with_sample_count() {
        let config = VerificationConfig::with_sample_count(500_000);
        assert_eq!(config.sample_count, 500_000);
        assert_eq!(config.exhaustive_threshold, EXHAUSTIVE_WIDTH_THRESHOLD);
    }

    /// Test that a custom sample count is respected by verify_by_evaluation_with_config.
    ///
    /// We verify a correct 32-bit obligation with a very low sample count (10)
    /// and a high sample count (200_000). Both should pass for a correct rule.
    #[test]
    fn test_custom_sample_count_respected() {
        let obligation = proof_iadd_i32();

        // Low sample count -- still passes for a correct rule
        let config_low = VerificationConfig::with_sample_count(10);
        let result = verify_by_evaluation_with_config(&obligation, &config_low);
        assert!(
            matches!(result, VerificationResult::Valid),
            "Correct rule should pass even with low sample count"
        );

        // High sample count -- also passes
        let config_high = VerificationConfig::with_sample_count(200_000);
        let result = verify_by_evaluation_with_config(&obligation, &config_high);
        assert!(
            matches!(result, VerificationResult::Valid),
            "Correct rule should pass with high sample count"
        );
    }

    /// Test that a wrong rule is caught even with low sample count, because
    /// edge cases are always tested first.
    #[test]
    fn test_wrong_rule_caught_with_low_samples() {
        let a = SmtExpr::var("a", 32);
        let b = SmtExpr::var("b", 32);

        let obligation = ProofObligation {
            machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
            name: "WRONG: Iadd_I32 -> SUB".to_string(),
            trust_ir_expr: a.clone().bvadd(b.clone()),
            aarch64_expr: a.bvsub(b),
            inputs: vec![("a".to_string(), 32), ("b".to_string(), 32)],
            preconditions: vec![],
            fp_inputs: vec![],
            category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
        };

        // Even with 0 random samples, edge cases should catch add != sub
        let config = VerificationConfig::with_sample_count(0);
        let result = verify_by_evaluation_with_config(&obligation, &config);
        assert!(
            matches!(result, VerificationResult::Invalid { .. }),
            "Wrong rule should be caught by edge cases even with 0 random samples"
        );
    }

    /// Test that the exhaustive threshold is respected: a 16-bit obligation
    /// uses exhaustive verification when threshold is raised to 16.
    #[test]
    fn test_custom_exhaustive_threshold() {
        let a = SmtExpr::var("a", 16);

        // Single-input 16-bit obligation (65536 evaluations -- feasible)
        let obligation = ProofObligation {
            machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
            name: "Identity_I16".to_string(),
            trust_ir_expr: a.clone(),
            aarch64_expr: a,
            inputs: vec![("a".to_string(), 16)],
            preconditions: vec![],
            fp_inputs: vec![],
            category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
        };

        // One 16-bit input fits the default two-8-bit-input work budget.
        let config_default = VerificationConfig::default();
        assert_eq!(
            exhaustive_input_count(&obligation, &config_default),
            Some(65_536)
        );

        // With raised threshold, it should use exhaustive
        let config_16 = VerificationConfig {
            sample_count: 10,
            exhaustive_threshold: 16,
            ..VerificationConfig::default()
        };
        let result = verify_by_evaluation_with_config(&obligation, &config_16);
        assert!(matches!(result, VerificationResult::Valid));
    }

    // -----------------------------------------------------------------------
    // Floating-point lowering proof tests
    // -----------------------------------------------------------------------

    #[test]
    fn fp_static_evaluation_errors_refuse() {
        for original in [
            proof_fsqrt_f32(),
            proof_fsqrt_f64(),
            proof_fdiv_f32(),
            proof_fdiv_f64(),
        ] {
            for side in 0..3 {
                let mut obligation = original.clone();
                let missing = SmtExpr::var("unbound_fp_operand", 64);
                if side != 1 {
                    obligation.trust_ir_expr = missing.clone();
                }
                if side != 0 {
                    obligation.aarch64_expr = missing;
                }
                assert!(
                    matches!(
                        verify_fp_by_evaluation(&obligation),
                        VerificationResult::Unknown { .. }
                    ),
                    "{} side {side} accepted an evaluation error",
                    original.name
                );
            }
        }
    }

    #[test]
    fn fp_reconstructed_evaluation_errors_refuse() {
        for width in [32, 64] {
            for arity in 1..=3 {
                for side in 0..3 {
                    let mut obligation = if width == 32 {
                        proof_fsqrt_f32()
                    } else {
                        proof_fsqrt_f64()
                    };
                    let format = if width == 32 { (8, 24) } else { (11, 53) };
                    obligation.fp_inputs = (0..arity)
                        .map(|i| (format!("recon_{i}"), format.0, format.1))
                        .collect();
                    let bound = SmtExpr::var("recon_a", width).fp_neg();
                    let missing = SmtExpr::var("unbound_fp_operand", width).fp_neg();
                    obligation.trust_ir_expr = if side == 1 {
                        bound.clone()
                    } else {
                        missing.clone()
                    };
                    obligation.aarch64_expr = if side == 0 { bound } else { missing };
                    assert!(
                        matches!(
                            verify_fp_reconstructed_by_evaluation(&obligation),
                            VerificationResult::Unknown { .. }
                        ),
                        "width {width}, arity {arity}, side {side} accepted an evaluation error"
                    );
                }
            }
        }
    }

    /// Helper: verify a floating-point proof obligation and assert Valid.
    fn assert_fp_valid(obligation: &ProofObligation) {
        let result = verify_fp_by_evaluation(obligation);
        match &result {
            VerificationResult::Valid => {} // expected
            VerificationResult::Invalid { counterexample } => {
                panic!(
                    "FP Proof '{}' FAILED with counterexample: {}",
                    obligation.name, counterexample
                );
            }
            VerificationResult::Unknown { reason } => {
                panic!(
                    "FP Proof '{}' returned Unknown: {}",
                    obligation.name, reason
                );
            }
        }
    }

    #[test]
    fn test_proof_fadd_f32() {
        assert_fp_valid(&proof_fadd_f32());
    }

    #[test]
    fn test_proof_fadd_f64() {
        assert_fp_valid(&proof_fadd_f64());
    }

    #[test]
    fn test_proof_fsub_f32() {
        assert_fp_valid(&proof_fsub_f32());
    }

    #[test]
    fn test_proof_fsub_f64() {
        assert_fp_valid(&proof_fsub_f64());
    }

    #[test]
    fn test_proof_fmul_f32() {
        assert_fp_valid(&proof_fmul_f32());
    }

    #[test]
    fn test_proof_fmul_f64() {
        assert_fp_valid(&proof_fmul_f64());
    }

    #[test]
    fn test_proof_fneg_f32() {
        assert_fp_valid(&proof_fneg_f32());
    }

    #[test]
    fn test_proof_fneg_f64() {
        assert_fp_valid(&proof_fneg_f64());
    }

    #[test]
    fn test_proof_fdiv_f32() {
        assert_fp_valid(&proof_fdiv_f32());
    }

    #[test]
    fn test_proof_fdiv_f64() {
        assert_fp_valid(&proof_fdiv_f64());
    }

    // FABS: absolute value proofs
    #[test]
    fn test_proof_fabs_f32() {
        assert_fp_valid(&proof_fabs_f32());
    }

    #[test]
    fn test_proof_fabs_f64() {
        assert_fp_valid(&proof_fabs_f64());
    }

    // FRINTM/FRINTP/FRINTZ: round-to-integral floor/ceil/trunc proofs
    #[test]
    fn test_proof_ffloor_f32() {
        assert_fp_valid(&proof_ffloor_f32());
    }
    #[test]
    fn test_proof_ffloor_f64() {
        assert_fp_valid(&proof_ffloor_f64());
    }
    #[test]
    fn test_proof_fceil_f32() {
        assert_fp_valid(&proof_fceil_f32());
    }
    #[test]
    fn test_proof_fceil_f64() {
        assert_fp_valid(&proof_fceil_f64());
    }
    #[test]
    fn test_proof_ftrunc_f32() {
        assert_fp_valid(&proof_ftrunc_f32());
    }
    #[test]
    fn test_proof_ftrunc_f64() {
        assert_fp_valid(&proof_ftrunc_f64());
    }

    // FSQRT: square root proofs
    #[test]
    fn test_proof_fsqrt_f32() {
        assert_fp_valid(&proof_fsqrt_f32());
    }

    #[test]
    fn test_proof_fsqrt_f64() {
        assert_fp_valid(&proof_fsqrt_f64());
    }

    // FCMP ordered comparison proofs
    #[test]
    fn test_proof_fcmp_eq_f32() {
        assert_fp_valid(&proof_fcmp_eq_f32());
    }

    #[test]
    fn test_proof_fcmp_eq_f64() {
        assert_fp_valid(&proof_fcmp_eq_f64());
    }

    #[test]
    fn test_proof_fcmp_ne_f32() {
        assert_fp_valid(&proof_fcmp_ne_f32());
    }

    #[test]
    fn test_proof_fcmp_ne_f64() {
        assert_fp_valid(&proof_fcmp_ne_f64());
    }

    #[test]
    fn test_proof_fcmp_lt_f32() {
        assert_fp_valid(&proof_fcmp_lt_f32());
    }

    #[test]
    fn test_proof_fcmp_lt_f64() {
        assert_fp_valid(&proof_fcmp_lt_f64());
    }

    #[test]
    fn test_proof_fcmp_le_f32() {
        assert_fp_valid(&proof_fcmp_le_f32());
    }

    #[test]
    fn test_proof_fcmp_le_f64() {
        assert_fp_valid(&proof_fcmp_le_f64());
    }

    #[test]
    fn test_proof_fcmp_gt_f32() {
        assert_fp_valid(&proof_fcmp_gt_f32());
    }

    #[test]
    fn test_proof_fcmp_gt_f64() {
        assert_fp_valid(&proof_fcmp_gt_f64());
    }

    #[test]
    fn test_proof_fcmp_ge_f32() {
        assert_fp_valid(&proof_fcmp_ge_f32());
    }

    #[test]
    fn test_proof_fcmp_ge_f64() {
        assert_fp_valid(&proof_fcmp_ge_f64());
    }

    // FCMP ordering predicate proofs
    #[test]
    fn test_proof_fcmp_ord_f32() {
        assert_fp_valid(&proof_fcmp_ord_f32());
    }

    #[test]
    fn test_proof_fcmp_ord_f64() {
        assert_fp_valid(&proof_fcmp_ord_f64());
    }

    #[test]
    fn test_proof_fcmp_uno_f32() {
        assert_fp_valid(&proof_fcmp_uno_f32());
    }

    #[test]
    fn test_proof_fcmp_uno_f64() {
        assert_fp_valid(&proof_fcmp_uno_f64());
    }

    // FCMP unordered comparison proofs
    #[test]
    fn test_proof_fcmp_ueq_f32() {
        assert_fp_valid(&proof_fcmp_ueq_f32());
    }

    #[test]
    fn test_proof_fcmp_ueq_f64() {
        assert_fp_valid(&proof_fcmp_ueq_f64());
    }

    #[test]
    fn test_proof_fcmp_une_f32() {
        assert_fp_valid(&proof_fcmp_une_f32());
    }

    #[test]
    fn test_proof_fcmp_une_f64() {
        assert_fp_valid(&proof_fcmp_une_f64());
    }

    #[test]
    fn test_proof_fcmp_ult_f32() {
        assert_fp_valid(&proof_fcmp_ult_f32());
    }

    #[test]
    fn test_proof_fcmp_ult_f64() {
        assert_fp_valid(&proof_fcmp_ult_f64());
    }

    #[test]
    fn test_proof_fcmp_ule_f32() {
        assert_fp_valid(&proof_fcmp_ule_f32());
    }

    #[test]
    fn test_proof_fcmp_ule_f64() {
        assert_fp_valid(&proof_fcmp_ule_f64());
    }

    #[test]
    fn test_proof_fcmp_ugt_f32() {
        assert_fp_valid(&proof_fcmp_ugt_f32());
    }

    #[test]
    fn test_proof_fcmp_ugt_f64() {
        assert_fp_valid(&proof_fcmp_ugt_f64());
    }

    #[test]
    fn test_proof_fcmp_uge_f32() {
        assert_fp_valid(&proof_fcmp_uge_f32());
    }

    #[test]
    fn test_proof_fcmp_uge_f64() {
        assert_fp_valid(&proof_fcmp_uge_f64());
    }

    /// Verify the FP proof count matches expectations.
    #[test]
    fn test_fp_lowering_proof_count() {
        let proofs = all_fp_lowering_proofs();
        // 8 original (fadd/fsub/fmul/fneg x f32/f64) + 2 fdiv + 4 fabs/fsqrt
        // + 6 frint (ffloor/fceil/ftrunc x f32/f64) + 28 fcmp = 48
        assert_eq!(proofs.len(), 48, "Expected 48 FP lowering proofs");
    }

    #[test]
    fn test_all_fp_lowering_proofs() {
        for obligation in all_fp_lowering_proofs() {
            assert_fp_valid(&obligation);
        }
    }

    /// Verify that FP proof obligations produce valid SMT-LIB2 output.
    #[test]
    fn test_fp_proof_smt2_output() {
        let obligation = proof_fadd_f64();
        let smt2 = obligation.to_smt2();
        // Raw symbolic operands occur in the actual formula, not just declarations.
        assert!(smt2.contains("(declare-const fp_a_bits (_ BitVec 64))"));
        assert!(smt2.contains("(declare-const fp_b_bits (_ BitVec 64))"));
        assert!(smt2.contains("((_ to_fp 11 53) fp_a_bits)"));
        assert!(smt2.contains("((_ to_fp 11 53) fp_b_bits)"));
        assert!(smt2.contains("(check-sat)"));
    }

    /// Negative test: verify that wrong FP lowering is detected.
    #[test]
    fn test_wrong_fp_rule_detected() {
        // Claim FADD = FMUL -- should find a counterexample.
        use crate::smt::RoundingMode;

        let a = SmtExpr::fp64_const(0.0);
        let b = SmtExpr::fp64_const(0.0);

        let obligation = ProofObligation {
            machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
            name: "WRONG: Fadd -> FMUL".to_string(),
            trust_ir_expr: SmtExpr::fp_add(RoundingMode::RNE, a.clone(), b.clone()),
            aarch64_expr: SmtExpr::fp_mul(RoundingMode::RNE, a, b),
            inputs: vec![],
            preconditions: vec![],
            fp_inputs: vec![("a".to_string(), 11, 53), ("b".to_string(), 11, 53)],
            category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
        };

        let result = verify_fp_by_evaluation(&obligation);
        match result {
            VerificationResult::Invalid { .. } => {} // expected
            other => panic!("Expected Invalid for wrong FP rule, got {:?}", other),
        }
    }

    /// Test that verify_by_evaluation uses the default sample count.
    #[test]
    fn test_verify_by_evaluation_uses_defaults() {
        // This is a sanity check -- verify_by_evaluation should produce the
        // same result as verify_by_evaluation_with_config with default config.
        let obligation = proof_iadd_i64();
        let result_default = verify_by_evaluation(&obligation);
        let result_config =
            verify_by_evaluation_with_config(&obligation, &VerificationConfig::default());

        // Both should be Valid for a correct rule
        assert!(matches!(result_default, VerificationResult::Valid));
        assert!(matches!(result_config, VerificationResult::Valid));
    }

    // -----------------------------------------------------------------------
    // Load/Store lowering proofs
    // -----------------------------------------------------------------------

    #[test]
    fn test_proof_load_i32_lowering() {
        assert_valid(&proof_load_i32_lowering());
    }

    #[test]
    fn test_proof_load_i64_lowering() {
        assert_valid(&proof_load_i64_lowering());
    }

    #[test]
    fn test_proof_store_i32_lowering() {
        assert_valid(&proof_store_i32_lowering());
    }

    #[test]
    fn test_proof_store_i64_lowering() {
        assert_valid(&proof_store_i64_lowering());
    }

    #[test]
    fn test_proof_load_i8_lowering() {
        assert_valid(&proof_load_i8_lowering());
    }

    #[test]
    fn test_proof_load_i16_lowering() {
        assert_valid(&proof_load_i16_lowering());
    }

    #[test]
    fn test_proof_store_i8_lowering() {
        assert_valid(&proof_store_i8_lowering());
    }

    #[test]
    fn test_proof_store_i16_lowering() {
        assert_valid(&proof_store_i16_lowering());
    }

    #[test]
    fn test_proof_load_store_roundtrip_i32() {
        assert_valid(&proof_load_store_roundtrip_i32());
    }

    #[test]
    fn test_proof_load_store_roundtrip_i64() {
        assert_valid(&proof_load_store_roundtrip_i64());
    }

    #[test]
    fn test_all_load_store_proofs() {
        // #62 retraction: the 8 degenerate "Load_I*/Store_I* -> LDR/STR*ui [Xn,#0]"
        // X==X self-equalities were removed; only the GENUINE store-then-load
        // roundtrip proofs remain (real coverage via the array memory model).
        let names: Vec<_> = all_load_store_proofs()
            .into_iter()
            .map(|obligation| obligation.name)
            .collect();
        assert_eq!(
            names,
            vec![
                "Roundtrip_I32: store then load",
                "Roundtrip_I64: store then load",
            ]
        );
    }

    /// Verify that load/store proofs use the array-based memory model.
    #[test]
    fn test_load_store_proof_count() {
        let proofs = all_load_store_proofs();
        assert_eq!(
            proofs.len(),
            2,
            "Expected 2 genuine load/store roundtrip proofs (8 degenerate \
             Load_I*/Store_I* X==X retracted in #62)"
        );
    }

    /// Verify that load/store proof obligations produce valid SMT-LIB2 output.
    #[test]
    fn test_load_store_smt2_output() {
        let obligation = proof_load_i32_lowering();
        let smt2 = obligation.to_smt2();
        assert!(smt2.contains("(set-logic"), "SMT2 should have set-logic");
        assert!(
            smt2.contains("(declare-const base (_ BitVec 64))"),
            "SMT2 should declare base address"
        );
        assert!(smt2.contains("(check-sat)"), "SMT2 should have check-sat");
    }

    /// Verify that store proof obligations include value declarations.
    #[test]
    fn test_store_proof_has_value_input() {
        let obligation = proof_store_i32_lowering();
        assert!(
            obligation.inputs.iter().any(|(name, _)| name == "value"),
            "Store proof should have 'value' input"
        );
        assert!(
            obligation.inputs.iter().any(|(name, _)| name == "base"),
            "Store proof should have 'base' input"
        );
    }

    // -----------------------------------------------------------------------
    // I8 bitwise/shift proofs (exhaustive -- all 2^16 or 2^8 combos)
    // -----------------------------------------------------------------------

    #[test]
    fn test_proof_band_i8() {
        assert_valid(&proof_band_i8());
    }

    #[test]
    fn test_proof_bor_i8() {
        assert_valid(&proof_bor_i8());
    }

    #[test]
    fn test_proof_bxor_i8() {
        assert_valid(&proof_bxor_i8());
    }

    #[test]
    fn test_proof_bnot_i8() {
        assert_valid(&proof_bnot_i8());
    }

    #[test]
    fn test_proof_ishl_i8() {
        assert_valid(&proof_ishl_i8());
    }

    #[test]
    fn test_proof_ushr_i8() {
        assert_valid(&proof_ushr_i8());
    }

    #[test]
    fn test_proof_sshr_i8() {
        assert_valid(&proof_sshr_i8());
    }

    // -----------------------------------------------------------------------
    // I16 bitwise/shift proofs (statistical -- edge cases + random sampling)
    // -----------------------------------------------------------------------

    #[test]
    fn test_proof_band_i16() {
        assert_valid(&proof_band_i16());
    }

    #[test]
    fn test_proof_bor_i16() {
        assert_valid(&proof_bor_i16());
    }

    #[test]
    fn test_proof_bxor_i16() {
        assert_valid(&proof_bxor_i16());
    }

    #[test]
    fn test_proof_bnot_i16() {
        assert_valid(&proof_bnot_i16());
    }

    #[test]
    fn test_proof_ishl_i16() {
        assert_valid(&proof_ishl_i16());
    }

    #[test]
    fn test_proof_ushr_i16() {
        assert_valid(&proof_ushr_i16());
    }

    #[test]
    fn test_proof_sshr_i16() {
        assert_valid(&proof_sshr_i16());
    }

    // -----------------------------------------------------------------------
    // Aggregate bitwise/shift proof test
    // -----------------------------------------------------------------------

    #[test]
    fn test_all_bitwise_shift_proofs() {
        for obligation in all_bitwise_shift_proofs() {
            assert_valid(&obligation);
        }
    }

    /// Verify that the bitwise/shift collection has the expected count.
    ///
    /// Breakdown (34 = 18 base + 16 I32/I64 widening for issue #449):
    ///   - I8 : band, bor, bxor, bnot, ishl, ushr, sshr, bic, orn  (9)
    ///   - I16: band, bor, bxor, bnot, ishl, ushr, sshr, bic, orn  (9)
    ///   - I32: band, bor, bxor,       ishl, ushr, sshr, bic, orn  (8)
    ///   - I64: band, bor, bxor,       ishl, ushr, sshr, bic, orn  (8)
    ///
    /// (bnot not yet added at I32/I64; filed if/when that becomes a gap.)
    #[test]
    fn test_bitwise_shift_proof_count() {
        let proofs = all_bitwise_shift_proofs();
        assert_eq!(
            proofs.len(),
            72,
            "Expected 72 bitwise proofs (22 base + the 10 EOR-ROR shifted-register \
             obligations + the 10 standalone ROR-immediate obligations + the 20 \
             ADD/SUB-LSL shifted-register obligations, 10 ADD + 10 SUB, + the 10 \
             ADD-LSR shifted-register obligations; 22 = 34 minus the 12 degenerate \
             scalar shift Ishl/Ushr/Sshr X==X retracted in #62), got {}",
            proofs.len()
        );
    }

    /// The FAITHFUL ADD/SUB-LSL obligations: all genuine (structurally distinct,
    /// NOT X==X) and all discharge Valid under the in-house evaluator.
    #[test]
    fn test_add_sub_lsl_shift_proofs_valid_and_genuine() {
        let proofs = all_add_sub_lsl_shift_proofs();
        assert_eq!(
            proofs.len(),
            20,
            "10 ADD + 10 SUB (5 amounts x {{W,X}} each)"
        );
        for obligation in &proofs {
            assert!(
                obligation.is_genuinely_proven(),
                "ADD/SUB-LSL proof '{}' is DEGENERATE (X==X)",
                obligation.name
            );
            assert_valid(obligation);
        }
    }

    /// NON-VACUITY: every wrong-encoding control (wrong-amount, wrong-op
    /// ADD-vs-SUB, SUB operand-swap) must REFUTE under the in-house evaluator.
    #[test]
    fn test_add_sub_lsl_shift_controls_refute() {
        let controls = add_sub_lsl_shift_wrong_controls();
        assert_eq!(controls.len(), 8, "4 controls x {{W,X}}");
        for obligation in &controls {
            assert!(
                obligation.is_genuinely_proven(),
                "ADD/SUB-LSL control '{}' is degenerate",
                obligation.name
            );
            let result = verify_by_evaluation(obligation);
            assert!(
                !matches!(result, VerificationResult::Valid),
                "ADD/SUB-LSL NEGATIVE control '{}' was VALID — a wrong shifted-register \
                 ADD/SUB encoding must refute, so the positive obligation is vacuous",
                obligation.name
            );
        }
    }

    /// The FAITHFUL ADD-LSR obligations: all genuine (structurally distinct,
    /// NOT X==X — bvudiv source vs bvlshr machine) and all discharge Valid under
    /// the in-house evaluator.
    #[test]
    fn test_add_lsr_shift_proofs_valid_and_genuine() {
        let proofs = all_add_lsr_shift_proofs();
        assert_eq!(proofs.len(), 10, "5 amounts x {{W,X}}");
        for obligation in &proofs {
            assert!(
                obligation.is_genuinely_proven(),
                "ADD-LSR proof '{}' is DEGENERATE (X==X)",
                obligation.name
            );
            assert_valid(obligation);
        }
    }

    /// NON-VACUITY: every wrong-encoding control (wrong-amount, ASR-not-LSR,
    /// LSL-not-LSR, SUB-not-ADD) must REFUTE under the in-house evaluator.
    #[test]
    fn test_add_lsr_shift_controls_refute() {
        let controls = add_lsr_shift_wrong_controls();
        assert_eq!(controls.len(), 8, "4 controls x {{W,X}}");
        for obligation in &controls {
            assert!(
                obligation.is_genuinely_proven(),
                "ADD-LSR control '{}' is degenerate",
                obligation.name
            );
            let result = verify_by_evaluation(obligation);
            assert!(
                !matches!(result, VerificationResult::Valid),
                "ADD-LSR NEGATIVE control '{}' was VALID — a wrong shifted-register \
                 ADD encoding must refute, so the positive obligation is vacuous",
                obligation.name
            );
        }
    }

    /// The FAITHFUL EOR-ROR obligations: all genuine (structurally distinct,
    /// NOT X==X) and all discharge Valid under the in-house evaluator.
    #[test]
    fn test_eor_ror_shift_proofs_valid_and_genuine() {
        let proofs = all_eor_ror_shift_proofs();
        assert_eq!(proofs.len(), 10, "5 amounts x {{W,X}}");
        for obligation in &proofs {
            assert!(
                obligation.is_genuinely_proven(),
                "EOR-ROR proof '{}' is DEGENERATE (X==X)",
                obligation.name
            );
            assert_valid(obligation);
        }
    }

    /// NON-VACUITY: every wrong-encoding control (wrong-amount, wrong-shift-kind
    /// ROR-vs-LSR, operand-swap) must REFUTE under the in-house evaluator.
    #[test]
    fn test_eor_ror_shift_controls_refute() {
        let controls = eor_ror_shift_wrong_controls();
        assert_eq!(controls.len(), 6, "3 controls x {{W,X}}");
        for obligation in &controls {
            assert!(
                obligation.is_genuinely_proven(),
                "EOR-ROR control '{}' is degenerate",
                obligation.name
            );
            let result = verify_by_evaluation(obligation);
            assert!(
                !matches!(result, VerificationResult::Valid),
                "EOR-ROR NEGATIVE control '{}' was VALID — a wrong shifted-register EOR \
                 encoding must refute, so the positive obligation is vacuous",
                obligation.name
            );
        }
    }

    /// The FAITHFUL standalone ROR-immediate obligations: all genuine
    /// (structurally distinct, NOT X==X) and all discharge Valid under the
    /// in-house evaluator.
    #[test]
    fn test_ror_immediate_proofs_valid_and_genuine() {
        let proofs = all_ror_immediate_proofs();
        assert_eq!(proofs.len(), 10, "5 amounts x {{W,X}}");
        for obligation in &proofs {
            assert!(
                obligation.is_genuinely_proven(),
                "ROR-immediate proof '{}' is DEGENERATE (X==X)",
                obligation.name
            );
            assert_valid(obligation);
        }
    }

    /// NON-VACUITY: every wrong-encoding control (wrong-amount, wrong-kind
    /// ROR-vs-LSR, wrong-direction ROR-vs-ROL) must REFUTE under the in-house
    /// evaluator.
    #[test]
    fn test_ror_immediate_controls_refute() {
        let controls = ror_immediate_wrong_controls();
        assert_eq!(controls.len(), 6, "3 controls x {{W,X}}");
        for obligation in &controls {
            assert!(
                obligation.is_genuinely_proven(),
                "ROR-immediate control '{}' is degenerate",
                obligation.name
            );
            let result = verify_by_evaluation(obligation);
            assert!(
                !matches!(result, VerificationResult::Valid),
                "ROR-immediate NEGATIVE control '{}' was VALID — a wrong rotate \
                 encoding must refute, so the positive obligation is vacuous",
                obligation.name
            );
        }
    }

    /// The FAITHFUL FCSEL obligations: all genuine (structurally distinct, NOT
    /// X==X) and all discharge Valid under the in-house evaluator.
    #[test]
    fn test_fcsel_proofs_valid_and_genuine() {
        let proofs = all_fcsel_proofs();
        assert_eq!(proofs.len(), 12, "6 conditions x {{S,D}}");
        for obligation in &proofs {
            assert!(
                obligation.is_genuinely_proven(),
                "FCSEL proof '{}' is DEGENERATE (X==X)",
                obligation.name
            );
            assert_valid(obligation);
        }
    }

    /// NON-VACUITY: every wrong-encoding control (inverted-cond, operand-swap)
    /// must REFUTE under the in-house evaluator.
    #[test]
    fn test_fcsel_controls_refute() {
        let controls = fcsel_wrong_controls();
        assert_eq!(controls.len(), 8, "2 control types x 2 conds x {{S,D}}");
        for obligation in &controls {
            assert!(
                obligation.is_genuinely_proven(),
                "FCSEL control '{}' is degenerate",
                obligation.name
            );
            let result = verify_by_evaluation(obligation);
            assert!(
                !matches!(result, VerificationResult::Valid),
                "FCSEL NEGATIVE control '{}' was VALID — a wrong FCSEL encoding must \
                 refute, so the positive obligation is vacuous",
                obligation.name
            );
        }
    }

    #[test]
    fn test_proof_bic_i8() {
        assert_valid(&proof_bic_i8());
    }

    #[test]
    fn test_proof_orn_i8() {
        assert_valid(&proof_orn_i8());
    }

    #[test]
    fn test_proof_bic_i16() {
        assert_valid(&proof_bic_i16());
    }

    #[test]
    fn test_proof_orn_i16() {
        assert_valid(&proof_orn_i16());
    }

    /// Negative test: load at different offsets should not be equivalent.
    #[test]
    fn test_wrong_load_offset_lowering_detected() {
        use crate::memory_proofs::{
            encode_aarch64_ldr_imm, encode_store_le, encode_trust_ir_load, symbolic_memory,
        };

        let mem = symbolic_memory("mem_default");
        let base = SmtExpr::var("base", 64);
        let value = SmtExpr::var("value", 32);

        // Store a value at base
        let mem_with_data = encode_store_le(&mem, &base, &value, 4);

        // trust_ir: load at byte offset 0
        let trust_ir_at_0 = encode_trust_ir_load(&mem_with_data, &base, 0, 4);
        // AArch64: load at scaled offset 1 (byte offset 4) -- WRONG
        let aarch64_at_1 = encode_aarch64_ldr_imm(&mem_with_data, &base, 1, 4);

        let obligation = ProofObligation {
            machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
            name: "WRONG: Load I32 offset 0 == Load I32 offset 4".to_string(),
            trust_ir_expr: trust_ir_at_0,
            aarch64_expr: aarch64_at_1,
            inputs: vec![
                ("base".to_string(), 64),
                ("value".to_string(), 32),
                ("mem_default".to_string(), 8),
            ],
            preconditions: vec![],
            fp_inputs: vec![],
            category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
        };

        let result = verify_by_evaluation(&obligation);
        match result {
            VerificationResult::Invalid { .. } => {} // expected
            other => panic!("Expected Invalid for wrong load offset, got {:?}", other),
        }
    }
}

#[cfg(test)]
mod chunked_sampling_tests {
    use super::*;

    /// `sample_lcg_jump(seed, n)` is exactly `n` sequential steps, across the
    /// chunk starts the splitter actually produces (and a few awkward ones).
    #[test]
    fn lcg_jump_matches_sequential_stepping() {
        let seeds = [
            0u64,
            1,
            0xcafe_babe_dead_beef,
            u64::MAX,
            0x9E37_79B9_7F4A_7C15,
        ];
        let ns = [
            0u64, 1, 2, 3, 7, 8, 100, 4095, 4096, 4097, 8192, 12_500, 25_000, 99_999, 100_000,
            200_000, 300_003, 1_000_003,
        ];
        for &seed in &seeds {
            let mut state = seed;
            let mut stepped = 0u64;
            for &n in &ns {
                while stepped < n {
                    state = sample_lcg_step(state);
                    stepped += 1;
                }
                assert_eq!(sample_lcg_jump(seed, n), state, "seed={seed:#x} n={n}");
            }
        }
    }

    /// Outside any pool, or on a single-worker pool, nothing is chunked. Inside
    /// a pool the chunks tile `[0, trials)` exactly once, in order.
    #[test]
    fn chunking_only_inside_a_pool_and_tiles_exactly() {
        // The helper-pool test registers a process-wide pool; hold its lock so
        // "no pool" here really means no pool.
        let _guard = HELPER_POOL_TEST_LOCK
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        assert_eq!(sample_chunking(100_000), (1, 100_000));
        assert_eq!(sample_chunking(8_191), (1, 8_191));
        let pool = rayon::ThreadPoolBuilder::new()
            .num_threads(4)
            .build()
            .unwrap();
        pool.install(|| {
            for trials in [8_192u64, 100_000, 100_001, 123_457] {
                let (chunks, per) = sample_chunking(trials);
                assert!((2..=8).contains(&chunks), "trials={trials} chunks={chunks}");
                let mut covered = 0u64;
                for i in 0..chunks {
                    let start = i * per;
                    let count = trials.saturating_sub(start).min(per);
                    assert_eq!(
                        start,
                        covered,
                        "chunk {i} does not start where {} ended",
                        i.wrapping_sub(1)
                    );
                    covered += count;
                }
                assert_eq!(covered, trials);
            }
            assert_eq!(
                sample_chunking(8_191),
                (1, 8_191),
                "too little work must stay whole"
            );
        });
        let one = rayon::ThreadPoolBuilder::new()
            .num_threads(1)
            .build()
            .unwrap();
        one.install(|| assert_eq!(sample_chunking(100_000), (1, 100_000)));
    }

    fn v(name: &str) -> Arc<SmtExpr> {
        Arc::new(SmtExpr::Var {
            name: name.to_string(),
            width: 64,
        })
    }
    fn k(value: u64) -> Arc<SmtExpr> {
        Arc::new(SmtExpr::BvConst { value, width: 64 })
    }
    /// `a`, except at each `hit` value where it is `a + 1`: wrong at exactly
    /// those inputs and nowhere else.
    fn wrong_at(hits: &[u64]) -> SmtExpr {
        let mut expr = SmtExpr::Var {
            name: "a".to_string(),
            width: 64,
        };
        for &h in hits.iter().rev() {
            expr = SmtExpr::Ite {
                cond: Arc::new(SmtExpr::Eq {
                    lhs: v("a"),
                    rhs: k(h),
                }),
                then_expr: Arc::new(SmtExpr::BvAdd {
                    lhs: v("a"),
                    rhs: k(1),
                    width: 64,
                }),
                else_expr: Arc::new(expr),
            };
        }
        expr
    }
    fn obligation(name: &str, inputs: &[&str], hits: &[u64]) -> ProofObligation {
        ProofObligation {
            machine_side_provenance: MachineSideProvenance::StaticDb,
            name: name.to_string(),
            trust_ir_expr: SmtExpr::Var {
                name: "a".to_string(),
                width: 64,
            },
            aarch64_expr: wrong_at(hits),
            inputs: inputs.iter().map(|n| (n.to_string(), 64)).collect(),
            preconditions: vec![],
            fp_inputs: vec![],
            category: None,
        }
    }
    /// Mixed-width sampling must not shift its u64 carrier by an i128 width.
    /// It still finds an actual wrong result; a successful sample is not a proof.
    #[test]
    fn wide_multi_input_sampling_preserves_refutation_without_shift_overflow() {
        let mut ob = obligation("wide_multi_input", &["a", "b", "flag"], &[]);
        ob.inputs = vec![("a".into(), 128), ("b".into(), 128), ("flag".into(), 1)];
        ob.trust_ir_expr = SmtExpr::var("a", 128);
        ob.aarch64_expr = SmtExpr::var("a", 128).bvadd(SmtExpr::bv_const(1, 128));
        let cfg = VerificationConfig {
            sample_count: 16,
            ..VerificationConfig::default()
        };
        assert!(matches!(
            verify_by_evaluation_with_config(&ob, &cfg),
            VerificationResult::Invalid { .. }
        ));
        for edge_idx in 0..MULTI_INPUT_EDGE_COMBOS as usize {
            let mut env = multi_input_sweep_env(&ob);
            fill_env_edge(&mut env, &ob.inputs, edge_idx);
            assert!(*env.get("flag").unwrap() <= 1);
        }
    }

    /// The value of input `a` (the first draw) at sample index `k` of an
    /// obligation with `draws` inputs — what the sequential loop draws there.
    fn a_at(name: &str, draws: u64, k: u64) -> u64 {
        let value = mask(sample_lcg_jump(sample_seed(name), draws * k + 1), 64);
        let edges = [0, 1, u64::MAX, u64::MAX - 1, 1u64 << 63, (1u64 << 63) - 1];
        assert!(
            !edges.contains(&value),
            "sample {k} of `{name}` collides with an edge case"
        );
        value
    }
    fn sequential(ob: &ProofObligation) -> String {
        assert!(rayon::current_thread_index().is_none());
        format!(
            "{:?}",
            verify_by_evaluation_with_config(ob, &VerificationConfig::default())
        )
    }
    fn chunked(ob: &ProofObligation) -> String {
        let pool = rayon::ThreadPoolBuilder::new()
            .num_threads(4)
            .build()
            .unwrap();
        pool.install(|| {
            assert_eq!(sample_chunking(DEFAULT_SAMPLE_COUNT).0, 8);
            format!(
                "{:?}",
                verify_by_evaluation_with_config(ob, &VerificationConfig::default())
            )
        })
    }

    /// 2-input path: the only wrong input is sample 77,777 — deep inside chunk
    /// 6 of 8. The chunked sweep must find it, and report the very same
    /// counterexample text as the sequential sweep.
    #[test]
    fn two_input_counterexample_in_a_late_chunk_is_identical() {
        let name = "chunk-test: hit deep in chunk 6";
        let ob = obligation(name, &["a", "b"], &[a_at(name, 2, 77_777)]);
        let s = sequential(&ob);
        assert!(s.starts_with("Invalid"), "{s}");
        assert_eq!(chunked(&ob), s);
    }

    /// Multi-input path (3 draws per sample): same shape, hit at sample 91,234
    /// in the last chunk. Exercises the `draws × k` jump arithmetic.
    #[test]
    fn multi_input_counterexample_in_the_last_chunk_is_identical() {
        let name = "chunk-test: multi-input hit in chunk 7";
        let ob = obligation(name, &["a", "b", "c"], &[a_at(name, 3, 91_234)]);
        let s = sequential(&ob);
        assert!(s.starts_with("Invalid"), "{s}");
        assert_eq!(chunked(&ob), s);
    }

    /// Two wrong inputs, in chunks 2 and 7. Whichever chunk finishes first, the
    /// reported counterexample is the EARLIER sample — the sequential answer.
    #[test]
    fn earliest_counterexample_wins_regardless_of_chunk_finish_order() {
        let name = "chunk-test: hits in chunks 2 and 7";
        let first = a_at(name, 2, 30_001);
        let second = a_at(name, 2, 90_005);
        let both = obligation(name, &["a", "b"], &[first, second]);
        let only_first = obligation(name, &["a", "b"], &[first]);
        let only_second = obligation(name, &["a", "b"], &[second]);
        let s = sequential(&both);
        assert_eq!(
            s,
            sequential(&only_first),
            "sequential reports the earlier hit"
        );
        assert_ne!(s, sequential(&only_second));
        for _ in 0..8 {
            assert_eq!(chunked(&both), s);
        }
    }

    /// A repeated input NAME: the env has one slot per name and the LAST draw
    /// wins (`[a, a]` → `a` holds each sample's second draw; `[a, b, a]` → the
    /// third). The batched lanes must sweep exactly that, and did not (they
    /// were per input index) — found by adversarial review.
    #[test]
    fn repeated_input_names_sweep_the_env_the_scalar_loop_fills() {
        let scalar = |ob: &ProofObligation| {
            let co = CompiledObligation::try_new_scalar_only(ob);
            format!(
                "{:?}",
                verify_by_evaluation_with_compiled(ob, &VerificationConfig::default(), co.as_ref())
            )
        };
        let name = "chunk-test: repeated name a,a";
        let hit = mask(sample_lcg_jump(sample_seed(name), 2 * 4_321 + 2), 64);
        let ob = obligation(name, &["a", "a"], &[hit]);
        let s = scalar(&ob);
        assert!(s.starts_with("Invalid"), "{s}");
        assert_eq!(chunked(&ob), s);

        let name = "chunk-test: repeated name a,b,a";
        let hit = mask(sample_lcg_jump(sample_seed(name), 3 * 9_876 + 3), 64);
        let ob = obligation(name, &["a", "b", "a"], &[hit]);
        let s = scalar(&ob);
        assert!(s.starts_with("Invalid"), "{s}");
        assert_eq!(chunked(&ob), s);
    }

    fn valid_but_not_identical(name: &str) -> ProofObligation {
        // `a` vs `a + 0`: Valid, but not identical-sided, so the
        // trust_ir == aarch64 short-circuit does not fire and the sweep runs.
        let mut ob = obligation(name, &["a", "b"], &[]);
        ob.aarch64_expr = SmtExpr::BvAdd {
            lhs: v("a"),
            rhs: k(0),
            width: 64,
        };
        assert!(CompiledObligation::try_new(&ob).is_some());
        ob
    }

    /// Two callers of ONE uncached kind on a 2-worker pool, the second while
    /// the first is mid-sweep: the second blocks on the memo cell; the first
    /// must finish without ever executing the second's job. The `collect()`
    /// fan-out hung here 3/3 (gdb: the sweeping worker re-entered its own
    /// cell) — found by adversarial review.
    #[test]
    fn same_key_second_caller_does_not_deadlock_the_chunked_sweep() {
        for iter in 0..3 {
            let ob = Arc::new(valid_but_not_identical(&format!(
                "chunk-test: deadlock {} {iter}",
                std::process::id()
            )));
            let pool = Arc::new(
                rayon::ThreadPoolBuilder::new()
                    .num_threads(2)
                    .build()
                    .unwrap(),
            );
            let (tx, rx) = std::sync::mpsc::channel::<()>();
            for i in 0..2 {
                let (ob, pool, tx) = (Arc::clone(&ob), Arc::clone(&pool), tx.clone());
                std::thread::spawn(move || {
                    let cfg = VerificationConfig::with_sample_count(1_000_000);
                    let r = pool.install(|| memoized_verify_by_evaluation(&ob, &cfg));
                    assert_eq!(format!("{r:?}"), "Valid");
                    let _ = tx.send(());
                });
                if i == 0 {
                    std::thread::sleep(std::time::Duration::from_millis(40));
                }
            }
            for _ in 0..2 {
                rx.recv_timeout(std::time::Duration::from_secs(60))
                    .unwrap_or_else(|_| panic!("iteration {iter}: the chunked sweep deadlocked"));
            }
        }
    }

    /// The production shape as first shipped (a plain `par_iter` of discharges;
    /// production now bounds the owners, which only makes this easier): the
    /// init-time speculative sweep and the first CGU's pre-warm are two
    /// installs on ONE pool with overlapping kinds.
    #[test]
    fn overlapping_prewarm_installs_on_one_pool_do_not_deadlock() {
        use rayon::prelude::*;
        for iter in 0..4 {
            let kinds: Arc<Vec<ProofObligation>> = Arc::new(
                (0..13)
                    .map(|j| {
                        valid_but_not_identical(&format!(
                            "chunk-test: prewarm {} {iter} {j}",
                            std::process::id()
                        ))
                    })
                    .collect(),
            );
            let pool = Arc::new(
                rayon::ThreadPoolBuilder::new()
                    .num_threads(8)
                    .build()
                    .unwrap(),
            );
            let (tx, rx) = std::sync::mpsc::channel::<()>();
            for i in 0..2 {
                let (kinds, pool, tx) = (Arc::clone(&kinds), Arc::clone(&pool), tx.clone());
                std::thread::spawn(move || {
                    let cfg = VerificationConfig::with_sample_count(400_000);
                    pool.install(|| {
                        kinds.par_iter().for_each(|ob| {
                            assert_eq!(
                                format!("{:?}", memoized_verify_by_evaluation(ob, &cfg)),
                                "Valid"
                            );
                        })
                    });
                    let _ = tx.send(());
                });
                if i == 0 {
                    std::thread::sleep(std::time::Duration::from_millis(15));
                }
            }
            for _ in 0..2 {
                rx.recv_timeout(std::time::Duration::from_secs(60))
                    .unwrap_or_else(|_| {
                        panic!("iteration {iter}: overlapping pre-warms deadlocked")
                    });
            }
        }
    }

    /// With a helper pool registered, a sweep owned by a PLAIN thread (the
    /// certificate walk's shape: the verifier pool has one worker) is chunked
    /// onto that pool and stays verdict- and text-identical; and the two
    /// deadlock shapes hold with owners on one-worker pools and helpers on
    /// the registered pool.
    #[test]
    fn registered_helper_pool_serves_sweeps_from_any_thread() {
        let _guard = HELPER_POOL_TEST_LOCK
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        let helpers = Arc::new(
            rayon::ThreadPoolBuilder::new()
                .num_threads(4)
                .build()
                .unwrap(),
        );
        set_sweep_helper_pool(Some(Arc::clone(&helpers)));
        // Chunked from a plain thread now.
        assert_eq!(sample_chunking(DEFAULT_SAMPLE_COUNT).0, 8);
        let name = "chunk-test: helper pool, plain owner";
        let ob = obligation(name, &["a", "b"], &[a_at(name, 2, 77_777)]);
        let s = format!(
            "{:?}",
            verify_by_evaluation_with_config(&ob, &VerificationConfig::default())
        );
        set_sweep_helper_pool(None);
        assert!(s.starts_with("Invalid"), "{s}");
        assert_eq!(sequential(&ob), s);
        // Owners on a ONE-worker pool (the walk), helpers on the registered pool,
        // two callers of one uncached kind.
        set_sweep_helper_pool(Some(Arc::clone(&helpers)));
        for iter in 0..3 {
            let ob = Arc::new(valid_but_not_identical(&format!(
                "chunk-test: helper-pool deadlock {} {iter}",
                std::process::id()
            )));
            let walk = Arc::new(
                rayon::ThreadPoolBuilder::new()
                    .num_threads(1)
                    .build()
                    .unwrap(),
            );
            let (tx, rx) = std::sync::mpsc::channel::<()>();
            for i in 0..2 {
                let (ob, walk, tx) = (Arc::clone(&ob), Arc::clone(&walk), tx.clone());
                std::thread::spawn(move || {
                    let cfg = VerificationConfig::with_sample_count(1_000_000);
                    let r = walk.install(|| memoized_verify_by_evaluation(&ob, &cfg));
                    assert_eq!(format!("{r:?}"), "Valid");
                    let _ = tx.send(());
                });
                if i == 0 {
                    std::thread::sleep(std::time::Duration::from_millis(40));
                }
            }
            for _ in 0..2 {
                rx.recv_timeout(std::time::Duration::from_secs(60))
                    .unwrap_or_else(|_| panic!("iteration {iter}: helper-pool sweep deadlocked"));
            }
        }
        set_sweep_helper_pool(None);
    }

    static HELPER_POOL_TEST_LOCK: std::sync::Mutex<()> = std::sync::Mutex::new(());

    /// `[a, a, b]`: a repeated name followed by a NEW one. The env has two
    /// slots; `Var(b)` numbered by position in `inputs` read slot 2 and panicked
    /// in the compiled scalar sweep. Both evaluators now number by distinct
    /// name and must agree — and the sweep must not panic.
    #[test]
    fn repeated_name_followed_by_a_new_name_does_not_read_past_the_env() {
        let scalar = |ob: &ProofObligation| {
            let co = CompiledObligation::try_new_scalar_only(ob);
            assert!(co.is_some(), "must take the compiled path");
            format!(
                "{:?}",
                verify_by_evaluation_with_compiled(ob, &VerificationConfig::default(), co.as_ref())
            )
        };
        // trust_ir = a, aarch64 = ite(a == K, a + 1, a); with [a, a, b] the
        // scalar loop draws a, a, b per sample and `a` keeps its SECOND draw.
        let name = "chunk-test: repeated name a,a,b";
        let hit = mask(sample_lcg_jump(sample_seed(name), 3 * 5_555 + 2), 64);
        let ob = obligation(name, &["a", "a", "b"], &[hit]);
        let s = scalar(&ob);
        assert!(s.starts_with("Invalid"), "{s}");
        assert_eq!(chunked(&ob), s);
        // And a tape that actually reads `b` after the repeat: b == b is Valid.
        let mut uses_b = obligation("chunk-test: a,a,b reads b", &["a", "a", "b"], &[]);
        uses_b.trust_ir_expr = SmtExpr::Var {
            name: "b".to_string(),
            width: 64,
        };
        uses_b.aarch64_expr = SmtExpr::BvAdd {
            lhs: Arc::new(SmtExpr::Var {
                name: "b".to_string(),
                width: 64,
            }),
            rhs: k(0),
            width: 64,
        };
        assert_eq!(scalar(&uses_b), "Valid");
        assert_eq!(chunked(&uses_b), "Valid");
    }

    /// The evidence count is summed over EVERY chunk. The only sample that
    /// satisfies this precondition is sample 77,777 — deep inside chunk 6 of 8
    /// — so the sweep compared exactly one point, in a late chunk, and must be
    /// `Valid` pooled and sequential alike; dropping any chunk's count would
    /// turn it into the vacuous-sample `Unknown`. With that one point excluded
    /// as well, nothing is compared and both ways must say so.
    #[test]
    fn a_lone_satisfying_sample_in_a_late_chunk_is_counted() {
        let name = "chunk-test: lone satisfying sample in chunk 6";
        let lone = a_at(name, 2, 77_777);
        let is_lone = SmtExpr::Eq {
            lhs: v("a"),
            rhs: k(lone),
        };
        let mut ob = valid_but_not_identical(name);
        ob.preconditions = vec![is_lone.clone()];
        let compiled = CompiledObligation::try_new(&ob).expect("compiled");
        let whole = random_chunk_2(
            &ob,
            Some(&compiled),
            64,
            sample_seed(name),
            0,
            DEFAULT_SAMPLE_COUNT,
            &two_input_sweep_env(&ob),
        );
        assert!(
            matches!(whole, Ok(1)),
            "exactly one random sample satisfies the precondition: {whole:?}"
        );
        assert_eq!(sequential(&ob), "Valid");
        assert_eq!(chunked(&ob), "Valid");

        ob.preconditions.push(is_lone.not_expr());
        let s = sequential(&ob);
        assert!(s.contains("vacuous sample"), "{s}");
        assert_eq!(chunked(&ob), s);
    }

    /// A correct obligation is Valid both ways (no false counterexample from a
    /// mis-seeded chunk).
    #[test]
    fn valid_obligation_is_valid_both_ways() {
        let ob = obligation("chunk-test: nothing wrong", &["a", "b"], &[]);
        assert_eq!(sequential(&ob), "Valid");
        assert_eq!(chunked(&ob), "Valid");
    }

    /// Every obligation in the fixed registry: verdict and counterexample text
    /// identical between a one-thread sweep and a pooled, chunked sweep.
    #[test]
    fn whole_registry_verdicts_identical_sequential_vs_chunked() {
        let db = crate::proof_database::ProofDatabase::new();
        let config = VerificationConfig::with_sample_count(20_000);
        // The integer sample paths are what chunking touches. FP-only
        // obligations (`inputs` empty) take `verify_fp_by_evaluation`, which is
        // untouched here — and one registry entry (`FCmp_OEq_f32 -> wasm`)
        // panics its name parser (it expects an `Fcmp_` prefix), so sweeping it
        // directly is not a test of this change.
        let integer: Vec<&ProofObligation> = db
            .all()
            .iter()
            .map(|cp| &cp.obligation)
            .filter(|ob| !ob.inputs.is_empty())
            .collect();
        // The sequential side runs the SCALAR tapes only; the pooled side runs
        // whatever `try_new` produces (the batched twin, for every obligation
        // in its subset). So this pins chunking AND batching at once.
        let seq: Vec<String> = integer
            .iter()
            .map(|ob| {
                let scalar = CompiledObligation::try_new_scalar_only(ob);
                format!(
                    "{:?}",
                    verify_by_evaluation_with_compiled(ob, &config, scalar.as_ref())
                )
            })
            .collect();
        let pool = rayon::ThreadPoolBuilder::new()
            .num_threads(6)
            .build()
            .unwrap();
        let par: Vec<String> = pool.install(|| {
            use rayon::prelude::*;
            integer
                .par_iter()
                .map(|ob| format!("{:?}", verify_by_evaluation_with_config(ob, &config)))
                .collect()
        });
        assert_eq!(seq.len(), par.len());
        assert!(
            seq.len() >= 50,
            "registry unexpectedly small: {}",
            seq.len()
        );
        for (i, (s, p)) in seq.iter().zip(&par).enumerate() {
            assert_eq!(
                s, p,
                "registry obligation #{i} `{}` differs",
                integer[i].name
            );
        }
    }
}

#[cfg(test)]
mod fp_name_parser_tests {
    use super::*;

    /// Every FCMP obligation in the fixed registry — both the `Fcmp_` and the
    /// wasm `FCmp_` spelling — follows the condition naming inventory. This is
    /// not how the evaluator chooses the semantics of a stored expression.
    #[test]
    fn every_registry_fcmp_name_parses() {
        let db = crate::proof_database::ProofDatabase::new();
        let mut seen = 0;
        for cp in db.all() {
            let name = &cp.obligation.name;
            if name.starts_with("Fcmp_") || name.starts_with("FCmp_") {
                seen += 1;
                assert!(
                    parse_float_cc_from_name(name).is_some(),
                    "unparsed FCMP name `{name}`"
                );
            }
        }
        assert!(
            seen >= 20,
            "expected both spellings in the registry, saw {seen}"
        );
        assert!(parse_float_cc_from_name("FCmp_Bogus_f32 -> wasm").is_none());
        assert!(parse_float_cc_from_name("Fadd_F32 -> FADD").is_none());
    }

    /// The evaluator must return a verdict — never panic — for EVERY registry
    /// obligation, FP ones included (`FCmp_OEq_f32 -> wasm` used to panic the
    /// name parser). A panic inside the process-wide memo cell would take a
    /// compile down; an unknown name is an `Unknown` verdict instead.
    ///
    /// "A verdict" includes the honest NON-verdict: the source-bound frame
    /// theorem binds initial memory as the uninterpreted function
    /// `entry_memory`, which concrete evaluation cannot interpret. It used to
    /// panic `SmtExpr::eval`; it must now be `Unknown` naming that function —
    /// and never `Valid`, which the evaluator has no evidence for.
    #[test]
    fn evaluator_returns_a_verdict_for_every_registry_obligation() {
        let db = crate::proof_database::ProofDatabase::new();
        let config = VerificationConfig::with_sample_count(2_000);
        let mut fp = 0;
        let mut uf_bearing = Vec::new();
        for cp in db.all() {
            let ob = &cp.obligation;
            if ob.inputs.is_empty() {
                fp += 1;
            }
            let verdict = verify_by_evaluation_with_config(ob, &config);
            let ufs = evaluator_uninterpreted_functions(ob);
            if ufs.is_empty() {
                continue;
            }
            uf_bearing.push(ob.name.clone());
            match &verdict {
                VerificationResult::Unknown { reason } => {
                    assert!(
                        reason.starts_with("evaluator cannot decide: uninterpreted function"),
                        "`{}`: non-verdict must be named, got {reason:?}",
                        ob.name
                    );
                    for uf in &ufs {
                        assert!(
                            reason.contains(&format!("'{uf}'")),
                            "`{}`: reason does not name UF {uf}: {reason:?}",
                            ob.name
                        );
                    }
                }
                other => panic!(
                    "`{}` carries UF(s) {ufs:?} but the evaluator returned {other:?}",
                    ob.name
                ),
            }
        }
        assert!(
            fp >= 20,
            "expected FP-only obligations in the registry, saw {fp}"
        );
        assert!(
            uf_bearing
                .iter()
                .any(|n| n == crate::source_bound_frame::FRAME_OBLIGATION_NAME),
            "expected the frame theorem among the UF-bearing entries, saw {uf_bearing:?}"
        );
    }

    /// The exportable source-bound frame theorem the registry carries applies
    /// the uninterpreted `entry_memory` array; evaluation must decline it as
    /// inconclusive, naming the function, not panic in `SmtExpr::eval` and not
    /// credit a vacuous `Valid`.
    #[test]
    fn evaluator_declines_the_registry_frame_theorem_naming_its_uninterpreted_memory() {
        let ob = crate::source_bound_frame::frame_obligation();
        let result =
            verify_by_evaluation_with_config(&ob, &VerificationConfig::with_sample_count(8));
        assert!(
            matches!(&result, VerificationResult::Unknown { reason } if reason.contains("entry_memory")),
            "{result:?}"
        );
    }
}

#[cfg(test)]
mod uf_undecidable_tests {
    //! A term the concrete evaluator has no interpretation for is a named,
    //! fail-closed NON-verdict — never `Valid`, never a panic — on every
    //! entry (primary, memoized, the scalar-only test seam) and identically
    //! sequential vs chunked. Pinned after the frame theorem's `entry_memory`
    //! took `SmtExpr::eval` down inside two registry sweeps.
    use super::*;
    use crate::memory_proofs::{encode_load_le, encode_store_le, memory_sort};
    use crate::smt::{SmtExpr as E, SmtSort};

    fn inputs(names: &[&str]) -> Vec<(String, u32)> {
        names.iter().map(|n| (n.to_string(), 64)).collect()
    }

    fn obligation(
        name: &str,
        trust_ir: E,
        machine: E,
        pre: Vec<E>,
        ins: &[&str],
    ) -> ProofObligation {
        ProofObligation {
            name: name.into(),
            trust_ir_expr: trust_ir,
            aarch64_expr: machine,
            inputs: inputs(ins),
            preconditions: pre,
            fp_inputs: Vec::new(),
            category: None,
            machine_side_provenance: MachineSideProvenance::StaticDb,
        }
    }

    /// `entry_memory` shaped exactly like the frame theorems: a store then a
    /// load through a zero-argument array-valued UF.
    fn memory_roundtrip() -> E {
        let sp = E::var("sp", 64);
        let v = E::var("v", 64);
        let memory = E::uf("entry_memory", Vec::new(), memory_sort());
        encode_load_le(&encode_store_le(&memory, &sp, &v, 8), &sp, 8)
    }

    fn assert_uf_non_verdict(verdict: &VerificationResult, uf: &str) {
        match verdict {
            VerificationResult::Unknown { reason } => {
                assert!(
                    reason.starts_with("evaluator cannot decide: uninterpreted function")
                        && reason.contains(&format!("'{uf}'")),
                    "reason must name the UF: {reason:?}"
                );
            }
            other => panic!("expected a UF non-verdict, got {other:?}"),
        }
    }

    #[test]
    fn uninterpreted_functions_are_collected_from_every_term() {
        let ob = obligation(
            "uf: collect",
            E::uf("f", vec![E::var("a", 64)], SmtSort::BitVec(64)),
            E::uf(
                "g",
                vec![E::uf("h", Vec::new(), SmtSort::BitVec(64))],
                SmtSort::BitVec(64),
            ),
            vec![E::uf("p", Vec::new(), SmtSort::Bool)],
            &["a"],
        );
        assert_eq!(evaluator_uninterpreted_functions(&ob), ["f", "g", "h", "p"]);
        assert_eq!(
            evaluator_uninterpreted_function_sites(&ob),
            ["source expression", "machine expression", "precondition 0"]
        );
        let plain = obligation("uf: none", E::var("a", 64), E::var("a", 64), vec![], &["a"]);
        assert!(evaluator_uninterpreted_functions(&plain).is_empty());
        assert!(evaluator_undecidable(&plain).is_none());
    }

    /// The machine side reads back what it stored — true under EVERY
    /// interpretation of `entry_memory`, and still not the evaluator's to
    /// credit: it has no interpretation at all.
    #[test]
    fn uf_on_one_side_is_a_named_non_verdict_not_valid_and_not_a_panic() {
        let ob = obligation(
            "uf: memory roundtrip",
            E::var("v", 64),
            memory_roundtrip(),
            vec![],
            &["sp", "v"],
        );
        let cfg = VerificationConfig::with_sample_count(500);
        assert_uf_non_verdict(&verify_by_evaluation_with_config(&ob, &cfg), "entry_memory");
        assert_uf_non_verdict(&verify_by_evaluation(&ob), "entry_memory");
        assert_uf_non_verdict(&memoized_verify_by_evaluation(&ob, &cfg), "entry_memory");
    }

    /// A UF only in a precondition must not be skipped as "unmet": on the
    /// sampling path a skipped point is a vacuous pass, and `a == a` with
    /// every point skipped would finish `Valid`.
    #[test]
    fn uf_in_a_precondition_is_a_non_verdict_never_a_vacuous_valid() {
        let a = E::var("a", 64);
        let ob = obligation(
            "uf: precondition",
            a.clone(),
            a.clone().bvadd(E::bv_const(0, 64)),
            vec![E::uf("admissible", vec![a], SmtSort::Bool)],
            &["a", "b"],
        );
        let cfg = VerificationConfig::with_sample_count(500);
        assert_uf_non_verdict(&verify_by_evaluation_with_config(&ob, &cfg), "admissible");
        // The scalar-only seam (no whole-obligation gate would still reach
        // `check_single_point`): same answer.
        let scalar = CompiledObligation::try_new_scalar_only(&ob);
        assert!(
            scalar.is_none(),
            "a UF must keep the obligation off the compiled tapes"
        );
        assert_uf_non_verdict(
            &verify_by_evaluation_with_compiled(&ob, &cfg, scalar.as_ref()),
            "admissible",
        );
    }

    /// Identical sides carrying a UF: the shortcut that credits `e == e`
    /// without a sweep is declined in lockstep on the primary entry and the
    /// memo's elided copy of it. Both must say the same thing.
    #[test]
    fn identical_sides_with_a_uf_are_declined_in_lockstep_with_the_memo() {
        let f = E::uf("f", vec![E::var("a", 64)], SmtSort::BitVec(64));
        let ob = obligation("uf: identical sides", f.clone(), f, vec![], &["a", "b"]);
        let cfg = VerificationConfig::with_sample_count(500);
        assert!(
            exhaustive_input_count(&ob, &cfg).is_none(),
            "must be on the statistical path"
        );
        let primary = verify_by_evaluation_with_config(&ob, &cfg);
        let memo = memoized_verify_by_evaluation(&ob, &cfg);
        assert_uf_non_verdict(&primary, "f");
        assert_eq!(format!("{primary:?}"), format!("{memo:?}"));
    }

    /// Sequential (scalar seam) and pooled/chunked sweeps agree on the
    /// non-verdict, text included — it depends on the obligation, not on which
    /// point or chunk saw it first.
    #[test]
    fn uf_non_verdict_is_identical_sequential_vs_chunked() {
        let ob = obligation(
            "uf: chunked",
            E::var("v", 64),
            memory_roundtrip(),
            vec![],
            &["sp", "v", "w"],
        );
        let cfg = VerificationConfig::with_sample_count(20_000);
        let seq = format!(
            "{:?}",
            verify_by_evaluation_with_compiled(
                &ob,
                &cfg,
                CompiledObligation::try_new_scalar_only(&ob).as_ref()
            )
        );
        let pool = rayon::ThreadPoolBuilder::new()
            .num_threads(4)
            .build()
            .unwrap();
        let par = pool.install(|| format!("{:?}", verify_by_evaluation_with_config(&ob, &cfg)));
        assert_eq!(seq, par);
        assert!(seq.contains("'entry_memory'"), "{seq}");
    }

    /// The registry's own frame theorem, end to end.
    #[test]
    fn frame_theorem_is_a_named_non_verdict() {
        let ob = crate::source_bound_frame::frame_obligation();
        let cfg = VerificationConfig::with_sample_count(2_000);
        assert_uf_non_verdict(&verify_by_evaluation_with_config(&ob, &cfg), "entry_memory");
        assert_uf_non_verdict(&memoized_verify_by_evaluation(&ob, &cfg), "entry_memory");
    }

    /// The point-level backstop, for a term `try_eval` refuses that is NOT a
    /// UF: a `select` on a bitvector is out of the compiled subset, so it
    /// reaches the interpreter, which errors — the sweep stops with `Unknown`
    /// (naming the failure), not a panic and not a skipped point.
    #[test]
    fn a_non_uf_evaluation_error_is_a_non_verdict_not_a_panic() {
        let bad = E::select(E::var("a", 64), E::var("b", 64));
        let ob = obligation(
            "select on bv",
            E::var("a", 64),
            bad.clone(),
            vec![],
            &["a", "b"],
        );
        assert!(
            evaluator_undecidable(&ob).is_none(),
            "no UF here: the gate must not fire"
        );
        assert!(CompiledObligation::try_new(&ob).is_none());
        let cfg = VerificationConfig::with_sample_count(500);
        match verify_by_evaluation_with_config(&ob, &cfg) {
            VerificationResult::Unknown { reason } => assert!(
                reason.starts_with("cannot concretely evaluate machine expression")
                    && reason.contains("select on non-array"),
                "{reason:?}"
            ),
            other => panic!("expected Unknown, got {other:?}"),
        }
        // ... and in a precondition, the same: never an unmet-skip.
        let ob = obligation(
            "select on bv (precondition)",
            E::var("a", 64),
            E::var("a", 64).bvadd(E::bv_const(0, 64)),
            vec![bad.eq_expr(E::bv_const(0, 8))],
            &["a", "b"],
        );
        match verify_by_evaluation_with_config(&ob, &cfg) {
            VerificationResult::Unknown { reason } => assert!(
                reason.starts_with("cannot concretely evaluate precondition 0")
                    && reason.contains("select on non-array"),
                "{reason:?}"
            ),
            other => panic!("expected Unknown, got {other:?}"),
        }
    }
}

#[cfg(test)]
#[path = "lowering_proof_eval_errors.rs"]
mod eval_error_tests;

#[cfg(test)]
#[path = "lowering_proof_vacuous_sample_tests.rs"]
mod vacuous_sample_tests;

/// Least number of precondition-satisfying points the directed trials must
/// contribute for [`assert_directed_sampling_holds_at`]: a sweep whose only
/// evidence is a handful of points is not the evidence these tests claim.
#[cfg(test)]
pub(crate) const MIN_DIRECTED_EVIDENCE: u64 = 64;

/// Test support for an obligation whose preconditions RELATE its inputs (two
/// aligned, disjoint addresses; `x == y`; `is_fixed == 1`) so that the
/// uniform draws of the multi-input sweep never satisfy them and only its
/// precondition-directed trials do (NEW-CG-SAMPLER; before them the sweep
/// compared nothing and reported the vacuous-sample `Unknown`, TRUSTCG-02).
/// [`verify_by_evaluation`] must be `Valid`, the directed trials alone must
/// have compared at least [`MIN_DIRECTED_EVIDENCE`] points, and the claim is
/// also checked at each explicit `witness` (every input bound, in range):
/// every precondition must hold and both sides must evaluate and agree.
#[cfg(test)]
pub(crate) fn assert_directed_sampling_holds_at(
    obligation: &ProofObligation,
    witnesses: &[&[(&str, u64)]],
) {
    assert_directed_sampling_valid(obligation);
    assert!(
        !witnesses.is_empty(),
        "'{}': explicit witnesses are required",
        obligation.name
    );
    for witness in witnesses {
        assert_holds_at_witness(obligation, witness);
    }
}

/// The sampled half of [`assert_directed_sampling_holds_at`]: the sweep is
/// `Valid` and its directed trials alone compared at least
/// [`MIN_DIRECTED_EVIDENCE`] points.
#[cfg(test)]
pub(crate) fn assert_directed_sampling_valid(obligation: &ProofObligation) {
    let sampled = verify_by_evaluation(obligation);
    assert!(
        matches!(sampled, VerificationResult::Valid),
        "'{}': the directed trials reach its preconditions, so the sweep must compare \
         points and agree, got {sampled:?}",
        obligation.name
    );
    assert!(
        needs_multi_input_sampling(obligation),
        "'{}'",
        obligation.name
    );
    let compiled = CompiledObligation::try_new(obligation);
    let mut env = multi_input_sweep_env(obligation);
    let directed = directed_chunk_multi(
        obligation,
        compiled.as_ref(),
        directed_trial_count(obligation, VerificationConfig::default().sample_count),
        &mut env,
    )
    .expect("a correct obligation has no terminal directed point");
    assert!(
        directed >= MIN_DIRECTED_EVIDENCE,
        "'{}': the directed trials compared only {directed} points",
        obligation.name
    );
}

/// Every precondition holds at `witness` (every input bound, in range) and
/// both sides evaluate and agree there.
#[cfg(test)]
fn assert_holds_at_witness(obligation: &ProofObligation, witness: &[(&str, u64)]) {
    let mut env = EvalEnv::default();
    for (name, value) in witness.iter() {
        env.insert((*name).to_string(), *value);
    }
    for (name, width) in &obligation.inputs {
        let value = *env.get(name).unwrap_or_else(|| {
            panic!(
                "'{}': witness {witness:?} leaves `{name}` unbound",
                obligation.name
            )
        });
        assert_eq!(
            value,
            mask(value, *width),
            "'{}': witness value for `{name}` exceeds {width} bits",
            obligation.name
        );
    }
    for (index, pre) in obligation.preconditions.iter().enumerate() {
        let held = pre
            .try_eval(&env)
            .unwrap_or_else(|error| panic!("'{}': precondition {index}: {error}", obligation.name));
        assert!(
            held.as_bool(),
            "'{}': witness {witness:?} must satisfy precondition {index}",
            obligation.name
        );
    }
    let source = obligation
        .trust_ir_expr
        .try_eval(&env)
        .unwrap_or_else(|error| panic!("'{}': source side: {error}", obligation.name));
    let machine = obligation
        .aarch64_expr
        .try_eval(&env)
        .unwrap_or_else(|error| panic!("'{}': machine side: {error}", obligation.name));
    assert!(
        source.semantically_equal(&machine),
        "'{}' disagrees at witness {witness:?}: source={source:?}, machine={machine:?}",
        obligation.name
    );
}
