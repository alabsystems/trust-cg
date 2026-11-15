// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! Source-bound AArch64 whole-body theorem for frameless leaf bodies with
//! Boolean, bitwise, shift, select and acyclic control-flow semantics.
//!
//! One theorem per function states that the value the final allocated
//! AArch64 body returns equals the value its exact LIR source returns, for
//! every input on which the source is defined:
//!
//! ```text
//! inputs      e_i   the caller's 64-bit X register of parameter i (i < 8)
//!             g_k   every other register and NZCV flag at entry, read before
//!                   the body writes it (arbitrary: the caller's value)
//! premises    (= S expr)   the source's returned value, gated over its
//!                          return blocks (see `source`)
//!             (= M expr)   the machine's X0 at RET (W0 for I32 and B1
//!                          results, including I8/I16 ABI results carried in
//!                          I32; a B1 must be exactly 0 or 1 in W0),
//!                          gated over its RET blocks (see `machine`)
//!             (= n expr)   any other definition whose expanded term
//!                          exceeds `INLINE_LIMIT`; smaller ones are written
//!                          inline into their uses
//!             D            only when the source can be undefined: no
//!                          executed shift has an amount that is not below
//!                          its width (trust-ir `ShiftInRange`); the one
//!                          premise that is not a definition, the domain the
//!                          theorem quantifies over
//! theorem     (= S M)
//! ```
//!
//! Both sides are *gated* DAGs: every block has a reach bit, every edge a
//! taken bit (its block's reach and its branch condition), every join value
//! the value its one taken edge carries. The source's join parameters are
//! LIR block arguments: each predecessor's argument copies are read before
//! any is assigned and the parameters take them together (the simultaneous
//! substitution rule). The machine's merged registers and flags follow the
//! same rule over its own edges. Neither side's paths are paired with the
//! other's: the theorem compares the two returned values as functions of the
//! inputs, so if-conversion, block merging, branch inversion, fused compare
//! branches and layout changes are all judged by what they compute.
//!
//! **Domain.** Applicability is decided by the LIR source alone
//! ([`source_admits_a64_body_owner`]): an acyclic CFG of at most sixteen
//! blocks of `Jump`/`Brif`/`Return`, up to eight `I8`/`I16`/`I32`/`I64`/`B1` parameters
//! and one such result, over `Iconst`, `Uextend`, `Copy`, `Iadd`, `Isub`, `Ineg`,
//! `Band`, `Bor`, `Bxor`, `Bnot`, `BandNot`, `BorNot` (bitwise on integers,
//! the connectives on `B1`), `Ishl`, `Ushr`, `Sshr`, `Icmp` and
//! `Select` (`Eq`/`Ne` test) — see `source`. The machine must be frameless
//! (a body inside the sixteen-byte FP/LR envelope belongs to the frame owner,
//! [`crate::source_bound_frame`]) and made only of the rows `machine` models.
//! Value-carrying and conditional loops are refused by name on both sides.
//! There is one separate control domain: a zero-argument, zero-result body
//! containing only unconditional Jumps, including cycles. Its theorem equates
//! each source next-PC with the independently decoded B word's next-PC for an
//! arbitrary image base, not a returned value. See [`pure_jump`].
//!
//! **Source authority.** Here "source" is the complete retained LIR function;
//! private admission below checks its SSA and this owner's semantic domain.
//! Borrowed Core/module custody or a separately checked frontend claim does
//! not replace that admission or extend the domain to calls, memory or
//! aggregate results. This owner neither issues a Core `BodyGate` license nor
//! composes a source-language refinement. Conditional call/world queries need
//! their own checked relation witnesses; they are not a body replay owner.
//!
//! **Refusals.** [`A64BodyRefusal::Unsupported`] makes no claim. A
//! [`A64BodyRefusal::Mismatch`] names a recognized body that is wrong: a
//! signature that differs, a branch that does not land where its CFG says,
//! a write to a register the caller observes unchanged (X18-X30), or a
//! returned value that differs from the source's on a concrete input on
//! which the source is defined. That last check evaluates both gated DAGs on
//! a fixed set of inputs and can only REFUSE: agreement grants nothing.
//!
//! **Credit.** Construction is not discharge. Only an AY proof of the exact
//! theorem that Clean independently replays credits anything
//! ([`crate::source_bound_replay`]), and then only the rows in the
//! observable's backward slice (rows whose definitions the returned value
//! depends on, through data, flags or branch conditions) and the direct
//! transfers that make up the CFG the theorem is stated over (a different
//! target is a different theorem). Register copies and wide-move constants
//! in that slice are credited by the same replay, under OD-35's route C
//! (`docs/decision-record.md`): the theorem composes each one from its own
//! allocated operands, so a wrong register route, immediate, halfword or
//! width changes the returned value the theorem equates. A live literal
//! materialization (including a copy from a zero register) also admits a body:
//! its independently built returned-value equality is refutable. Copies of
//! numbered registers alone do not admit an identity body
//! ([`A64BodyUnsupported::NoCoveredRow`]). Dead rows, dead constants (route A2's domain, which
//! this frameless owner does not implement) and `RET` receive nothing from
//! this owner.
//!
//! **Binding to the emitted words.** The theorem is built from the allocated
//! `MachInst`s the encoder turns into words. Each row's semantics here is the
//! meaning of the word the encoder emits for it, and on a proof-grade route
//! ENC-5 decodes every emitted word against its row (refusing any word it
//! cannot decode) and the final-layout cross-check re-derives every branch
//! displacement from the final bytes and binds it to the recorded CFG
//! (`trust-cg-codegen` `pipeline.rs`). Those two checks, not this theorem,
//! bind the rows to the bytes.
//!
//! **Trusted.** This translator (the LIR semantics in `source`, the word
//! semantics in `machine`), the AAPCS64 argument rule (an `I32` is the low
//! half of its X register, a `B1` an 8-bit 0/1 whose bits 1..7 are zero;
//! nothing else about the upper bits), the rule that a correct body writes
//! no register but X0-X17 and NZCV (the walk refuses every other write, so
//! preservation rests on it, not on the solver), the CFG walk (word offsets,
//! displacement resolution, fallthrough), and the SMT-LIB serializer.

use std::collections::{HashMap, HashSet};

use trust_cg_ir::{InstId, MachFunction};
use trust_cg_lower::Function;

use crate::lowering_proof::{MachineSideProvenance, ProofObligation, TransvalCheckKind};
use crate::smt::SmtExpr as E;
use crate::source_bound_frame::BranchTargetDefect;

#[path = "source_bound_a64_body_source.rs"]
mod source;

#[path = "source_bound_a64_pure_jump.rs"]
mod pure_jump;

#[path = "source_bound_a64_body_machine.rs"]
pub(crate) mod machine;

#[cfg(test)]
#[path = "source_bound_a64_body_tests.rs"]
mod tests;

pub use machine::ADMITTED_MACHINE_OPCODES;
pub use source::ADMITTED_LIR_OPCODES;

/// Whether the owner admits the LIR opcode `opcode` (its operand types are
/// checked separately; `Select` only with an `Equal`/`NotEqual` test).
pub fn admits_lir_opcode(opcode: &trust_cg_lower::instructions::Opcode) -> bool {
    source::admitted_opcode(opcode)
}

/// Whether a bound body may contain the AArch64 opcode `opcode` (its
/// operands are checked by the walk).
pub fn admits_machine_opcode(opcode: trust_cg_ir::AArch64Opcode) -> bool {
    machine::admitted_row(opcode)
}

/// Name of the whole-body theorem. The certificate text carries it.
pub const A64_BODY_OBLIGATION_NAME: &str = "Source-bound AArch64 whole-body theorem (final allocated frameless body): the replayed theorem credits the returned value's slice and the body's transfers";

/// Reason of every covered row when no independently checked proof of the
/// body theorem exists. Such rows are never credited.
pub const A64_BODY_NEEDS_REPLAY: &str =
    "source-bound AArch64 body needs independently replayed proof";

/// LIR value types the owner admits.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub(crate) enum Ty {
    I8,
    I16,
    I32,
    I64,
    B1,
}

impl Ty {
    /// The width of the value's SMT term (a `B1` is one bit).
    pub(crate) fn width(self) -> u32 {
        match self {
            Ty::I8 => 8,
            Ty::I16 => 16,
            Ty::I32 => 32,
            Ty::I64 => 64,
            Ty::B1 => 1,
        }
    }

    /// Bits of the machine's return register the caller observes.
    fn observed_bits(self) -> u32 {
        match self {
            Ty::I64 => 64,
            Ty::I8 | Ty::I16 | Ty::I32 | Ty::B1 => 32,
        }
    }
}

/// `term == #b1` for a one-bit term.
pub(crate) fn is_one(term: E) -> E {
    term.eq_expr(E::bv_const(1, 1))
}

/// `a & b` of two one-bit terms, without the identity of a constant 1 (the
/// entry block's reach bit).
pub(crate) fn and_bit(a: E, b: E) -> E {
    let one = E::bv_const(1, 1);
    if a == one {
        b
    } else if b == one {
        a
    } else {
        a.bvand(b)
    }
}

/// A Boolean as a one-bit term.
pub(crate) fn bool_bv(condition: E) -> E {
    E::ite(condition, E::bv_const(1, 1), E::bv_const(0, 1))
}

/// Which side of the theorem a definition belongs to.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Side {
    Source,
    Machine,
}

struct Definition {
    name: String,
    width: u32,
    expr: E,
    side: Side,
    /// The machine rows whose effect this definition states.
    origins: Vec<InstId>,
}

/// The definitions and free inputs of one theorem, in definition order.
#[derive(Default)]
pub(crate) struct Defs {
    definitions: Vec<Definition>,
    inputs: Vec<(String, u32)>,
}

impl Defs {
    fn define(&mut self, prefix: &str, expr: E, side: Side, origins: &[InstId]) -> E {
        let atomic = matches!(expr, E::Var { .. } | E::BvConst { .. });
        if atomic && origins.is_empty() {
            return expr;
        }
        let width = expr.bv_width();
        let name = format!("{prefix}{}", self.definitions.len());
        self.definitions.push(Definition {
            name: name.clone(),
            width,
            expr,
            side,
            origins: origins.to_vec(),
        });
        E::var(name, width)
    }

    /// Name a source term.
    pub(crate) fn source(&mut self, expr: E) -> E {
        self.define("s", expr, Side::Source, &[])
    }

    /// Name a machine term, recording the rows whose effect it states.
    pub(crate) fn machine(&mut self, expr: E, origins: &[InstId]) -> E {
        self.define("m", expr, Side::Machine, origins)
    }

    /// Whether `term` is provably an unsigned value below `bound`: a constant
    /// below it, or a bitwise AND with such an operand (`x & y <= y`),
    /// looking through named definitions.
    pub(crate) fn provably_below(&self, term: &E, bound: u64) -> bool {
        match term {
            E::BvConst { value, .. } => *value < bound,
            E::BvAnd { lhs, rhs, .. } => {
                self.provably_below(lhs, bound) || self.provably_below(rhs, bound)
            }
            E::Var { name, .. } => self
                .definitions
                .iter()
                .find(|d| d.name == *name)
                .is_some_and(|d| self.provably_below(&d.expr, bound)),
            _ => false,
        }
    }

    /// A free input of `width` bits.
    pub(crate) fn input(&mut self, name: String, width: u32) -> E {
        if !self.inputs.iter().any(|(existing, _)| *existing == name) {
            self.inputs.push((name.clone(), width));
        }
        E::var(name, width)
    }
}

/// Immutable binding of one exact (LIR, final allocated AArch64 body) pair to
/// its whole-body theorem. No public constructor: only
/// [`source_bound_a64_body`] builds one.
pub struct SourceBoundA64Body<'a> {
    source: &'a Function,
    machine: &'a MachFunction,
    /// Computing rows credited by a Valid replay, ascending.
    covered: Vec<InstId>,
    /// Register copies and wide-move constants of the slice, credited by a
    /// Valid replay (OD-35 route C), ascending.
    copies_and_constants: Vec<InstId>,
    obligation: ProofObligation,
}

impl<'a> SourceBoundA64Body<'a> {
    pub fn source(&self) -> &'a Function {
        self.source
    }

    pub fn machine(&self) -> &'a MachFunction {
        self.machine
    }

    /// The whole-body theorem. Construction is not discharge.
    pub fn obligation(&self) -> &ProofObligation {
        &self.obligation
    }

    /// The computing rows a Valid replay credits: the observable's backward
    /// slice and the direct transfers, without register copies, wide-move
    /// constants, `RET` and inert rows.
    pub fn covered(&self) -> &[InstId] {
        &self.covered
    }

    /// The register copies and wide-move constants of the observable's
    /// backward slice, which a Valid replay also credits (OD-35 route C).
    pub fn copies_and_constants(&self) -> &[InstId] {
        &self.copies_and_constants
    }

    /// Whether a Valid replay credits row `id`: a computing row of
    /// [`Self::covered`] or a copy or constant of
    /// [`Self::copies_and_constants`].
    pub fn covers(&self, id: InstId) -> bool {
        self.covered.binary_search(&id).is_ok()
            || self.copies_and_constants.binary_search(&id).is_ok()
    }
}

/// Why [`source_bound_a64_body`] built no theorem.
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
pub enum A64BodyRefusal {
    /// Outside the checked domain: no claim; ordinary coverage rules apply.
    #[error("unsupported source-bound AArch64 body: {0}")]
    Unsupported(A64BodyUnsupported),
    /// An admitted source whose recognized machine body is wrong. Enforcing
    /// callers reject the function by name.
    #[error("source-bound AArch64 body mismatch: {0}")]
    Mismatch(A64BodyMismatch),
}

impl A64BodyRefusal {
    /// The typed mismatch, when this refusal identifies an erroneous target.
    pub fn mismatch(&self) -> Option<&A64BodyMismatch> {
        match self {
            Self::Mismatch(mismatch) => Some(mismatch),
            Self::Unsupported(_) => None,
        }
    }
}

/// A pair outside the owner's domain. None grants or withholds any other
/// authority.
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
pub enum A64BodyUnsupported {
    /// The LIR control flow is outside the acyclic domain (a loop, an
    /// unmodelled terminator, an unreachable block, a size bound).
    #[error("LIR source control flow is outside the acyclic domain: {0}")]
    SourceShape(String),
    #[error("LIR source is outside the body domain: {0}")]
    SourceDomain(String),
    /// A function without a result has nothing the theorem could observe.
    #[error("the function returns nothing, so no non-vacuous theorem exists")]
    NoObservable,
    #[error("machine function is outside the body domain: {0}")]
    MachineFunction(String),
    #[error("machine control flow is outside the body domain: {0}")]
    MachineControl(String),
    #[error("machine row {inst:?} is outside the body domain: {detail}")]
    MachineRow { inst: InstId, detail: String },
    /// The returned value depends on neither a computing row nor a literal
    /// materialization. Numbered-register copies alone do not admit a body.
    #[error("the returned value depends on no creditable machine row")]
    NoCoveredRow,
    /// No sampled input reaches a return without executing an out-of-range
    /// shift: the theorem could be vacuous, so none is built.
    #[error(
        "the source executes an out-of-range shift on every sampled input, so the theorem \
         could be vacuous"
    )]
    NeverDefined,
    /// A builder invariant failed. Never credit.
    #[error("the body theorem failed its definitional construction check: {0}")]
    Construction(String),
}

/// A recognized body that disagrees with its admitted source or with its own
/// control skeleton. No correct lowering produces one.
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
pub enum A64BodyMismatch {
    #[error("machine signature differs from the LIR source signature")]
    Signature,
    #[error(
        "pure-jump branch in block {block:?} (instruction {instruction:?}) has displacement {actual_words} words, expected {expected_words} from the exact LIR destination"
    )]
    PureJumpTarget {
        block: trust_cg_ir::BlockId,
        instruction: InstId,
        expected_words: i64,
        actual_words: i64,
    },
    #[error("the machine does not implement the admitted pure-jump graph: {detail}")]
    PureJumpBody { detail: String },
    #[error("branch in block {block:?} (instruction {instruction:?}) {defect}")]
    BranchTarget {
        block: trust_cg_ir::BlockId,
        instruction: Option<InstId>,
        defect: BranchTargetDefect,
    },
    #[error("row {inst:?} writes {register}, which the caller observes unchanged")]
    PreservedWrite { inst: InstId, register: String },
    /// A concrete input on which the source is defined and the two returned
    /// values differ.
    #[error("the machine returns a different value than its LIR source: {witness}")]
    ReturnValue { witness: String },
}

/// The proof category a credited row is reported under: its own role in the
/// body (the theorem is one; the category says what the row does).
pub fn a64_body_row_category(
    opcode: trust_cg_ir::AArch64Opcode,
) -> crate::proof_database::ProofCategory {
    use crate::proof_database::ProofCategory as C;
    use trust_cg_ir::AArch64Opcode as M;
    match opcode {
        M::AddRR
        | M::SubRR
        | M::AddRI
        | M::AddRIShift12
        | M::SubRI
        | M::Neg
        | M::AddRRShift
        | M::SubRRShift
        | M::AddRRShiftLsr => C::Arithmetic,
        M::Uxtb | M::Uxth | M::Uxtw | M::Sxtb | M::Sxth | M::Sxtw => C::ExtensionTruncation,
        M::CmpRR | M::CmpRI | M::Tst | M::CSet | M::Csel | M::Csinc | M::Csinv | M::Csneg => {
            C::Comparison
        }
        M::B | M::BCond | M::Cbz | M::Cbnz | M::Tbz | M::Tbnz => C::Branch,
        // A copy or wide-move constant of the returned value's slice (OD-35
        // route C) moves a value; it is labelled with the arithmetic rows.
        M::MovR | M::MOVWrr | M::MOVXrr | M::Movz | M::Movn | M::Movk | M::MovI => C::Arithmetic,
        _ => C::BitwiseShift,
    }
}

/// The categories [`a64_body_row_category`] can give (an export payload's
/// category must be one of them).
pub fn a64_body_row_categories() -> [crate::proof_database::ProofCategory; 5] {
    use crate::proof_database::ProofCategory as C;
    [
        C::Arithmetic,
        C::ExtensionTruncation,
        C::Comparison,
        C::Branch,
        C::BitwiseShift,
    ]
}

/// The verdict a covered row receives from its body theorem's replay:
/// `Valid` (an AY proof Clean independently accepted) credits Formal under
/// the theorem's name and the row's category; a refutation fails the row; no
/// independently checked proof leaves it unverified ([`A64_BODY_NEEDS_REPLAY`]).
pub(crate) fn a64_body_row_result(
    obligation: &ProofObligation,
    opcode: trust_cg_ir::AArch64Opcode,
    verdict: Option<&crate::verify::VerificationResult>,
    why: Option<&str>,
) -> crate::function_verifier::InstructionVerificationResult {
    use crate::function_verifier::InstructionVerificationResult as R;
    use crate::verify::VerificationResult as V;
    match verdict {
        Some(V::Valid) => R::Verified {
            proof_name: obligation.name.clone(),
            category: a64_body_row_category(opcode),
            strength: crate::verify::VerificationStrength::Formal,
            degenerate: obligation.is_degenerate(),
        },
        Some(V::Invalid { counterexample }) => R::Failed {
            proof_name: obligation.name.clone(),
            detail: counterexample.clone(),
        },
        Some(V::Unknown { reason }) => R::Failed {
            proof_name: obligation.name.clone(),
            detail: format!("Unknown: {reason}"),
        },
        None => R::Unverified {
            reason: match why {
                Some(why) => format!("{A64_BODY_NEEDS_REPLAY} ({why})"),
                None => A64_BODY_NEEDS_REPLAY.into(),
            },
        },
    }
}

pub(crate) fn unsupported(reason: A64BodyUnsupported) -> A64BodyRefusal {
    A64BodyRefusal::Unsupported(reason)
}

pub(crate) fn mismatch(reason: A64BodyMismatch) -> A64BodyRefusal {
    A64BodyRefusal::Mismatch(reason)
}

/// Whether [`source_bound_a64_body`] judges any machine lowering of
/// `source`. `false` means every lowering is `Unsupported` before its
/// machine code is inspected. `true` claims nothing about a machine body.
pub fn source_admits_a64_body_owner(source: &Function) -> bool {
    pure_jump::source_edges(source).is_some() || source::admit(source).is_ok()
}

/// Why `source` is outside the owner's domain, or `None` when it is admitted
/// (diagnostics and the opcode census).
pub fn a64_body_source_refusal(source: &Function) -> Option<A64BodyRefusal> {
    if pure_jump::source_edges(source).is_some() {
        None
    } else {
        source::admit(source).err()
    }
}

fn entry_name(index: usize) -> String {
    format!("e{index}")
}

/// Build the whole-body theorem for an admitted source and a recognized
/// frameless machine body. See the module documentation.
pub fn source_bound_a64_body<'a>(
    source: &'a Function,
    machine: &'a MachFunction,
) -> Result<SourceBoundA64Body<'a>, A64BodyRefusal> {
    build(source, machine, true)
}

/// The theorem [`source_bound_a64_body`] would build, WITHOUT its concrete
/// refutation check, so a wrong body's query can be put to the solver lane
/// (the corruption controls). This is not an owner and grants nothing: the
/// verifier never calls it, and no replay path accepts its result.
pub fn diagnostic_a64_body_obligation(
    source: &Function,
    machine: &MachFunction,
) -> Result<ProofObligation, A64BodyRefusal> {
    build(source, machine, false).map(|owner| owner.obligation)
}

fn build<'a>(
    source: &'a Function,
    machine: &'a MachFunction,
    refute: bool,
) -> Result<SourceBoundA64Body<'a>, A64BodyRefusal> {
    if let Some(edges) = pure_jump::source_edges(source) {
        // This complete source domain is already recognized. No target-side
        // refusal may fall back to unrelated per-row coverage (including an
        // all-skipped inventory after every branch was dropped).
        return pure_jump::build(source, machine, &edges, refute).map_err(
            |refusal| match refusal {
                A64BodyRefusal::Unsupported(reason) => mismatch(A64BodyMismatch::PureJumpBody {
                    detail: reason.to_string(),
                }),
                refusal => refusal,
            },
        );
    }
    let admitted = source::admit(source)?;
    if source.name != machine.name {
        return Err(unsupported(A64BodyUnsupported::MachineFunction(
            "the machine function is not the source's".into(),
        )));
    }
    let mut defs = Defs::default();
    let entry: Vec<E> = (0..admitted.params.len())
        .map(|i| defs.input(entry_name(i), 64))
        .collect();
    let source_side = admitted.encode(&mut defs, &entry);
    let machine_side = machine::encode(machine, &admitted, &mut defs, &entry)?;
    let observed = admitted.returns.observed_bits();
    let source_observed = match admitted.returns {
        Ty::B1 => source_side.result.clone().zero_ext(observed - 1),
        _ => source_side.result.clone(),
    };
    let machine_observed = machine_side.result.clone();
    // Rows in the observable's backward slice.
    let index: HashMap<&str, usize> = defs
        .definitions
        .iter()
        .enumerate()
        .map(|(i, d)| (d.name.as_str(), i))
        .collect();
    let mut slice: HashSet<InstId> = HashSet::new();
    let mut visited: HashSet<usize> = HashSet::new();
    let mut pending: Vec<String> = machine_side.result.free_vars();
    while let Some(name) = pending.pop() {
        let Some(&position) = index.get(name.as_str()) else {
            continue;
        };
        if !visited.insert(position) {
            continue;
        }
        let definition = &defs.definitions[position];
        if definition.side != Side::Machine {
            return Err(unsupported(A64BodyUnsupported::Construction(format!(
                "the machine side reads the source definition {name}"
            ))));
        }
        slice.extend(definition.origins.iter().copied());
        pending.extend(definition.expr.free_vars());
    }
    let mut covered = Vec::new();
    let mut copies_and_constants = Vec::new();
    for row in &machine_side.rows {
        let inst = &machine.insts[row.0 as usize];
        // Every direct transfer is part of the CFG the theorem is stated
        // over (a different target is a different theorem); a value row
        // counts only in the returned value's data and flag slice.
        if !slice.contains(row) && !machine::is_transfer(inst.opcode) {
            continue;
        }
        if machine::copy_or_constant(inst.opcode) {
            copies_and_constants.push(*row);
        } else if !machine::is_inert(inst) && inst.opcode != trust_cg_ir::AArch64Opcode::Ret {
            covered.push(*row);
        }
    }
    covered.sort_unstable();
    copies_and_constants.sort_unstable();
    if refute {
        // The source's own constants (and their neighbours) join the corner
        // values: an input equal to a compared constant is where a wrong
        // comparison or select shows.
        let constants: Vec<u64> = source
            .blocks
            .values()
            .flat_map(|block| &block.instructions)
            .filter_map(|inst| match inst.opcode {
                trust_cg_lower::instructions::Opcode::Iconst { imm, .. } => Some(imm as u64),
                _ => None,
            })
            .flat_map(|value| [value, value.wrapping_sub(1), value.wrapping_add(1)])
            .collect();
        concrete_refutation(
            &defs,
            &constants,
            &source_observed,
            &machine_side.result,
            &source_side.defined,
            source_side.domain.as_ref(),
        )?;
    }
    // A wrong body is a mismatch before it is a body without credit (the
    // diagnostic builder states the theorem whatever it would credit).
    let live_constant = copies_and_constants
        .iter()
        .any(|row| machine::constant_materialization(&machine.insts[row.0 as usize]));
    if refute
        && !live_constant
        && !covered
            .iter()
            .any(|row| !machine::is_transfer(machine.insts[row.0 as usize].opcode))
    {
        return Err(unsupported(A64BodyUnsupported::NoCoveredRow));
    }
    let obligation = build_obligation(
        &defs,
        source_observed.clone(),
        machine_observed,
        [&source_side.result, &machine_side.result],
        source_side.domain.as_ref(),
    )
    .map_err(|reason| unsupported(A64BodyUnsupported::Construction(reason)))?;
    Ok(SourceBoundA64Body {
        source,
        machine,
        covered,
        copies_and_constants,
        obligation,
    })
}

/// Largest expanded term (in SMT nodes) a definition may have and still be
/// written inline into its uses; a larger one stays a named premise. One
/// fixed rule for every function: small bodies become one quantifier-free
/// term per side. The choice was made from unrecorded development runs of
/// the unit fixtures against the overlay AY/Clean pair, in which inlining
/// certified more of them than named premises; it is a design choice, not
/// recorded evidence (`reports/2026-10-01-aarch64-source-bound-body`).
const INLINE_LIMIT: usize = 512;

/// Only the threshold matters: visit at most INLINE_LIMIT + 1 nodes.
/// Keep the walk iterative so a deep term does not consume the call stack.
fn exceeds_inline_limit(expr: &E) -> bool {
    use E::*;
    if matches!(expr, Var { .. } | BvConst { .. } | BoolConst(_)) {
        return false;
    }
    let mut pending = vec![expr];
    let mut visited = 0;
    while let Some(expr) = pending.pop() {
        visited += 1;
        if visited > INLINE_LIMIT {
            return true;
        }
        match expr {
            Var { .. } | BvConst { .. } | BoolConst(_) => {}
            BvNeg { operand, .. }
            | Not { operand }
            | Extract { operand, .. }
            | ZeroExtend { operand, .. }
            | SignExtend { operand, .. } => pending.push(operand),
            BvAdd { lhs, rhs, .. }
            | BvSub { lhs, rhs, .. }
            | BvAnd { lhs, rhs, .. }
            | BvOr { lhs, rhs, .. }
            | BvXor { lhs, rhs, .. }
            | BvShl { lhs, rhs, .. }
            | BvLshr { lhs, rhs, .. }
            | BvAshr { lhs, rhs, .. }
            | BvSlt { lhs, rhs, .. }
            | BvUlt { lhs, rhs, .. }
            | Eq { lhs, rhs }
            | And { lhs, rhs }
            | Or { lhs, rhs } => {
                pending.push(rhs);
                pending.push(lhs);
            }
            Ite {
                cond,
                then_expr,
                else_expr,
            } => {
                pending.push(else_expr);
                pending.push(then_expr);
                pending.push(cond);
            }
            // Constructors outside this owner's domain always stay named.
            _ => return true,
        }
    }
    false
}

/// `expr` with every name bound in `env` replaced by its term. Only the
/// constructors this owner builds are admitted.
fn substitute(expr: &E, env: &HashMap<String, E>) -> Result<E, String> {
    use E::*;
    let sub = |e: &E| substitute(e, env);
    Ok(match expr {
        Var { name, .. } => env.get(name).cloned().unwrap_or_else(|| expr.clone()),
        BvConst { .. } | BoolConst(_) => expr.clone(),
        BvNeg { operand, .. } => sub(operand)?.bvneg(),
        Not { operand } => sub(operand)?.not_expr(),
        Extract {
            high, low, operand, ..
        } => sub(operand)?.extract(*high, *low),
        ZeroExtend {
            operand,
            extra_bits,
            ..
        } => sub(operand)?.zero_ext(*extra_bits),
        SignExtend {
            operand,
            extra_bits,
            ..
        } => sub(operand)?.sign_ext(*extra_bits),
        BvAdd { lhs, rhs, .. } => sub(lhs)?.bvadd(sub(rhs)?),
        BvSub { lhs, rhs, .. } => sub(lhs)?.bvsub(sub(rhs)?),
        BvAnd { lhs, rhs, .. } => sub(lhs)?.bvand(sub(rhs)?),
        BvOr { lhs, rhs, .. } => sub(lhs)?.bvor(sub(rhs)?),
        BvXor { lhs, rhs, .. } => sub(lhs)?.bvxor(sub(rhs)?),
        BvShl { lhs, rhs, .. } => sub(lhs)?.bvshl(sub(rhs)?),
        BvLshr { lhs, rhs, .. } => sub(lhs)?.bvlshr(sub(rhs)?),
        BvAshr { lhs, rhs, .. } => sub(lhs)?.bvashr(sub(rhs)?),
        BvSlt { lhs, rhs, .. } => sub(lhs)?.bvslt(sub(rhs)?),
        BvUlt { lhs, rhs, .. } => sub(lhs)?.bvult(sub(rhs)?),
        Eq { lhs, rhs } => sub(lhs)?.eq_expr(sub(rhs)?),
        And { lhs, rhs } => sub(lhs)?.and_expr(sub(rhs)?),
        Or { lhs, rhs } => sub(lhs)?.or_expr(sub(rhs)?),
        Ite {
            cond,
            then_expr,
            else_expr,
        } => E::ite(sub(cond)?, sub(then_expr)?, sub(else_expr)?),
        other => return Err(format!("unexpected term {other}")),
    })
}

/// Assemble the obligation. Each side's returned value is one named
/// definition (so the two sides are never one term); every other definition
/// is written inline into its uses unless its expanded term exceeds
/// [`INLINE_LIMIT`], when it stays a named premise `(= name expr)`. Premises
/// are stored so the serialized conjunction lists them in definition order.
/// The source's definedness, when it does not always hold, is the one premise
/// that is not a definition: the domain the theorem quantifies over, placed
/// last (innermost) beside the negated claim. The concrete check has already
/// found an input inside it, so the premises are satisfiable.
fn build_obligation(
    defs: &Defs,
    source_observed: E,
    machine_observed: E,
    observed: [&E; 2],
    domain: Option<&E>,
) -> Result<ProofObligation, String> {
    let keep: HashSet<String> = observed
        .iter()
        .flat_map(|term| match term {
            E::Var { name, .. } => Some(name.clone()),
            _ => None,
        })
        .collect();
    let mut env: HashMap<String, E> = HashMap::new();
    let mut premises: Vec<(String, u32, E)> = Vec::new();
    let free: HashSet<String> = defs.inputs.iter().map(|(name, _)| name.clone()).collect();
    let mut named: HashSet<String> = HashSet::new();
    for definition in &defs.definitions {
        if free.contains(&definition.name)
            || named.contains(&definition.name)
            || env.contains_key(&definition.name)
        {
            return Err(format!("{} is declared twice", definition.name));
        }
        if definition.expr.try_bv_width().ok() != Some(definition.width) {
            return Err(format!("{} is defined at another width", definition.name));
        }
        for name in definition.expr.free_vars() {
            if !free.contains(&name) && !named.contains(&name) && !env.contains_key(&name) {
                return Err(format!(
                    "{} uses {name} before its definition",
                    definition.name
                ));
            }
        }
        let term = substitute(&definition.expr, &env)?;
        if keep.contains(&definition.name) || exceeds_inline_limit(&term) {
            named.insert(definition.name.clone());
            premises.push((definition.name.clone(), definition.width, term));
        } else {
            env.insert(definition.name.clone(), term);
        }
    }
    let source_observed = substitute(&source_observed, &env)?;
    let machine_observed = substitute(&machine_observed, &env)?;
    let domain = domain.map(|term| substitute(term, &env)).transpose()?;
    let used: HashSet<String> = premises
        .iter()
        .flat_map(|(_, _, term)| term.free_vars())
        .chain(source_observed.free_vars())
        .chain(machine_observed.free_vars())
        .chain(domain.iter().flat_map(E::free_vars))
        .collect();
    for name in &used {
        if !free.contains(name) && !named.contains(name) {
            return Err(format!("the theorem uses undeclared {name}"));
        }
    }
    let mut inputs: Vec<(String, u32)> = defs
        .inputs
        .iter()
        .filter(|(name, _)| used.contains(name))
        .cloned()
        .collect();
    inputs.extend(
        premises
            .iter()
            .map(|(name, width, _)| (name.clone(), *width)),
    );
    if source_observed.try_bv_width().ok() != machine_observed.try_bv_width().ok() {
        return Err("the source and machine observables have different widths".into());
    }
    if source_observed == machine_observed {
        return Err("the two observables are one term".into());
    }
    let preconditions = domain
        .into_iter()
        .chain(
            premises
                .into_iter()
                .rev()
                .map(|(name, width, term)| E::var(name, width).eq_expr(term)),
        )
        .collect();
    Ok(ProofObligation {
        name: A64_BODY_OBLIGATION_NAME.into(),
        trust_ir_expr: source_observed,
        aarch64_expr: machine_observed,
        inputs,
        preconditions,
        fp_inputs: Vec::new(),
        category: Some(TransvalCheckKind::InstructionLowering),
        machine_side_provenance: MachineSideProvenance::StaticDb,
    })
}

/// Concrete inputs the refutation check evaluates: corner values of every
/// width the domain uses and the source's constants (`corners`), alone or
/// with a perturbed low byte, and a fixed pseudo-random stream.
fn sample_value(sample: usize, input: usize, state: &mut u64, corners: &[u64]) -> u64 {
    let random = {
        // xorshift64*: deterministic, so a refusal is reproducible.
        *state ^= *state >> 12;
        *state ^= *state << 25;
        *state ^= *state >> 27;
        state.wrapping_mul(0x2545_f491_4f6c_dd1d)
    };
    let corner = corners[(random as usize) % corners.len()];
    match (sample + input * 7) % 4 {
        0 | 1 => corner,
        2 => random,
        _ => corner ^ (random & 0xff),
    }
}

/// Corner values of every width the domain uses.
const CORNERS: [u64; 22] = [
    0,
    1,
    2,
    3,
    5,
    7,
    31,
    32,
    33,
    63,
    64,
    0x7f,
    0x80,
    0xff,
    0x7fff_ffff,
    0x8000_0000,
    0xffff_ffff,
    0x1_0000_0000,
    0x7fff_ffff_ffff_ffff,
    0x8000_0000_0000_0000,
    u64::MAX,
    u64::MAX - 1,
];

const REFUTATION_SAMPLES: usize = 1024;

/// Evaluate both gated DAGs on fixed inputs. A sample on which the source is
/// defined and the two returned values differ is a definite mismatch;
/// agreement grants nothing (only replay of the theorem can).
///
/// The source's definedness has two encodings: the one-bit flag evaluated
/// here and the Boolean domain premise the theorem quantifies over. Every
/// sample also evaluates the premise, and one on which the two differ (or on
/// which the premise cannot be evaluated) refuses the theorem as a
/// construction defect: a premise narrower than the flag would let the
/// theorem skip inputs on which the source is defined.
fn concrete_refutation(
    defs: &Defs,
    constants: &[u64],
    source_observed: &E,
    machine_result: &E,
    defined: &E,
    domain: Option<&E>,
) -> Result<(), A64BodyRefusal> {
    let value = |expr: &E, env: &HashMap<String, u64>| -> Option<u64> {
        match expr.try_eval(env).ok()? {
            crate::smt::EvalResult::Bv(value) => Some(value),
            crate::smt::EvalResult::Bool(value) => Some(u64::from(value)),
            _ => None,
        }
    };
    let mut corners = CORNERS.to_vec();
    corners.extend_from_slice(constants);
    corners.sort_unstable();
    corners.dedup();
    let mut state = 0x9e37_79b9_7f4a_7c15u64;
    let mut defined_samples = 0usize;
    for sample in 0..REFUTATION_SAMPLES {
        let mut env: HashMap<String, u64> = HashMap::new();
        for (input, (name, width)) in defs.inputs.iter().enumerate() {
            let raw = if sample == 0 {
                0
            } else if sample == 1 {
                u64::MAX
            } else {
                sample_value(sample, input, &mut state, &corners)
            };
            env.insert(name.clone(), crate::smt::mask(raw, *width));
        }
        let mut complete = true;
        for definition in &defs.definitions {
            let Some(result) = value(&definition.expr, &env) else {
                complete = false;
                break;
            };
            env.insert(definition.name.clone(), result);
        }
        if !complete {
            // The evaluator does not model some term; no claim either way.
            return Ok(());
        }
        let (Some(source), Some(machine), Some(defined)) = (
            value(source_observed, &env),
            value(machine_result, &env),
            value(defined, &env),
        ) else {
            return Ok(());
        };
        let premise = match domain {
            None => Some(1),
            Some(domain) => value(domain, &env),
        };
        if premise != Some(defined) {
            return Err(unsupported(A64BodyUnsupported::Construction(format!(
                "the domain premise ({premise:?}) and the definedness flag ({defined}) differ \
                 on a sample"
            ))));
        }
        defined_samples += usize::from(defined == 1);
        if defined == 1 && source != machine {
            let mut inputs: Vec<String> = defs
                .inputs
                .iter()
                .filter(|(name, _)| name.starts_with('e'))
                .map(|(name, _)| format!("{name}={:#x}", env[name]))
                .collect();
            inputs.sort();
            return Err(mismatch(A64BodyMismatch::ReturnValue {
                witness: format!(
                    "at {} the source returns {source:#x} and the machine {machine:#x}",
                    inputs.join(" ")
                ),
            }));
        }
    }
    if defined_samples == 0 {
        return Err(unsupported(A64BodyUnsupported::NeverDefined));
    }
    Ok(())
}
