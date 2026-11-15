// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! Source-bound AArch64 scalar-cell caller: one whole-call theorem per
//! function, stated under the AAPCS64 callee contract (ruling
//! `LD-89`, `docs/decision-record.md`).
//!
//! **Domain.** A Linux AArch64 C caller whose original TrustIR and retained
//! LIR [`super::check_aarch64_scalar_cell_source`] binds to one ordered byte
//! contract: F32 or F64 parameters and result, one escaped stack cell of that
//! type, and direct calls `void S(T *, T)` to declared, bodyless C externals.
//! The machine function is the final allocated chain the scalar-cell
//! correspondence checker ([`super::check_aarch64_scalar_cell_frame`]) admits.
//! That checker is an ADMISSION FILTER here: its acceptance decides only that
//! a theorem is built, never that a row is credited. Production admits only
//! the qualified domain, exactly one call and at most two parameters
//! (`QUALIFIED_CALLS`, `QUALIFIED_PARAMETERS`); the translator is general.
//!
//! **Theorem.** Over free inputs `entry_sp`, the entry value `e_x{r}` of every
//! X register read before it is written, both 64-bit halves `e_v{r}_lo` and
//! `e_v{r}_hi` of every SIMD&FP register read before it is written, an
//! arbitrary byte memory `entry_memory`, the cell bytes `d{c}_{hex(S)}` call
//! `c` to symbol `S` leaves, and the values `k{c}_*` it leaves in
//! caller-saved state, under the premises `entry_sp & 15 = 0` and
//! `entry_sp >= STACK_WINDOW_BYTES`, the conjunction of:
//!
//! ```text
//! C1_c  the low |T| bytes of V0 at call c       = the source's argument bytes
//! C2_c  X0 at call c (c >= 1)                   = X0 at call 0
//! C3_c  the |T| bytes at X0_0 in memory at c    = the source's cell bytes
//! C4_c  SP at call c                            is 16-byte aligned
//! C5_c  SP_c <= X0_0; for c = 0 also X0_0 <= entry_sp - |T|, X0_0 aligned
//!       to |T|, entry_sp - STACK_WINDOW_BYTES <= SP_0
//! C12_c the 16 bytes at X29 at call c           = e_x29, e_x30 (frame record)
//! C6_r  every memory access r lies at or above its SP floor and below
//!       entry_sp, and at or above SP at every earlier call
//! C6_s  every SP value written lies in [entry_sp - STACK_WINDOW_BYTES,
//!       entry_sp] and is 16-byte aligned
//! C7    the low |T| bytes of V0 at RET          = the source's result bytes
//! C8    SP at RET = entry_sp;  C9  X30 at RET = e_x30
//! C10   X_r at RET = e_x{r} for every r in 19..=29 a row writes
//! C11   V_r[63:0] at RET = e_v{r}_lo for every r in 8..=15 a row writes
//! CB    for every B: word(B) + the displacement its operand encodes = the
//!       start word of the next laid-out block
//! ```
//!
//! **Walk.** The theorem interprets the rows of the laid-out blocks in
//! `block_order`, one word per non-pseudo row ([`laid_out_rows`]): the fetch
//! order of straight-line code, built from the layout alone and never by
//! following a branch. Every row but `B`, `BL` and `RET` moves to the next
//! word (Arm ARM); `BL` returns to the next word (callee contract item 1);
//! `RET` ends the walk; a `B` must be the last row of its block and lands at
//! `word + displacement`, which CB states equals the next laid-out block's
//! start, the word the walk continues at. That start is the layout's, so a
//! displacement or `Block` target that lands anywhere else falsifies CB (a
//! closed conjunct). The admission filter's chain walk, which follows the
//! branch, also refuses such a `B` first in production; the theorem does not
//! rely on it.
//!
//! The source side is the checked contract's bytes: parameter `i` is the low
//! `|T|` bytes of `e_v{i}_lo` (the verify-owned AAPCS64 float argument
//! table), a constant is its bits, and a call result is the shared `d` input
//! named by the source's callee. Every machine row is translated operand by
//! operand from the allocated `MachInst` the encoder turns into its word
//! (Arm ARM DDI 0487); memory is one inline store chain over the nullary
//! array `entry_memory` (no array equality, no other uninterpreted function).
//! A call stores `d{c}_{hex(S)}` at the X0 it receives, clobbers X0-X18, X30,
//! V0-V7, V16-V31 and bits 127:64 of V8-V15 with fresh inputs, and keeps
//! everything else. Every definition is written inline; a conjunct that
//! construction makes an identity is dropped. An 8-byte load is spelled as
//! its two 4-byte halves and a 64-bit equation over one as two 32-bit
//! equations (the same bytes and the same claim; see [`load`]). The theorem
//! is replayed in parts ([`SourceBoundScalarCellCaller::parts`]).
//!
//! **Credit.** Construction is not discharge. Only an AY proof of the exact
//! theorem that Clean independently replays credits anything
//! ([`crate::source_bound_replay`]), and then only the frame/SP arithmetic,
//! cell address, argument copy, constant, call and chain-branch rows whose
//! semantics the theorem genuinely uses: for each such row the constructor
//! rebuilds the theorem with that row's stated value changed (`x ^ 1`), and
//! the row is credited only if a concrete sample of the inputs then
//! falsifies the theorem. The check can only remove credit. A function with
//! no load-bearing frame, address or call row has no owner
//! ([`ScalarCellCallerRefusal::NoCoveredRow`]). Memory rows keep their own
//! Formal-only bound-memory route and `RET` is covered elsewhere: the theorem
//! interprets both and credits neither.
//!
//! **Trusted.** The AAPCS64 callee contract and environment premises of the
//! ruling; this translator (each admitted row's Arm ARM meaning, including
//! `NeonOrrV` and `FmovGprFpr`, and the shared memory-access operand reading
//! [`crate::aarch64_memory_effect::memory_access`]); the verify-owned AAPCS64
//! float argument and result table; the word layout ([`layout`]: the encoder
//! emits the rows of the laid-out blocks in `block_order`, one word per
//! non-pseudo row) and the encoder's `B` field (an `Imm` displacement in
//! words as `imm26`, a `Block` target resolved to its block's start word);
//! the positional pairing of machine calls with source calls
//! by symbol (callee identity, order and count are checked here in Rust; the
//! theorem refutes a mismatch only where the call's result is observed); the
//! TrustIR/LIR contract interpreter; the encoder's `BL` fixup into
//! `R_AARCH64_CALL26`; ENC-5's binding of words to rows; the SMT-LIB
//! serializer. Linux AArch64 only (`aarch64-unknown-linux-gnu`); the source
//! check refuses every other triple.

use std::collections::{BTreeSet, HashMap};

use trust_cg_ir::regs::SpecialReg;
use trust_cg_ir::{
    AArch64Opcode as M, InstFlags, InstId, MachFunction, MachInst, MachOperand as O,
};
use trust_cg_lower::Function;

use super::cell_source::values::Contract;
use super::output_memory::Byte;
use super::{CheckedAarch64ScalarCellSource, ScalarCellFrameError, ScalarCellSourceError};
use crate::aarch64_memory_effect::{AccessForm, memory_access};
use crate::aarch64_pair_memory_proofs::PairMode;
use crate::lowering_proof::{MachineSideProvenance, ProofObligation, TransvalCheckKind};
use crate::memory_proofs::memory_sort;
use crate::proof_database::ProofCategory;
use crate::smt::SmtExpr as E;

/// Name of the whole-call theorem. The certificate text carries it.
pub const SCALAR_CELL_CALLER_OBLIGATION_NAME: &str =
    "Source-bound AArch64 scalar-cell caller: whole-call theorem under the AAPCS64 callee contract";

/// Reason of every covered row when no independently checked proof of the
/// whole-call theorem exists. Such rows are never credited.
pub const SCALAR_CELL_CALLER_NEEDS_REPLAY: &str =
    "source-bound AArch64 scalar-cell caller needs independently replayed proof";

/// Bytes below the entry SP the theorem lets the function use: every SP
/// value and every access must stay within them. Equal to the frame
/// lowering's probing bound (`trust_cg_codegen::frame::STACK_PROBE_MAX_UNPROBED`;
/// a unit test pins the two together). The environment premise E2 of the
/// ruling is about exactly this window.
pub const STACK_WINDOW_BYTES: u64 = 1024;

/// Calls a production owner admits: the qualified domain. Every theorem of
/// the qualification run had exactly one call; the 2- and 16-call fixtures
/// exercise the translator in unit tests only.
const QUALIFIED_CALLS: usize = 1;

/// Parameters a production owner admits (the qualified families have one
/// or two).
const QUALIFIED_PARAMETERS: usize = 2;

/// Samples the concrete checks evaluate per theorem.
const SAMPLES: usize = 64;

/// What a credited row does in the function. The theorem is one; the
/// category says what the row contributes.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CellRowRole {
    /// `SUB`/`ADD SP, SP, #imm`.
    StackAdjust,
    /// `ADD X29, SP, #imm`.
    FrameEstablish,
    /// `ADD`/`SUB Xd, Xn, #imm` that is neither of the above (the cell
    /// address).
    CellAddress,
    /// `MOV Xd, Xm`, `MOV Vd.16B, Vn.16B`, `FMOV Sd|Dd, Wn|Xn`.
    ArgumentCopy,
    /// `MOVZ`/`MOVN`/`MOVK`.
    Constant,
    /// `BL S`.
    Call,
    /// A chain `B`.
    Transfer,
}

impl CellRowRole {
    /// The proof category a credited row of this role is reported under.
    pub fn category(self) -> ProofCategory {
        match self {
            Self::StackAdjust | Self::FrameEstablish | Self::CellAddress => {
                ProofCategory::FrameLayout
            }
            Self::ArgumentCopy | Self::Call => ProofCategory::CallLowering,
            Self::Constant => ProofCategory::ConstantMaterialization,
            Self::Transfer => ProofCategory::Branch,
        }
    }

    /// Whether this role computes something (a frame, address or call row)
    /// rather than copying, materializing or transferring.
    fn computes(self) -> bool {
        matches!(
            self,
            Self::StackAdjust | Self::FrameEstablish | Self::CellAddress | Self::Call
        )
    }
}

/// Why no scalar-cell caller owner was built. Every refusal makes no claim:
/// the rows keep the verdicts they would have without this owner.
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
pub enum ScalarCellCallerRefusal {
    #[error("scalar-cell caller source: {0}")]
    Source(#[from] ScalarCellSourceError),
    #[error("scalar-cell caller admission filter: {0}")]
    Admission(ScalarCellFrameError),
    #[error("outside the qualified scalar-cell caller domain: {0}")]
    Domain(String),
    #[error("machine control is outside the scalar-cell caller's laid-out walk")]
    Control,
    #[error("row {inst:?} is outside the scalar-cell caller translator: {detail}")]
    Row { inst: InstId, detail: String },
    #[error("the whole-call theorem failed its construction check: {0}")]
    Construction(String),
    #[error("a concrete input falsifies the whole-call theorem: {0}")]
    Refuted(String),
    #[error("no frame, address or call row is load-bearing in the whole-call theorem")]
    NoCoveredRow,
}

/// Immutable binding of one exact (TrustIR, LIR, final allocated AArch64
/// function) triple to its whole-call theorem. No public constructor: only
/// [`source_bound_scalar_cell_caller`] builds one, and the value itself is
/// the replay capability ([`crate::source_bound_replay`]).
pub struct SourceBoundScalarCellCaller<'a> {
    source: CheckedAarch64ScalarCellSource<'a>,
    machine: &'a MachFunction,
    /// Rows a Valid replay credits, ascending, with their roles.
    covered: Vec<(InstId, CellRowRole)>,
    /// The statement: the whole-call theorem, never replayed itself.
    obligation: ProofObligation,
    /// The statement in parts, replayed in order (ruling
    /// `LD-91`).
    parts: Vec<ProofObligation>,
}

/// One part of a whole-call theorem stated in parts. Handed out only by its
/// built owner ([`SourceBoundScalarCellCaller::replay_parts`]); the value is
/// the replay capability of that one part.
pub struct ScalarCellCallerPart<'a> {
    obligation: &'a ProofObligation,
}

impl ScalarCellCallerPart<'_> {
    pub fn obligation(&self) -> &ProofObligation {
        self.obligation
    }
}

impl<'a> SourceBoundScalarCellCaller<'a> {
    pub fn source(&self) -> &CheckedAarch64ScalarCellSource<'a> {
        &self.source
    }

    pub fn machine(&self) -> &'a MachFunction {
        self.machine
    }

    /// The whole-call theorem (the statement). Construction is not
    /// discharge, and the statement is replayed only as its parts.
    pub fn obligation(&self) -> &ProofObligation {
        &self.obligation
    }

    /// The statement in parts, in replay order: the conjuncts that read no
    /// memory in groups of at most six, then one part per conjunct that
    /// does. Their conjunction is the statement ([`Self::check_parts`]).
    pub fn parts(&self) -> &[ProofObligation] {
        &self.parts
    }

    /// The parts as replay capabilities, in order.
    pub(crate) fn replay_parts(&self) -> impl Iterator<Item = ScalarCellCallerPart<'_>> {
        self.parts
            .iter()
            .map(|obligation| ScalarCellCallerPart { obligation })
    }

    /// The part inventory against the statement: the parts' conjuncts, in
    /// order, are exactly the statement's; every part keeps the statement's
    /// name prefix, category and provenance, carries premises only from the
    /// statement's and declares exactly the inputs it uses.
    pub fn check_parts(&self) -> Result<(), String> {
        check_parts(&self.obligation, &self.parts)
    }

    /// The rows a Valid replay credits, ascending.
    pub fn covered(&self) -> Vec<InstId> {
        self.covered.iter().map(|(id, _)| *id).collect()
    }

    /// Whether a Valid replay credits row `id`.
    pub fn covers(&self, id: InstId) -> bool {
        self.role(id).is_some()
    }

    /// The role of a covered row.
    pub fn role(&self, id: InstId) -> Option<CellRowRole> {
        self.covered
            .binary_search_by_key(&id, |(row, _)| *row)
            .ok()
            .map(|index| self.covered[index].1)
    }
}

/// The verdict a covered row receives from the whole-call theorem's replay:
/// `Valid` (an AY proof Clean independently accepted) credits Formal under
/// the theorem's name and the row's role category; a refutation or an
/// unknown fails the row; no independently checked proof leaves it
/// unverified ([`SCALAR_CELL_CALLER_NEEDS_REPLAY`]).
pub(crate) fn scalar_cell_row_result(
    obligation: &ProofObligation,
    role: CellRowRole,
    verdict: Option<&crate::verify::VerificationResult>,
    why: Option<&str>,
) -> crate::function_verifier::InstructionVerificationResult {
    use crate::function_verifier::InstructionVerificationResult as R;
    use crate::verify::VerificationResult as V;
    match verdict {
        Some(V::Valid) => R::Verified {
            proof_name: obligation.name.clone(),
            category: role.category(),
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
                Some(why) => format!("{SCALAR_CELL_CALLER_NEEDS_REPLAY} ({why})"),
                None => SCALAR_CELL_CALLER_NEEDS_REPLAY.into(),
            },
        },
    }
}

/// Build the owner: the source check, the admission filter, the qualified
/// domain, the theorem, its concrete sanity check and the per-row
/// load-bearing check. See the module documentation.
pub fn source_bound_scalar_cell_caller<'a>(
    module: &'a trust_ir::Module,
    lir: &'a Function,
    machine: &'a MachFunction,
) -> Result<SourceBoundScalarCellCaller<'a>, ScalarCellCallerRefusal> {
    let source = super::check_aarch64_scalar_cell_source(module, lir)?;
    // Judge the emitted function: arena rows no block lists are retired
    // (ruling LD-92).
    let emitted = emitted_view(machine);
    let machine_view = emitted.as_ref().unwrap_or(machine);
    super::cell_frame::checked(lir, machine_view).map_err(ScalarCellCallerRefusal::Admission)?;
    let contract = source.contract();
    if contract.calls.len() != QUALIFIED_CALLS || contract.parameters > QUALIFIED_PARAMETERS {
        return Err(ScalarCellCallerRefusal::Domain(format!(
            "{} call(s) and {} parameter(s); the qualified domain is {QUALIFIED_CALLS} call and \
             at most {QUALIFIED_PARAMETERS} parameters",
            contract.calls.len(),
            contract.parameters
        )));
    }
    let (obligation, covered) = theorem_and_credit(contract, machine_view)?;
    let parts = split_parts(&obligation)?;
    check_parts(&obligation, &parts).map_err(ScalarCellCallerRefusal::Construction)?;
    Ok(SourceBoundScalarCellCaller {
        source,
        machine,
        covered,
        obligation,
        parts,
    })
}

/// The function as it is emitted, or `None` when it already is: every
/// arena row that no block lists retired as an operand-free pseudo `NOP`.
/// The encoder emits exactly the rows the laid-out blocks list, in
/// `block_order` (`trust-cg-codegen` `pipeline.rs`), and ENC-5 binds every
/// emitted word to its row, so a row in no block is never emitted, executed
/// or credited (the verifier walks the blocks too). Passes that remove a row
/// from its block (`cse`, `dce`, ...) leave it in the arena, with whatever
/// operands it had, virtual registers included. Every row a block lists,
/// laid out or not, is judged unchanged.
fn emitted_view(machine: &MachFunction) -> Option<MachFunction> {
    let mut listed = vec![false; machine.insts.len()];
    for block in &machine.blocks {
        for id in &block.insts {
            if let Some(slot) = listed.get_mut(id.0 as usize) {
                *slot = true;
            }
        }
    }
    let retired = MachInst::new(M::Nop, Vec::new());
    let is_retired = |inst: &MachInst| {
        inst.opcode == M::Nop
            && inst.operands.is_empty()
            && inst.flags == retired.flags
            && inst.implicit_defs.is_empty()
            && inst.implicit_uses.is_empty()
    };
    let orphans: Vec<usize> = listed
        .iter()
        .enumerate()
        .filter(|(index, listed)| !**listed && !is_retired(&machine.insts[*index]))
        .map(|(index, _)| index)
        .collect();
    if orphans.is_empty() {
        return None;
    }
    let mut view = machine.clone();
    for index in orphans {
        view.insts[index] = retired.clone();
    }
    Some(view)
}

/// Which step of the admission filter's layout check refuses `machine`, and
/// the rows that make it refuse (diagnostics under `solve-trace`; grants and
/// withholds nothing).
pub(crate) fn admission_layout_diagnosis(lir: &Function, machine: &MachFunction) -> String {
    let emitted = emitted_view(machine);
    let machine = emitted.as_ref().unwrap_or(machine);
    if super::linear::source_view(lir).is_none() {
        return "the LIR is not one chain".into();
    }
    let chain = match super::linear::machine_chain(machine) {
        Ok(chain) => chain,
        Err(refusal) => {
            let refusal = match refusal {
                super::ControlRefusal::Shape => "shape".to_owned(),
                super::ControlRefusal::Branch(mismatch) => format!("branch: {mismatch}"),
            };
            return format!(
                "machine chain: {refusal}; block_order={:?}; blocks={:?}",
                machine.block_order,
                machine
                    .blocks
                    .iter()
                    .map(|block| (&block.insts, &block.preds, &block.succs))
                    .collect::<Vec<_>>()
            );
        }
    };
    let unowned: Vec<String> = machine
        .insts
        .iter()
        .enumerate()
        .filter(|(index, inst)| {
            !chain.live.contains(&InstId(*index as u32))
                && !(super::cell_frame::inert(inst, machine.next_vreg)
                    && inst.implicit_uses.is_empty())
                && !super::linear::inactive_branch_tombstone(inst, machine)
        })
        .map(|(index, inst)| format!("{index}:{inst:?}"))
        .collect();
    let duplicated = chain.live.len()
        != chain
            .live
            .iter()
            .collect::<std::collections::BTreeSet<_>>()
            .len();
    format!(
        "unowned rows {unowned:?}; duplicated live row: {duplicated}; block_order={:?}",
        machine.block_order
    )
}

// Reuse the exact complete-goal/premise/input inventory contract shared with
// the actual defined-call trace. The old statement label and opaque input
// spelling stay unchanged, as do its numerical grouping limits.
fn split_parts(
    statement: &ProofObligation,
) -> Result<Vec<ProofObligation>, ScalarCellCallerRefusal> {
    crate::conjunctive_obligations::split_parts(statement, SCALAR_CELL_CALLER_OBLIGATION_NAME)
        .map_err(ScalarCellCallerRefusal::Construction)
}
fn check_parts(statement: &ProofObligation, parts: &[ProofObligation]) -> Result<(), String> {
    crate::conjunctive_obligations::check_parts(
        statement,
        parts,
        SCALAR_CELL_CALLER_OBLIGATION_NAME,
        &["entry_memory"],
    )
}
#[cfg(test)]
use crate::conjunctive_obligations::conjuncts_of;

/// The theorem [`source_bound_scalar_cell_caller`] would build, WITHOUT the
/// admission filter (its chain walk, envelope and observation check), the
/// qualified-domain bound and the concrete sanity and credit checks, so a
/// machine function mutated past the Rust filter can be put to the solver
/// lane (the non-vacuity and mutation controls). Only the ownership rule is
/// kept, over the laid-out rows: every non-inert arena row is laid out once.
/// This is not an owner and grants nothing: the verifier never calls it, and
/// no replay path accepts its result.
pub fn diagnostic_scalar_cell_caller_obligation(
    module: &trust_ir::Module,
    lir: &Function,
    machine: &MachFunction,
) -> Result<ProofObligation, ScalarCellCallerRefusal> {
    let source = super::check_aarch64_scalar_cell_source(module, lir)?;
    if lir.name != machine.name {
        return Err(ScalarCellCallerRefusal::Construction(
            "the machine function is not the source's".into(),
        ));
    }
    let emitted = emitted_view(machine);
    let machine = emitted.as_ref().unwrap_or(machine);
    let live: Vec<InstId> = laid_out_rows(machine)?
        .into_iter()
        .map(|(id, _)| id)
        .collect();
    super::check_owned_instructions_with(machine, &live, false, |inst| {
        super::cell_frame::inert(inst, machine.next_vreg)
    })
    .ok_or(ScalarCellCallerRefusal::Control)?;
    Ok(build(source.contract(), machine, None, InitialMemory::Symbolic)?.obligation)
}

/// The theorem with the stated value of row `perturb` changed (`x ^ 1`), as
/// the load-bearing check builds it (tests: the solver-backed half of the
/// non-vacuity control). Grants nothing.
#[cfg(test)]
pub(crate) fn perturbed_obligation(
    module: &trust_ir::Module,
    lir: &Function,
    machine: &MachFunction,
    perturb: InstId,
) -> Result<ProofObligation, ScalarCellCallerRefusal> {
    let source = super::check_aarch64_scalar_cell_source(module, lir)?;
    Ok(build(
        source.contract(),
        machine,
        Some(perturb),
        InitialMemory::Symbolic,
    )?
    .obligation)
}

/// The rows the load-bearing check considers, with their roles (tests).
#[cfg(test)]
pub(crate) fn candidate_rows(
    module: &trust_ir::Module,
    lir: &Function,
    machine: &MachFunction,
) -> Result<Vec<(InstId, CellRowRole)>, ScalarCellCallerRefusal> {
    let source = super::check_aarch64_scalar_cell_source(module, lir)?;
    Ok(build(source.contract(), machine, None, InitialMemory::Symbolic)?.candidates)
}

/// Whether a concrete sample falsifies `obligation` with `entry_memory` a
/// constant array (tests: the solver-free half of the controls).
#[cfg(test)]
pub(crate) fn concretely_falsified(
    module: &trust_ir::Module,
    lir: &Function,
    machine: &MachFunction,
    perturb: Option<InstId>,
) -> Result<bool, ScalarCellCallerRefusal> {
    let source = super::check_aarch64_scalar_cell_source(module, lir)?;
    falsified(source.contract(), machine, perturb)
}

/// The part of the (possibly perturbed) statement that holds the first
/// conjunct a concrete sample falsifies, or `None` when no sample
/// falsifies it (tests: the solver-backed refutation controls put only this
/// part to AY). The machine function is taken as it is: no admission
/// filter.
#[cfg(test)]
pub(crate) fn falsified_part(
    module: &trust_ir::Module,
    lir: &Function,
    machine: &MachFunction,
    perturb: Option<InstId>,
) -> Result<Option<ProofObligation>, ScalarCellCallerRefusal> {
    let source = super::check_aarch64_scalar_cell_source(module, lir)?;
    let contract = source.contract();
    let Some(index) = first_falsified(contract, machine, perturb)? else {
        return Ok(None);
    };
    let statement = build(contract, machine, perturb, InitialMemory::Symbolic)?.obligation;
    let target = conjuncts_of(&statement.aarch64_expr)
        .get(index)
        .cloned()
        .ok_or_else(|| ScalarCellCallerRefusal::Construction("conjunct index".into()))?;
    Ok(split_parts(&statement)?
        .into_iter()
        .find(|part| conjuncts_of(&part.aarch64_expr).contains(&target)))
}

fn theorem_and_credit(
    contract: &Contract,
    machine: &MachFunction,
) -> Result<(ProofObligation, Vec<(InstId, CellRowRole)>), ScalarCellCallerRefusal> {
    let built = build(contract, machine, None, InitialMemory::Symbolic)?;
    if falsified(contract, machine, None)? {
        return Err(ScalarCellCallerRefusal::Refuted(
            "a sampled input with a constant initial memory".into(),
        ));
    }
    let mut covered = Vec::new();
    for (row, role) in &built.candidates {
        if falsified(contract, machine, Some(*row))? {
            covered.push((*row, *role));
        }
    }
    covered.sort_by_key(|(row, _)| *row);
    if !covered.iter().any(|(_, role)| role.computes()) {
        return Err(ScalarCellCallerRefusal::NoCoveredRow);
    }
    Ok((built.obligation, covered))
}

/// Whether some sample satisfies the premises and falsifies the theorem
/// (built with `perturb` applied) under a constant initial memory. Only the
/// sample stream varies between calls: it is fixed, so a verdict is
/// reproducible.
fn falsified(
    contract: &Contract,
    machine: &MachFunction,
    perturb: Option<InstId>,
) -> Result<bool, ScalarCellCallerRefusal> {
    Ok(first_falsified(contract, machine, perturb)?.is_some())
}

/// The index of the first conjunct some sample falsifies (see
/// [`falsified`]).
fn first_falsified(
    contract: &Contract,
    machine: &MachFunction,
    perturb: Option<InstId>,
) -> Result<Option<usize>, ScalarCellCallerRefusal> {
    let mut state = 0x9e37_79b9_7f4a_7c15u64;
    let mut next = || {
        state ^= state >> 12;
        state ^= state << 25;
        state ^= state >> 27;
        state.wrapping_mul(0x2545_f491_4f6c_dd1d)
    };
    for sample in 0..SAMPLES {
        let fill = (next() & 0xff) as u8;
        let built = build(contract, machine, perturb, InitialMemory::Constant(fill))?;
        let mut env: HashMap<String, u64> = HashMap::new();
        for (name, width) in &built.obligation.inputs {
            let raw = if name == "entry_sp" {
                // A legal entry SP: 16-byte aligned and above the window.
                let sp = match sample {
                    0 => 0x10_0000,
                    1 => !15u64,
                    _ => next() & !15,
                };
                sp.max(STACK_WINDOW_BYTES)
            } else {
                next()
            };
            env.insert(name.clone(), crate::smt::mask(raw, *width));
        }
        let holds = |term: &E| -> Result<bool, ScalarCellCallerRefusal> {
            match term.try_eval(&env) {
                Ok(crate::smt::EvalResult::Bool(value)) => Ok(value),
                other => Err(ScalarCellCallerRefusal::Construction(format!(
                    "a conjunct does not evaluate to a Boolean: {other:?}"
                ))),
            }
        };
        let mut premises = true;
        for premise in &built.obligation.preconditions {
            premises &= holds(premise)?;
        }
        if !premises {
            return Err(ScalarCellCallerRefusal::Construction(
                "a sampled entry SP violates the theorem's premises".into(),
            ));
        }
        for (index, conjunct) in built.conjuncts.iter().enumerate() {
            if !holds(conjunct)? {
                return Ok(Some(index));
            }
        }
    }
    Ok(None)
}

/// The initial memory a theorem is built over.
#[derive(Clone, Copy)]
enum InitialMemory {
    /// The nullary array `entry_memory` (the replayed theorem).
    Symbolic,
    /// A constant array of this byte (the concrete checks only).
    Constant(u8),
}

struct Built {
    obligation: ProofObligation,
    conjuncts: Vec<E>,
    candidates: Vec<(InstId, CellRowRole)>,
}

/// A register (or register half) as the walk knows it.
#[derive(Clone)]
enum Slot {
    /// The caller's value at entry: input `e_*`, created on first read.
    Entry,
    /// Left by call `c`: input `k{c}_*`, created on first read.
    Clobbered(usize),
    Value(E),
}

/// One call as the theorem observes it.
struct CallPoint {
    symbol: String,
    x0: E,
    v0_lo: E,
    sp: E,
    x29: E,
    memory: E,
}

/// The state `RET` observes: V0's low half, SP, X30, and every X19-X29 and
/// V8-V15 (low half) a row wrote, with the value it holds.
struct Returned {
    v0_lo: E,
    sp: E,
    x30: E,
    saved_x: Vec<(u8, E)>,
    saved_v: Vec<(u8, E)>,
}

/// One memory access as C6 bounds it.
struct Access {
    address: E,
    bytes: u64,
    floor: E,
    calls_before: usize,
}

struct Walk<'m> {
    machine: &'m MachFunction,
    width: u32,
    perturb: Option<InstId>,
    inputs: Vec<(String, u32)>,
    x: Vec<Slot>,
    v: Vec<[Slot; 2]>,
    sp: E,
    memory: StoreChain,
    calls: Vec<CallPoint>,
    accesses: Vec<Access>,
    sp_values: Vec<E>,
    written_x: BTreeSet<u8>,
    written_v_lo: BTreeSet<u8>,
    transfers: Vec<E>,
    candidates: Vec<(InstId, CellRowRole)>,
    returned: Option<Returned>,
}

/// A 64-bit general-purpose operand of `ADD`/`SUB` (immediate): register 31
/// is SP there, spelled `Special(SP)` or the `SP` register.
#[derive(Clone, Copy, PartialEq, Eq)]
enum AddressReg {
    X(u8),
    Sp,
}

fn address_reg(operand: &O) -> Option<AddressReg> {
    match operand {
        O::PReg(reg) if reg.encoding() <= 30 => Some(AddressReg::X(reg.encoding() as u8)),
        O::PReg(reg) if reg.encoding() == 31 => Some(AddressReg::Sp),
        O::Special(SpecialReg::SP) => Some(AddressReg::Sp),
        _ => None,
    }
}

/// A general-purpose register of a move-wide, `MOV` (register) or `FMOV`
/// (general) operand: X0-X30 (64) or W0-W30 (32). Register 31 is the zero
/// register there; it is admitted only where `zero` allows it.
fn general_reg(operand: &O, zero: bool) -> Option<(Option<u8>, u32)> {
    match operand {
        O::PReg(reg) => match reg.encoding() {
            n @ 0..=30 => Some((Some(n as u8), 64)),
            n @ 32..=62 => Some((Some((n - 32) as u8), 32)),
            160 if zero => Some((None, 64)),
            161 if zero => Some((None, 32)),
            _ => None,
        },
        O::Special(SpecialReg::XZR) if zero => Some((None, 64)),
        O::Special(SpecialReg::WZR) if zero => Some((None, 32)),
        _ => None,
    }
}

/// An S or D register operand: (V register number, bytes).
fn scalar_fp_reg(operand: &O) -> Option<(u8, u32)> {
    match operand {
        O::PReg(reg) => match reg.encoding() {
            n @ 96..=127 => Some(((n - 96) as u8, 8)),
            n @ 128..=159 => Some(((n - 128) as u8, 4)),
            _ => None,
        },
        _ => None,
    }
}

/// What `MOV Vd.16B, Vn.16B, Vm.16B` (`NeonOrrV [Vd, Vn, Vm, Imm(1)]`) names:
/// the three V register numbers. Only the S/D-class spelling the pipeline
/// emits and the `.16B` arrangement selector `Imm(1)` (Q = 1) are admitted;
/// the encoder maps each register by `preg_hw`.
pub(crate) fn neon_orr_reading(inst: &MachInst) -> Option<[u8; 3]> {
    let [d, n, m, O::Imm(1)] = inst.operands.as_slice() else {
        return None;
    };
    Some([
        scalar_fp_reg(d)?.0,
        scalar_fp_reg(n)?.0,
        scalar_fp_reg(m)?.0,
    ])
}

/// What `FMOV Sd, Wn` / `FMOV Dd, Xn` (`FmovGprFpr`) names: (V register,
/// general register, bytes). The widths must agree; the zero register is
/// refused.
pub(crate) fn fmov_general_reading(inst: &MachInst) -> Option<(u8, u8, u32)> {
    let [d, n] = inst.operands.as_slice() else {
        return None;
    };
    let (vd, bytes) = scalar_fp_reg(d)?;
    let (Some(rn), width) = general_reg(n, false)? else {
        return None;
    };
    (width == bytes * 8).then_some((vd, rn, bytes))
}

/// Flags and implicit operands of an ordinary value or memory row: the
/// opcode's own flags, optionally marked as call-argument setup, and no
/// implicit operands.
fn ordinary(inst: &MachInst) -> bool {
    let own = MachInst::new(inst.opcode, Vec::new()).flags;
    inst.implicit_defs.is_empty()
        && inst.implicit_uses.is_empty()
        && (inst.flags == own || inst.flags == (own | InstFlags::IS_CALL_ARG_SETUP))
}

/// AAPCS64 caller-saved registers (any view): X0-X18, X30, and V0-V7,
/// V16-V31 in every SIMD&FP view.
fn caller_saved(reg: trust_cg_ir::regs::PReg) -> bool {
    match reg.encoding() {
        0..=18 | 30 | 32..=50 | 62 => true,
        n @ (64..=95 | 96..=127 | 128..=159 | 165..=196) => {
            let base = match n {
                64..=95 => 64,
                96..=127 => 96,
                128..=159 => 128,
                _ => 165,
            };
            matches!(n - base, 0..=7 | 16..=31)
        }
        _ => false,
    }
}

/// `base + displacement`, or `base` itself for a zero displacement (the
/// address an access names with an immediate of 0).
fn offset(base: E, displacement: i64) -> E {
    if displacement == 0 {
        base
    } else {
        base.bvadd(E::bv_const(displacement as u64, 64))
    }
}

/// The address of byte `index` of an access at `address`: `address` itself
/// for byte 0, else `address + index`, the spelling
/// [`crate::memory_proofs::encode_store_le`] gives a stored byte, so a load
/// of a stored byte names the same address term.
fn byte_address(address: &E, index: u32) -> E {
    if index == 0 {
        address.clone()
    } else {
        address.clone().bvadd(E::bv_const(u64::from(index), 64))
    }
}

/// Bytes `from..from + count` at `address`, assembled little-endian as
/// [`crate::memory_proofs::encode_load_le`] assembles them (each byte
/// zero-extended, shifted to its place and OR-ed in).
fn load_bytes(memory: &E, address: &E, from: u32, count: u32) -> E {
    let width = 8 * count;
    let mut value: Option<E> = None;
    for k in 0..count {
        let byte = E::select(memory.clone(), byte_address(address, from + k));
        let byte = if width > 8 {
            byte.zero_ext(width - 8)
        } else {
            byte
        };
        let byte = if k == 0 {
            byte
        } else {
            byte.bvshl(E::bv_const(u64::from(8 * k), width))
        };
        value = Some(match value {
            None => byte,
            Some(low) => low.bvor(byte),
        });
    }
    value.expect("a load reads at least one byte")
}

/// A little-endian load of `bytes` bytes at `address`. An 8-byte load is
/// spelled as the concatenation of its two 4-byte halves: the same eight
/// bytes in the same order (`load8(a) = load4(a + 4) ++ load4(a)`), so the
/// claim is unchanged; AY's strict certification on this host rejects its
/// own proof of one 8-byte load through the frame's store chain and accepts
/// the halves (ruling LD-91).
fn load(memory: &E, address: &E, bytes: u32) -> E {
    if bytes == 8 {
        load_bytes(memory, address, 4, 4).concat(load_bytes(memory, address, 0, 4))
    } else {
        load_bytes(memory, address, 0, bytes)
    }
}

/// Memory as the walk builds it: the initial array and the byte stores made
/// since, in order. A store to a byte address term already stored to
/// replaces that earlier store (`store(store(m, a, x) .., a, y)` reads as
/// `store(.. m .., a, y)` at every index, whatever stores lie between: the
/// array read-over-write identity), so the chain the theorem states holds no
/// overwritten byte; AY's strict certification on this host rejects its own
/// proofs through the longer chain (ruling
/// LD-91).
#[derive(Clone)]
struct StoreChain {
    initial: E,
    stores: Vec<(E, E)>,
}

impl StoreChain {
    /// Store `bytes` little-endian bytes of `value` at `address`
    /// ([`crate::memory_proofs::encode_store_le`]'s byte decomposition).
    fn store(&mut self, address: &E, value: &E, bytes: u32) {
        for i in 0..bytes {
            let at = byte_address(address, i);
            let byte = if bytes == 1 {
                value.clone()
            } else {
                value.clone().extract(8 * i + 7, 8 * i)
            };
            self.stores.retain(|(stored, _)| *stored != at);
            self.stores.push((at, byte));
        }
    }

    /// The array term.
    fn term(&self) -> E {
        self.stores
            .iter()
            .fold(self.initial.clone(), |memory, (address, byte)| {
                E::store(memory, address.clone(), byte.clone())
            })
    }
}

/// The equation `lhs = rhs`, stated as its two 32-bit halves when `lhs` is
/// such a concatenation (equivalent: two words are equal iff both halves
/// are), so that each half becomes its own part.
fn equations(lhs: E, rhs: E) -> Vec<E> {
    match &lhs {
        E::Concat { hi, lo, width: 64 } if lo.bv_width() == 32 => vec![
            (**lo).clone().eq_expr(rhs.clone().extract(31, 0)),
            (**hi).clone().eq_expr(rhs.extract(63, 32)),
        ],
        _ => vec![lhs.eq_expr(rhs)],
    }
}

/// The low `width` bits of a 64-bit term (the term itself at 64).
fn low_bits(term: E, width: u32) -> E {
    if width == 64 {
        term
    } else {
        term.extract(width - 1, 0)
    }
}

fn hex(symbol: &str) -> String {
    symbol.bytes().map(|byte| format!("{byte:02x}")).collect()
}

fn call_result_name(call: usize, symbol: &str) -> String {
    format!("d{call}_{}", hex(symbol))
}

impl<'m> Walk<'m> {
    fn input(&mut self, name: String, width: u32) -> E {
        if !self.inputs.iter().any(|(existing, _)| *existing == name) {
            self.inputs.push((name.clone(), width));
        }
        E::var(name, width)
    }

    fn row_value(&self, id: InstId, value: E) -> E {
        if self.perturb == Some(id) {
            let width = value.bv_width();
            value.bvxor(E::bv_const(1, width))
        } else {
            value
        }
    }

    fn read_x(&mut self, r: u8) -> E {
        match self.x[r as usize].clone() {
            Slot::Entry => self.input(format!("e_x{r}"), 64),
            Slot::Clobbered(c) => self.input(format!("k{c}_x{r}"), 64),
            Slot::Value(value) => value,
        }
    }

    fn read_v(&mut self, r: u8, half: usize) -> E {
        let suffix = if half == 0 { "lo" } else { "hi" };
        match self.v[r as usize][half].clone() {
            Slot::Entry => self.input(format!("e_v{r}_{suffix}"), 64),
            Slot::Clobbered(c) => self.input(format!("k{c}_v{r}_{suffix}"), 64),
            Slot::Value(value) => value,
        }
    }

    fn write_x(&mut self, id: InstId, r: u8, value: E) {
        let value = self.row_value(id, value);
        self.x[r as usize] = Slot::Value(value);
        self.written_x.insert(r);
    }

    fn write_sp(&mut self, id: InstId, value: E) {
        let value = self.row_value(id, value);
        self.sp = value.clone();
        self.sp_values.push(value);
    }

    fn write_v(&mut self, id: InstId, r: u8, lo: E, hi: E) {
        let lo = self.row_value(id, lo);
        let hi = self.row_value(id, hi);
        self.v[r as usize] = [Slot::Value(lo), Slot::Value(hi)];
        self.written_v_lo.insert(r);
    }

    fn read_address(&mut self, reg: AddressReg) -> E {
        match reg {
            AddressReg::X(r) => self.read_x(r),
            AddressReg::Sp => self.sp.clone(),
        }
    }

    fn refuse(id: InstId, detail: impl Into<String>) -> ScalarCellCallerRefusal {
        ScalarCellCallerRefusal::Row {
            inst: id,
            detail: detail.into(),
        }
    }

    fn step(
        &mut self,
        id: InstId,
        contract: &Contract,
        transfer: Option<Transfer>,
    ) -> Result<(), ScalarCellCallerRefusal> {
        let inst = &self.machine.insts[id.0 as usize];
        if super::cell_frame::inert(inst, self.machine.next_vreg) {
            return Ok(());
        }
        let refuse = |detail: &str| Err(Self::refuse(id, format!("{:?}: {detail}", inst.opcode)));
        if self.returned.is_some() {
            return refuse("follows RET");
        }
        match inst.opcode {
            M::AddRI | M::SubRI => {
                let [d, n, O::Imm(imm @ 0..=4095)] = inst.operands.as_slice() else {
                    return refuse("takes two X/SP registers and an imm12");
                };
                let (Some(d), Some(n)) = (address_reg(d), address_reg(n)) else {
                    return refuse("an operand is not X0-X30 or SP");
                };
                if !ordinary(inst) {
                    return refuse("flags or implicit operands");
                }
                let base = self.read_address(n);
                let constant = E::bv_const(*imm as u64, 64);
                let value = if inst.opcode == M::AddRI {
                    base.bvadd(constant)
                } else {
                    base.bvsub(constant)
                };
                let role = match d {
                    AddressReg::Sp => {
                        self.write_sp(id, value);
                        CellRowRole::StackAdjust
                    }
                    AddressReg::X(29) if n == AddressReg::Sp => {
                        self.write_x(id, 29, value);
                        CellRowRole::FrameEstablish
                    }
                    AddressReg::X(r) => {
                        self.write_x(id, r, value);
                        CellRowRole::CellAddress
                    }
                };
                self.candidates.push((id, role));
            }
            M::MOVXrr => {
                let [O::PReg(d), n] = inst.operands.as_slice() else {
                    return refuse("takes two registers");
                };
                let (Some((Some(d), 64)), Some((n, 64))) =
                    (general_reg(&O::PReg(*d), false), general_reg(n, true))
                else {
                    return refuse("operands are not X0-X30 (source: or XZR)");
                };
                if !ordinary(inst) {
                    return refuse("flags or implicit operands");
                }
                let value = match n {
                    Some(n) => self.read_x(n),
                    None => E::bv_const(0, 64),
                };
                self.write_x(id, d, value);
                self.candidates.push((id, CellRowRole::ArgumentCopy));
            }
            M::Movz | M::Movn | M::Movk => {
                let (d, imm, shift) = match inst.operands.as_slice() {
                    [d, O::Imm(imm)] => (d, *imm, 0),
                    [d, O::Imm(imm), O::Imm(shift)] => (d, *imm, *shift),
                    _ => return refuse("takes a register, an imm16 and a shift"),
                };
                let Some((Some(d), width)) = general_reg(d, false) else {
                    return refuse("destination is not X0-X30 or W0-W30");
                };
                // MOVZ/MOVN at shift 0 only (the frameless body owner's
                // admission); MOVK at any halfword of its width.
                let shift_ok = if inst.opcode == M::Movk {
                    shift % 16 == 0 && (0..i64::from(width)).contains(&shift)
                } else {
                    shift == 0
                };
                if !(0..=0xffff).contains(&imm) || !shift_ok || !ordinary(inst) {
                    return refuse("immediate, shift, flags or implicit operands");
                }
                let mask = crate::smt::mask(u64::MAX, width);
                let field = (imm as u64) << shift;
                let value = match inst.opcode {
                    M::Movz => E::bv_const(field, width),
                    M::Movn => E::bv_const(!field & mask, width),
                    _ => {
                        let old = self.read_x(d);
                        let old = if width == 64 { old } else { old.extract(31, 0) };
                        old.bvand(E::bv_const(!(0xffffu64 << shift) & mask, width))
                            .bvor(E::bv_const(field, width))
                    }
                };
                // A W write zero-extends into X.
                let value = if width == 64 {
                    value
                } else {
                    value.zero_ext(32)
                };
                self.write_x(id, d, value);
                self.candidates.push((id, CellRowRole::Constant));
            }
            M::FmovGprFpr => {
                let Some((vd, rn, bytes)) = fmov_general_reading(inst) else {
                    return refuse("takes Sd, Wn or Dd, Xn");
                };
                if !ordinary(inst) {
                    return refuse("flags or implicit operands");
                }
                // FMOV (general) writes the low |T| bytes and zeroes every
                // bit above them.
                let source = self.read_x(rn);
                let lo = if bytes == 8 {
                    source
                } else {
                    source.extract(31, 0).zero_ext(32)
                };
                self.write_v(id, vd, lo, E::bv_const(0, 64));
                self.candidates.push((id, CellRowRole::ArgumentCopy));
            }
            M::NeonOrrV => {
                let Some([vd, vn, vm]) = neon_orr_reading(inst) else {
                    return refuse("takes three S/D registers and the .16B selector Imm(1)");
                };
                if !ordinary(inst) {
                    return refuse("flags or implicit operands");
                }
                let lo = self.read_v(vn, 0).bvor(self.read_v(vm, 0));
                let hi = self.read_v(vn, 1).bvor(self.read_v(vm, 1));
                self.write_v(id, vd, lo, hi);
                self.candidates.push((id, CellRowRole::ArgumentCopy));
            }
            M::Bl => {
                let [O::Symbol(symbol)] = inst.operands.as_slice() else {
                    return refuse("takes one symbol");
                };
                let argument =
                    trust_cg_ir::regs::PReg::new(if self.width == 32 { 128 } else { 96 });
                if inst.flags != MachInst::new(M::Bl, Vec::new()).flags
                    || inst.implicit_uses != [trust_cg_ir::regs::PReg::new(0), argument]
                    || !inst.implicit_defs.iter().copied().all(caller_saved)
                {
                    return refuse("flags or implicit operands differ from (X0, S0|D0) -> void");
                }
                let call = self.calls.len();
                let Some(expected) = contract.calls.get(call) else {
                    return refuse("the source has no call at this position");
                };
                if *symbol != expected.name {
                    return refuse("the callee symbol differs from the source call's");
                }
                let point = CallPoint {
                    symbol: symbol.clone(),
                    x0: self.read_x(0),
                    v0_lo: self.read_v(0, 0),
                    sp: self.sp.clone(),
                    x29: self.read_x(29),
                    memory: self.memory.term(),
                };
                let bytes = self.width / 8;
                let result = self.input(call_result_name(call, symbol), self.width);
                let result = self.row_value(id, result);
                self.memory.store(&point.x0, &result, bytes);
                self.calls.push(point);
                for r in (0..=18).chain([30]) {
                    self.x[r] = Slot::Clobbered(call);
                }
                for (r, halves) in self.v.iter_mut().enumerate() {
                    if (8..=15).contains(&r) {
                        halves[1] = Slot::Clobbered(call);
                    } else {
                        *halves = [Slot::Clobbered(call), Slot::Clobbered(call)];
                    }
                }
                self.candidates.push((id, CellRowRole::Call));
            }
            M::B => {
                let Some(Transfer {
                    word,
                    displacement,
                    next,
                }) = transfer
                else {
                    return refuse(
                        "is not the last row of a laid-out block with a laid-out block after it",
                    );
                };
                if inst.flags != MachInst::new(M::B, Vec::new()).flags
                    || !inst.implicit_defs.is_empty()
                    || !inst.implicit_uses.is_empty()
                {
                    return refuse("flags or implicit operands");
                }
                // B: PC <- PC + displacement (in words). `next` is the
                // layout's word the walk continues at, never derived from the
                // displacement (CB).
                let pc = self.row_value(
                    id,
                    E::bv_const(word as u64, 64).bvadd(E::bv_const(displacement as u64, 64)),
                );
                self.transfers
                    .push(pc.eq_expr(E::bv_const(next as u64, 64)));
                self.candidates.push((id, CellRowRole::Transfer));
            }
            M::Ret => {
                let argument =
                    trust_cg_ir::regs::PReg::new(if self.width == 32 { 128 } else { 96 });
                if inst.operands != [O::PReg(trust_cg_ir::regs::X30)]
                    || inst.flags != MachInst::new(M::Ret, Vec::new()).flags
                    || !inst.implicit_defs.is_empty()
                    || inst.implicit_uses != [argument]
                {
                    return refuse("is not RET X30 with the scalar result's implicit use");
                }
                let v0 = self.read_v(0, 0);
                let x30 = self.read_x(30);
                let saved_x: Vec<u8> = self
                    .written_x
                    .iter()
                    .copied()
                    .filter(|r| (19..=29).contains(r))
                    .collect();
                let saved_x = saved_x.into_iter().map(|r| (r, self.read_x(r))).collect();
                let saved_v: Vec<u8> = self
                    .written_v_lo
                    .iter()
                    .copied()
                    .filter(|r| (8..=15).contains(r))
                    .collect();
                let saved_v = saved_v
                    .into_iter()
                    .map(|r| (r, self.read_v(r, 0)))
                    .collect();
                self.returned = Some(Returned {
                    v0_lo: v0,
                    sp: self.sp.clone(),
                    x30,
                    saved_x,
                    saved_v,
                });
            }
            _ => {
                let Some(access) = memory_access(inst) else {
                    return refuse("is not a row of the scalar-cell caller translator");
                };
                if !ordinary(inst) {
                    return refuse("flags or implicit operands");
                }
                self.memory_row(id, access)?;
            }
        }
        Ok(())
    }

    /// An X-pair access on SP or an S/D access on an X base, through the
    /// shared operand reading of [`crate::aarch64_memory_effect`].
    fn memory_row(
        &mut self,
        id: InstId,
        access: crate::aarch64_memory_effect::MemoryAccess,
    ) -> Result<(), ScalarCellCallerRefusal> {
        let lane0 = access.lane0_displacement();
        let writeback = access.writeback_displacement();
        let constant = |value: i64| E::bv_const(value as u64, 64);
        match access.form {
            AccessForm::Pair(mode) => {
                if access.simd || access.bytes != 8 || access.base != 31 {
                    return Err(Self::refuse(id, "a pair other than X registers on SP"));
                }
                let before = self.sp.clone();
                let first = offset(before.clone(), lane0);
                let second = first.clone().bvadd(constant(8));
                let after = match writeback {
                    Some(0) | None => None,
                    Some(delta) => Some(before.clone().bvadd(constant(delta))),
                };
                let floor = match mode {
                    PairMode::PreIndex => after.clone().unwrap_or_else(|| before.clone()),
                    PairMode::Offset | PairMode::PostIndex => before.clone(),
                };
                if access.load {
                    if access.zero.iter().any(|zero| *zero)
                        || access.transfer[0] == access.transfer[1]
                        || access.transfer.iter().any(|r| *r > 30)
                    {
                        return Err(Self::refuse(id, "an LDP into XZR or one register twice"));
                    }
                    let memory = self.memory.term();
                    let a = load(&memory, &first, 8);
                    let b = load(&memory, &second, 8);
                    self.write_x(id, access.transfer[0], a);
                    self.write_x(id, access.transfer[1], b);
                } else {
                    let mut values = Vec::new();
                    for lane in 0..2 {
                        values.push(if access.zero[lane] {
                            E::bv_const(0, 64)
                        } else if access.transfer[lane] <= 30 {
                            self.read_x(access.transfer[lane])
                        } else {
                            return Err(Self::refuse(id, "an STP of register 31 as data"));
                        });
                    }
                    self.memory.store(&first, &values[0], 8);
                    self.memory.store(&second, &values[1], 8);
                }
                self.accesses.push(Access {
                    address: first,
                    bytes: 16,
                    floor,
                    calls_before: self.calls.len(),
                });
                if let Some(after) = after {
                    self.write_sp(id, after);
                }
            }
            AccessForm::ScalarUnsigned | AccessForm::ScalarUnscaled => {
                if !access.simd
                    || !matches!(access.bytes, 4 | 8)
                    || access.base > 30
                    || writeback.is_some()
                    || access.extension != crate::aarch64_memory_effect::LoadExtension::Zero
                {
                    return Err(Self::refuse(
                        id,
                        "a scalar access other than S/D on an X base",
                    ));
                }
                let base = self.read_x(access.base);
                let address = offset(base, lane0);
                let register = access.transfer[0];
                if access.load {
                    let value = load(&self.memory.term(), &address, access.bytes);
                    let lo = if access.bytes == 8 {
                        value
                    } else {
                        value.zero_ext(32)
                    };
                    self.write_v(id, register, lo, E::bv_const(0, 64));
                } else {
                    let data = self.read_v(register, 0);
                    let data = if access.bytes == 8 {
                        data
                    } else {
                        data.extract(31, 0)
                    };
                    self.memory.store(&address, &data, access.bytes);
                }
                self.accesses.push(Access {
                    address,
                    bytes: u64::from(access.bytes),
                    floor: self.sp.clone(),
                    calls_before: self.calls.len(),
                });
            }
            _ => return Err(Self::refuse(id, "an unadmitted addressing form")),
        }
        Ok(())
    }
}

/// The word layout of every laid-out instruction (one word per non-pseudo
/// instruction, as the encoder emits) and of every laid-out block start.
/// Callers check that every block and row index is in range first
/// ([`laid_out_rows`]).
fn layout(machine: &MachFunction) -> (HashMap<InstId, i64>, HashMap<trust_cg_ir::BlockId, i64>) {
    let mut words = HashMap::new();
    let mut starts = HashMap::new();
    let mut word = 0i64;
    for block in &machine.block_order {
        starts.insert(*block, word);
        for id in &machine.blocks[block.0 as usize].insts {
            words.insert(*id, word);
            word += i64::from(!machine.insts[id.0 as usize].is_pseudo());
        }
    }
    (words, starts)
}

/// What the theorem states of a `B` (CB): the row's word, the displacement
/// its operand encodes, and the word the walk continues at. `next` is the
/// start of the next laid-out block, from the layout alone.
#[derive(Clone, Copy, Debug)]
struct Transfer {
    word: i64,
    displacement: i64,
    next: i64,
}

/// The rows the theorem interprets, in fetch order: every row of the
/// laid-out blocks in `block_order`, each laid out once, from the entry
/// block. A `B` is admitted only as the last row of its block with a
/// laid-out block after it, and carries its [`Transfer`]; its operand is an
/// `Imm` displacement in words or a laid-out `Block` target (the encoder
/// resolves it to that block's start). No branch is followed, so the walk
/// does not depend on any `B`'s operand: CB states where each lands.
fn laid_out_rows(
    machine: &MachFunction,
) -> Result<Vec<(InstId, Option<Transfer>)>, ScalarCellCallerRefusal> {
    use ScalarCellCallerRefusal::Control;
    if machine.block_order.first() != Some(&machine.entry) {
        return Err(Control);
    }
    let mut blocks_seen = BTreeSet::new();
    let mut rows_seen = BTreeSet::new();
    for block in &machine.block_order {
        let listed = machine.blocks.get(block.0 as usize).ok_or(Control)?;
        if !blocks_seen.insert(*block) {
            return Err(Control);
        }
        for id in &listed.insts {
            if machine.insts.get(id.0 as usize).is_none() || !rows_seen.insert(*id) {
                return Err(Control);
            }
        }
    }
    let (words, starts) = layout(machine);
    let mut rows = Vec::new();
    for (position, block) in machine.block_order.iter().enumerate() {
        let listed = &machine.blocks[block.0 as usize].insts;
        for (k, id) in listed.iter().enumerate() {
            let inst = &machine.insts[id.0 as usize];
            let transfer = if inst.opcode == M::B && k + 1 == listed.len() {
                let word = words[id];
                let displacement = match inst.operands.as_slice() {
                    [O::Imm(displacement)] => *displacement,
                    [O::Block(target)] => starts.get(target).ok_or(Control)? - word,
                    _ => return Err(Control),
                };
                let following = machine.block_order.get(position + 1).ok_or(Control)?;
                Some(Transfer {
                    word,
                    displacement,
                    next: starts[following],
                })
            } else {
                None
            };
            rows.push((*id, transfer));
        }
    }
    Ok(rows)
}

fn bytes_term(
    bytes: &[Byte],
    width: usize,
    sources: &mut dyn FnMut(&Byte) -> Option<(E, usize)>,
) -> Result<E, ScalarCellCallerRefusal> {
    // Each byte is (a 64-bit or narrower term, the byte's index in it), or a
    // constant. Consecutive bytes of one term at consecutive indices become
    // one extract; consecutive constants one constant.
    #[derive(Clone)]
    enum Piece {
        Slice { term: E, low: usize, count: usize },
        Constant { value: u64, count: usize },
    }
    let mut pieces: Vec<Piece> = Vec::new();
    for byte in bytes {
        let piece = match byte {
            Byte::Constant(value) => Piece::Constant {
                value: u64::from(*value),
                count: 1,
            },
            other => {
                let (term, index) = sources(other).ok_or_else(|| {
                    ScalarCellCallerRefusal::Construction(format!(
                        "the source contract names an unmodelled byte {other:?}"
                    ))
                })?;
                Piece::Slice {
                    term,
                    low: index,
                    count: 1,
                }
            }
        };
        match (pieces.last_mut(), piece) {
            (
                Some(Piece::Slice { term, low, count }),
                Piece::Slice {
                    term: next,
                    low: next_low,
                    ..
                },
            ) if *term == next && *low + *count == next_low => *count += 1,
            (Some(Piece::Constant { value, count }), Piece::Constant { value: next, .. }) => {
                *value |= next << (8 * *count);
                *count += 1;
            }
            (_, piece) => pieces.push(piece),
        }
    }
    let mut term: Option<E> = None;
    for piece in pieces {
        let part = match piece {
            Piece::Slice { term, low, count } => {
                let high = (8 * (low + count) - 1) as u32;
                let low = (8 * low) as u32;
                if low == 0 && high + 1 == term.bv_width() {
                    term
                } else {
                    term.extract(high, low)
                }
            }
            Piece::Constant { value, count } => E::bv_const(value, (8 * count) as u32),
        };
        // Bytes are listed least significant first.
        term = Some(match term {
            None => part,
            Some(low) => part.concat(low),
        });
    }
    let term = term.ok_or_else(|| ScalarCellCallerRefusal::Construction("no bytes".into()))?;
    if term.bv_width() as usize != 8 * width {
        return Err(ScalarCellCallerRefusal::Construction(
            "a source value has another width".into(),
        ));
    }
    Ok(term)
}

fn build(
    contract: &Contract,
    machine: &MachFunction,
    perturb: Option<InstId>,
    memory: InitialMemory,
) -> Result<Built, ScalarCellCallerRefusal> {
    let width = (contract.width * 8) as u32;
    let bytes = contract.width as u32;
    let rows = laid_out_rows(machine)?;
    let initial = match memory {
        InitialMemory::Symbolic => E::uf("entry_memory", Vec::new(), memory_sort()),
        InitialMemory::Constant(byte) => E::const_array(
            crate::smt::SmtSort::BitVec(64),
            E::bv_const(u64::from(byte), 8),
        ),
    };
    let mut walk = Walk {
        machine,
        width,
        perturb,
        inputs: Vec::new(),
        x: vec![Slot::Entry; 31],
        v: vec![[Slot::Entry, Slot::Entry]; 32],
        sp: E::var("entry_sp", 64),
        memory: StoreChain {
            initial,
            stores: Vec::new(),
        },
        calls: Vec::new(),
        accesses: Vec::new(),
        sp_values: Vec::new(),
        written_x: BTreeSet::new(),
        written_v_lo: BTreeSet::new(),
        transfers: Vec::new(),
        candidates: Vec::new(),
        returned: None,
    };
    let entry_sp = walk.input("entry_sp".into(), 64);
    // The laid-out rows in fetch order; a `B` carries what CB states of it.
    for (id, transfer) in rows {
        walk.step(id, contract, transfer)?;
    }
    let Some(Returned {
        v0_lo: v0_ret,
        sp: sp_ret,
        x30: x30_ret,
        saved_x,
        saved_v,
    }) = walk.returned.take()
    else {
        return Err(ScalarCellCallerRefusal::Control);
    };
    if walk.calls.len() != contract.calls.len() {
        return Err(ScalarCellCallerRefusal::Construction(format!(
            "the machine makes {} call(s) and the source {}",
            walk.calls.len(),
            contract.calls.len()
        )));
    }
    // The source's terms over the same inputs.
    let mut source_inputs: Vec<(String, u32)> = Vec::new();
    let mut sources = |byte: &Byte| -> Option<(E, usize)> {
        match byte {
            Byte::Parameter(i, b) => {
                let name = format!("e_v{i}_lo");
                source_inputs.push((name.clone(), 64));
                Some((low_bits(E::var(name, 64), width), *b))
            }
            Byte::Call(c, b) => {
                let name = call_result_name(*c, &contract.calls.get(*c)?.name);
                source_inputs.push((name.clone(), width));
                Some((E::var(name, width), *b))
            }
            _ => None,
        }
    };
    let mut conjuncts: Vec<E> = Vec::new();
    let x0_first = walk.calls[0].x0.clone();
    let window = E::bv_const(STACK_WINDOW_BYTES, 64);
    let floor = entry_sp.clone().bvsub(window);
    let aligned16 = |term: E| term.bvand(E::bv_const(15, 64)).eq_expr(E::bv_const(0, 64));
    let x29_entry = walk.input("e_x29".into(), 64);
    let x30_entry = walk.input("e_x30".into(), 64);
    for (c, (point, call)) in walk.calls.iter().zip(&contract.calls).enumerate() {
        let argument = bytes_term(&call.argument, contract.width, &mut sources)?;
        conjuncts.extend(equations(low_bits(point.v0_lo.clone(), width), argument));
        if c > 0 {
            conjuncts.push(point.x0.clone().eq_expr(x0_first.clone()));
        }
        let cell = bytes_term(&call.cell_before, contract.width, &mut sources)?;
        conjuncts.extend(equations(load(&point.memory, &x0_first, bytes), cell));
        conjuncts.push(aligned16(point.sp.clone()));
        conjuncts.push(point.sp.clone().bvule(x0_first.clone()));
        if c == 0 {
            conjuncts.push(
                x0_first
                    .clone()
                    .bvule(entry_sp.clone().bvsub(E::bv_const(u64::from(bytes), 64))),
            );
            conjuncts.push(
                x0_first
                    .clone()
                    .bvand(E::bv_const(u64::from(bytes) - 1, 64))
                    .eq_expr(E::bv_const(0, 64)),
            );
            conjuncts.push(floor.clone().bvule(point.sp.clone()));
        }
        conjuncts.extend(equations(
            load(&point.memory, &point.x29, 8),
            x29_entry.clone(),
        ));
        conjuncts.extend(equations(
            load(
                &point.memory,
                &point.x29.clone().bvadd(E::bv_const(8, 64)),
                8,
            ),
            x30_entry.clone(),
        ));
        if point.symbol != call.name {
            return Err(ScalarCellCallerRefusal::Construction(
                "a positional callee differs".into(),
            ));
        }
    }
    for access in &walk.accesses {
        conjuncts.push(access.floor.clone().bvule(access.address.clone()));
        conjuncts.push(
            access
                .address
                .clone()
                .bvule(entry_sp.clone().bvsub(E::bv_const(access.bytes, 64))),
        );
        for point in &walk.calls[..access.calls_before] {
            conjuncts.push(point.sp.clone().bvule(access.address.clone()));
        }
    }
    for sp in &walk.sp_values {
        conjuncts.push(floor.clone().bvule(sp.clone()));
        conjuncts.push(sp.clone().bvule(entry_sp.clone()));
        conjuncts.push(aligned16(sp.clone()));
    }
    let result = bytes_term(&contract.result, contract.width, &mut sources)?;
    conjuncts.extend(equations(low_bits(v0_ret, width), result));
    conjuncts.push(sp_ret.eq_expr(entry_sp.clone()));
    conjuncts.extend(equations(x30_ret, x30_entry.clone()));
    for (r, value) in saved_x {
        let entry = walk.input(format!("e_x{r}"), 64);
        conjuncts.extend(equations(value, entry));
    }
    for (r, value) in saved_v {
        let entry = walk.input(format!("e_v{r}_lo"), 64);
        conjuncts.extend(equations(value, entry));
    }
    conjuncts.extend(walk.transfers.iter().cloned());
    // A conjunct construction made an identity (`x = x`, `x <= x`) is true
    // on every input, and a repeated conjunct adds nothing (two accesses at
    // one address state one bound): drop both.
    conjuncts.retain(|conjunct| {
        !matches!(conjunct,
            E::Eq { lhs, rhs } | E::BvUle { lhs, rhs, .. } | E::BvUge { lhs, rhs, .. }
                if lhs == rhs)
    });
    let mut kept: Vec<E> = Vec::new();
    for conjunct in conjuncts {
        if !kept.contains(&conjunct) {
            kept.push(conjunct);
        }
    }
    let conjuncts = kept;
    for (name, width) in source_inputs {
        walk.input(name, width);
    }
    let complete = conjuncts
        .iter()
        .cloned()
        .reduce(|a, b| a.and_expr(b))
        .ok_or_else(|| ScalarCellCallerRefusal::Construction("no conclusion".into()))?;
    let preconditions = vec![
        aligned16(entry_sp.clone()),
        entry_sp.clone().bvuge(E::bv_const(STACK_WINDOW_BYTES, 64)),
    ];
    let mut used: BTreeSet<String> = complete.free_vars().into_iter().collect();
    for premise in &preconditions {
        used.extend(premise.free_vars());
    }
    let inputs: Vec<(String, u32)> = walk
        .inputs
        .iter()
        .filter(|(name, _)| used.contains(name))
        .cloned()
        .collect();
    structural_check(&complete, &conjuncts, &inputs, &used, &walk.calls, memory)?;
    let obligation = ProofObligation {
        name: SCALAR_CELL_CALLER_OBLIGATION_NAME.into(),
        trust_ir_expr: E::bool_const(true),
        aarch64_expr: complete,
        inputs,
        preconditions,
        fp_inputs: Vec::new(),
        category: Some(TransvalCheckKind::InstructionLowering),
        machine_side_provenance: MachineSideProvenance::StaticDb,
    };
    Ok(Built {
        obligation,
        conjuncts,
        candidates: walk.candidates,
    })
}

/// The spelling and structural rules of the built theorem: arrays only under
/// `select`/`store` over the one nullary `entry_memory` (or the concrete
/// checks' constant array), no array equality and no other function symbol;
/// every conjunct an equation of two terms of one width or an unsigned
/// bound; every declared input used and every used name declared; and every
/// call's result in the theorem (so a substituted or reordered callee is
/// refutable wherever the result reaches a conclusion).
fn structural_check(
    complete: &E,
    conjuncts: &[E],
    inputs: &[(String, u32)],
    used: &BTreeSet<String>,
    calls: &[CallPoint],
    memory: InitialMemory,
) -> Result<(), ScalarCellCallerRefusal> {
    let fail = |why: String| Err(ScalarCellCallerRefusal::Construction(why));
    for conjunct in conjuncts {
        match conjunct {
            E::Eq { lhs, rhs } => {
                if lhs.try_bv_width().ok().is_none()
                    || lhs.try_bv_width().ok() != rhs.try_bv_width().ok()
                {
                    return fail("an equation is not between bit-vectors of one width".into());
                }
            }
            E::BvUle { .. } | E::BvUge { .. } => {}
            other => {
                return fail(format!(
                    "a conjunct is neither an equation nor a bound: {other}"
                ));
            }
        }
    }
    let mut stack = vec![complete];
    while let Some(term) = stack.pop() {
        match term {
            E::UF { name, args, .. } => {
                if name != "entry_memory"
                    || !args.is_empty()
                    || !matches!(memory, InitialMemory::Symbolic)
                {
                    return fail(format!("function symbol {name}"));
                }
            }
            E::ConstArray { .. } if matches!(memory, InitialMemory::Symbolic) => {
                return fail("a constant array in the replayed theorem".into());
            }
            E::Eq { lhs, .. } if matches!(lhs.sort(), crate::smt::SmtSort::Array { .. }) => {
                return fail("an array equality".into());
            }
            _ => {}
        }
        stack.extend(children(term));
    }
    let declared: BTreeSet<String> = inputs.iter().map(|(name, _)| name.clone()).collect();
    for name in used {
        if name != "entry_memory" && !declared.contains(name) {
            return fail(format!("the theorem uses undeclared {name}"));
        }
    }
    for (c, call) in calls.iter().enumerate() {
        let name = call_result_name(c, &call.symbol);
        if !used.contains(&name) {
            return fail(format!(
                "call {c}'s result {name} reaches no conclusion, so its callee is not refutable"
            ));
        }
    }
    Ok(())
}

/// The direct subterms of `term` (the constructors this owner builds).
fn children(term: &E) -> Vec<&E> {
    use E::*;
    match term {
        Var { .. } | BvConst { .. } | BoolConst(_) => Vec::new(),
        Not { operand } => vec![operand],
        Extract { operand, .. } | ZeroExtend { operand, .. } => vec![operand],
        BvAdd { lhs, rhs, .. }
        | BvSub { lhs, rhs, .. }
        | BvAnd { lhs, rhs, .. }
        | BvOr { lhs, rhs, .. }
        | BvXor { lhs, rhs, .. }
        | BvShl { lhs, rhs, .. }
        | BvUle { lhs, rhs, .. }
        | BvUge { lhs, rhs, .. }
        | Eq { lhs, rhs }
        | And { lhs, rhs } => vec![lhs, rhs],
        Concat { hi, lo, .. } => vec![hi, lo],
        Select { array, index } => vec![array, index],
        Store {
            array,
            index,
            value,
        } => vec![array, index, value],
        ConstArray { value, .. } => vec![value],
        UF { args, .. } => args.iter().collect(),
        _ => Vec::new(),
    }
}

#[cfg(test)]
#[path = "source_bound_cell_caller_tests.rs"]
mod tests;
