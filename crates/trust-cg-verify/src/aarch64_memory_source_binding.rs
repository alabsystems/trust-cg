// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! Source-bound credit for AArch64 memory-effect rows (ledger `L07-P2`,
//! `X-OPCODES-P1`).
//!
//! The word-bound memory-effect decomposition
//! ([`crate::aarch64_memory_effect`]) shows that an instruction WORD performs
//! the memory access its machine-IR OPERANDS name. Neither it nor the
//! Formal-only bound-memory rule's form theorems
//! ([`crate::bound_memory_authority`]) say that those operands are the access
//! the SOURCE asks for: a prologue that saves the wrong pair, or a load that
//! reads the wrong slot, is certified exactly as well. This module closes that
//! gap for two shapes, each owned by a checker that has already bound the
//! complete function to its source:
//!
//! * **Frame records.** The save `STP X29, X30, [SP, #-16]!` and the restore
//!   `LDP X29, X30, [SP], #16` of a [`SourceBoundFrame`], whose owner checked
//!   the complete body against its LIR source and whose fixed frame theorem
//!   ([`crate::source_bound_frame::frame_obligation`]) states what the two
//!   records must do: store the entry FP and LR at `SP - 16` and `SP - 8`,
//!   leave SP at `SP - 16`, and later load both back and restore SP. The
//!   access each record must perform is that theorem's
//!   ([`ContractAccess::frame_record`]), derived from its constants.
//! * **Leaf accesses.** Each scalar load or store of a
//!   [`SourceBoundMemoryLeaf`], whose checker matched the machine's access
//!   trace to the LIR `Load`/`Store` trace in lock step: the base register
//!   holds the source pointer, the offset reaches the source address, the
//!   width is the source type's, a load zero-extends into the register the
//!   source's later uses read, and a store writes the source value's low bits.
//!   The access each must perform is the one that checker recorded.
//!
//! A [`SourceBoundMemoryRow`] exists only when its instruction's operands name
//! EXACTLY its contract access ([`ContractAccess::check`]): the same
//! direction, addressing form, bank, width, base, offset (the slot) and
//! transfer registers. Its parts are the memory-effect decomposition of the
//! instruction's re-derived word, the word ENC-5 binds to the emitted one.
//!
//! # Credit
//!
//! A bound row is `Verified` at `Formal` only when all of the following hold:
//!
//! 1. its owner's evidence: for a frame record, the frame theorem's
//!    independently replayed proof (the frame row's own verdict); for a leaf
//!    access, the complete source/body check that built the leaf;
//! 2. no part is refuted or undecided in process
//!    ([`crate::aarch64_memory_effect::decide_in_process`]);
//! 3. EVERY part's exact query has an AY proof that the accepted Clean checker
//!    fully verified: the source-bound replay every source-bound owner takes
//!    (`source_bound_replay`; `Valid` only for
//!    `AYResult::Verified`), recorded as [`PartReceipt`]s that carry the
//!    SHA-256 of the exact query they judged. [`SourceBoundMemoryRow::credit`]
//!    refuses a receipt whose part or query digest is not this row's (a stale
//!    or foreign certificate).
//!
//! An in-process decision is never credit, and a part without a checked
//! certificate leaves the row `Unverified` with
//! [`SOURCE_BOUND_MEMORY_NOT_CREDITED`], how far the parts got and why. A
//! solver counterexample fails it. This route is additive: a row the
//! Formal-only rule already credits keeps that credit, and a frame record
//! needs the frame theorem AND its parts (it no longer rests on the frame
//! theorem alone).
//!
//! # Authority (OD-139 in `docs/decision-record.md`)
//!
//! The checker authority is the one every source-bound owner already uses: an
//! AY the identity rule admits ([`crate::ay_identity`]: the SHA-256 of
//! `<sysroot>/bin/ay` recorded when this crate was built) and the Clean the
//! checker policy selects ([`crate::obligation_cert_store`]). A local OVERLAY
//! toolchain (`scripts/assemble_trust_overlay.py`) is an accepted instance of
//! that authority, not an exception to it: `build.rs` records the overlay's
//! AY digest only when `overlay.json` names exactly the bytes of its
//! `bin/ay` and `bin/clean`, an overlay build accepts no checker but that
//! pinned Clean, and the compile's proof evidence names both
//! ([`crate::ay_identity::AyIdentity::describe`]: the AY's banner and
//! SHA-256, plus `overlay-toolchain manifest-sha256 … clean-sha256 …
//! clean-commit …`). With the installed Trust package (9192) the same route
//! certifies no part: its AY answers holey `unsat` or `unknown` for every part
//! and its Clean lacks `carcara-verify`
//! (`reports/2026-09-29-darwin-memory-effect-certificates`), so every bound
//! row stays refused, by name.
//!
//! This is the shipped default, taken as OD-139 (2026-10-06), not a pending
//! proposal: under [`VerificationConfig::for_proof_promotion`] with a pair
//! that checks every part, the walk credits bound rows and the verifying JIT
//! publishes them. It admits Clean-checked parts only together with a source
//! binding, the evidence class the frame and ALU owners are already credited
//! on; an unbound row's checked parts still credit nothing (OD-39 stands for
//! those). Reversing it is a new dated ruling, which would gate the credited
//! arm of `FunctionVerifier::frame_record_row` and
//! `FunctionVerifier::leaf_access_row`.
//!
//! # Sidecar export
//!
//! A formal lowering sidecar (`--emit-proofs`) that carries the frame theorem
//! also carries the twelve frame-record parts
//! ([`frame_record_part_obligations`]) and replays them under the sidecar's
//! own admitted AY, so it holds every obligation a frame record's credit
//! needed. A credited leaf access has no `ProofDatabase` obligation and its
//! parts depend on its word, so `--emit-proofs` refuses its function by name
//! rather than export a partial record.
//!
//! # Not covered
//!
//! Callee-saved register pairs (`STP`/`LDP` of X19 to X28 and D8 to D15, and
//! the FP/LR pair of a frame larger than sixteen bytes): no source-bound frame
//! contract owns them, so they keep the Formal-only rule's verdict. Scalar
//! accesses outside a [`SourceBoundMemoryLeaf`] (any function with a call,
//! a branch, a frame, a spill or a register-offset, writeback or
//! sign-extending access).

use sha2::{Digest, Sha256};
use trust_cg_ir::{InstId, MachInst};

use crate::aarch64_memory_effect::{
    AccessForm, InProcess, MemoryAccess, MemoryEffectObligation, MemoryEffectPart,
    decide_in_process, memory_access, memory_effect,
};
use crate::aarch64_pair_memory_proofs::PairMode;
use crate::lowering_proof::{ProofObligation, VerificationConfig};
use crate::source_bound_frame::{
    FRAME_RECORD_BYTES, FRAME_RECORD_LANE_BYTES, FrameEnvelopeRole, SourceBoundFrame,
    SourceBoundMemoryLeaf,
};
use crate::verify::{VerificationResult, VerificationStrength};

/// Reason clause of a source-bound memory row that is not credited: bound,
/// but some part has no Clean-checked certificate (or a part is undecided).
pub const SOURCE_BOUND_MEMORY_NOT_CREDITED: &str = "source-bound memory row (credited only when \
     every memory-effect part has a Clean-checked certificate of its exact query)";

/// Proof name prefix of a credited leaf access.
pub const SOURCE_BOUND_MEMORY_PROOF_PREFIX: &str = "Source-bound AArch64 memory access";

/// Tag of the diagnostic census line [`trace`] prints under `solve-trace`.
pub const SOURCE_BOUND_MEMORY_TRACE_TAG: &str = "[TCG-SOURCE-BOUND-MEMORY] v1";

// ===========================================================================
// The contract access
// ===========================================================================

/// The access a source-side contract names for one machine memory row: what
/// the operands must say, field for field ([`Self::check`]).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ContractAccess {
    /// True for a load.
    pub load: bool,
    /// `Some(mode)` for a pair, `None` for a scalar access (either immediate
    /// encoding: the unsigned scaled and unscaled forms address alike).
    pub pair: Option<PairMode>,
    /// True for SIMD&FP transfer registers.
    pub simd: bool,
    /// Bytes per transfer lane.
    pub bytes: u32,
    /// Byte offset from the base register (the slot).
    pub offset: i64,
    /// Five-bit transfer register fields (a scalar access uses lane 0).
    pub transfer: [u8; 2],
    /// Whether each transfer lane is the zero register.
    pub zero: [bool; 2],
    /// Five-bit base register field (31 is SP).
    pub base: u8,
}

impl ContractAccess {
    /// A scalar general-purpose access. Every scalar load this module binds
    /// zero-extends: [`memory_access`] admits no sign-extending form, so a
    /// sign-extending machine load is refused before this contract is
    /// consulted ([`MemoryBindingRefusal::NotAdmitted`]).
    pub(crate) fn scalar(
        load: bool,
        bytes: u32,
        offset: i64,
        base: u8,
        data: u8,
        zero: bool,
    ) -> Self {
        Self {
            load,
            pair: None,
            simd: false,
            bytes,
            offset,
            transfer: [data, data],
            zero: [zero, zero],
            base,
        }
    }

    /// The access the source-bound frame theorem names for `role`, from its
    /// own constants: the save stores the entry FP (X29) at `SP - 16` and LR
    /// (X30) one lane above, leaving SP at `SP - 16` (pre-index `#-16` on SP);
    /// the restore loads both from the record at SP and moves SP back up by
    /// sixteen (post-index `#16`). `None` for the establishing ADD, which is
    /// no memory access.
    pub fn frame_record(role: FrameEnvelopeRole) -> Option<Self> {
        let record = FRAME_RECORD_BYTES as i64;
        let (load, pair, offset) = match role {
            FrameEnvelopeRole::Save => (false, PairMode::PreIndex, -record),
            FrameEnvelopeRole::Restore => (true, PairMode::PostIndex, record),
            FrameEnvelopeRole::Establish => return None,
        };
        Some(Self {
            load,
            pair: Some(pair),
            simd: false,
            bytes: FRAME_RECORD_LANE_BYTES as u32,
            offset,
            transfer: [29, 30],
            zero: [false, false],
            base: 31,
        })
    }

    fn lanes(&self) -> usize {
        if self.pair.is_some() { 2 } else { 1 }
    }

    /// Whether `machine` (an instruction's operands, [`memory_access`]) names
    /// exactly this access.
    pub fn check(&self, machine: &MemoryAccess) -> Result<(), MemoryBindingRefusal> {
        use MemoryBindingRefusal as R;
        if machine.load != self.load {
            return Err(R::Direction {
                contract_load: self.load,
            });
        }
        let form = match (self.pair, machine.form) {
            (Some(mode), AccessForm::Pair(machine)) => mode == machine,
            (None, AccessForm::ScalarUnsigned | AccessForm::ScalarUnscaled) => true,
            _ => false,
        };
        if !form {
            return Err(R::Form {
                contract: format!("{:?}", self.pair),
                machine: format!("{:?}", machine.form),
            });
        }
        if machine.simd != self.simd {
            return Err(R::Bank);
        }
        if machine.bytes != self.bytes {
            return Err(R::Width {
                contract: self.bytes,
                machine: machine.bytes,
            });
        }
        if machine.base != self.base {
            return Err(R::Base {
                contract: self.base,
                machine: machine.base,
            });
        }
        if machine.offset != self.offset {
            return Err(R::Slot {
                contract: self.offset,
                machine: machine.offset,
            });
        }
        for lane in 0..self.lanes() {
            if machine.zero[lane] != self.zero[lane]
                || (!self.zero[lane] && machine.transfer[lane] != self.transfer[lane])
            {
                return Err(R::Data {
                    lane: lane as u8,
                    contract: self.transfer[lane],
                    machine: machine.transfer[lane],
                });
            }
        }
        Ok(())
    }
}

/// Why a memory row was not bound to its source-side contract. Each is a
/// refusal of the binding (the row keeps its ordinary lanes), never a credit.
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
pub enum MemoryBindingRefusal {
    /// The instruction is no access the memory-effect decomposition admits.
    #[error("the instruction is no access the memory-effect decomposition admits")]
    NotAdmitted,
    /// The owner binds no access at this instruction.
    #[error("the owner binds no memory access at this instruction")]
    NotOwned,
    /// A load where the contract stores, or the reverse.
    #[error("the operands {} where the contract {}", if *contract_load { "store" } else { "load" }, if *contract_load { "loads" } else { "stores" })]
    Direction { contract_load: bool },
    /// Another addressing form than the contract's.
    #[error("addressing form {machine} where the contract names {contract}")]
    Form { contract: String, machine: String },
    /// Another register bank than the contract's.
    #[error("another register bank than the contract's")]
    Bank,
    /// Another lane width than the contract's.
    #[error("{machine}-byte lanes where the contract names {contract}-byte lanes")]
    Width { contract: u32, machine: u32 },
    /// Another base register than the contract's.
    #[error("base register {machine} where the contract names {contract}")]
    Base { contract: u8, machine: u8 },
    /// Another slot (offset) than the contract's.
    #[error("slot offset {machine} where the contract names {contract}")]
    Slot { contract: i64, machine: i64 },
    /// Another transfer register (or zero register) in a lane.
    #[error("transfer lane {lane} names register {machine} where the contract names {contract}")]
    Data { lane: u8, contract: u8, machine: u8 },
}

/// The memory-effect part obligations of the two frame records of every
/// source-bound frame, save then restore, each in part order. The frame owner
/// admits exactly one spelling of each record
/// ([`crate::source_bound_frame::frame_record_instruction`]), so these are
/// exactly the parts a credited frame record had replayed and checked. A
/// formal lowering sidecar that carries the frame theorem carries them too
/// (`trust-cg-cli` `emit_proofs`), so the export holds every obligation the
/// compile's frame-record credit needed.
pub fn frame_record_part_obligations() -> Vec<ProofObligation> {
    [FrameEnvelopeRole::Save, FrameEnvelopeRole::Restore]
        .into_iter()
        .flat_map(|role| {
            let inst = crate::source_bound_frame::frame_record_instruction(role)
                .expect("a pair role has a record");
            let contract = ContractAccess::frame_record(role).expect("a pair role has a record");
            let row = SourceBoundMemoryRow::bind(
                &inst,
                InstId(0),
                contract,
                MemoryRowBinding::FrameRecord { role },
            )
            .expect("the owner's record names the frame theorem's record");
            row.parts.into_iter().map(|part| part.effect.obligation)
        })
        .collect()
}

// ===========================================================================
// The bound row
// ===========================================================================

/// What a bound row is bound to.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum MemoryRowBinding {
    /// A record of a source-bound frame's FP/LR envelope.
    FrameRecord { role: FrameEnvelopeRole },
    /// A scalar access of a source-bound memory leaf: the LIR instruction at
    /// `source_index` of the source's only block, the `position`-th access.
    LeafAccess {
        block: u32,
        source_index: usize,
        position: usize,
    },
}

impl std::fmt::Display for MemoryRowBinding {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::FrameRecord { role } => write!(f, "the source-bound frame's {role} record"),
            Self::LeafAccess {
                block,
                source_index,
                position,
            } => write!(
                f,
                "source access {position}, LIR instruction lir{block}.{source_index}"
            ),
        }
    }
}

/// One part of a bound row: the memory-effect obligation, replayable only
/// through the source-bound route because a binding minted it.
#[derive(Debug, Clone)]
pub struct SourceBoundMemoryPart {
    effect: MemoryEffectObligation,
}

impl SourceBoundMemoryPart {
    /// Which fact the part states.
    pub fn part(&self) -> MemoryEffectPart {
        self.effect.part
    }

    /// The obligation, exactly as the decomposition built it.
    pub fn obligation(&self) -> &ProofObligation {
        &self.effect.obligation
    }

    /// SHA-256 of the part's exact SMT-LIB serialization.
    pub fn query_sha256(&self) -> [u8; 32] {
        Sha256::digest(crate::serialize_to_smt2(self.obligation()).as_bytes()).into()
    }
}

/// A memory row bound to its owner's contract. No public constructor: only
/// [`Self::bind_frame_record`] and [`Self::bind_leaf_access`] build one, and
/// each borrows its owner, so a row cannot outlive or change its inputs.
#[derive(Debug)]
pub struct SourceBoundMemoryRow<'owner> {
    _owner: std::marker::PhantomData<&'owner ()>,
    instruction: InstId,
    opcode: trust_cg_ir::AArch64Opcode,
    binding: MemoryRowBinding,
    contract: ContractAccess,
    word: u32,
    parts: Vec<SourceBoundMemoryPart>,
}

impl<'owner> SourceBoundMemoryRow<'owner> {
    /// Bind the envelope pair `id` of `frame` to the frame theorem's record.
    pub fn bind_frame_record(
        frame: &'owner SourceBoundFrame<'_>,
        id: InstId,
    ) -> Result<Self, MemoryBindingRefusal> {
        let [save, restore] = frame.pair_instructions();
        let role = if id == save {
            FrameEnvelopeRole::Save
        } else if id == restore {
            FrameEnvelopeRole::Restore
        } else {
            return Err(MemoryBindingRefusal::NotOwned);
        };
        let contract = ContractAccess::frame_record(role).expect("a pair role has a record");
        let inst = frame
            .machine()
            .insts
            .get(id.0 as usize)
            .ok_or(MemoryBindingRefusal::NotOwned)?;
        Self::bind(inst, id, contract, MemoryRowBinding::FrameRecord { role })
    }

    /// Bind access `id` of `leaf` to the source access its checker matched.
    pub fn bind_leaf_access(
        leaf: &'owner SourceBoundMemoryLeaf<'_>,
        id: InstId,
    ) -> Result<Self, MemoryBindingRefusal> {
        let access = leaf.access(id).ok_or(MemoryBindingRefusal::NotOwned)?;
        let inst = leaf
            .machine()
            .insts
            .get(id.0 as usize)
            .ok_or(MemoryBindingRefusal::NotOwned)?;
        Self::bind(
            inst,
            id,
            access.contract,
            MemoryRowBinding::LeafAccess {
                block: leaf.source().entry_block.0,
                source_index: access.source_index,
                position: access.position,
            },
        )
    }

    /// The shared binding step: the operands must name the contract access,
    /// and the parts are the decomposition of the re-derived word. Private:
    /// only the two owner binders above choose the contract.
    fn bind(
        inst: &MachInst,
        instruction: InstId,
        contract: ContractAccess,
        binding: MemoryRowBinding,
    ) -> Result<Self, MemoryBindingRefusal> {
        let access = memory_access(inst).ok_or(MemoryBindingRefusal::NotAdmitted)?;
        // A source contract names a zero-extending general-purpose immediate
        // access (or a frame pair): it has no extension, bank, writeback or
        // index to compare, so the scalar forms the decomposition admits only
        // through the form binder (L04-P1) bind nothing here.
        if access.is_binder_scalar_form() {
            return Err(MemoryBindingRefusal::NotAdmitted);
        }
        contract.check(&access)?;
        let decomposition = memory_effect(inst).ok_or(MemoryBindingRefusal::NotAdmitted)?;
        Ok(Self {
            _owner: std::marker::PhantomData,
            instruction,
            opcode: inst.opcode,
            binding,
            contract,
            word: decomposition.word,
            parts: decomposition
                .parts
                .into_iter()
                .map(|effect| SourceBoundMemoryPart { effect })
                .collect(),
        })
    }

    pub fn instruction(&self) -> InstId {
        self.instruction
    }

    pub fn binding(&self) -> MemoryRowBinding {
        self.binding
    }

    pub fn contract(&self) -> &ContractAccess {
        &self.contract
    }

    /// The re-derived word every part carries.
    pub fn word(&self) -> u32 {
        self.word
    }

    pub fn parts(&self) -> &[SourceBoundMemoryPart] {
        &self.parts
    }

    /// `A64 memory effect <opcode> <word>`, as the decomposition names it.
    pub fn label(&self) -> String {
        format!("A64 memory effect {:?} {:#010x}", self.opcode, self.word)
    }

    /// The proof name a credited LEAF access carries. A credited frame record
    /// keeps the frame theorem's row.
    pub fn proof_name(&self) -> String {
        format!(
            "{SOURCE_BOUND_MEMORY_PROOF_PREFIX}: {:?} {:#010x} bound to {}",
            self.opcode, self.word, self.binding
        )
    }

    /// Decide every part in process. `Err((part name, counterexample))` for a
    /// refuted part; otherwise how they were decided, with the first
    /// undecided part if any. Never credit.
    pub(crate) fn decide(
        &self,
        config: &VerificationConfig,
    ) -> Result<InProcessSummary, (String, String)> {
        let mut summary = InProcessSummary::default();
        for part in &self.parts {
            match decide_in_process(&part.effect, config) {
                InProcess::Holds(VerificationStrength::Statistical { sample_count }) => {
                    summary.sampled = Some(sample_count);
                }
                InProcess::Holds(_) => summary.exact += 1,
                InProcess::Refuted(counterexample) => {
                    return Err((part.obligation().name.clone(), counterexample));
                }
                InProcess::Undecided(reason) => {
                    summary.undecided.get_or_insert((part.part(), reason));
                }
            }
        }
        summary.parts = self.parts.len();
        Ok(summary)
    }

    /// Replay every part with `replay`, serially and in part order, stopping
    /// at the first part without a `Valid` verdict (the parts after it are
    /// recorded as not replayed). This is the only place a [`PartReceipt`] is
    /// minted on the production path, each from the part it just replayed, so
    /// a receipt there cannot name another part or query; the custody of the
    /// verdict itself (the exact query AY solved and Clean checked, and any
    /// memo or stored certificate standing for it) is the replay route's,
    /// shared with the frame and ALU owners.
    pub(crate) fn replay_parts(
        &self,
        mut replay: impl FnMut(&SourceBoundMemoryPart) -> (Option<VerificationResult>, Option<String>),
    ) -> Vec<PartReceipt> {
        let mut stopped = false;
        self.parts
            .iter()
            .map(|part| {
                if stopped {
                    return PartReceipt::of(
                        part,
                        None,
                        Some("not replayed: an earlier part has no Valid replay".into()),
                    );
                }
                let (verdict, why) = replay(part);
                stopped = !matches!(verdict, Some(VerificationResult::Valid));
                PartReceipt::of(part, verdict, why)
            })
            .collect()
    }

    /// Judge the row's part receipts, in part order. Every receipt must be
    /// this row's: the same part, minted over the same exact query (a receipt
    /// for another word, another row or an older decomposition is refused as
    /// [`MemoryCredit::Foreign`]). Since [`Self::replay_parts`] mints each
    /// receipt from the part it replays, this check is defence in depth on
    /// the production path; the unit tests drive it with receipts of another
    /// row.
    pub(crate) fn credit(&self, receipts: &[PartReceipt]) -> MemoryCredit {
        if receipts.len() != self.parts.len() {
            return MemoryCredit::Foreign {
                index: receipts.len().min(self.parts.len()),
                why: "the receipts do not cover exactly this row's parts",
            };
        }
        for (index, (part, receipt)) in self.parts.iter().zip(receipts).enumerate() {
            if receipt.part != part.part() {
                return MemoryCredit::Foreign {
                    index,
                    why: "a receipt judged another part",
                };
            }
            if receipt.query_sha256 != part.query_sha256() {
                return MemoryCredit::Foreign {
                    index,
                    why: "a receipt judged another query (a stale or foreign certificate)",
                };
            }
        }
        if let Some((part, counterexample)) =
            self.parts
                .iter()
                .zip(receipts)
                .find_map(|(part, receipt)| match &receipt.verdict {
                    Some(VerificationResult::Invalid { counterexample }) => {
                        Some((part, counterexample.clone()))
                    }
                    _ => None,
                })
        {
            return MemoryCredit::Refuted {
                part: part.obligation().name.clone(),
                counterexample,
            };
        }
        let checked = receipts
            .iter()
            .take_while(|receipt| matches!(receipt.verdict, Some(VerificationResult::Valid)))
            .count();
        if checked == self.parts.len() {
            return MemoryCredit::Checked;
        }
        // The solver's text names per-run temporary files; drop every path
        // token so the reason is reproducible.
        let why = receipts[checked]
            .why
            .as_deref()
            .unwrap_or("no verdict")
            .split_whitespace()
            .filter(|token| !token.contains('/'))
            .collect::<Vec<_>>()
            .join(" ");
        MemoryCredit::Partial {
            checked,
            first: self.parts[checked].part(),
            why,
        }
    }
}

/// How the parts of a bound row were decided in process.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub(crate) struct InProcessSummary {
    pub(crate) parts: usize,
    pub(crate) exact: usize,
    pub(crate) sampled: Option<u64>,
    pub(crate) undecided: Option<(MemoryEffectPart, String)>,
}

impl std::fmt::Display for InProcessSummary {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match (&self.undecided, self.sampled) {
            (Some((part, reason)), _) => {
                write!(f, "is undecided in process: part `{part}`: {reason}")
            }
            (None, Some(samples)) => write!(
                f,
                "holds in process: {} part(s) exactly, {} with no counterexample in {samples} \
                 sampled inputs",
                self.exact,
                self.parts - self.exact
            ),
            (None, None) => write!(f, "holds in process: all {} parts exactly", self.parts),
        }
    }
}

/// The verdict of one part's source-bound replay, bound to the exact query
/// it judged. Minted only in this module, by [`Self::of`] from the part
/// itself ([`SourceBoundMemoryRow::replay_parts`]); the rest of the crate can
/// neither build one nor choose its verdict.
#[derive(Debug, Clone)]
pub(crate) struct PartReceipt {
    part: MemoryEffectPart,
    query_sha256: [u8; 32],
    verdict: Option<VerificationResult>,
    why: Option<String>,
}

impl PartReceipt {
    fn of(
        part: &SourceBoundMemoryPart,
        verdict: Option<VerificationResult>,
        why: Option<String>,
    ) -> Self {
        Self {
            part: part.part(),
            query_sha256: part.query_sha256(),
            verdict,
            why,
        }
    }
}

/// [`SourceBoundMemoryRow::credit`]'s judgement of a row's receipts.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum MemoryCredit {
    /// Every part has a Clean-checked certificate of its exact query.
    Checked,
    /// A part's replay found a counterexample.
    Refuted {
        part: String,
        counterexample: String,
    },
    /// The receipt at `index` is not this row's.
    Foreign { index: usize, why: &'static str },
    /// The first `checked` parts have a certificate; `first` has none.
    Partial {
        checked: usize,
        first: MemoryEffectPart,
        why: String,
    },
}

impl MemoryCredit {
    /// The clause an uncredited row carries for this judgement (`None` for
    /// [`Self::Checked`] and [`Self::Refuted`], which are verdicts).
    pub(crate) fn uncredited_clause(&self, parts: usize) -> Option<String> {
        match self {
            Self::Checked | Self::Refuted { .. } => None,
            Self::Foreign { index, why } => Some(format!(
                "0 of {parts} parts credited: receipt {index} refused ({why})"
            )),
            Self::Partial {
                checked,
                first,
                why,
            } => Some(format!(
                "{checked} of {parts} parts have a Clean-checked certificate; the first without \
                 one is `{first}` ({why})"
            )),
        }
    }
}

/// Print one census line for a bound row under `solve-trace` (diagnostic
/// only; never a verdict input).
pub(crate) fn trace(function: &str, index: usize, row: &SourceBoundMemoryRow<'_>, outcome: &str) {
    if !crate::diag::solve_trace_enabled() {
        return;
    }
    let binding = match row.binding {
        MemoryRowBinding::FrameRecord { role } => format!("frame-record:{role}"),
        MemoryRowBinding::LeafAccess {
            block,
            source_index,
            ..
        } => format!("leaf-access:lir{block}.{source_index}"),
    };
    let outcome = outcome.replace(['\t', '\n'], " ");
    eprintln!(
        "{SOURCE_BOUND_MEMORY_TRACE_TAG}\tfunction={}\tinst={index}\topcode=AArch64::{:?}\t\
         word={:#010x}\tbinding={binding}\tparts={}\toutcome={outcome}",
        function.replace(['\t', '\n'], " "),
        row.opcode,
        row.word,
        row.parts.len()
    );
}

/// Print one census line, under `solve-trace`, for a function with admitted
/// memory rows that the memory-leaf checker did not bind, naming why
/// (diagnostic only; never a verdict input). A function without a memory
/// access the decomposition admits prints nothing.
pub(crate) fn trace_unbound(
    machine: &trust_cg_ir::MachFunction,
    refusal: &crate::source_bound_frame::MemoryLeafRefusal,
) {
    if !crate::diag::solve_trace_enabled() {
        return;
    }
    let rows = machine
        .blocks
        .iter()
        .flat_map(|block| &block.insts)
        .filter(|id| {
            machine
                .insts
                .get(id.0 as usize)
                .and_then(memory_access)
                .is_some()
        })
        .count();
    if rows == 0 {
        return;
    }
    eprintln!(
        "{SOURCE_BOUND_MEMORY_TRACE_TAG}\tunbound\tfunction={}\tmemory_rows={rows}\treason={}",
        machine.name.replace(['\t', '\n'], " "),
        refusal.to_string().replace(['\t', '\n'], " ")
    );
}

#[cfg(test)]
#[path = "aarch64_memory_source_binding_tests.rs"]
mod tests;
