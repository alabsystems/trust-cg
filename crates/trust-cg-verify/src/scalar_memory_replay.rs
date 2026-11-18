// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! Complete original-Core/LIR/MachIR/final-word scalar-memory inventory.
//!
//! Construction retains unresolved relations. Only independent replay of
//! EVERY exact part under one captured enforcing proof-promotion request can
//! construct the conditional certificate below. Status, arbitrary final-byte
//! equality and every read/write demand remain separate mandatory parts.
//! The encoded semantics retain their stated trusted transcription boundary.
//! No caller liveness, initialization, readable/writable permission, stable
//! Normal-memory condition, frame/ABI capability, native/publication receipt,
//! per-instruction credit or artifact/cache reuse follows from this inventory.
//! Untagged addresses and disabled GCS remain external conditions too.

use crate::FunctionVerificationRequest;
use crate::function_request::FunctionDischargeContext;
use crate::lowering_proof::{ProofObligation, VerificationConfig};
use crate::provenance_xcheck::ProvenanceXCheckMode;
use crate::read_only_target::{
    ReadOnlyTargetError, ScalarMemoryTargetQueries, bind_scalar_memory_bytes,
    bind_scalar_memory_machine,
};
use crate::source_bound_frame::ScalarMemorySourceQueries;
use crate::verify::VerificationResult;
use trust_cg_ir::MachFunction;

#[cfg(feature = "source-defined-call")]
#[path = "void_memory_receipt.rs"]
mod void_receipt;
#[cfg(feature = "source-defined-call")]
pub use void_receipt::ReplayedVoidMemoryCompilation;

#[cfg(feature = "source-defined-call")]
#[path = "word_status_receipt.rs"]
mod word_status_receipt;
#[cfg(feature = "source-defined-call")]
pub use word_status_receipt::ReplayedWordStatusCompilation;

#[cfg(test)]
#[path = "scalar_memory_replay_tests.rs"]
mod tests;

#[cfg(all(test, target_arch = "aarch64", target_os = "macos"))]
#[path = "scalar_memory_replay_diagnostic_tests.rs"]
mod diagnostic_tests;

#[cfg(all(test, target_arch = "aarch64", target_os = "macos"))]
#[path = "scalar_memory_closed_definition_tests.rs"]
mod closed_definition_tests;

/// Actual endpoints, not stages inferred from query names or producer hints.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum ScalarMemoryRelationStage {
    CoreToLir,
    CoreToMachine,
    CoreToFinalBytes,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum ScalarMemoryRelationKind {
    Status,
    FinalMemory,
    Read,
    Write,
}

/// An index into an immutable stage/kind inventory, never an instruction or
/// caller-memory license. Constructing an ID does not construct a replay part.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct ScalarMemoryRelationId {
    pub stage: ScalarMemoryRelationStage,
    pub kind: ScalarMemoryRelationKind,
    pub index: usize,
}

/// Exact original source and actual endpoints with complete deterministic
/// coverage. Only the shared source/target binders supply these obligations.
pub struct ScalarMemoryCompilerRelations<'a> {
    source: &'a ScalarMemorySourceQueries<'a>,
    machine: &'a MachFunction,
    final_bytes: &'a [u8],
    machine_queries: ScalarMemoryTargetQueries<'a>,
    byte_queries: ScalarMemoryTargetQueries<'a>,
    inventory: Vec<ScalarMemoryRelationId>,
}

impl<'a> ScalarMemoryCompilerRelations<'a> {
    pub fn bind(
        source: &'a ScalarMemorySourceQueries<'a>,
        machine: &'a MachFunction,
        final_bytes: &'a [u8],
    ) -> Result<Self, ReadOnlyTargetError> {
        if source.is_void() {
            return Err(ReadOnlyTargetError::Machine(
                "void entry has no scalar result",
            ));
        }
        Self::bind_memory(source, machine, final_bytes)
    }

    fn bind_memory(
        source: &'a ScalarMemorySourceQueries<'a>,
        machine: &'a MachFunction,
        final_bytes: &'a [u8],
    ) -> Result<Self, ReadOnlyTargetError> {
        let (machine_queries, byte_queries) = if source.is_void() {
            (
                crate::read_only_target::bind_memory_machine(source, machine)?,
                crate::read_only_target::bind_memory_bytes(source, final_bytes)?,
            )
        } else {
            (
                bind_scalar_memory_machine(source, machine)?,
                bind_scalar_memory_bytes(source, final_bytes)?,
            )
        };
        let counts = [
            2,
            source.read_obligations().len(),
            source.write_obligations().len(),
            machine_queries.return_obligations().len(),
            machine_queries.memory_obligations().len(),
            machine_queries.read_obligations().len(),
            machine_queries.write_obligations().len(),
            byte_queries.return_obligations().len(),
            byte_queries.memory_obligations().len(),
            byte_queries.read_obligations().len(),
            byte_queries.write_obligations().len(),
        ];
        // Shared constructors already bound each inventory. Check cardinality
        // arithmetic before allocating the combined, non-cloning index list.
        let count = counts.into_iter().try_fold(0usize, |n, count| {
            n.checked_add(count).ok_or(ReadOnlyTargetError::Budget(
                "scalar-memory replay inventory",
            ))
        })?;
        let mut inventory = Vec::with_capacity(count);
        let mut append = |stage, kind, count| {
            inventory.extend((0..count).map(|index| ScalarMemoryRelationId { stage, kind, index }));
        };
        append(
            ScalarMemoryRelationStage::CoreToLir,
            ScalarMemoryRelationKind::Status,
            1,
        );
        append(
            ScalarMemoryRelationStage::CoreToLir,
            ScalarMemoryRelationKind::FinalMemory,
            1,
        );
        append(
            ScalarMemoryRelationStage::CoreToLir,
            ScalarMemoryRelationKind::Read,
            source.read_obligations().len(),
        );
        append(
            ScalarMemoryRelationStage::CoreToLir,
            ScalarMemoryRelationKind::Write,
            source.write_obligations().len(),
        );
        for (stage, queries) in [
            (ScalarMemoryRelationStage::CoreToMachine, &machine_queries),
            (ScalarMemoryRelationStage::CoreToFinalBytes, &byte_queries),
        ] {
            append(
                stage,
                ScalarMemoryRelationKind::Status,
                queries.return_obligations().len(),
            );
            append(
                stage,
                ScalarMemoryRelationKind::FinalMemory,
                queries.memory_obligations().len(),
            );
            append(
                stage,
                ScalarMemoryRelationKind::Read,
                queries.read_obligations().len(),
            );
            append(
                stage,
                ScalarMemoryRelationKind::Write,
                queries.write_obligations().len(),
            );
        }
        Ok(Self {
            source,
            machine,
            final_bytes,
            machine_queries,
            byte_queries,
            inventory,
        })
    }

    pub fn source(&self) -> &'a ScalarMemorySourceQueries<'a> {
        self.source
    }
    pub fn machine(&self) -> &'a MachFunction {
        self.machine
    }
    pub fn final_bytes(&self) -> &'a [u8] {
        self.final_bytes
    }
    pub fn machine_queries(&self) -> &ScalarMemoryTargetQueries<'a> {
        &self.machine_queries
    }
    pub fn byte_queries(&self) -> &ScalarMemoryTargetQueries<'a> {
        &self.byte_queries
    }
    pub fn len(&self) -> usize {
        self.inventory.len()
    }
    pub fn is_empty(&self) -> bool {
        self.inventory.is_empty()
    }

    /// Parts originate only in the complete privately assembled inventory.
    /// No arbitrary query, query name or externally constructed ID is admitted.
    pub fn parts(
        &self,
    ) -> impl ExactSizeIterator<Item = ScalarMemoryReplayPart<'_>> + DoubleEndedIterator {
        self.inventory.iter().map(|id| ScalarMemoryReplayPart {
            id: *id,
            obligation: self.obligation(*id),
        })
    }

    fn obligation(&self, id: ScalarMemoryRelationId) -> &ProofObligation {
        match id.stage {
            ScalarMemoryRelationStage::CoreToLir => match id.kind {
                ScalarMemoryRelationKind::Status => self.source.status_obligation(),
                ScalarMemoryRelationKind::FinalMemory => self.source.memory_obligation(),
                ScalarMemoryRelationKind::Read => &self.source.read_obligations()[id.index],
                ScalarMemoryRelationKind::Write => &self.source.write_obligations()[id.index],
            },
            stage => {
                let queries = match stage {
                    ScalarMemoryRelationStage::CoreToMachine => &self.machine_queries,
                    ScalarMemoryRelationStage::CoreToFinalBytes => &self.byte_queries,
                    ScalarMemoryRelationStage::CoreToLir => unreachable!(),
                };
                match id.kind {
                    ScalarMemoryRelationKind::Status => &queries.return_obligations()[id.index],
                    ScalarMemoryRelationKind::FinalMemory => {
                        &queries.memory_obligations()[id.index]
                    }
                    ScalarMemoryRelationKind::Read => &queries.read_obligations()[id.index],
                    ScalarMemoryRelationKind::Write => &queries.write_obligations()[id.index],
                }
            }
        }
    }

    pub(crate) fn policy_refusal(
        &self,
        request: &FunctionVerificationRequest,
    ) -> Option<ScalarMemoryReplayRefusal> {
        if request.mode() != ProvenanceXCheckMode::Enforce {
            Some(ScalarMemoryReplayRefusal::ProvenanceNotEnforced)
        } else if !request.config_matches(&VerificationConfig::for_proof_promotion()) {
            Some(ScalarMemoryReplayRefusal::ProofPromotionConfigurationMismatch)
        } else {
            None
        }
    }

    /// Replay through the shared exact original-part protocol under the SAME
    /// captured request. A non-Valid part stops later attempts, never coverage.
    pub fn replay<'r>(
        &'r self,
        request: &'r FunctionVerificationRequest,
    ) -> ScalarMemoryReplayReport<'r, 'a> {
        let refusal = self.policy_refusal(request);
        let context = FunctionDischargeContext::new(request);
        let outcomes = context.scalar_memory_relations(self);
        let all_valid = refusal.is_none()
            && !self.is_empty()
            && outcomes.len() == self.len()
            && outcomes.iter().zip(&self.inventory).all(|(outcome, id)| {
                outcome.id == *id
                    && outcome.attempted
                    && matches!(outcome.verdict, Some(VerificationResult::Valid))
            });
        let certificate = all_valid.then(|| ScalarMemoryReplayCertificate {
            relations: self,
            request,
            transport: if context.replays_bound() && request.reuse_identity().is_some() {
                ScalarMemoryReplayTransport::CapturedRequestBound
            } else {
                ScalarMemoryReplayTransport::FreshNonReusable
            },
        });
        ScalarMemoryReplayReport {
            relations: self,
            request,
            outcomes,
            refusal,
            certificate,
        }
    }
}

/// Sealed live replay capability for ONE exact inventory row. There is no
/// public constructor, Clone implementation or mutable obligation accessor.
pub struct ScalarMemoryReplayPart<'a> {
    id: ScalarMemoryRelationId,
    obligation: &'a ProofObligation,
}
impl ScalarMemoryReplayPart<'_> {
    pub fn id(&self) -> ScalarMemoryRelationId {
        self.id
    }
    pub fn obligation(&self) -> &ProofObligation {
        self.obligation
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ScalarMemoryReplayRefusal {
    ProvenanceNotEnforced,
    ProofPromotionConfigurationMismatch,
}
impl std::fmt::Display for ScalarMemoryReplayRefusal {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(match self {
            Self::ProvenanceNotEnforced => {
                "scalar-memory replay requires Enforce provenance policy"
            }
            Self::ProofPromotionConfigurationMismatch => {
                "scalar-memory replay requires the exact proof-promotion verification configuration"
            }
        })
    }
}

/// One diagnostic row for EVERY part, including those deliberately not run.
#[derive(Debug)]
pub struct ScalarMemoryReplayOutcome {
    id: ScalarMemoryRelationId,
    verdict: Option<VerificationResult>,
    why: Option<String>,
    attempted: bool,
}
impl ScalarMemoryReplayOutcome {
    pub(crate) fn replayed(
        id: ScalarMemoryRelationId,
        verdict: Option<VerificationResult>,
        why: Option<String>,
    ) -> Self {
        Self {
            id,
            verdict,
            why,
            attempted: true,
        }
    }
    pub(crate) fn not_run(id: ScalarMemoryRelationId, why: String) -> Self {
        Self {
            id,
            verdict: None,
            why: Some(why),
            attempted: false,
        }
    }
    pub fn id(&self) -> ScalarMemoryRelationId {
        self.id
    }
    pub fn verdict(&self) -> Option<&VerificationResult> {
        self.verdict.as_ref()
    }
    pub fn why(&self) -> Option<&str> {
        self.why.as_deref()
    }
    pub fn attempted(&self) -> bool {
        self.attempted
    }
}

/// Diagnostic transport only. Neither variant authorizes artifact reuse.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ScalarMemoryReplayTransport {
    CapturedRequestBound,
    FreshNonReusable,
}

/// EVERY exact relation independently replayed Valid under this request.
/// This immutable conditional evidence has no conversion to native, caller,
/// frame/ABI, per-instruction, publication or artifact/cache authority.
pub struct ScalarMemoryReplayCertificate<'r, 'a> {
    relations: &'r ScalarMemoryCompilerRelations<'a>,
    request: &'r FunctionVerificationRequest,
    transport: ScalarMemoryReplayTransport,
}
impl<'r, 'a> ScalarMemoryReplayCertificate<'r, 'a> {
    pub fn relations(&self) -> &'r ScalarMemoryCompilerRelations<'a> {
        self.relations
    }
    pub fn request(&self) -> &'r FunctionVerificationRequest {
        self.request
    }
    pub fn transport(&self) -> ScalarMemoryReplayTransport {
        self.transport
    }
}

pub struct ScalarMemoryReplayReport<'r, 'a> {
    relations: &'r ScalarMemoryCompilerRelations<'a>,
    request: &'r FunctionVerificationRequest,
    outcomes: Vec<ScalarMemoryReplayOutcome>,
    refusal: Option<ScalarMemoryReplayRefusal>,
    certificate: Option<ScalarMemoryReplayCertificate<'r, 'a>>,
}
impl<'r, 'a> ScalarMemoryReplayReport<'r, 'a> {
    /// Exact diagnostic query for the first actually attempted non-Valid
    /// original part, rendered inside this capture's existing policy. This
    /// is data only and grants no replay, caller or installation authority.
    pub fn first_failed_original_problem(&self) -> Option<String> {
        let (_, part) = self
            .outcomes
            .iter()
            .zip(self.relations.parts())
            .find(|(outcome, _)| {
                outcome.attempted() && !matches!(outcome.verdict(), Some(VerificationResult::Valid))
            })?;
        Some(self.request.with_policy(|| {
            crate::ay_bridge::generate_smt2_query_raw(
                part.obligation(),
                &crate::verdict_db::live_source_bound_config(),
            )
        }))
    }

    pub fn relations(&self) -> &'r ScalarMemoryCompilerRelations<'a> {
        self.relations
    }
    pub fn request(&self) -> &'r FunctionVerificationRequest {
        self.request
    }
    pub fn outcomes(&self) -> &[ScalarMemoryReplayOutcome] {
        &self.outcomes
    }
    pub fn refusal(&self) -> Option<ScalarMemoryReplayRefusal> {
        self.refusal
    }
    pub fn certificate(&self) -> Option<&ScalarMemoryReplayCertificate<'r, 'a>> {
        self.certificate.as_ref()
    }
    /// Consume the actual complete replay capability. Refused/partial
    /// diagnostics remain retained and cannot mint a source/storage owner.
    pub fn into_certificate(mut self) -> Result<ScalarMemoryReplayCertificate<'r, 'a>, Self> {
        self.certificate.take().ok_or(self)
    }
}

/// Exact void normal-return, final-byte and access inventory. The private
/// shared protocol is reused; no scalar query owner/certificate is exported.
/// A successful replay remains conditional on the real caller-memory owner.
pub struct VoidMemoryCompilerRelations<'a> {
    source: &'a crate::source_bound_frame::VoidMemorySourceQueries<'a>,
    inner: ScalarMemoryCompilerRelations<'a>,
}
impl<'a> VoidMemoryCompilerRelations<'a> {
    pub fn bind(
        source: &'a crate::source_bound_frame::VoidMemorySourceQueries<'a>,
        machine: &'a MachFunction,
        final_bytes: &'a [u8],
    ) -> Result<Self, ReadOnlyTargetError> {
        if !source.inner.is_void() {
            return Err(ReadOnlyTargetError::Machine(
                "missing void terminal identity",
            ));
        }
        Ok(Self {
            source,
            inner: ScalarMemoryCompilerRelations::bind_memory(&source.inner, machine, final_bytes)?,
        })
    }
    pub fn source(&self) -> &'a crate::source_bound_frame::VoidMemorySourceQueries<'a> {
        self.source
    }
    pub fn machine(&self) -> &'a MachFunction {
        self.inner.machine
    }
    pub fn final_bytes(&self) -> &'a [u8] {
        self.inner.final_bytes
    }
    pub fn len(&self) -> usize {
        self.inner.len()
    }
    pub fn is_empty(&self) -> bool {
        self.inner.is_empty()
    }
    pub fn parts(
        &self,
    ) -> impl ExactSizeIterator<Item = VoidMemoryReplayPart<'_>> + DoubleEndedIterator {
        self.inner
            .parts()
            .map(|inner| VoidMemoryReplayPart { inner })
    }
    pub fn replay<'r>(
        &'r self,
        request: &'r FunctionVerificationRequest,
    ) -> VoidMemoryReplayReport<'r, 'a> {
        VoidMemoryReplayReport {
            relations: self,
            inner: self.inner.replay(request),
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum VoidMemoryRelationKind {
    NormalReturn,
    FinalMemory,
    Read,
    Write,
}
fn void_kind(kind: ScalarMemoryRelationKind) -> VoidMemoryRelationKind {
    match kind {
        ScalarMemoryRelationKind::Status => VoidMemoryRelationKind::NormalReturn,
        ScalarMemoryRelationKind::FinalMemory => VoidMemoryRelationKind::FinalMemory,
        ScalarMemoryRelationKind::Read => VoidMemoryRelationKind::Read,
        ScalarMemoryRelationKind::Write => VoidMemoryRelationKind::Write,
    }
}
pub struct VoidMemoryReplayPart<'p> {
    inner: ScalarMemoryReplayPart<'p>,
}
impl VoidMemoryReplayPart<'_> {
    pub fn stage(&self) -> ScalarMemoryRelationStage {
        self.inner.id.stage
    }
    pub fn kind(&self) -> VoidMemoryRelationKind {
        void_kind(self.inner.id.kind)
    }
    pub fn index(&self) -> usize {
        self.inner.id.index
    }
    pub fn obligation(&self) -> &ProofObligation {
        self.inner.obligation
    }
}
pub struct VoidMemoryReplayOutcome<'p> {
    inner: &'p ScalarMemoryReplayOutcome,
}
impl VoidMemoryReplayOutcome<'_> {
    pub fn stage(&self) -> ScalarMemoryRelationStage {
        self.inner.id.stage
    }
    pub fn kind(&self) -> VoidMemoryRelationKind {
        void_kind(self.inner.id.kind)
    }
    pub fn index(&self) -> usize {
        self.inner.id.index
    }
    pub fn verdict(&self) -> Option<&VerificationResult> {
        self.inner.verdict()
    }
    pub fn why(&self) -> Option<&str> {
        self.inner.why()
    }
    pub fn attempted(&self) -> bool {
        self.inner.attempted()
    }
}
pub struct VoidMemoryReplayReport<'r, 'a> {
    relations: &'r VoidMemoryCompilerRelations<'a>,
    inner: ScalarMemoryReplayReport<'r, 'a>,
}
impl<'r, 'a> VoidMemoryReplayReport<'r, 'a> {
    /// Diagnostic original problem for the first actual non-Valid part,
    /// rendered under THIS capture's policy and the unchanged live raw-query
    /// owner. It is neither a verdict nor a transferable replay capability.
    pub fn first_failed_original_problem(&self) -> Option<String> {
        let (_, part) = self
            .outcomes()
            .zip(self.relations.parts())
            .find(|(outcome, _)| {
                outcome.attempted() && !matches!(outcome.verdict(), Some(VerificationResult::Valid))
            })?;
        Some(self.inner.request.with_policy(|| {
            crate::ay_bridge::generate_smt2_query_raw(
                part.obligation(),
                &crate::verdict_db::live_source_bound_config(),
            )
        }))
    }
    pub fn outcomes(&self) -> impl ExactSizeIterator<Item = VoidMemoryReplayOutcome<'_>> {
        self.inner
            .outcomes
            .iter()
            .map(|inner| VoidMemoryReplayOutcome { inner })
    }
    pub fn refusal(&self) -> Option<ScalarMemoryReplayRefusal> {
        self.inner.refusal
    }
    pub fn is_complete(&self) -> bool {
        self.inner.certificate.is_some()
    }
    /// Move the actual all-parts replay receipt. No hash/ID/DTO or generic
    /// successful report can mint this typed conditional owner.
    pub fn into_certificate(mut self) -> Result<VoidMemoryReplayCertificate<'r, 'a>, Self> {
        match self.inner.certificate.take() {
            Some(receipt) => Ok(VoidMemoryReplayCertificate {
                relations: self.relations,
                receipt,
            }),
            None => Err(self),
        }
    }
}
pub struct VoidMemoryReplayCertificate<'r, 'a> {
    relations: &'r VoidMemoryCompilerRelations<'a>,
    receipt: ScalarMemoryReplayCertificate<'r, 'a>,
}
impl<'r, 'a> VoidMemoryReplayCertificate<'r, 'a> {
    pub fn relations(&self) -> &'r VoidMemoryCompilerRelations<'a> {
        self.relations
    }
    pub fn request(&self) -> &'r FunctionVerificationRequest {
        self.receipt.request
    }
    pub fn transport(&self) -> ScalarMemoryReplayTransport {
        self.receipt.transport
    }
}
