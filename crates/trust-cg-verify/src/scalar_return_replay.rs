// Copyright 2026 Andrew Yates | Apache-2.0

//! Source-bound replay for every ordered internal scalar result, complete
//! byte memory, and every read/write demand. This is conditional semantic
//! evidence only; it cannot manufacture a native provider, call/stack ABI,
//! memory permission, per-instruction credit or executable artifact.

use crate::FunctionVerificationRequest;
use crate::function_request::FunctionDischargeContext;
use crate::lowering_proof::{ProofObligation, VerificationConfig};
use crate::provenance_xcheck::ProvenanceXCheckMode;
use crate::read_only_replay::{
    ScalarMemoryRelationStage, ScalarMemoryReplayRefusal, ScalarMemoryReplayTransport,
};
use crate::read_only_target::{
    ReadOnlyTargetError, ScalarReturnTargetQueries, bind_scalar_return_bytes,
    bind_scalar_return_machine,
};
use crate::source_bound_frame::ScalarReturnSourceQueries;
use crate::verify::VerificationResult;
use trust_cg_ir::MachFunction;

#[cfg(all(test, target_arch = "aarch64", target_os = "macos"))]
#[path = "scalar_return_replay_tests.rs"]
mod tests;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum ScalarReturnRelationKind {
    OrderedResult,
    FinalMemory,
    Read,
    Write,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct ScalarReturnRelationId {
    pub stage: ScalarMemoryRelationStage,
    pub kind: ScalarReturnRelationKind,
    /// OrderedResult is lane-indexed at CoreToLir, and path-major then
    /// lane-indexed at either actual target endpoint.
    pub index: usize,
}

pub struct ScalarReturnCompilerRelations<'a> {
    source: &'a ScalarReturnSourceQueries<'a>,
    machine: &'a MachFunction,
    final_bytes: &'a [u8],
    machine_queries: ScalarReturnTargetQueries<'a>,
    byte_queries: ScalarReturnTargetQueries<'a>,
    inventory: Vec<ScalarReturnRelationId>,
}

impl<'a> ScalarReturnCompilerRelations<'a> {
    pub fn bind(
        source: &'a ScalarReturnSourceQueries<'a>,
        machine: &'a MachFunction,
        final_bytes: &'a [u8],
    ) -> Result<Self, ReadOnlyTargetError> {
        let machine_queries = bind_scalar_return_machine(source, machine)?;
        let byte_queries = bind_scalar_return_bytes(source, final_bytes)?;
        let groups = [
            (
                ScalarMemoryRelationStage::CoreToLir,
                [
                    source.return_obligations().len(),
                    1,
                    source.read_obligations().len(),
                    source.write_obligations().len(),
                ],
            ),
            (
                ScalarMemoryRelationStage::CoreToMachine,
                [
                    machine_queries.return_obligations().len(),
                    machine_queries.memory_obligations().len(),
                    machine_queries.read_obligations().len(),
                    machine_queries.write_obligations().len(),
                ],
            ),
            (
                ScalarMemoryRelationStage::CoreToFinalBytes,
                [
                    byte_queries.return_obligations().len(),
                    byte_queries.memory_obligations().len(),
                    byte_queries.read_obligations().len(),
                    byte_queries.write_obligations().len(),
                ],
            ),
        ];
        let count = groups
            .iter()
            .flat_map(|(_, counts)| counts)
            .try_fold(0usize, |n, count| n.checked_add(*count))
            .ok_or(ReadOnlyTargetError::Budget(
                "scalar-return replay inventory",
            ))?;
        let mut inventory = Vec::with_capacity(count);
        for (stage, counts) in groups {
            for (kind, count) in [
                ScalarReturnRelationKind::OrderedResult,
                ScalarReturnRelationKind::FinalMemory,
                ScalarReturnRelationKind::Read,
                ScalarReturnRelationKind::Write,
            ]
            .into_iter()
            .zip(counts)
            {
                inventory.extend((0..count).map(|index| ScalarReturnRelationId {
                    stage,
                    kind,
                    index,
                }));
            }
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
    pub fn source(&self) -> &'a ScalarReturnSourceQueries<'a> {
        self.source
    }
    pub fn machine(&self) -> &'a MachFunction {
        self.machine
    }
    pub fn final_bytes(&self) -> &'a [u8] {
        self.final_bytes
    }
    pub fn machine_queries(&self) -> &ScalarReturnTargetQueries<'a> {
        &self.machine_queries
    }
    pub fn byte_queries(&self) -> &ScalarReturnTargetQueries<'a> {
        &self.byte_queries
    }
    pub fn len(&self) -> usize {
        self.inventory.len()
    }
    pub fn is_empty(&self) -> bool {
        self.inventory.is_empty()
    }
    pub fn parts(
        &self,
    ) -> impl ExactSizeIterator<Item = ScalarReturnReplayPart<'_>> + DoubleEndedIterator {
        self.inventory.iter().map(|id| ScalarReturnReplayPart {
            id: *id,
            obligation: self.obligation(*id),
        })
    }
    fn obligation(&self, id: ScalarReturnRelationId) -> &ProofObligation {
        use ScalarReturnRelationKind::*;
        if id.stage == ScalarMemoryRelationStage::CoreToLir {
            return match id.kind {
                OrderedResult => &self.source.return_obligations()[id.index],
                FinalMemory => self.source.memory_obligation(),
                Read => &self.source.read_obligations()[id.index],
                Write => &self.source.write_obligations()[id.index],
            };
        }
        let queries = match id.stage {
            ScalarMemoryRelationStage::CoreToMachine => &self.machine_queries,
            ScalarMemoryRelationStage::CoreToFinalBytes => &self.byte_queries,
            ScalarMemoryRelationStage::CoreToLir => unreachable!(),
        };
        match id.kind {
            OrderedResult => &queries.return_obligations()[id.index],
            FinalMemory => &queries.memory_obligations()[id.index],
            Read => &queries.read_obligations()[id.index],
            Write => &queries.write_obligations()[id.index],
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
    /// One existing captured request, no recapture or renewed budget. The
    /// first non-Valid part stops replay; every later part remains not-run.
    pub fn replay<'r>(
        &'r self,
        request: &'r FunctionVerificationRequest,
    ) -> ScalarReturnReplayReport<'r, 'a> {
        let refusal = self.policy_refusal(request);
        let context = FunctionDischargeContext::new(request);
        let outcomes = context.scalar_return_relations(self);
        let all_valid = refusal.is_none()
            && !self.is_empty()
            && outcomes.len() == self.len()
            && outcomes.iter().zip(&self.inventory).all(|(outcome, id)| {
                outcome.id == *id
                    && outcome.attempted
                    && matches!(outcome.verdict, Some(VerificationResult::Valid))
            });
        let certificate = all_valid.then(|| ScalarReturnReplayCertificate {
            relations: self,
            request,
            transport: if context.replays_bound() && request.reuse_identity().is_some() {
                ScalarMemoryReplayTransport::CapturedRequestBound
            } else {
                ScalarMemoryReplayTransport::FreshNonReusable
            },
        });
        ScalarReturnReplayReport {
            relations: self,
            request,
            outcomes,
            refusal,
            certificate,
        }
    }
}

/// Only the complete privately constructed inventory can issue these parts.
pub struct ScalarReturnReplayPart<'a> {
    id: ScalarReturnRelationId,
    obligation: &'a ProofObligation,
}
impl ScalarReturnReplayPart<'_> {
    pub fn id(&self) -> ScalarReturnRelationId {
        self.id
    }
    pub fn obligation(&self) -> &ProofObligation {
        self.obligation
    }
}

#[derive(Debug)]
pub struct ScalarReturnReplayOutcome {
    id: ScalarReturnRelationId,
    verdict: Option<VerificationResult>,
    why: Option<String>,
    attempted: bool,
}
impl ScalarReturnReplayOutcome {
    pub(crate) fn new(
        id: ScalarReturnRelationId,
        verdict: Option<VerificationResult>,
        why: Option<String>,
        attempted: bool,
    ) -> Self {
        Self {
            id,
            verdict,
            why,
            attempted,
        }
    }
    pub fn id(&self) -> ScalarReturnRelationId {
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

/// All exact relations independently replayed Valid. The source geometry is
/// still conditional, and no provider/ABI/storage/native conversion exists.
pub struct ScalarReturnReplayCertificate<'r, 'a> {
    relations: &'r ScalarReturnCompilerRelations<'a>,
    request: &'r FunctionVerificationRequest,
    transport: ScalarMemoryReplayTransport,
}
impl<'r, 'a> ScalarReturnReplayCertificate<'r, 'a> {
    pub fn relations(&self) -> &'r ScalarReturnCompilerRelations<'a> {
        self.relations
    }
    pub fn request(&self) -> &'r FunctionVerificationRequest {
        self.request
    }
    pub fn transport(&self) -> ScalarMemoryReplayTransport {
        self.transport
    }
}
pub struct ScalarReturnReplayReport<'r, 'a> {
    relations: &'r ScalarReturnCompilerRelations<'a>,
    request: &'r FunctionVerificationRequest,
    outcomes: Vec<ScalarReturnReplayOutcome>,
    refusal: Option<ScalarMemoryReplayRefusal>,
    certificate: Option<ScalarReturnReplayCertificate<'r, 'a>>,
}
impl<'r, 'a> ScalarReturnReplayReport<'r, 'a> {
    pub fn relations(&self) -> &'r ScalarReturnCompilerRelations<'a> {
        self.relations
    }
    pub fn request(&self) -> &'r FunctionVerificationRequest {
        self.request
    }
    pub fn outcomes(&self) -> &[ScalarReturnReplayOutcome] {
        &self.outcomes
    }
    pub fn refusal(&self) -> Option<ScalarMemoryReplayRefusal> {
        self.refusal
    }
    pub fn certificate(&self) -> Option<&ScalarReturnReplayCertificate<'r, 'a>> {
        self.certificate.as_ref()
    }
}
