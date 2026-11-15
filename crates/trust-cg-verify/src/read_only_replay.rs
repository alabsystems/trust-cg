// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! Immutable original-Core/LIR/MachIR/final-word relation inventory.
//!
//! Construction is pending evidence. Only independent replay of EVERY exact
//! inventory part under one captured, enforcing proof-promotion request yields
//! the conditional certificate below. This certificate concerns these encoded
//! relations only: the Rust transcriptions remain their stated trusted base.
//! It is not instruction/form credit, a caller-memory or ABI capability, a
//! native/publication receipt, or permission to reuse an artifact from a cache.
//! Caller readability, provenance, initialization, stable Normal memory,
//! untagged addresses and disabled GCS remain external requirements.

use crate::FunctionVerificationRequest;
use crate::function_request::FunctionDischargeContext;
use crate::lowering_proof::{ProofObligation, VerificationConfig};
use crate::provenance_xcheck::ProvenanceXCheckMode;
use crate::read_only_target::{
    ReadOnlyTargetError, ReadOnlyTargetQueries, bind_read_only_bytes, bind_read_only_machine,
};
use crate::source_bound_frame::ReadOnlySourceQueries;
use crate::verify::VerificationResult;
use trust_cg_ir::MachFunction;

#[path = "read_only_result.rs"]
mod result;

#[path = "scalar_memory_replay.rs"]
mod scalar_memory;
pub use scalar_memory::{
    ScalarMemoryCompilerRelations, ScalarMemoryRelationId, ScalarMemoryRelationKind,
    ScalarMemoryRelationStage, ScalarMemoryReplayCertificate, ScalarMemoryReplayOutcome,
    ScalarMemoryReplayPart, ScalarMemoryReplayRefusal, ScalarMemoryReplayReport,
    ScalarMemoryReplayTransport,
};

#[path = "scalar_return_replay.rs"]
mod scalar_returns;
pub use scalar_returns::{
    ScalarReturnCompilerRelations, ScalarReturnRelationId, ScalarReturnRelationKind,
    ScalarReturnReplayCertificate, ScalarReturnReplayOutcome, ScalarReturnReplayPart,
    ScalarReturnReplayReport,
};

#[cfg(test)]
#[path = "read_only_replay_tests.rs"]
mod tests;

#[cfg(all(test, target_arch = "aarch64", target_os = "macos"))]
#[path = "read_only_replay_diagnostic_tests.rs"]
mod diagnostic_tests;

/// Source endpoints are retained, not inferred from the spelling of a query.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum ReadOnlyRelationStage {
    CoreToLir,
    CoreToMachine,
    CoreToFinalBytes,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum ReadOnlyRelationKind {
    Return,
    Load,
}

/// An index into one exact stage/kind inventory, not an instruction license.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct ReadOnlyRelationId {
    pub stage: ReadOnlyRelationStage,
    pub kind: ReadOnlyRelationKind,
    pub index: usize,
}

/// Borrowed immutable source and actual endpoints with deterministic complete
/// query coverage. Only the existing source/target binders construct queries.
pub struct ReadOnlyCompilerRelations<'a> {
    source: &'a ReadOnlySourceQueries<'a>,
    machine: &'a MachFunction,
    final_bytes: &'a [u8],
    machine_queries: ReadOnlyTargetQueries<'a>,
    byte_queries: ReadOnlyTargetQueries<'a>,
    inventory: Vec<ReadOnlyRelationId>,
}

impl<'a> ReadOnlyCompilerRelations<'a> {
    pub fn bind(
        source: &'a ReadOnlySourceQueries<'a>,
        machine: &'a MachFunction,
        final_bytes: &'a [u8],
    ) -> Result<Self, ReadOnlyTargetError> {
        let machine_queries = bind_read_only_machine(source, machine)?;
        let byte_queries = bind_read_only_bytes(source, final_bytes)?;
        let mut inventory = vec![ReadOnlyRelationId {
            stage: ReadOnlyRelationStage::CoreToLir,
            kind: ReadOnlyRelationKind::Return,
            index: 0,
        }];
        let mut append = |stage, kind, count| {
            inventory.extend((0..count).map(|index| ReadOnlyRelationId { stage, kind, index }));
        };
        append(
            ReadOnlyRelationStage::CoreToLir,
            ReadOnlyRelationKind::Load,
            source.load_obligations().len(),
        );
        for (stage, queries) in [
            (ReadOnlyRelationStage::CoreToMachine, &machine_queries),
            (ReadOnlyRelationStage::CoreToFinalBytes, &byte_queries),
        ] {
            append(
                stage,
                ReadOnlyRelationKind::Return,
                queries.return_obligations().len(),
            );
            append(
                stage,
                ReadOnlyRelationKind::Load,
                queries.load_obligations().len(),
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

    pub fn source(&self) -> &'a ReadOnlySourceQueries<'a> {
        self.source
    }
    pub fn machine(&self) -> &'a MachFunction {
        self.machine
    }
    pub fn final_bytes(&self) -> &'a [u8] {
        self.final_bytes
    }
    pub fn machine_queries(&self) -> &ReadOnlyTargetQueries<'a> {
        &self.machine_queries
    }
    pub fn byte_queries(&self) -> &ReadOnlyTargetQueries<'a> {
        &self.byte_queries
    }
    pub fn len(&self) -> usize {
        self.inventory.len()
    }
    pub fn is_empty(&self) -> bool {
        self.inventory.is_empty()
    }

    /// Capabilities can only originate in this privately built inventory.
    /// Neither an arbitrary query nor a query name constructs a replay part.
    pub fn parts(
        &self,
    ) -> impl ExactSizeIterator<Item = ReadOnlyReplayPart<'_>> + DoubleEndedIterator {
        self.inventory.iter().map(|id| ReadOnlyReplayPart {
            id: *id,
            obligation: self.obligation(*id),
        })
    }

    fn obligation(&self, id: ReadOnlyRelationId) -> &ProofObligation {
        match id.stage {
            ReadOnlyRelationStage::CoreToLir => match id.kind {
                ReadOnlyRelationKind::Return => self.source.return_obligation(),
                ReadOnlyRelationKind::Load => &self.source.load_obligations()[id.index],
            },
            stage => {
                let queries = match stage {
                    ReadOnlyRelationStage::CoreToMachine => &self.machine_queries,
                    ReadOnlyRelationStage::CoreToFinalBytes => &self.byte_queries,
                    ReadOnlyRelationStage::CoreToLir => unreachable!(),
                };
                match id.kind {
                    ReadOnlyRelationKind::Return => &queries.return_obligations()[id.index],
                    ReadOnlyRelationKind::Load => &queries.load_obligations()[id.index],
                }
            }
        }
    }

    pub(crate) fn policy_refusal(
        &self,
        request: &FunctionVerificationRequest,
    ) -> Option<ReadOnlyReplayRefusal> {
        if request.mode() != ProvenanceXCheckMode::Enforce {
            Some(ReadOnlyReplayRefusal::ProvenanceNotEnforced)
        } else if !request.config_matches(&VerificationConfig::for_proof_promotion()) {
            Some(ReadOnlyReplayRefusal::ProofPromotionConfigurationMismatch)
        } else {
            None
        }
    }

    /// Replay serially under the original captured authority; stop at the
    /// first non-Valid part, preserving every later inventory row as not run.
    /// No solver UNSAT, statistical result or plain report can certify this.
    pub fn replay<'r>(
        &'r self,
        request: &'r FunctionVerificationRequest,
    ) -> ReadOnlyReplayReport<'r, 'a> {
        let refusal = self.policy_refusal(request);
        let context = FunctionDischargeContext::new(request);
        let outcomes = context.read_only_relations(self);
        let all_valid = refusal.is_none()
            && !self.is_empty()
            && outcomes.len() == self.len()
            && outcomes.iter().zip(&self.inventory).all(|(outcome, id)| {
                outcome.id == *id
                    && outcome.attempted
                    && matches!(outcome.verdict, Some(VerificationResult::Valid))
            });
        let certificate = all_valid.then(|| ReadOnlyReplayCertificate {
            relations: self,
            request,
            transport: if context.replays_bound() && request.reuse_identity().is_some() {
                ReadOnlyReplayTransport::CapturedRequestBound
            } else {
                ReadOnlyReplayTransport::FreshNonReusable
            },
        });
        ReadOnlyReplayReport {
            relations: self,
            request,
            outcomes,
            refusal,
            certificate,
        }
    }
}

/// A sealed live-replay capability for one original-source-bound relation.
/// There is deliberately no public constructor, clone or mutable query getter.
pub struct ReadOnlyReplayPart<'a> {
    id: ReadOnlyRelationId,
    obligation: &'a ProofObligation,
}
impl ReadOnlyReplayPart<'_> {
    pub fn id(&self) -> ReadOnlyRelationId {
        self.id
    }
    pub fn obligation(&self) -> &ProofObligation {
        self.obligation
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ReadOnlyReplayRefusal {
    ProvenanceNotEnforced,
    ProofPromotionConfigurationMismatch,
}
impl std::fmt::Display for ReadOnlyReplayRefusal {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(match self {
            Self::ProvenanceNotEnforced => "read-only replay requires Enforce provenance policy",
            Self::ProofPromotionConfigurationMismatch => {
                "read-only replay requires the exact proof-promotion verification configuration"
            }
        })
    }
}

/// A diagnostic for EVERY inventory item, including those not replayed.
#[derive(Debug)]
pub struct ReadOnlyReplayOutcome {
    id: ReadOnlyRelationId,
    verdict: Option<VerificationResult>,
    why: Option<String>,
    attempted: bool,
}
impl ReadOnlyReplayOutcome {
    pub(crate) fn replayed(
        id: ReadOnlyRelationId,
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
    pub(crate) fn not_run(id: ReadOnlyRelationId, why: String) -> Self {
        Self {
            id,
            verdict: None,
            why: Some(why),
            attempted: false,
        }
    }
    pub fn id(&self) -> ReadOnlyRelationId {
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

/// Diagnostic transport only; neither variant authorizes cache reuse.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ReadOnlyReplayTransport {
    CapturedRequestBound,
    FreshNonReusable,
}

/// All relations independently replayed Valid under this exact request.
/// This immutable conditional evidence has no conversion to native, frame,
/// memory-permission, per-instruction or artifact/cache authority.
pub struct ReadOnlyReplayCertificate<'r, 'a> {
    relations: &'r ReadOnlyCompilerRelations<'a>,
    request: &'r FunctionVerificationRequest,
    transport: ReadOnlyReplayTransport,
}
impl<'r, 'a> ReadOnlyReplayCertificate<'r, 'a> {
    pub fn relations(&self) -> &'r ReadOnlyCompilerRelations<'a> {
        self.relations
    }
    pub fn request(&self) -> &'r FunctionVerificationRequest {
        self.request
    }
    pub fn transport(&self) -> ReadOnlyReplayTransport {
        self.transport
    }
    /// Instantiate the actual original return-memory expression only after
    /// EVERY compiler/machine/final-byte relation has replayed. These are
    /// caller candidate expressions, not physical inputs or memory authority.
    /// Original read/geometry premises and actual caller ABI correspondence
    /// remain owed by the composed caller; no normal return is asserted here.
    pub fn instantiate_result(
        &self,
        arguments: &[std::sync::Arc<crate::smt::SmtExpr>],
        entry_memory: &std::sync::Arc<crate::smt::SmtExpr>,
    ) -> Result<std::sync::Arc<crate::smt::SmtExpr>, String> {
        result::instantiate(self.relations.source(), arguments, entry_memory)
    }
}

pub struct ReadOnlyReplayReport<'r, 'a> {
    relations: &'r ReadOnlyCompilerRelations<'a>,
    request: &'r FunctionVerificationRequest,
    outcomes: Vec<ReadOnlyReplayOutcome>,
    refusal: Option<ReadOnlyReplayRefusal>,
    certificate: Option<ReadOnlyReplayCertificate<'r, 'a>>,
}
impl<'r, 'a> ReadOnlyReplayReport<'r, 'a> {
    pub fn relations(&self) -> &'r ReadOnlyCompilerRelations<'a> {
        self.relations
    }
    pub fn request(&self) -> &'r FunctionVerificationRequest {
        self.request
    }
    pub fn outcomes(&self) -> &[ReadOnlyReplayOutcome] {
        &self.outcomes
    }
    pub fn refusal(&self) -> Option<ReadOnlyReplayRefusal> {
        self.refusal
    }
    pub fn certificate(&self) -> Option<&ReadOnlyReplayCertificate<'r, 'a>> {
        self.certificate.as_ref()
    }
}
