// Copyright 2026 Andrew Yates | Apache-2.0

//! Additional whole Source/Core ownership over the existing one-word native
//! peer. Native emission, complete frame/callee replay, final linking, physical
//! storage and installation remain owned by the ordinary peer pipeline.
//! The source proof covers every supported U64 argument once; invocation does
//! not build a proof or specialize the original caller to a constant.

use super::*;
use trust_cg_verify::core_defined_call_entry::DefinedCallSourceSelection;
use trust_ir_build::clean_kernel::{Environment, Expr};

struct SourceWordEvidence {
    // Clone the SAME Arc allocation. A module clone/digest match cannot inherit
    // the original borrowed source/Core proof's custody.
    module: Arc<trust_ir::Module>,
    caller: trust_ir::FuncId,
    callee: trust_ir::FuncId,
    judgment: Expr,
    proof: Expr,
    environment: Environment,
    argument_codec_claim: Expr,
    argument_codec_proof: Expr,
}

fn source_evidence(
    peer: &ConditionalCorePeerArtifact,
    selection: &DefinedCallSourceSelection,
) -> Result<SourceWordEvidence, String> {
    if !trust_cg_process_env::artifact_reuse_environment_safety().is_reuse_safe() {
        return Err("source word entry contains unkeyed controls".into());
    }
    let module = &peer.plan.plan.parts.module;
    let requirement = peer.prepared.link.requirement();
    if requirement.argument_count() != 1
        || requirement.function() != selection.caller
        || requirement.callee() != selection.callee
        || requirement.module_digest() != module.stable_digest()
    {
        return Err("source/Core selection differs from the original one-word native peer".into());
    }
    let report = trust_ir_build::validate_module_with_config(
        module,
        &trust_ir_build::ValidationConfig::pinned()
            .with_bound_certificates(true)
            .with_source_bound_certificates(true)
            .with_gate_evidence(true),
    );
    let core = trust_ir_build::core_execution::derive_defined_word_add_call_entry(
        &report,
        selection.caller,
        selection.callee,
    )
    .map_err(|e| format!("original universal word Core entry: {e}"))?;
    let source =
        trust_ir_build::source_call_operational::check_source_bound_defined_word_add_call_entry(
            &report,
            &core,
            &selection.island,
            &selection.caller_source,
            &selection.callee_source,
        )
        .map_err(|e| format!("independent source/universal Core word entry: {e}"))?;
    let (caller, callee) = source.functions_in(module).map_err(|e| e.to_string())?;
    if caller != selection.caller || callee != selection.callee {
        return Err("checked source/Core word entry selects other original functions".into());
    }
    Ok(SourceWordEvidence {
        module: Arc::clone(module),
        caller,
        callee,
        judgment: source.judgment().clone(),
        proof: source.proof().clone(),
        environment: source.environment().clone(),
        argument_codec_claim: source.argument_codec_claim().clone(),
        argument_codec_proof: source.argument_codec_proof().clone(),
    })
}

/// Retained original conditional peer when the additional source/Core check
/// refuses. A partial source proof creates no entry or installation authority.
pub struct CoreWordSourceFailure {
    reason: String,
    predecessor: ConditionalCorePeerArtifact,
}
impl std::fmt::Debug for CoreWordSourceFailure {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("CoreWordSourceFailure")
            .field("reason", &self.reason)
            .finish_non_exhaustive()
    }
}
impl std::fmt::Display for CoreWordSourceFailure {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(&self.reason)
    }
}
impl std::error::Error for CoreWordSourceFailure {}
impl CoreWordSourceFailure {
    pub fn reason(&self) -> &str {
        &self.reason
    }
    pub fn predecessor(&self) -> &ConditionalCorePeerArtifact {
        &self.predecessor
    }
    pub fn into_predecessor(self) -> ConditionalCorePeerArtifact {
        self.predecessor
    }
}

/// Whole source/Core evidence coupled to the SAME original pending native peer.
/// Real writable storage and normal publication permissions remain owed.
pub struct CoreSourceWordPeerArtifact {
    peer: ConditionalCorePeerArtifact,
    source: SourceWordEvidence,
}
impl std::fmt::Debug for CoreSourceWordPeerArtifact {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("CoreSourceWordPeerArtifact")
            .field("caller", &self.source.caller)
            .field("callee", &self.source.callee)
            .finish_non_exhaustive()
    }
}

impl ConditionalCorePeerArtifact {
    /// Check actual initialization, all five original Core steps and halt for
    /// every canonical U64, plus the independent source declarations and codec.
    /// The current profile is a closed C(U64)->U64 forwarding caller and an
    /// internal CONST/U64-ADD/RETURN leaf; other bodies remain refused.
    /// The checked native peer already authenticates its actual parameter,
    /// returned result, frame and final BL; none is supplied as a new premise.
    pub fn check_source_word_entry(
        self,
        selection: &DefinedCallSourceSelection,
    ) -> Result<CoreSourceWordPeerArtifact, CoreWordSourceFailure> {
        match source_evidence(&self, selection) {
            Ok(source) => Ok(CoreSourceWordPeerArtifact { peer: self, source }),
            Err(reason) => Err(CoreWordSourceFailure {
                reason,
                predecessor: self,
            }),
        }
    }
}

impl CoreSourceWordPeerArtifact {
    pub fn source_judgment(&self) -> &Expr {
        &self.source.judgment
    }
    /// Preserve the ordinary peer's real stack, certificate lifetimes, final
    /// image readback, manifest/ABI and native-install gates. This adds no raw
    /// function-pointer conversion or alternate certificate constructor.
    pub fn install_owned_stack(
        self,
        stack: OwnedEntryStack,
        manifest: ArtifactManifestV1,
        generation: CompileGeneration,
    ) -> Result<(CoreSourceWordEntry, ArtifactManifestV1), EntryStackError> {
        if !Arc::ptr_eq(&self.source.module, &self.peer.plan.plan.parts.module)
            || self.source.caller != self.peer.prepared.source_function
            || self.source.callee != self.peer.prepared.link.requirement().callee()
        {
            return Err(EntryStackError::Source(
                "original source/Core peer custody changed".into(),
            ));
        }
        let (entry, manifest) = self.peer.install_owned_stack(stack, manifest, generation)?;
        Ok((
            CoreSourceWordEntry {
                entry,
                source: self.source,
            },
            manifest,
        ))
    }
}

/// Installed parameterized source program. The closed source/Core theorem and
/// argument codec remain owned beside the original module and native entry.
/// Logical empty-memory/Nat-HOST0 scope does not grant a TY/provider relation.
pub struct CoreSourceWordEntry {
    entry: CoreBoundPeerEntry,
    source: SourceWordEvidence,
}
impl std::fmt::Debug for CoreSourceWordEntry {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("CoreSourceWordEntry")
            .field("caller", &self.source.caller)
            .field("callee", &self.source.callee)
            .finish_non_exhaustive()
    }
}
impl CoreSourceWordEntry {
    pub fn source_function(&self) -> trust_ir::FuncId {
        self.source.caller
    }
    pub fn required_private_stack_bytes(&self) -> usize {
        self.entry.required_private_stack_bytes()
    }
    pub fn proof_evidence(&self) -> &crate::jit_contract::ProofEvidenceSummary {
        self.entry.entry.proof_evidence()
    }
    pub fn original_module(&self) -> &trust_ir::Module {
        &self.source.module
    }
    pub fn source_judgment(&self) -> &Expr {
        &self.source.judgment
    }
    pub fn source_proof(&self) -> &Expr {
        &self.source.proof
    }
    pub fn source_environment(&self) -> &Environment {
        &self.source.environment
    }
    pub fn argument_codec_claim(&self) -> &Expr {
        &self.source.argument_codec_claim
    }
    pub fn argument_codec_proof(&self) -> &Expr {
        &self.source.argument_codec_proof
    }
    /// U64 is the exact shared source/Core/ABI carrier. The existing native
    /// owner takes a fresh exclusive loan of its actual stack on every call.
    pub fn invoke1_u64(&mut self, argument: u64) -> Result<u64, EntryStackError> {
        self.entry.invoke1_u64(argument)
    }
}
