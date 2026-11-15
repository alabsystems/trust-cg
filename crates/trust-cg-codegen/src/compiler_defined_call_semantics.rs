// Copyright 2026 Andrew Yates | Apache-2.0

//! A checked original-source/Core and actual linked-machine entry. The owner
//! retains the genuine rejected row report unchanged. Its successful aggregate
//! replay is separate evidence, not a manufactured per-function certificate.
//! This module grants no mapping, publication, provider or stack permission.

use super::CoreDefinedCallLinkedImage;
use trust_cg_verify::core_defined_call_entry::{
    DefinedCallSourceSelection, derive_core_defined_call_source,
};
use trust_cg_verify::lowering_proof::ProofObligation;
use trust_cg_verify::source_bound_defined_call::DefinedCallTrace;
use trust_ir::proof::ProofDigest;
use trust_ir_build::clean_kernel::{Environment, Expr};

/// Move-only semantic evidence for this exact immutable linked image. Public
/// byte vectors, source labels and proposed SMT conclusions cannot mint it.
/// The source theorem's first world is explicit: empty abstract byte memory,
/// Nat HOST0, no imports, and the actual initializer/four-step/halt execution.
/// The native trace separately quantifies its register/memory inputs, assuming
/// aligned nonwrapping disjoint image/stack placement and live private storage.
pub struct CoreCheckedDefinedCallImage {
    linked: CoreDefinedCallLinkedImage,
    source_judgment: Expr,
    source_proof: Expr,
    source_environment: Environment,
    native_obligation: ProofObligation,
    private_stack_bytes: usize,
    executed_words: usize,
    replayed_parts: usize,
    native_part_provenance: Vec<Option<String>>,
    caller: trust_ir::FuncId,
    callee: trust_ir::FuncId,
    identity: ProofDigest,
}

impl std::fmt::Debug for CoreCheckedDefinedCallImage {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("CoreCheckedDefinedCallImage")
            .field("linked", &self.linked)
            .field("caller", &self.caller)
            .field("callee", &self.callee)
            .field("identity", &self.identity)
            .finish_non_exhaustive()
    }
}

/// Failure retains the exact linked predecessor and its original rejected
/// report. Neither partial proof construction nor a solver error is admitted.
pub struct CoreDefinedCallSemanticFailure {
    reason: String,
    predecessor: CoreDefinedCallLinkedImage,
}
impl std::fmt::Debug for CoreDefinedCallSemanticFailure {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("CoreDefinedCallSemanticFailure")
            .field("reason", &self.reason)
            .finish_non_exhaustive()
    }
}
impl std::fmt::Display for CoreDefinedCallSemanticFailure {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(&self.reason)
    }
}
impl std::error::Error for CoreDefinedCallSemanticFailure {}
impl CoreDefinedCallSemanticFailure {
    pub fn reason(&self) -> &str {
        &self.reason
    }
    pub fn predecessor(&self) -> &CoreDefinedCallLinkedImage {
        &self.predecessor
    }
    pub fn into_predecessor(self) -> CoreDefinedCallLinkedImage {
        self.predecessor
    }
}

struct CheckedParts {
    judgment: Expr,
    proof: Expr,
    environment: Environment,
    obligation: ProofObligation,
    private_bytes: usize,
    words: usize,
    parts: usize,
    provenance: Vec<Option<String>>,
    identity: ProofDigest,
}

fn derive(
    linked: &CoreDefinedCallLinkedImage,
    selection: &DefinedCallSourceSelection,
) -> Result<CheckedParts, String> {
    let endpoints = linked.verification_endpoints()?;
    let report = trust_ir_build::validate_module_with_config(
        endpoints.module(),
        &trust_ir_build::ValidationConfig::pinned()
            .with_bound_certificates(true)
            .with_source_bound_certificates(true)
            .with_gate_evidence(true),
    );
    let source = derive_core_defined_call_source(&report, selection)
        .map_err(|e| format!("original source/Core entry: {e}"))?;
    let bytes = endpoints
        .check_bytes()
        .map_err(|e| format!("actual linked source/LIR/bytes: {e}"))?;
    let (caller, callee) = source.functions_in(bytes.module())?;
    if caller != bytes.source().id || callee != bytes.callee().checked_bytes().source().id {
        return Err(
            "source/Core and actual linked trace select different original functions".into(),
        );
    }
    let trace =
        DefinedCallTrace::build(&bytes).map_err(|e| format!("actual linked word trace: {e}"))?;
    let replay = trace
        .replay(endpoints.request())
        .map_err(|e| format!("independent native aggregate replay: {e}"))?;
    if !replay.matches_request(endpoints.request()) {
        return Err("aggregate replay belongs to another original request".into());
    }
    // Digests are custody/correlation only. The constructors above perform
    // the actual canonical source/kernel and independent native replay.
    let judgment = trust_ir::proof::encode_clean_expr_dag_v2(source.judgment())
        .map_err(|e| format!("closed source judgment codec: {e:?}"))?;
    let proof = trust_ir::proof::encode_clean_expr_dag_v2(source.proof())
        .map_err(|e| format!("closed source proof codec: {e:?}"))?;
    let identity = super::core_address_free_encoded_digest(
        "trust-cg.checked-original-source-linked-defined-entry.v1",
        |sink| {
            super::core_identity_digest(sink, linked.identity())?;
            super::core_identity_u32(sink, caller.index())?;
            super::core_identity_u32(sink, callee.index())?;
            for source in [&selection.caller_source, &selection.callee_source] {
                super::core_identity_str(sink, &source.decl)?;
                super::core_identity_digest(sink, source.closure_digest)?;
            }
            super::core_identity_digest(
                sink,
                ProofDigest::sha256(crate::jit_cert::sha256_digest(&judgment)),
            )?;
            super::core_identity_digest(
                sink,
                ProofDigest::sha256(crate::jit_cert::sha256_digest(&proof)),
            )?;
            Ok(())
        },
    )
    .map_err(|e| e.to_string())?;
    Ok(CheckedParts {
        judgment: source.judgment().clone(),
        proof: source.proof().clone(),
        environment: source.environment().clone(),
        obligation: trace.obligation().clone(),
        private_bytes: bytes.required_private_stack_bytes(),
        words: trace.executed_words(),
        parts: replay.checked_parts(),
        provenance: replay.part_provenance().to_vec(),
        identity,
    })
}

impl CoreDefinedCallLinkedImage {
    /// Consume this original-module linked image only after BOTH its selected
    /// source/Core theorem and actual-word native trace pass their real owners.
    /// No callee result/termination premise, caller certificate or arbitrary
    /// source/solver proposal is accepted as an argument.
    pub fn check_source(
        self,
        selection: &DefinedCallSourceSelection,
    ) -> Result<CoreCheckedDefinedCallImage, CoreDefinedCallSemanticFailure> {
        if !trust_cg_process_env::artifact_reuse_environment_safety().is_reuse_safe() {
            return Err(CoreDefinedCallSemanticFailure {
                reason: "checked-image environment contains unkeyed controls".into(),
                predecessor: self,
            });
        }
        // These immutable mathematics are checked under the retained request's
        // explicit policy scopes. They perform no artifact-cache transaction;
        // those scopes correctly invalidate an OUTER cache epoch permit.
        // Acquire a NEW permit only for receipt construction after they end.
        // This owner grants no cache reuse or native publication permission.
        let checked = derive(&self, selection).and_then(|parts| {
            let permit = trust_cg_process_env::artifact_reuse_permit()
                .ok_or_else(|| "checked-image environment permit unavailable".to_string())?;
            if permit.is_valid() {
                Ok(parts)
            } else {
                Err("checked-image environment changed during receipt construction".into())
            }
        });
        match checked {
            Err(reason) => Err(CoreDefinedCallSemanticFailure {
                reason,
                predecessor: self,
            }),
            Ok(parts) => Ok(CoreCheckedDefinedCallImage {
                linked: self,
                source_judgment: parts.judgment,
                source_proof: parts.proof,
                source_environment: parts.environment,
                native_obligation: parts.obligation,
                private_stack_bytes: parts.private_bytes,
                executed_words: parts.words,
                replayed_parts: parts.parts,
                native_part_provenance: parts.provenance,
                caller: selection.caller,
                callee: selection.callee,
                identity: parts.identity,
            }),
        }
    }
}

impl CoreCheckedDefinedCallImage {
    pub fn linked(&self) -> &CoreDefinedCallLinkedImage {
        &self.linked
    }
    pub fn source_judgment(&self) -> &Expr {
        &self.source_judgment
    }
    pub fn source_proof(&self) -> &Expr {
        &self.source_proof
    }
    pub fn source_environment(&self) -> &Environment {
        &self.source_environment
    }
    pub fn native_obligation(&self) -> &ProofObligation {
        &self.native_obligation
    }
    pub fn required_private_stack_bytes(&self) -> usize {
        self.private_stack_bytes
    }
    pub fn executed_words(&self) -> usize {
        self.executed_words
    }
    /// All independently checked conjunctive parts; not per-function reports.
    pub fn replayed_native_parts(&self) -> usize {
        self.replayed_parts
    }
    pub fn native_part_provenance(&self) -> &[Option<String>] {
        &self.native_part_provenance
    }
    pub fn caller(&self) -> trust_ir::FuncId {
        self.caller
    }
    pub fn callee(&self) -> trust_ir::FuncId {
        self.callee
    }
    pub fn identity(&self) -> ProofDigest {
        self.identity
    }
}
