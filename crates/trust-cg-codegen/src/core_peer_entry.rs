// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! Conditional compilation stays non-promotable until this consuming owner
//! takes actual RW storage. The same mapping remains owned through publication
//! and every invocation. Caller certificates contain only a Weak reference to
//! this private real owner: checked certificate status expires with storage.
//! Generic compile/install APIs never receive the conditional result.

use super::*;
use crate::compile_service::CompileGeneration;
use crate::jit::entry_stack::{EntryStackError, OwnedEntryStack, SourceEntryStackRequirement};
use crate::jit_contract::ArtifactManifestV1;
use sha2::{Digest, Sha256};
use std::sync::{Arc, Mutex};
use trust_cg_verify::function_verifier::{
    FunctionVerificationReport, InstructionOpcode, InstructionReport, InstructionVerificationResult,
};

pub(super) struct PreparedPeer {
    pub(super) previous: Vec<CoreAddressFreeMachineFunction>,
    pub(super) caller: trust_cg_ir::MachFunction,
    pub(super) source_function: trust_ir::FuncId,
    pub(super) final_code: Vec<u8>,
    pub(super) symbolic_digest: trust_ir::proof::ProofDigest,
    pub(super) verifier_input: [u8; 32],
    pub(super) link: super::core_peer_link::CoreCheckedPeerLink,
    pub(super) inventory: CoreAddressFreeFixupInventory,
    pub(super) proof_bundle: CoreProofBundleAccumulator,
    pub(super) proof_optimization_certificates: Vec<ProofOptimizationCertificateCitation>,
    pub(super) code_size_bytes: usize,
    pub(super) machine_code_evidence: AArch64MachineCodeEvidence,
    pub(super) caller_machine_code_evidence: AArch64MachineCodeEvidence,
}

/// Non-callable conditional output. Its diagnostic report remains Unverified;
/// it exposes neither generic certificates nor ordinary arithmetic exports.
pub struct ConditionalCorePeerArtifact {
    plan: PolicyQualifiedCoreJitCompilationPlan,
    prepared: PreparedPeer,
}
impl std::fmt::Debug for ConditionalCorePeerArtifact {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("ConditionalCorePeerArtifact")
            .field("function", &self.prepared.source_function)
            .field("physical_storage_pending", &true)
            .finish_non_exhaustive()
    }
}

/// Owns the actual storage and exact conditional source/final-link replay.
/// Private construction below requires an actual exclusive mapping loan.
/// A certificate can hold only Weak custody of this owner, never a numeric mint.
pub(crate) struct CoreBoundPeerProof {
    stack: Mutex<OwnedEntryStack>,
    requirement: SourceEntryStackRequirement,
    link: super::core_peer_link::CoreCheckedPeerLink,
    entry_sp: usize,
    allocation: u64,
    binding_digest: trust_ir::proof::ProofDigest,
    function: String,
    input: [u8; 32],
}
impl std::fmt::Debug for CoreBoundPeerProof {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("CoreBoundPeerProof")
            .field("function", &self.function)
            .field("binding", &self.binding_digest)
            .finish_non_exhaustive()
    }
}

/// Existing opaque entry plus its privately retained actual stack owner.
/// No raw entry, installed buffer, stack swap, clone or serialization is exposed.
pub struct CoreBoundPeerEntry {
    entry: CoreOwnedStackEntry,
    storage: Arc<CoreBoundPeerProof>,
}
impl std::fmt::Debug for CoreBoundPeerEntry {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("CoreBoundPeerEntry")
            .field("entry", &self.entry)
            .finish_non_exhaustive()
    }
}

impl PolicyQualifiedCoreJitCompilationPlan {
    pub fn compile_for_owned_peer_entry(
        self,
        entry: &str,
    ) -> Result<ConditionalCorePeerArtifact, CoreAddressFreeMachineCompilationFailure> {
        let mut rejection = None;
        let result = (|| {
            super::core_artifact_install::source_contract(&self.plan.parts.module)
                .map_err(CompileError::CoreInstallationContract)?;
            if !self.plan.native_runtime_catalog.is_empty()
                || !self
                    .plan
                    .parts
                    .declared_import_manifest
                    .imports()
                    .is_empty()
            {
                return Err(CompileError::CoreInstallationContract(
                    "conditional peers require complete empty provider/import inventories".into(),
                )
                .into());
            }
            match compile_policy_qualified_core_machine_mode(&self, &mut rejection, Some(entry))? {
                CoreMachineCompilationOutcome::Conditional(prepared) => Ok(prepared),
                CoreMachineCompilationOutcome::Ordinary(_) => Err(
                    CompileError::CoreInstallationContract("conditional peer owner missing".into())
                        .into(),
                ),
            }
        })();
        match result {
            Ok(prepared) => Ok(ConditionalCorePeerArtifact {
                plan: self,
                prepared,
            }),
            Err(error) => Err(CoreAddressFreeMachineCompilationFailure {
                error,
                plan: self,
                machine_rejection: rejection,
            }),
        }
    }
}

impl ConditionalCorePeerArtifact {
    pub fn source_function(&self) -> trust_ir::FuncId {
        self.prepared.source_function
    }
    pub fn required_private_stack_bytes(&self) -> usize {
        self.prepared
            .link
            .requirement()
            .required_private_stack_bytes()
    }
    pub fn diagnostic_report(&self) -> FunctionVerificationReport {
        self.prepared.link.replay().diagnostic_report()
    }
    /// A checked resource observation alone grants no report/certificate grade.
    pub fn check_entry_storage(&self, stack: &mut OwnedEntryStack) -> Result<(), EntryStackError> {
        let requirement =
            SourceEntryStackRequirement::from_conditional_peer(self.prepared.link.requirement())?;
        let invocation = stack.borrow_invocation(&requirement)?;
        let _binding = invocation.bind_peer_requirement(self.prepared.link.requirement())?;
        Ok(())
    }
    /// Consume both conditional source and a real owned mapping. The mapping
    /// remains private to the returned entry through every certificate lifetime.
    pub fn install_owned_stack(
        self,
        stack: OwnedEntryStack,
        manifest: ArtifactManifestV1,
        generation: CompileGeneration,
    ) -> Result<(CoreBoundPeerEntry, ArtifactManifestV1), EntryStackError> {
        let ConditionalCorePeerArtifact { plan, prepared } = self;
        super::core_artifact_install::source_contract(&plan.plan.parts.module)
            .map_err(EntryStackError::Source)?;
        let PreparedPeer {
            mut previous,
            caller,
            source_function,
            final_code,
            symbolic_digest,
            verifier_input,
            link,
            inventory,
            mut proof_bundle,
            proof_optimization_certificates,
            code_size_bytes,
            machine_code_evidence,
            caller_machine_code_evidence,
        } = prepared;
        let source = plan
            .plan
            .parts
            .lir_functions
            .iter()
            .find(|(lir, _)| lir.name == caller.name)
            .map(|(lir, _)| lir)
            .ok_or_else(|| EntryStackError::Source("retained actual caller LIR missing".into()))?;
        let modules = trust_cg_verify::FunctionSourceModules::capture(
            &plan.plan.parts.module,
            &plan.plan.parts.module,
        )
        .map_err(|e| EntryStackError::Source(e.to_string()))?;
        if !link
            .replay()
            .original_caller()
            .matches_aarch64_input_with_modules(&caller, Some(source), &modules)
        {
            return Err(EntryStackError::Source(
                "conditional actual caller input changed".into(),
            ));
        }
        link.check_prepared(
            &plan.plan.parts.module,
            &previous,
            source_function,
            &caller.name,
            caller.text_align_log2,
            &final_code,
            &inventory,
        )
        .map_err(EntryStackError::Source)?;
        let storage = CoreBoundPeerProof::new(stack, link, caller.name.clone(), verifier_input)?;
        let (certificate, function_proofs) =
            storage.issue_caller_certificate(&caller, &final_code)?;
        let compiler = Compiler::new_for_target_spec(
            plan.plan.effective_options.compiler_config.clone(),
            plan.plan.effective_options.target_spec,
        );
        compiler
            .ensure_proofs_promotable(Some(&function_proofs))
            .map_err(|e| EntryStackError::Source(e.to_string()))?;
        proof_bundle
            .extend(&function_proofs)
            .map_err(|e| EntryStackError::Source(e.to_string()))?;
        let certificate_digest = trust_ir::proof::ProofDigest::sha256(
            certificate
                .core_semantic_digest()
                .ok_or(EntryStackError::Extent)?,
        );
        let code_digest = trust_ir::proof::ProofDigest::sha256(Sha256::digest(&final_code).into());
        previous.push(CoreAddressFreeMachineFunction {
            source_function,
            name: caller.name.clone(),
            text_align_log2: caller.text_align_log2,
            code: final_code,
            normalized_code_digest: code_digest,
            symbolic_fixup_manifest_digest: symbolic_digest,
            certificate_digest,
            certificate,
            function_target_features: caller.function_target_features,
            machine_code_evidence: caller_machine_code_evidence,
            defined_callee: Ok(None),
        });
        let proof_report_count = proof_bundle.len();
        let verified_proof_report_count = proof_bundle.verified_count;
        let proof_bundle_digest = proof_bundle
            .finish()
            .map_err(|e| EntryStackError::Source(e.to_string()))?;
        let proof_opt =
            core_address_free_proof_optimization_digest(&proof_optimization_certificates)
                .map_err(|e| EntryStackError::Source(e.to_string()))?;
        let identity = core_address_free_machine_identity(
            &plan.plan,
            &previous,
            &inventory,
            proof_bundle_digest,
            proof_opt,
        )
        .map_err(|e| EntryStackError::Source(e.to_string()))?;
        let compiled = PreparedCoreAddressFreeMachine {
            functions: previous,
            fixup_inventory: inventory,
            proof_optimization_certificates,
            proof_report_count,
            verified_proof_report_count,
            proof_bundle_digest,
            code_size_bytes,
            machine_code_evidence,
            identity,
        };
        let (artifact, source) =
            into_core_address_free_machine_artifact_with_source(plan, compiled);
        let core =
            super::core_artifact_install::CoreInstallationArtifact::from_physically_bound_peer(
                artifact,
                source,
                verified_proof_report_count,
                &storage,
            )
            .map_err(EntryStackError::Source)?;
        let (installed, manifest) = core
            .install_physically_bound_peer(&storage, manifest, generation)
            .map_err(EntryStackError::Publication)?;
        storage
            .check_image(installed.buffer.code_slice())
            .map_err(EntryStackError::Source)?;
        let requirement =
            SourceEntryStackRequirement::from_conditional_peer(storage.link.requirement())?;
        let entry = CoreOwnedStackEntry::new(installed, manifest.clone(), caller.name, requirement);
        Ok((CoreBoundPeerEntry { entry, storage }, manifest))
    }
}

impl CoreBoundPeerProof {
    fn new(
        mut stack: OwnedEntryStack,
        link: super::core_peer_link::CoreCheckedPeerLink,
        function: String,
        input: [u8; 32],
    ) -> Result<Arc<Self>, EntryStackError> {
        let requirement = SourceEntryStackRequirement::from_conditional_peer(link.requirement())?;
        let (entry_sp, allocation) = {
            let invocation = stack.borrow_invocation(&requirement)?;
            let binding = invocation.bind_peer_requirement(link.requirement())?;
            (binding.entry_sp(), binding.allocation_identity())
        };
        let mut hash = Sha256::new();
        hash.update(b"trust-cg.actual-owned-peer-entry.v1\0");
        hash.update(link.requirement().module_digest().bytes);
        hash.update(link.requirement().final_image_digest().bytes);
        hash.update(input);
        hash.update((entry_sp as u64).to_le_bytes());
        hash.update(allocation.to_le_bytes());
        hash.update(Sha256::digest(
            trust_cg_verify::serialize_to_smt2(link.replay().statement()).as_bytes(),
        ));
        let binding_digest = trust_ir::proof::ProofDigest::sha256(hash.finalize().into());
        Ok(Arc::new(Self {
            stack: Mutex::new(stack),
            requirement,
            link,
            entry_sp,
            allocation,
            binding_digest,
            function,
            input,
        }))
    }
    pub(crate) fn binding_digest(&self) -> trust_ir::proof::ProofDigest {
        self.binding_digest
    }
    pub(crate) fn matches_certificate(
        &self,
        function: &str,
        input: &str,
        code: &str,
        binding: trust_ir::proof::ProofDigest,
    ) -> bool {
        self.binding_digest == binding
            && self.function == function
            && input == crate::jit_cert::digest_hex(&self.input)
            && code
                == crate::jit_cert::digest_hex(&self.link.requirement().final_code_digest().bytes)
    }
    fn issue_caller_certificate(
        self: &Arc<Self>,
        machine: &trust_cg_ir::MachFunction,
        code: &[u8],
    ) -> Result<(crate::jit_cert::JitCertificate, Vec<ProofCertificate>), EntryStackError> {
        if machine.name != self.function
            || trust_ir::proof::ProofDigest::sha256(Sha256::digest(code).into())
                != self.link.requirement().final_code_digest()
        {
            return Err(EntryStackError::Source(
                "physically bound peer code/input differs".into(),
            ));
        }
        let query = Sha256::digest(
            trust_cg_verify::serialize_to_smt2(self.link.replay().statement()).as_bytes(),
        );
        let name = format!(
            "{}; original-query={query:x}; actual-storage={}",
            self.link.replay().statement().name,
            self.binding_digest
        );
        let report = FunctionVerificationReport {
            function_name: machine.name.clone(),
            precondition_failure: None,
            instructions: self
                .link
                .replay()
                .covered_instructions()
                .iter()
                .map(|id| InstructionReport {
                    inst_index: id.0 as usize,
                    opcode: InstructionOpcode::AArch64(machine.insts[id.0 as usize].opcode),
                    result: InstructionVerificationResult::Verified {
                        proof_name: name.clone(),
                        category: trust_cg_verify::proof_database::ProofCategory::FrameLayout,
                        strength: trust_cg_verify::VerificationStrength::Formal,
                        degenerate: false,
                    },
                })
                .collect(),
        };
        // This ordinary view exists only inside the real mapped-storage owner.
        // It never leaves through the conditional public API or a plain export.
        let proofs = proof_certificates_from_aarch64_report_with_obligations(
            &report,
            &[],
            crate::decode_check::DecodeCheckBacking::Enforced,
        );
        let certificate = crate::jit_cert::JitCertificate::from_physically_bound_peer(
            machine,
            &report,
            0..code.len() as u64,
            self.input,
            Sha256::digest(code).into(),
            self,
        )
        .with_request_ay_refusal_note(self.link.replay().original_caller().ay_refusal_note());
        if !certificate.has_checked_semantics() || !certificate.replay_check() {
            return Err(EntryStackError::Source(
                "physically bound peer certificate refused".into(),
            ));
        }
        Ok((certificate, proofs))
    }
    pub(super) fn check_artifact(
        &self,
        artifact: &CoreAddressFreeMachineArtifact,
        source: &CoreCompilationSource,
    ) -> Result<(), String> {
        self.link.check(artifact, source)
    }
    pub(crate) fn caller(&self) -> trust_ir::FuncId {
        self.link.caller()
    }
    pub(crate) fn check_image(&self, image: &[u8]) -> Result<(), String> {
        self.link.check_running_image(image)
    }
    pub(crate) fn branch(&self) -> (&str, usize, usize) {
        self.link.branch()
    }
}

impl CoreBoundPeerEntry {
    pub fn source_function(&self) -> trust_ir::FuncId {
        self.entry.source_function()
    }
    pub fn required_private_stack_bytes(&self) -> usize {
        self.entry.required_private_stack_bytes()
    }
    pub fn invoke0_u64(&mut self) -> Result<u64, EntryStackError> {
        self.invoke_scalar_u64(None)
    }

    /// Invoke the checked one-U64 forwarding caller through the same owned
    /// stack and final-image lifetime. Other source signatures still refuse.
    pub fn invoke1_u64(&mut self, argument: u64) -> Result<u64, EntryStackError> {
        self.invoke_scalar_u64(Some(argument))
    }

    fn invoke_scalar_u64(&mut self, argument: Option<u64>) -> Result<u64, EntryStackError> {
        let actual = usize::from(argument.is_some());
        if self.storage.requirement.argument_count != actual {
            return Err(EntryStackError::ArgumentCount {
                expected: self.storage.requirement.argument_count,
                actual,
            });
        }
        let mut stack = self
            .storage
            .stack
            .lock()
            .map_err(|_| EntryStackError::Source("owned peer storage mutex poisoned".into()))?;
        if stack.allocation().identity != self.storage.allocation {
            return Err(EntryStackError::StaleInvocation);
        }
        {
            let call = stack.borrow_invocation(&self.storage.requirement)?;
            let binding = call.bind_peer_requirement(self.storage.link.requirement())?;
            if binding.entry_sp() != self.storage.entry_sp {
                return Err(EntryStackError::StaleInvocation);
            }
        }
        match argument {
            None => self.entry.invoke0_u64(&mut stack),
            Some(value) => self.entry.invoke1_u64(&mut stack, value),
        }
    }
}

#[cfg(feature = "source-defined-call")]
#[path = "core_peer_source_word.rs"]
mod source_word;
#[cfg(feature = "source-defined-call")]
pub use source_word::{CoreSourceWordEntry, CoreSourceWordPeerArtifact, CoreWordSourceFailure};

#[cfg(all(test, target_arch = "aarch64", target_os = "macos"))]
#[path = "../tests/common/private_peer_entry.rs"]
mod tests;
