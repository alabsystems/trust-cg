// Copyright 2026 Andrew Yates | Apache-2.0
//! Source-owned flat four-pointer/U64 entry. Numeric signatures or pending
//! memory queries cannot construct its source, replay, storage or image owners.
use super::*;
use crate::compile_service::{CompileGeneration, InstalledArtifact};
use crate::jit::context_output::{OwnedEntryContext, OwnedEntryOutput, disjoint};
use crate::jit::entry_stack::{EntryStackError, OwnedEntryStack, SourceEntryStackRequirement};
use crate::jit_contract::{ArtifactManifestV1, SymbolLookupContract};
use sha2::{Digest, Sha256};
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::{Arc, Mutex};
use trust_cg_verify::function_verifier::{
    FunctionVerificationReport, InstructionOpcode, InstructionReport, InstructionVerificationResult,
};
use trust_cg_verify::read_only_replay::{
    FourWordStatusClaim, ReplayedFourWordStatusClaim, ReplayedWordStatusCompilation,
    ScalarMemoryCompilerRelations,
};
use trust_ir_build::source_word_status_entry::{WordStatusEntryAccess, WordStatusEntryAddress};
struct Storage {
    inputs: [OwnedEntryContext<[u64]>; 2],
    outputs: [OwnedEntryOutput; 2],
    stack: OwnedEntryStack,
}
impl Storage {
    fn extents(&self) -> Result<[(usize, usize); 4], EntryStackError> {
        Ok([
            self.inputs[0].extent()?,
            self.inputs[1].extent()?,
            self.outputs[0].extent()?,
            self.outputs[1].extent()?,
        ])
    }
    fn words(&self) -> [u64; 4] {
        [
            self.inputs[0].value()[0],
            self.inputs[1].value()[0],
            self.outputs[0].words()[0],
            self.outputs[1].words()[0],
        ]
    }
    fn check_footprint(
        &self,
        accesses: &[WordStatusEntryAccess],
        addresses: &[WordStatusEntryAddress],
    ) -> Result<(), EntryStackError> {
        if self
            .inputs
            .iter()
            .any(|p| p.initialized_words() != Some(1) || p.value().len() != 1)
            || self.outputs.iter().any(|p| p.words().len() != 1)
        {
            return Err(EntryStackError::Source(
                "four-pointer owner requires exactly one initialized word per original role".into(),
            ));
        }
        let extents = self.extents()?;
        let stack = self.stack.mapped_extent()?;
        for (i, &a) in extents.iter().enumerate() {
            if a.1.checked_sub(a.0) != Some(8) || !a.0.is_multiple_of(8) {
                return Err(EntryStackError::Extent);
            }
            disjoint(a, stack)?;
            for &b in &extents[..i] {
                disjoint(a, b)?;
            }
        }
        for access in accesses {
            if access.role() >= 4
                || access.offset() != 0
                || access.alignment() != 8
                || access.is_write() != (access.role() >= 2)
                || !matches!(
                    access.ty(),
                    trust_ir::Ty::Ptr | trust_ir::Ty::I64 | trust_ir::Ty::U64
                )
            {
                return Err(EntryStackError::Source(
                    "original access is outside flat word roles/permissions".into(),
                ));
            }
        }
        for address in addresses {
            if address.role() >= 4
                || address.is_inbounds()
                || address.base_offset() != 0
                || address.offset() != 0
            {
                return Err(EntryStackError::Source(
                    "original derived address is outside flat word geometry".into(),
                ));
            }
        }
        Ok(())
    }
}
pub(super) struct StatusCompilation {
    storage: Option<Storage>,
    target_spec: crate::target::TargetSpec,
    pub(super) bound: Option<Arc<CoreBoundFourPointerStatusProof>>,
}
impl StatusCompilation {
    pub(super) fn bind(
        &mut self,
        module: &Arc<trust_ir::Module>,
        verification: &CoreSourceVerification<'_>,
        lir: &trust_cg_lower::Function,
        machine: &trust_cg_ir::MachFunction,
        code: &[u8],
        original: &trust_cg_verify::CapturedFunctionVerificationReport,
    ) -> Result<Arc<CoreBoundFourPointerStatusProof>, String> {
        if self.bound.is_some() || module.functions.len() != 1 {
            return Err("status entry requires one complete actual closed definition".into());
        }
        let storage = self
            .storage
            .take()
            .ok_or("status storage already consumed")?;
        let (storage, replay) = crate::jit_cert::run_on_proof_verifier_stack(
            "trust-cg-four-pointer-replay",
            move || {
                let config = trust_ir_build::ValidationConfig::pinned()
                    .with_bound_certificates(true)
                    .with_source_bound_certificates(true)
                    .with_gate_evidence(true);
                let report = trust_ir_build::validate_module_with_config(module, &config);
                let family =
                    trust_ir_build::source_word_status_entry::check_word_status_entry_source(
                        &report,
                    )?;
                storage
                    .check_footprint(family.accesses(), family.addresses())
                    .map_err(|e| e.to_string())?;
                let queries =
                    trust_cg_verify::source_bound_frame::bind_licensed_word_status_source(
                        &family, lir,
                    )?;
                let relations = ScalarMemoryCompilerRelations::bind(&queries, machine, code)
                    .map_err(|e| e.to_string())?;
                let result = relations.replay(&verification.request);
                let receipt = result.into_certificate().map_err(|r| {
                    let failed=r.outcomes().iter().zip(relations.parts()).find(|(outcome,_)|outcome.attempted() && !matches!(outcome.verdict(),Some(trust_cg_verify::verify::VerificationResult::Valid)));
                    let diagnostic=failed.map(|(outcome,part)| {
                        let raw=r.first_failed_original_problem().expect("the same actual first failed original part");
                        serde_json::json!({"scope":"diagnostic exact original failed four-pointer replay; no authority","part":format!("{:?}",part.id()),"verdict":format!("{:?}",outcome.verdict()),"why":outcome.why(),"smt2_sha256":format!("{:x}",Sha256::digest(raw.as_bytes())),"smt2":raw,"module_digest":module.stable_digest().to_string(),"matches_original_capture":original.matches_request_capture(&verification.request),"actual_ay":verification.request.ay_solver().map(|ay|ay.describe()),"lir":lir,"machine_debug":format!("{machine:#?}"),"final_bytes":code})
                    });
                    format!(
                        "complete original four-pointer replay refused: {:?}\nEXACT_FOUR_POINTER_REPLAY_FAILURE_JSON_BEGIN\n{}\nEXACT_FOUR_POINTER_REPLAY_FAILURE_JSON_END",
                        r.outcomes()
                            .iter()
                            .map(|o| (
                                o.id().stage,
                                o.id().kind,
                                o.attempted(),
                                o.why().map(str::to_owned)
                            ))
                            .collect::<Vec<_>>(),
                        diagnostic.map_or_else(||"null".into(),|value|value.to_string())
                    )
                })?;
                let replay =
                    receipt.retain_word_status(Arc::clone(module), &family, original.clone())?;
                Ok::<_, String>((storage, replay))
            },
        )?;
        let owner = CoreBoundFourPointerStatusProof::new(
            storage,
            replay,
            machine.name.clone(),
            verification
                .input_digest(machine, lir)
                .map_err(|e| e.to_string())?,
            self.target_spec,
        )
        .map_err(|e| e.to_string())?;
        self.bound = Some(Arc::clone(&owner));
        Ok(owner)
    }
}
pub(crate) struct CoreBoundFourPointerStatusProof {
    storage: Mutex<Storage>,
    replay: ReplayedWordStatusCompilation,
    requirement: SourceEntryStackRequirement,
    extents: [(usize, usize); 4],
    stack_identity: u64,
    entry_sp: usize,
    function: String,
    input: [u8; 32],
    binding: trust_ir::proof::ProofDigest,
    signature: crate::jit_contract::SymbolSignature,
    generation: AtomicU64,
}
impl std::fmt::Debug for CoreBoundFourPointerStatusProof {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("CoreBoundFourPointerStatusProof")
            .field("function", &self.function)
            .field("binding", &self.binding)
            .finish_non_exhaustive()
    }
}
impl CoreBoundFourPointerStatusProof {
    fn new(
        mut storage: Storage,
        replay: ReplayedWordStatusCompilation,
        function: String,
        input: [u8; 32],
        target: crate::target::TargetSpec,
    ) -> Result<Arc<Self>, EntryStackError> {
        storage.check_footprint(replay.accesses(), replay.addresses())?;
        let signature = crate::compile_service::symbol_signature_for_core_function(
            replay.module(),
            replay.function(),
            target,
        )
        .map_err(EntryStackError::Source)?;
        let requirement = SourceEntryStackRequirement::from_replayed_word_status_entry(&replay)?;
        let extents = storage.extents()?;
        let stack_identity = storage.stack.allocation().identity;
        let entry_sp = storage
            .stack
            .borrow_invocation(&requirement)?
            .actual_entry_sp();
        let mut hash = Sha256::new();
        hash.update(b"trust-cg.actual-owned-four-pointer-status.v1\0");
        hash.update(replay.statement_digest().bytes);
        hash.update(input);
        for (a, b) in extents {
            hash.update((a as u64).to_le_bytes());
            hash.update((b as u64).to_le_bytes());
        }
        hash.update((entry_sp as u64).to_le_bytes());
        hash.update(stack_identity.to_le_bytes());
        Ok(Arc::new(Self {
            storage: Mutex::new(storage),
            replay,
            requirement,
            extents,
            stack_identity,
            entry_sp,
            function,
            input,
            binding: trust_ir::proof::ProofDigest::sha256(hash.finalize().into()),
            signature,
            generation: AtomicU64::new(0),
        }))
    }
    pub(crate) fn binding_digest(&self) -> trust_ir::proof::ProofDigest {
        self.binding
    }
    pub(crate) fn matches_certificate(
        &self,
        function: &str,
        input: &str,
        code: &str,
        binding: trust_ir::proof::ProofDigest,
    ) -> bool {
        function == self.function
            && input == crate::jit_cert::digest_hex(&self.input)
            && code
                == crate::jit_cert::digest_hex(&Sha256::digest(self.replay.final_bytes()).into())
            && binding == self.binding
    }
    pub(super) fn report(
        &self,
        machine: &trust_cg_ir::MachFunction,
    ) -> Result<FunctionVerificationReport, String> {
        if machine.name != self.function || !self.replay.matches_machine(machine) {
            return Err("four-pointer/status machine identity differs".into());
        }
        let name = format!(
            "actual whole scalar-memory replay {}; physical storage {}",
            self.replay.statement_digest(),
            self.binding
        );
        Ok(FunctionVerificationReport {
            function_name: machine.name.clone(),
            precondition_failure: None,
            instructions: self
                .replay
                .covered_instructions()
                .iter()
                .map(|id| InstructionReport {
                    inst_index: id.0 as usize,
                    opcode: InstructionOpcode::AArch64(machine.insts[id.0 as usize].opcode),
                    result: InstructionVerificationResult::Verified {
                        proof_name: name.clone(),
                        category: trust_cg_verify::proof_database::ProofCategory::Memory,
                        strength: trust_cg_verify::VerificationStrength::Formal,
                        degenerate: false,
                    },
                })
                .collect(),
        })
    }
    pub(super) fn check_artifact(
        &self,
        artifact: &CoreAddressFreeMachineArtifact,
        source: &CoreCompilationSource,
    ) -> Result<(), String> {
        if artifact.functions.len() != 1
            || source.lir_functions.len() != 1
            || !Arc::ptr_eq(&source.module, self.replay.module())
        {
            return Err("four-pointer artifact/source allocation or cardinality differs".into());
        }
        let f = &artifact.functions[0];
        if f.name != self.function
            || f.source_function != self.replay.function()
            || crate::compile_service::symbol_signature_for_core_function(
                &source.module,
                self.replay.function(),
                artifact.target_contract.target_spec(),
            )? != self.signature
            || !self
                .replay
                .matches_source(&source.module, &source.lir_functions[0].0, &f.code)
        {
            return Err("four-pointer final artifact identity differs".into());
        }
        Ok(())
    }
}
/// Opaque installed closed C(input0,input1,output0,output1)->U64, with exactly
/// one initialized flat word per argument. No raw executable pointer escapes.
pub struct CoreOwnedFourPointerStatusEntry {
    installed: Arc<InstalledArtifact>,
    manifest: ArtifactManifestV1,
    owner: Arc<CoreBoundFourPointerStatusProof>,
}
impl std::fmt::Debug for CoreOwnedFourPointerStatusEntry {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("CoreOwnedFourPointerStatusEntry")
            .field("function", &self.owner.function)
            .finish_non_exhaustive()
    }
}
impl PolicyQualifiedCoreJitCompilationPlan {
    /// Consume a real checked source family, complete original compiler replay
    /// and four distinct flat allocations. Nested pointees, providers, imports,
    /// branches and call graphs remain outside this bounded entry contract.
    pub fn compile_install_owned_four_pointer_status(
        self,
        inputs: [OwnedEntryContext<[u64]>; 2],
        outputs: [OwnedEntryOutput; 2],
        stack: OwnedEntryStack,
        manifest: ArtifactManifestV1,
        generation: CompileGeneration,
    ) -> Result<(CoreOwnedFourPointerStatusEntry, ArtifactManifestV1), EntryStackError> {
        super::core_artifact_install::source_contract(&self.plan.parts.module)
            .map_err(EntryStackError::Source)?;
        if self.plan.parts.module.functions.len() != 1
            || !self.plan.native_runtime_catalog.is_empty()
            || !self
                .plan
                .parts
                .declared_import_manifest
                .imports()
                .is_empty()
        {
            return Err(EntryStackError::Source("four-pointer status entry requires one closed function and empty providers/imports".into()));
        }
        let source = &self.plan.parts.module.functions[0];
        let signature = crate::compile_service::symbol_signature_for_core_function(
            &self.plan.parts.module,
            source.id,
            self.plan.parts.target_contract.target_spec(),
        )
        .map_err(EntryStackError::Source)?;
        let mut symbols = manifest.symbols.iter().filter(|s| s.name == source.name);
        if symbols.next().is_none_or(|s| s.signature != signature) || symbols.next().is_some() {
            return Err(EntryStackError::Source(
                "manifest differs from actual four-pointer/status Core ABI".into(),
            ));
        }
        let mut mode = StatusCompilation {
            storage: Some(Storage {
                inputs,
                outputs,
                stack,
            }),
            target_spec: self.plan.parts.target_contract.target_spec(),
            bound: None,
        };
        let mut rejection = None;
        let compiled = match compile_policy_qualified_core_machine_mode(
            &self,
            &mut rejection,
            CoreMachineEntryMode::FourPointerStatus(&mut mode),
        )
        .map_err(|e| EntryStackError::Source(e.to_string()))?
        {
            CoreMachineCompilationOutcome::Ordinary(c) => c,
            CoreMachineCompilationOutcome::Conditional(_) => {
                return Err(EntryStackError::Source(
                    "conditional peer is not a four-pointer/status entry".into(),
                ));
            }
        };
        let owner = mode.bound.take().ok_or_else(|| {
            EntryStackError::Source("actual four-pointer replay/storage owner absent".into())
        })?;
        let verified = compiled.verified_proof_report_count;
        let (artifact, source) =
            into_core_address_free_machine_artifact_with_source(self, compiled);
        let core=super::core_artifact_install::CoreInstallationArtifact::from_physically_bound_four_pointer_status(artifact,source,verified,&owner).map_err(EntryStackError::Source)?;
        let (installed, manifest) = core
            .install(manifest, generation)
            .map_err(|e| EntryStackError::Publication(e.to_string()))?;
        let entry = CoreOwnedFourPointerStatusEntry {
            installed: Arc::new(installed),
            manifest: manifest.clone(),
            owner,
        };
        entry.check_installed()?;
        Ok((entry, manifest))
    }
}
impl CoreOwnedFourPointerStatusEntry {
    pub fn source_function(&self) -> trust_ir::FuncId {
        self.owner.replay.function()
    }
    pub fn proof_evidence(&self) -> &crate::jit_contract::ProofEvidenceSummary {
        &self.installed.metadata.proof_evidence_summary
    }
    pub fn words(&self) -> Result<[u64; 4], EntryStackError> {
        Ok(self
            .owner
            .storage
            .lock()
            .map_err(|_| EntryStackError::Source("four-pointer storage mutex poisoned".into()))?
            .words())
    }
    /// Every host update advances the epoch, even when it leaves equal bytes.
    pub fn replace_input_word(&mut self, index: usize, value: u64) -> Result<u64, EntryStackError> {
        self.check_installed()?;
        let mut storage =
            self.owner.storage.lock().map_err(|_| {
                EntryStackError::Source("four-pointer storage mutex poisoned".into())
            })?;
        if index >= 2 {
            return Err(EntryStackError::Source("no such read input role".into()));
        }
        let generation = self
            .owner
            .generation
            .load(Ordering::Relaxed)
            .checked_add(1)
            .ok_or(EntryStackError::StaleInvocation)?;
        self.owner.generation.store(generation, Ordering::Relaxed);
        Ok(std::mem::replace(
            &mut storage.inputs[index].value_mut()[0],
            value,
        ))
    }
    fn image_extent(&self) -> Result<(usize, usize), EntryStackError> {
        let a = self.installed.buffer.code_slice().as_ptr().addr();
        let b = a
            .checked_add(self.installed.buffer.allocated_size())
            .filter(|b| *b > a)
            .ok_or(EntryStackError::Extent)?;
        Ok((a, b))
    }
    fn check_installed(&self) -> Result<(), EntryStackError> {
        let code = self.installed.buffer.code_slice();
        let mut ranges = self.installed.buffer.function_ranges().iter();
        let (name, range) = ranges.next().ok_or_else(|| {
            EntryStackError::Publication("four-pointer installed range absent".into())
        })?;
        if ranges.next().is_some()
            || name != &self.owner.function
            || range.start != 0
            || usize::try_from(range.end).ok() != Some(code.len())
            || code != self.owner.replay.final_bytes()
        {
            return Err(EntryStackError::Source(
                "four-pointer installed final bytes/range differs".into(),
            ));
        }
        let storage =
            self.owner.storage.lock().map_err(|_| {
                EntryStackError::Source("four-pointer storage mutex poisoned".into())
            })?;
        storage.check_footprint(self.owner.replay.accesses(), self.owner.replay.addresses())?;
        let image = self.image_extent()?;
        for extent in storage
            .extents()?
            .into_iter()
            .chain([storage.stack.mapped_extent()?])
        {
            disjoint(extent, image)?;
        }
        Ok(())
    }
    /// Dispatch the actual installed entry, then independently replay original
    /// Core normal return, exact X0 status and every physical post byte. Failure
    /// after dispatch retains changed storage and invalidates all prior epochs;
    /// it issues no observation. Getters on an observation remain historical.
    pub fn invoke_observed(&mut self) -> Result<CoreFourWordStatusObservation, EntryStackError> {
        self.check_installed()?;
        let mut symbols = self
            .manifest
            .symbols
            .iter()
            .filter(|s| s.name == self.owner.function);
        let symbol = symbols
            .next()
            .ok_or_else(|| EntryStackError::Publication("four-pointer symbol absent".into()))?;
        if symbols.next().is_some() || symbol.signature != self.owner.signature {
            return Err(EntryStackError::Source(
                "installed four-pointer/status signature differs".into(),
            ));
        }
        let contract = SymbolLookupContract::new(
            &self.owner.function,
            symbol.signature.clone(),
            self.manifest.target.checksum(),
            self.manifest.abi.checksum(),
            self.manifest.layout.checksum(),
        )
        .with_invalidation_checksum(self.manifest.invalidation.checksum())
        .with_manifest_checksum(self.manifest.checksum())
        .with_proof_evidence(self.installed.metadata.proof_evidence_summary.clone());
        let target=self.installed.get_contract_symbol_bound::<extern "C" fn(*const u8,*const u8,*mut u8,*mut u8)->u64>(&self.manifest,&contract).map_err(|e|EntryStackError::Publication(e.to_string()))?.as_ptr();
        let execution = self
            .installed
            .buffer
            .execution_lease()
            .map_err(|e| EntryStackError::Publication(e.to_string()))?;
        execution.prepare_current_thread();
        let image = self.image_extent()?;
        let mut storage =
            self.owner.storage.lock().map_err(|_| {
                EntryStackError::Source("four-pointer storage mutex poisoned".into())
            })?;
        if storage.extents()? != self.owner.extents
            || storage.stack.allocation().identity != self.owner.stack_identity
            || !self.owner.replay.supports_word_memory_observation()
        {
            return Err(EntryStackError::StaleInvocation);
        }
        let before = storage.words();
        let Storage {
            inputs,
            outputs,
            stack,
        } = &mut *storage;
        let invocation = stack.borrow_invocation(&self.owner.requirement)?;
        if invocation.actual_entry_sp() != self.owner.entry_sp {
            return Err(EntryStackError::StaleInvocation);
        }
        let generation = self
            .owner
            .generation
            .load(Ordering::Relaxed)
            .checked_add(1)
            .ok_or(EntryStackError::StaleInvocation)?;
        self.owner.generation.store(generation, Ordering::Relaxed);
        // SAFETY: this sealed owner retains the exact original source and complete
        // replay, image/execution lease and all disjoint initialized allocations.
        let status =
            unsafe { invocation.invoke_four_pointer_status(target, inputs, outputs, image) }?;
        let after = [
            inputs[0].value()[0],
            inputs[1].value()[0],
            outputs[0].words()[0],
            outputs[1].words()[0],
        ];
        let addresses = self.owner.extents.map(|(a, _)| a as u64);
        let claim = FourWordStatusClaim {
            addresses,
            before,
            after,
            status,
        };
        let started = std::time::Instant::now();
        let replay = &self.owner.replay;
        let proof=crate::jit_cert::run_on_proof_verifier_stack("trust-cg-four-word-status-post",move||replay.replay_word_memory_claim(claim).map_err(|e|e.to_string())).map_err(|e|EntryStackError::Source(format!("post-memory/status replay after actual call epoch={generation} claim={claim:?}: {e}")))?;
        CoreFourWordStatusObservation::new(
            Arc::clone(&self.installed),
            Arc::clone(&self.owner),
            generation,
            claim,
            proof,
            started.elapsed(),
        )
    }
}
/// Historical actual invocation and independent original-Core post-memory /
/// U64-return replay, retaining exact source, installed image and allocations.
/// Only check_current authenticates this same owner's current memory epoch.
pub struct CoreFourWordStatusObservation {
    installed: Arc<InstalledArtifact>,
    owner: Arc<CoreBoundFourPointerStatusProof>,
    generation: u64,
    proof: ReplayedFourWordStatusClaim,
    proof_time: std::time::Duration,
}
impl std::fmt::Debug for CoreFourWordStatusObservation {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("CoreFourWordStatusObservation")
            .field("function", &self.owner.function)
            .field("generation", &self.generation)
            .field("claim", &self.proof.claim())
            .finish_non_exhaustive()
    }
}
impl CoreFourWordStatusObservation {
    fn new(
        installed: Arc<InstalledArtifact>,
        owner: Arc<CoreBoundFourPointerStatusProof>,
        generation: u64,
        claim: FourWordStatusClaim,
        proof: ReplayedFourWordStatusClaim,
        proof_time: std::time::Duration,
    ) -> Result<Self, EntryStackError> {
        if proof.claim() != claim
            || !owner.replay.owns_word_memory_claim(&proof)
            || owner.extents.map(|(a, _)| a as u64) != claim.addresses
        {
            return Err(EntryStackError::Source(
                "four-word source/proof/physical addresses differ".into(),
            ));
        }
        Ok(Self {
            installed,
            owner,
            generation,
            proof,
            proof_time,
        })
    }
    pub fn core_module(&self) -> &Arc<trust_ir::Module> {
        self.owner.replay.module()
    }
    pub fn source_function(&self) -> trust_ir::FuncId {
        self.owner.replay.function()
    }
    pub fn historical_words_and_status(&self) -> FourWordStatusClaim {
        self.proof.claim()
    }
    pub fn historical_extents(&self) -> [(usize, usize); 4] {
        self.owner.extents
    }
    pub fn compilation_statement(&self) -> trust_ir::proof::ProofDigest {
        self.owner.replay.statement_digest()
    }
    pub fn post_memory_statement(&self) -> trust_ir::proof::ProofDigest {
        self.proof.statement_digest()
    }
    pub fn proof_replay_time(&self) -> std::time::Duration {
        self.proof_time
    }
    pub fn proof_replay_diagnostics(&self) -> &[(String, Option<String>)] {
        self.proof.replay_diagnostics()
    }
    pub fn invocation_generation(&self) -> u64 {
        self.generation
    }
    pub fn check_current(
        &self,
        entry: &CoreOwnedFourPointerStatusEntry,
    ) -> Result<(), EntryStackError> {
        if !Arc::ptr_eq(&self.owner, &entry.owner)
            || !Arc::ptr_eq(&self.installed, &entry.installed)
        {
            return Err(EntryStackError::StaleInvocation);
        }
        entry.check_installed()?;
        let storage =
            self.owner.storage.lock().map_err(|_| {
                EntryStackError::Source("four-pointer storage mutex poisoned".into())
            })?;
        if self.owner.generation.load(Ordering::Relaxed) != self.generation
            || storage.extents()? != self.owner.extents
            || storage.stack.allocation().identity != self.owner.stack_identity
            || storage.words() != self.proof.claim().after
        {
            return Err(EntryStackError::StaleInvocation);
        }
        Ok(())
    }
}
#[cfg(all(test, target_arch = "aarch64", target_os = "macos"))]
#[path = "../tests/common/private_four_pointer_status.rs"]
mod tests;
