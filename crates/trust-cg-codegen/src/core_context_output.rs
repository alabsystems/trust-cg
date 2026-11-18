// Copyright 2026 Andrew Yates | Apache-2.0
//! Closed source-owned two-pointer/void entries. Neither a pointer signature
//! nor an output capacity supplies a footprint: the actual checked source and
//! complete original compiler replay determine every admitted access.

use super::*;
use crate::compile_service::{CompileGeneration, InstalledArtifact};
use crate::jit::context_output::{OwnedEntryContext, OwnedEntryOutput, disjoint};
use crate::jit::entry_stack::{EntryStackError, OwnedEntryStack, SourceEntryStackRequirement};
use crate::jit_contract::{ArtifactManifestV1, SymbolLookupContract};
use sha2::{Digest, Sha256};
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::{Arc, Mutex};
#[path = "core_context_output_observation.rs"]
mod observation;
pub use observation::CoreWordMemoryObservation;
use trust_cg_verify::function_verifier::{
    FunctionVerificationReport, InstructionOpcode, InstructionReport, InstructionVerificationResult,
};
use trust_cg_verify::read_only_replay::{
    ReplayedVoidMemoryCompilation, VoidMemoryCompilerRelations,
};
use trust_ir_build::source_byte_entry::{ByteEntryAccess, ByteEntryAddress, ByteEntryRole};

struct Storage {
    context: OwnedEntryContext<[u64]>,
    output: OwnedEntryOutput,
    stack: OwnedEntryStack,
}
impl Storage {
    fn check_footprint(
        &self,
        accesses: &[ByteEntryAccess],
        addresses: &[ByteEntryAddress],
    ) -> Result<(), EntryStackError> {
        let context = self.context.extent()?;
        let output = self.output.extent()?;
        if self.context.initialized_words() != Some(self.context.value().len())
            || context.1 - context.0
                != self
                    .context
                    .value()
                    .len()
                    .checked_mul(8)
                    .ok_or(EntryStackError::Extent)?
        {
            return Err(EntryStackError::Source(
                "context has no complete initialized word representation".into(),
            ));
        }
        disjoint(context, output)?;
        let stack = self.stack.mapped_extent()?;
        disjoint(context, stack)?;
        disjoint(output, stack)?;
        for access in accesses {
            let extent = match access.role() {
                ByteEntryRole::Context if !access.is_write() => context,
                ByteEntryRole::Output if access.is_write() => output,
                _ => {
                    return Err(EntryStackError::Source(
                        "source context/output access role differs".into(),
                    ));
                }
            };
            if !matches!(
                access.ty(),
                trust_ir::Ty::Ptr | trust_ir::Ty::I64 | trust_ir::Ty::U64
            ) {
                return Err(EntryStackError::Source(
                    "source access lacks the admitted word representation".into(),
                ));
            }
            let address = extent
                .0
                .checked_add(usize::try_from(access.offset()).map_err(|_| EntryStackError::Extent)?)
                .ok_or(EntryStackError::Extent)?;
            let end = address.checked_add(8).ok_or(EntryStackError::Extent)?;
            if address < extent.0
                || end > extent.1
                || !address.is_multiple_of(
                    usize::try_from(access.alignment()).map_err(|_| EntryStackError::Extent)?,
                )
            {
                return Err(EntryStackError::Source(
                    "actual owned storage does not cover an original typed access".into(),
                ));
            }
        }
        // Dead GEP arithmetic is part of the source's whole-effect result too.
        // Non-inbounds addresses need checked nonwrap, not invented permission
        // for an unused byte. Inbounds remains outside this target profile.
        for address in addresses {
            if address.is_inbounds() {
                return Err(EntryStackError::Source(
                    "inbounds source GEP has no target owner".into(),
                ));
            }
            let base = match address.role() {
                ByteEntryRole::Context => context.0,
                ByteEntryRole::Output => output.0,
            };
            base.checked_add(
                usize::try_from(address.base_offset()).map_err(|_| EntryStackError::Extent)?,
            )
            .ok_or(EntryStackError::Extent)?;
            base.checked_add(
                usize::try_from(address.offset()).map_err(|_| EntryStackError::Extent)?,
            )
            .ok_or(EntryStackError::Extent)?;
        }
        Ok(())
    }
}

/// Private compile mode. It owns all real storage before any conditional
/// proof can be promoted. The ordinary compile API cannot select this mode.
pub(super) struct ContextCompilation {
    storage: Option<Storage>,
    target_spec: crate::target::TargetSpec,
    pub(super) bound: Option<Arc<CoreBoundContextOutputProof>>,
}
impl ContextCompilation {
    pub(super) fn bind(
        &mut self,
        module: &Arc<trust_ir::Module>,
        verification: &CoreSourceVerification<'_>,
        lir: &trust_cg_lower::Function,
        machine: &trust_cg_ir::MachFunction,
        code: &[u8],
        original: &trust_cg_verify::CapturedFunctionVerificationReport,
    ) -> Result<Arc<CoreBoundContextOutputProof>, String> {
        if self.bound.is_some() || module.functions.len() != 1 {
            return Err("context/output compilation requires one actual closed definition".into());
        }
        let storage = self
            .storage
            .take()
            .ok_or("context storage already consumed")?;
        let (storage, replay) = crate::jit_cert::run_on_proof_verifier_stack(
            "trust-cg-owned-context-replay",
            move || {
                let config = trust_ir_build::ValidationConfig::pinned()
                    .with_bound_certificates(true)
                    .with_source_bound_certificates(true)
                    .with_gate_evidence(true);
                let report = trust_ir_build::validate_module_with_config(module, &config);
                let family = trust_ir_build::source_byte_entry::check_byte_entry_source(&report)?;
                storage
                    .check_footprint(family.accesses(), family.addresses())
                    .map_err(|e| e.to_string())?;
                let queries =
                    trust_cg_verify::source_bound_frame::bind_licensed_void_memory_source(
                        &family, lir,
                    )?;
                let relations = VoidMemoryCompilerRelations::bind(&queries, machine, code)
                    .map_err(|e| e.to_string())?;
                let result = relations.replay(&verification.request);
                let receipt = result.into_certificate().map_err(|r| {
                    // Preserve the exact first failed original problem and
                    // endpoint DATA before these borrowed query owners leave
                    // scope. This diagnostic grants no replay/caller credit.
                    let failed = r.outcomes().zip(relations.parts()).find(|(outcome, _)|
                        outcome.attempted() && !matches!(outcome.verdict(), Some(trust_cg_verify::verify::VerificationResult::Valid)));
                    let diagnostic = failed.map(|(outcome, part)| {
                        let smt2 = r.first_failed_original_problem().expect("same actual failed part");
                        serde_json::json!({
                            "scope": "diagnostic exact original failed replay; no authority",
                            "stage": format!("{:?}", part.stage()),
                            "kind": format!("{:?}", part.kind()),
                            "index": part.index(),
                            "verdict": format!("{:?}", outcome.verdict()),
                            "why": outcome.why(),
                            "smt2_sha256": format!("{:x}", Sha256::digest(smt2.as_bytes())),
                            "smt2": smt2,
                            "original_request_reuse_identity": verification.request.reuse_identity().map(|v| crate::jit_cert::digest_hex(&v)),
                            "actual_ay": verification.request.ay_solver().map(|ay| ay.describe()),
                            "module_digest": module.stable_digest().to_string(),
                            "captured_input": verification.input_digest(machine,lir).ok().map(|v| crate::jit_cert::digest_hex(&v)),
                            "matches_original_capture": original.matches_request_capture(&verification.request),
                            "lir": lir,
                            "machine_debug": format!("{machine:#?}"),
                            "final_bytes": code,
                        })
                    });
                    format!(
                        "complete original void-memory replay refused: {:?}\nEXACT_VOID_REPLAY_FAILURE_JSON_BEGIN\n{}\nEXACT_VOID_REPLAY_FAILURE_JSON_END",
                        r.outcomes()
                            .map(|o| (
                                o.stage(),
                                o.kind(),
                                o.attempted(),
                                o.why().map(str::to_owned)
                            ))
                            .collect::<Vec<_>>(),
                        diagnostic.map_or_else(|| "null".into(), |value| value.to_string())
                    )
                })?;
                let replay = receipt.retain(Arc::clone(module), &family, original.clone())?;
                Ok::<_, String>((storage, replay))
            },
        )?;
        let owner = CoreBoundContextOutputProof::new(
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

/// Actual source, exact replay and all real invocation allocations have one
/// lifetime. Certificates retain only Weak custody of this private owner.
pub(crate) struct CoreBoundContextOutputProof {
    storage: Mutex<Storage>,
    replay: ReplayedVoidMemoryCompilation,
    requirement: SourceEntryStackRequirement,
    context_extent: (usize, usize),
    output_extent: (usize, usize),
    stack_identity: u64,
    entry_sp: usize,
    function: String,
    input: [u8; 32],
    binding_digest: trust_ir::proof::ProofDigest,
    signature: crate::jit_contract::SymbolSignature,
    invocation_generation: AtomicU64,
}
impl std::fmt::Debug for CoreBoundContextOutputProof {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("CoreBoundContextOutputProof")
            .field("function", &self.function)
            .field("binding", &self.binding_digest)
            .finish_non_exhaustive()
    }
}
impl CoreBoundContextOutputProof {
    fn new(
        mut storage: Storage,
        replay: ReplayedVoidMemoryCompilation,
        function: String,
        input: [u8; 32],
        target_spec: crate::target::TargetSpec,
    ) -> Result<Arc<Self>, EntryStackError> {
        storage.check_footprint(replay.accesses(), replay.addresses())?;
        let signature = crate::compile_service::symbol_signature_for_core_function(
            replay.module(),
            replay.function(),
            target_spec,
        )
        .map_err(EntryStackError::Source)?;
        let requirement = SourceEntryStackRequirement::from_replayed_void_entry(&replay)?;
        let context_extent = storage.context.extent()?;
        let output_extent = storage.output.extent()?;
        let stack_identity = storage.stack.allocation().identity;
        let entry_sp = storage
            .stack
            .borrow_invocation(&requirement)?
            .actual_entry_sp();
        let mut hash = Sha256::new();
        hash.update(b"trust-cg.actual-owned-context-output.v1\0");
        hash.update(replay.statement_digest().bytes);
        hash.update(input);
        for n in [
            context_extent.0,
            context_extent.1,
            output_extent.0,
            output_extent.1,
            entry_sp,
        ] {
            hash.update((n as u64).to_le_bytes());
        }
        hash.update(stack_identity.to_le_bytes());
        let binding_digest = trust_ir::proof::ProofDigest::sha256(hash.finalize().into());
        Ok(Arc::new(Self {
            storage: Mutex::new(storage),
            replay,
            requirement,
            context_extent,
            output_extent,
            stack_identity,
            entry_sp,
            function,
            input,
            binding_digest,
            signature,
            invocation_generation: AtomicU64::new(0),
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
        function == self.function
            && input == crate::jit_cert::digest_hex(&self.input)
            && code
                == crate::jit_cert::digest_hex(&Sha256::digest(self.replay.final_bytes()).into())
            && binding == self.binding_digest
    }
    pub(super) fn report(
        &self,
        machine: &trust_cg_ir::MachFunction,
    ) -> Result<FunctionVerificationReport, String> {
        if machine.name != self.function || !self.replay.matches_machine(machine) {
            return Err("context/output machine identity differs".into());
        }
        let name = format!(
            "actual whole void replay {}; physical storage {}",
            self.replay.statement_digest(),
            self.binding_digest
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
            return Err("context/output artifact source allocation/cardinality differs".into());
        }
        let function = &artifact.functions[0];
        if function.name != self.function
            || function.source_function != self.replay.function()
            || crate::compile_service::symbol_signature_for_core_function(
                &source.module,
                self.replay.function(),
                artifact.target_contract.target_spec(),
            )? != self.signature
            || !self.replay.matches_source(
                &source.module,
                &source.lir_functions[0].0,
                &function.code,
            )
        {
            return Err("context/output final artifact identity differs".into());
        }
        Ok(())
    }
}

/// Opaque installed C(context pointer, output pointer)->void. The context is
/// actual initialized words, not an arbitrary Rust pointee or TY context proof.
pub struct CoreOwnedContextOutputEntry {
    installed: Arc<InstalledArtifact>,
    manifest: ArtifactManifestV1,
    owner: Arc<CoreBoundContextOutputProof>,
}
impl std::fmt::Debug for CoreOwnedContextOutputEntry {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("CoreOwnedContextOutputEntry")
            .field("function", &self.owner.function)
            .finish_non_exhaustive()
    }
}

impl PolicyQualifiedCoreJitCompilationPlan {
    /// Consume exact source and real owned allocations. No imports, providers,
    /// fixups, generic Rust padding or scalar return interpretation is admitted.
    pub fn compile_install_owned_context_output(
        self,
        context: OwnedEntryContext<[u64]>,
        output: OwnedEntryOutput,
        stack: OwnedEntryStack,
        manifest: ArtifactManifestV1,
        generation: CompileGeneration,
    ) -> Result<(CoreOwnedContextOutputEntry, ArtifactManifestV1), EntryStackError> {
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
            return Err(EntryStackError::Source("context/output entry requires a closed one-function module and empty providers/imports".into()));
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
                "manifest context/output signature differs from the actual Core signature".into(),
            ));
        }
        let mut context = ContextCompilation {
            storage: Some(Storage {
                context,
                output,
                stack,
            }),
            target_spec: self.plan.parts.target_contract.target_spec(),
            bound: None,
        };
        let mut rejection = None;
        let compiled = match compile_policy_qualified_core_machine_mode(
            &self,
            &mut rejection,
            CoreMachineEntryMode::ContextOutput(&mut context),
        )
        .map_err(|e| EntryStackError::Source(e.to_string()))?
        {
            CoreMachineCompilationOutcome::Ordinary(compiled) => compiled,
            CoreMachineCompilationOutcome::Conditional(_) => {
                return Err(EntryStackError::Source(
                    "peer compilation is not a context/output entry".into(),
                ));
            }
        };
        let owner = context.bound.take().ok_or_else(|| {
            EntryStackError::Source("actual context/output replay/storage owner absent".into())
        })?;
        let verified = compiled.verified_proof_report_count;
        let (artifact, source) =
            into_core_address_free_machine_artifact_with_source(self, compiled);
        let core=super::core_artifact_install::CoreInstallationArtifact::from_physically_bound_context_output(artifact,source,verified,&owner).map_err(EntryStackError::Source)?;
        let (installed, manifest) = core
            .install(manifest, generation)
            .map_err(|e| EntryStackError::Publication(e.to_string()))?;
        let entry = CoreOwnedContextOutputEntry {
            installed: Arc::new(installed),
            manifest: manifest.clone(),
            owner,
        };
        entry.check_installed()?;
        Ok((entry, manifest))
    }
}

impl CoreOwnedContextOutputEntry {
    pub fn source_function(&self) -> trust_ir::FuncId {
        self.owner.replay.function()
    }
    pub fn output_words(&self) -> Result<Vec<u64>, EntryStackError> {
        Ok(self
            .owner
            .storage
            .lock()
            .map_err(|_| EntryStackError::Source("context storage mutex poisoned".into()))?
            .output
            .words()
            .to_vec())
    }
    pub fn context_words(&self) -> Result<Vec<u64>, EntryStackError> {
        Ok(self
            .owner
            .storage
            .lock()
            .map_err(|_| EntryStackError::Source("context storage mutex poisoned".into()))?
            .context
            .value()
            .to_vec())
    }
    pub fn proof_evidence(&self) -> &crate::jit_contract::ProofEvidenceSummary {
        &self.installed.metadata.proof_evidence_summary
    }
    /// Replace the one initialized context word under exclusive custody,
    /// preserving its allocation and native read-only permission. Even an
    /// equal replacement invalidates every older current-memory observation.
    pub fn replace_context_word(&mut self, word: u64) -> Result<u64, EntryStackError> {
        self.check_installed()?;
        let mut storage = self
            .owner
            .storage
            .lock()
            .map_err(|_| EntryStackError::Source("context storage mutex poisoned".into()))?;
        if storage.context.value().len() != 1 || storage.output.words().len() != 1 {
            return Err(EntryStackError::Source(
                "word replacement requires exactly one context and output word".into(),
            ));
        }
        let generation = self
            .owner
            .invocation_generation
            .load(Ordering::Relaxed)
            .checked_add(1)
            .ok_or(EntryStackError::StaleInvocation)?;
        self.owner
            .invocation_generation
            .store(generation, Ordering::Relaxed);
        Ok(std::mem::replace(&mut storage.context.value_mut()[0], word))
    }
    fn image_extent(&self) -> Result<(usize, usize), EntryStackError> {
        let base = self.installed.buffer.code_slice().as_ptr().addr();
        let end = base
            .checked_add(self.installed.buffer.allocated_size())
            .filter(|e| *e > base)
            .ok_or(EntryStackError::Extent)?;
        Ok((base, end))
    }
    fn check_installed(&self) -> Result<(), EntryStackError> {
        let code = self.installed.buffer.code_slice();
        let mut ranges = self.installed.buffer.function_ranges().iter();
        let (name, range) = ranges.next().ok_or_else(|| {
            EntryStackError::Publication("context/output installed range absent".into())
        })?;
        if ranges.next().is_some()
            || name != &self.owner.function
            || range.start != 0
            || usize::try_from(range.end).ok() != Some(code.len())
            || code != self.owner.replay.final_bytes()
        {
            return Err(EntryStackError::Source(
                "context/output installed final bytes/range differs".into(),
            ));
        }
        let storage = self
            .owner
            .storage
            .lock()
            .map_err(|_| EntryStackError::Source("context storage mutex poisoned".into()))?;
        storage.check_footprint(self.owner.replay.accesses(), self.owner.replay.addresses())?;
        let image = self.image_extent()?;
        for extent in [
            storage.context.extent()?,
            storage.output.extent()?,
            storage.stack.mapped_extent()?,
        ] {
            disjoint(extent, image)?;
        }
        Ok(())
    }
    /// Void remains void. The original publisher, installed replay, typed
    /// manifest, execution lease and real storage are checked before BLR.
    pub fn invoke(&mut self) -> Result<(), EntryStackError> {
        self.invoke_with_observation(false).map(|_| ())
    }

    /// Invoke the existing closed entry on exactly one initialized context
    /// word and one separate output word. The result retains historical bytes,
    /// exact Core/image and independently replayed post-memory propositions.
    /// It supplies no wider ABI, provider, model or reusable current-byte fact.
    /// A post-replay refusal leaves the actual call's output in place and
    /// issues no observation; older current-state observations stay invalid.
    pub fn invoke_observed_word(&mut self) -> Result<CoreWordMemoryObservation, EntryStackError> {
        self.invoke_with_observation(true)?.ok_or_else(|| {
            EntryStackError::Source("word observation absent after requested replay".into())
        })
    }

    fn invoke_with_observation(
        &mut self,
        observe: bool,
    ) -> Result<Option<CoreWordMemoryObservation>, EntryStackError> {
        self.check_installed()?;
        let mut symbols = self
            .manifest
            .symbols
            .iter()
            .filter(|s| s.name == self.owner.function);
        let symbol = symbols
            .next()
            .ok_or_else(|| EntryStackError::Publication("context/output symbol absent".into()))?;
        if symbols.next().is_some() || symbol.signature != self.owner.signature {
            return Err(EntryStackError::Source(
                "installed context/output signature differs".into(),
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
        let target = self
            .installed
            .get_contract_symbol_bound::<extern "C" fn(*const u8, *mut u8)>(
                &self.manifest,
                &contract,
            )
            .map_err(|e| EntryStackError::Publication(e.to_string()))?
            .as_ptr();
        let execution = self
            .installed
            .buffer
            .execution_lease()
            .map_err(|e| EntryStackError::Publication(e.to_string()))?;
        execution.prepare_current_thread();
        let image = self.image_extent()?;
        let mut storage = self
            .owner
            .storage
            .lock()
            .map_err(|_| EntryStackError::Source("context storage mutex poisoned".into()))?;
        if storage.context.extent()? != self.owner.context_extent
            || storage.output.extent()? != self.owner.output_extent
            || storage.stack.allocation().identity != self.owner.stack_identity
        {
            return Err(EntryStackError::StaleInvocation);
        }
        let before = if observe {
            if storage.context.value().len() != 1
                || storage.output.words().len() != 1
                || !self.owner.replay.supports_word_memory_observation()
            {
                return Err(EntryStackError::Source(
                    "physical word observation requires exactly one context and output word".into(),
                ));
            }
            Some((storage.context.value()[0], storage.output.words()[0]))
        } else {
            None
        };
        let Storage {
            context,
            output,
            stack,
        } = &mut *storage;
        let invocation = stack.borrow_invocation(&self.owner.requirement)?;
        if invocation.actual_entry_sp() != self.owner.entry_sp {
            return Err(EntryStackError::StaleInvocation);
        }
        // Invalidate earlier current-memory observations BEFORE dispatch. Even
        // an adapter error after a machine write cannot revive an old epoch.
        let generation = self
            .owner
            .invocation_generation
            .load(Ordering::Relaxed)
            .checked_add(1)
            .ok_or(EntryStackError::StaleInvocation)?;
        self.owner
            .invocation_generation
            .store(generation, Ordering::Relaxed);
        // SAFETY: this owner retains genuine same-source replay and actual
        // initialized, disjoint allocations through the entire exclusive call.
        unsafe { invocation.invoke_context_output(target, context, output, image) }?;
        let Some((context_before, output_before)) = before else {
            return Ok(None);
        };
        let claim = trust_cg_verify::read_only_replay::VoidWordMemoryClaim {
            context_address: u64::try_from(self.owner.context_extent.0)
                .map_err(|_| EntryStackError::Extent)?,
            output_address: u64::try_from(self.owner.output_extent.0)
                .map_err(|_| EntryStackError::Extent)?,
            context_before,
            output_before,
            context_after: context.value()[0],
            output_after: output.words()[0],
        };
        let started = std::time::Instant::now();
        let replay = &self.owner.replay;
        let proof = crate::jit_cert::run_on_proof_verifier_stack(
            "trust-cg-owned-word-post-memory",
            move || replay.replay_word_memory_claim(claim),
        )
        .map_err(|error| EntryStackError::Source(format!("post-memory replay after actual native call: epoch={generation} actual_words={claim:?} compilation={}: {error}", self.owner.replay.statement_digest())))?;
        let proof_time = started.elapsed();
        Ok(Some(CoreWordMemoryObservation::new(
            Arc::clone(&self.installed),
            Arc::clone(&self.owner),
            generation,
            claim,
            proof,
            proof_time,
        )?))
    }
}

#[cfg(all(test, target_arch = "aarch64", target_os = "macos"))]
#[path = "../tests/common/private_context_output.rs"]
mod tests;
