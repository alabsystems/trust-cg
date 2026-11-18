// Copyright 2026 Andrew Yates | Apache-2.0
//! Move-only retention of an ACTUAL complete replay. This is conditional on
//! the original geometry and caller memory facts, never an ordinary report,
//! instruction certificate, pointer permission or callable entry.

use super::*;
use sha2::{Digest, Sha256};
use std::sync::Arc;
use trust_ir::proof::ProofDigest;
use trust_ir_build::source_byte_entry::{
    ByteEntryAccess, ByteEntryAddress, CheckedByteEntrySource,
};

pub struct ReplayedVoidMemoryCompilation {
    module: Arc<trust_ir::Module>,
    original: crate::CapturedFunctionVerificationReport,
    request: FunctionVerificationRequest,
    code: Vec<u8>,
    source_function: trust_ir::FuncId,
    accesses: Vec<ByteEntryAccess>,
    addresses: Vec<ByteEntryAddress>,
    statement_digest: ProofDigest,
    covered: Vec<trust_cg_ir::InstId>,
    machine: MachFunction,
    lir: trust_cg_lower::Function,
    word_observation: crate::void_memory_observation::Template,
    word_scope: Arc<()>,
}

impl VoidMemoryReplayCertificate<'_, '_> {
    /// Consumes the sealed all-parts replay capability itself. A generic
    /// successful function report or a supplied hash cannot mint this owner.
    pub fn retain(
        self,
        module: Arc<trust_ir::Module>,
        family: &CheckedByteEntrySource<'_>,
        original: crate::CapturedFunctionVerificationReport,
    ) -> Result<ReplayedVoidMemoryCompilation, String> {
        let source = self.relations.source();
        let function = family.function_in(&module)?;
        if !std::ptr::eq(source.module(), module.as_ref()) || source.source().id != function {
            return Err("void replay/source belongs to another original module".into());
        }
        let modules =
            crate::FunctionSourceModules::capture(&module, &module).map_err(|e| e.to_string())?;
        let machine = self.relations.machine();
        let lir = source.lir();
        if !original.matches_request_capture(self.request())
            || !original.matches_aarch64_input_with_modules(machine, Some(lir), &modules)
        {
            return Err("void replay does not belong to the actual original capture/input".into());
        }
        let ordinal = module
            .functions
            .iter()
            .position(|f| f.id == function)
            .ok_or("void replay original function is absent")?;
        crate::aarch64_affine_lowering::check_plain_integer_entry_abi(&module, ordinal, lir)
            .map_err(|e| format!("void entry ABI: {e}"))?;
        // This existing whole-chain owner additionally establishes the exact
        // frameless, no-SP/FP/LR-write and scratch-register ABI domain. The
        // independent final-word adapter has the same mandatory domain.
        crate::source_bound_frame::source_bound_memory_leaf(lir, machine)
            .map_err(|e| format!("void entry actual leaf: {e}"))?;
        if module.target_info.as_ref().map(|t| t.triple.as_str()) != Some("aarch64-apple-darwin") {
            return Err("owned context/output adapter requires ARM64/macOS".into());
        }
        let mut hash = Sha256::new();
        hash.update(b"trust-cg.actual-void-memory-replay.v1\0");
        hash.update(module.stable_digest().bytes);
        hash.update(function.index().to_le_bytes());
        hash.update(Sha256::digest(self.relations.final_bytes()));
        for part in self.relations.parts() {
            let rendered = self.request().with_policy(|| {
                crate::ay_bridge::generate_smt2_query_raw(
                    part.obligation(),
                    &crate::verdict_db::live_source_bound_config(),
                )
            });
            hash.update((rendered.len() as u64).to_le_bytes());
            hash.update(rendered.as_bytes());
        }
        let covered = (0..machine.insts.len())
            .map(|i| trust_cg_ir::InstId(i as u32))
            .collect();
        Ok(ReplayedVoidMemoryCompilation {
            module,
            original,
            request: self.request().clone(),
            code: self.relations.final_bytes().to_vec(),
            source_function: function,
            accesses: family.accesses().to_vec(),
            addresses: family.addresses().to_vec(),
            statement_digest: ProofDigest::sha256(hash.finalize().into()),
            covered,
            machine: machine.clone(),
            lir: lir.clone(),
            word_observation: crate::void_memory_observation::Template::capture(source, family),
            word_scope: Arc::new(()),
        })
    }
}

impl ReplayedVoidMemoryCompilation {
    /// Whether the original complete footprint fits the separate offset-zero
    /// word observation profile. This flag establishes no caller memory fact.
    pub fn supports_word_memory_observation(&self) -> bool {
        self.word_observation.applicable()
    }
    /// Check a concrete word-memory claim against this exact original Core.
    /// The inputs remain conditional logical data: this method supplies no
    /// live allocation, permission, call, installation or current-memory fact.
    pub fn replay_word_memory_claim(
        &self,
        claim: crate::void_memory_observation::VoidWordMemoryClaim,
    ) -> Result<crate::void_memory_observation::ReplayedVoidWordMemoryClaim, String> {
        self.word_observation.replay(
            &self.request,
            self.statement_digest,
            Arc::clone(&self.word_scope),
            claim,
        )
    }
    /// Require this exact retained compilation owner, rather than a matching
    /// digest or an independently compiled equal Core allocation.
    pub fn owns_word_memory_claim(
        &self,
        claim: &crate::void_memory_observation::ReplayedVoidWordMemoryClaim,
    ) -> bool {
        claim.compilation_statement() == self.statement_digest && claim.belongs_to(&self.word_scope)
    }
    pub fn module(&self) -> &Arc<trust_ir::Module> {
        &self.module
    }
    pub fn function(&self) -> trust_ir::FuncId {
        self.source_function
    }
    pub fn accesses(&self) -> &[ByteEntryAccess] {
        &self.accesses
    }
    pub fn addresses(&self) -> &[ByteEntryAddress] {
        &self.addresses
    }
    pub fn final_bytes(&self) -> &[u8] {
        &self.code
    }
    pub fn statement_digest(&self) -> ProofDigest {
        self.statement_digest
    }
    pub fn original_request(&self) -> &FunctionVerificationRequest {
        &self.request
    }
    pub fn covered_instructions(&self) -> &[trust_cg_ir::InstId] {
        &self.covered
    }
    pub fn matches_source(
        &self,
        module: &trust_ir::Module,
        lir: &trust_cg_lower::Function,
        code: &[u8],
    ) -> bool {
        self.matches_inputs(module, lir, &self.machine, code)
    }
    pub fn matches_machine(&self, machine: &MachFunction) -> bool {
        self.matches_inputs(&self.module, &self.lir, machine, &self.code)
    }
    pub fn matches_inputs(
        &self,
        module: &trust_ir::Module,
        lir: &trust_cg_lower::Function,
        machine: &MachFunction,
        code: &[u8],
    ) -> bool {
        std::ptr::eq(module, self.module.as_ref())
            && self.code == code
            && crate::FunctionSourceModules::capture(module, module)
                .ok()
                .is_some_and(|modules| {
                    self.original
                        .matches_aarch64_input_with_modules(machine, Some(lir), &modules)
                })
    }
}
