// Copyright 2026 Andrew Yates | Apache-2.0

//! Consuming typed final link from a genuine retained proof rejection. This
//! owner authenticates exact source/LIR/request/allocated machine and final
//! linked bytes. It neither changes the rejected report nor manufactures a
//! JitCertificate, caller proof, storage owner or installation permission.

use super::*;
use std::ops::Range;
use trust_cg_verify::aarch64_affine_lowering::{
    AttachedDefinedAffineCallee, CheckedAarch64DefinedCallBytes, check_aarch64_defined_call_bytes,
};

#[derive(Debug)]
pub struct CoreLinkedFunctionRange {
    function: trust_ir::FuncId,
    name: String,
    range: Range<usize>,
    normalized_digest: trust_ir::proof::ProofDigest,
    linked_digest: trust_ir::proof::ProofDigest,
}
impl CoreLinkedFunctionRange {
    pub fn function(&self) -> trust_ir::FuncId {
        self.function
    }
    pub fn name(&self) -> &str {
        &self.name
    }
    pub fn range(&self) -> Range<usize> {
        self.range.clone()
    }
    pub fn normalized_digest(&self) -> trust_ir::proof::ProofDigest {
        self.normalized_digest
    }
    pub fn linked_digest(&self) -> trust_ir::proof::ProofDigest {
        self.linked_digest
    }
}

/// Non-callable move-only owner. The original failed compilation remains
/// retained intact; only its separately owned linked copy contains a patch.
pub struct CoreDefinedCallLinkedImage {
    predecessor: CoreAddressFreeMachineCompilationFailure,
    image: Vec<u8>,
    functions: Vec<CoreLinkedFunctionRange>,
    caller_ordinal: usize,
    callee_ordinal: usize,
    branch_offset: u32,
    image_digest: trust_ir::proof::ProofDigest,
    identity: trust_ir::proof::ProofDigest,
}
impl std::fmt::Debug for CoreDefinedCallLinkedImage {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("CoreDefinedCallLinkedImage")
            .field("functions", &self.functions)
            .field("image_digest", &self.image_digest)
            .field("identity", &self.identity)
            .finish_non_exhaustive()
    }
}

pub struct CoreDefinedCallLinkFailure {
    reason: String,
    predecessor: CoreAddressFreeMachineCompilationFailure,
}
impl std::fmt::Debug for CoreDefinedCallLinkFailure {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("CoreDefinedCallLinkFailure")
            .field("reason", &self.reason)
            .finish_non_exhaustive()
    }
}
impl std::fmt::Display for CoreDefinedCallLinkFailure {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(&self.reason)
    }
}
impl std::error::Error for CoreDefinedCallLinkFailure {}
impl CoreDefinedCallLinkFailure {
    pub fn reason(&self) -> &str {
        &self.reason
    }
    pub fn predecessor(&self) -> &CoreAddressFreeMachineCompilationFailure {
        &self.predecessor
    }
    pub fn into_predecessor(self) -> CoreAddressFreeMachineCompilationFailure {
        self.predecessor
    }
}

/// Borrowed immutable original and linked verification endpoints. The attached
/// callee borrows this image's actual slice, not its pre-link vector or a copy.
pub struct CoreDefinedCallVerificationEndpoints<'a> {
    module: &'a trust_ir::Module,
    caller_lir: &'a trust_cg_lower::Function,
    request: &'a trust_cg_verify::FunctionVerificationRequest,
    callee: AttachedDefinedAffineCallee<'a>,
    image: &'a [u8],
    caller_ordinal: usize,
    caller_range: Range<usize>,
    callee_offset: usize,
}
impl<'a> CoreDefinedCallVerificationEndpoints<'a> {
    pub fn module(&self) -> &'a trust_ir::Module {
        self.module
    }
    pub fn caller_lir(&self) -> &'a trust_cg_lower::Function {
        self.caller_lir
    }
    pub fn request(&self) -> &'a trust_cg_verify::FunctionVerificationRequest {
        self.request
    }
    pub fn callee(&self) -> &AttachedDefinedAffineCallee<'a> {
        &self.callee
    }
    pub fn image(&self) -> &'a [u8] {
        self.image
    }
    pub fn check_bytes(&self) -> Result<CheckedAarch64DefinedCallBytes<'_, 'a>, String> {
        check_aarch64_defined_call_bytes(
            self.module,
            self.caller_ordinal,
            self.caller_lir,
            self.image,
            self.caller_range.start,
            self.caller_range.len(),
            self.callee_offset,
            &self.callee,
            self.request,
        )
        .map_err(|e| e.to_string())
    }
}

fn digest(code: &[u8]) -> trust_ir::proof::ProofDigest {
    trust_ir::proof::ProofDigest::sha256(crate::jit_cert::sha256_digest(code))
}

fn standard_frame(layout: Option<&crate::frame::FrameLayout>, code: &[u8]) -> Result<(), String> {
    let frame = layout.ok_or("retained caller has no frame layout")?;
    if frame.total_frame_size != 16
        || frame.callee_saved_area_size != 16
        || frame.spill_area_size != 0
        || frame.local_area_size != 0
        || frame.outgoing_arg_area_size != 0
        || !frame.uses_frame_pointer
        || frame.is_leaf
        || frame.uses_red_zone
        || frame.has_dynamic_alloc
        || frame.fp_to_spill_offset != 0
        || frame.callee_saved_pairs.len() != 1
        || frame.callee_saved_pairs[0].is_fpr
        || frame.callee_saved_pairs[0].reg1.encoding() != 29
        || frame.callee_saved_pairs[0].reg2.encoding() != 30
        || code.len() < 20
        || !code.len().is_multiple_of(4)
    {
        return Err("retained frame is outside standard16 defined-call domain".into());
    }
    let word = |offset: usize| u32::from_le_bytes(code[offset..offset + 4].try_into().unwrap());
    if word(0) != 0xa9bf7bfd
        || word(4) != 0x910003fd
        || word(code.len() - 8) != 0xa8c17bfd
        || word(code.len() - 4) != 0xd65f03c0
    {
        return Err("retained frame layout differs from actual complete words".into());
    }
    Ok(())
}

fn compare_emission(
    retained: &[u8],
    retained_sites: &[crate::pipeline::EncodedAarch64FixupSite],
    emitted: &[u8],
    emitted_sites: &[crate::pipeline::EncodedAarch64FixupSite],
) -> Result<(), String> {
    if retained != emitted || retained_sites != emitted_sites {
        return Err("re-emission differs from retained complete caller bytes/sites".into());
    }
    Ok(())
}

fn append_function(
    image: &mut Vec<u8>,
    code: &[u8],
    alignment: u8,
) -> Result<Range<usize>, String> {
    if alignment > 12 || code.is_empty() || !code.len().is_multiple_of(4) {
        return Err("unsupported final text alignment/extent".into());
    }
    let align = 1usize << alignment.max(2);
    let padding = (align - image.len() % align) % align;
    image
        .try_reserve(
            padding
                .checked_add(code.len())
                .ok_or("linked extent overflow")?,
        )
        .map_err(|e| e.to_string())?;
    for _ in 0..padding / 4 {
        image.extend_from_slice(&0xd503201fu32.to_le_bytes());
    }
    let start = image.len();
    image.extend_from_slice(code);
    Ok(start..image.len())
}

fn patch_defined_bl(image: &mut [u8], site: usize, target: usize) -> Result<(), String> {
    let offset = u32::try_from(site).map_err(|_| "BL image coordinate overflow")?;
    let target = u64::try_from(target).map_err(|_| "BL target coordinate overflow")?;
    let word = image
        .get(site..site.checked_add(4).ok_or("BL extent overflow")?)
        .ok_or("BL outside linked image")?;
    if !site.is_multiple_of(4)
        || !target.is_multiple_of(4)
        || u32::from_le_bytes(word.try_into().unwrap()) != 0x94000000
        || target >= image.len() as u64
    {
        return Err(
            "typed link requires an aligned canonical unpatched BL and image target".into(),
        );
    }
    #[cfg(target_arch = "aarch64")]
    crate::jit::patch_branch26(image, offset, target).map_err(|e| e.to_string())?;
    #[cfg(not(target_arch = "aarch64"))]
    {
        let _ = offset;
        return Err("typed Branch26 link currently requires ARM64 host".into());
    }
    #[allow(unreachable_code)]
    {
        let word = u32::from_le_bytes(image[site..site + 4].try_into().unwrap());
        let Some(trust_cg_verify::aarch64_instruction_word_proofs::DecodedWord::BranchImm {
            op: 1,
            imm26,
        }) = trust_cg_verify::aarch64_instruction_word_proofs::decode_word(word)
        else {
            return Err("patched word is not independently decoded BL".into());
        };
        let displacement = (i64::from(imm26) << 38) >> 36;
        if i64::try_from(site)
            .ok()
            .and_then(|pc| pc.checked_add(displacement))
            != i64::try_from(target).ok()
        {
            return Err("patched actual BL target differs from exact function entry".into());
        }
        Ok(())
    }
}

fn authenticate_call_site(
    caller_lir: &trust_cg_lower::Function,
    machine: &trust_cg_ir::MachFunction,
    site: &crate::pipeline::EncodedAarch64FixupSite,
    fixup: &crate::macho::fixup::Fixup,
    callee: trust_ir::FuncId,
    callee_name: &str,
) -> Result<(), String> {
    let block = caller_lir
        .blocks
        .get(&caller_lir.entry_block)
        .ok_or("missing caller LIR entry")?;
    let call = block
        .instructions
        .first()
        .ok_or("missing caller LIR call")?;
    let inst = machine
        .insts
        .get(site.inst.0 as usize)
        .ok_or("foreign retained BL instruction")?;
    if !matches!(
        inst.opcode,
        trust_cg_ir::AArch64Opcode::Bl | trust_cg_ir::AArch64Opcode::BL
    ) || inst.operands.len() != 1
        || fixup.offset != site.offset
        || site.placeholder_word != 0x94000000
        || !matches!(&call.opcode, trust_cg_lower::instructions::Opcode::Call {
        name, binding: trust_cg_lower::instructions::DirectCallBinding::ExactModuleFunction { function }
    } if name == callee_name && *function == callee.index())
        || !matches!(machine.inst_lowering_provenance(site.inst), trust_cg_ir::LoweringProvenance::SourceInst { id, digest, .. }
            if id.block == caller_lir.entry_block.0 && id.index == 0 && digest == call.lowering_digest())
        || !inst
            .flags
            .contains(trust_cg_ir::InstFlags::EXACT_MODULE_CALL)
        || inst.operands.first().and_then(|o| o.as_symbol()) != Some(callee_name)
        || fixup.kind != crate::macho::AArch64RelocKind::Branch26
        || fixup.addend != 0
        || fixup.tls_model.is_some()
        || !matches!(&fixup.target, crate::macho::fixup::FixupTarget::ExactNamedSymbol(name) if name == callee_name)
    {
        return Err("source/LIR/allocated BL/fixup exact identity differs".into());
    }
    Ok(())
}

type PreparedLink = (Vec<u8>, Vec<CoreLinkedFunctionRange>, usize, usize, u32);

fn prepare(failure: &CoreAddressFreeMachineCompilationFailure) -> Result<PreparedLink, String> {
    if !cfg!(target_arch = "aarch64") {
        return Err("typed final link currently requires ARM64 host".into());
    }
    let qualified = &failure.plan;
    if qualify_proof_grade_core_jit_plan(&qualified.plan).map_err(|e| e.to_string())?
        != qualified.fast_regalloc
    {
        return Err("qualified original plan selection changed".into());
    }
    let plan = &qualified.plan;
    if plan.effective_options.target_spec.architecture != Target::Aarch64
        || !plan.native_runtime_catalog.is_empty()
        || !plan.parts.declared_import_manifest.imports().is_empty()
        || !plan.native_dependency_references.is_empty()
        || !plan.lir_native_dependency_bindings.entries().is_empty()
        || plan.parts.module.functions.len() != 2
        || plan.parts.lir_functions.len() != 2
        || plan.retained_exact_module_call_count() != 1
    {
        return Err(
            "typed final link requires exactly two definitions, one exact call and no providers"
                .into(),
        );
    }
    let rejection = failure
        .machine_rejection
        .as_ref()
        .ok_or("original compilation retained no machine rejection")?;
    if !matches!(
        failure.error,
        CoreAddressFreeMachineCompilationError::Compile(
            CompileError::ProofPromotionRejected { .. }
        )
    ) || rejection.prior_functions.len() != 1
        || !rejection
            .captured
            .matches_request_capture(&rejection.request)
    {
        return Err(
            "requires genuine original proof-promotion rejection and one earlier callee".into(),
        );
    }
    let module = &plan.parts.module;
    let modules = trust_cg_verify::FunctionSourceModules::capture(module, module)
        .map_err(|e| e.to_string())?;
    let caller_ordinal = module
        .functions
        .iter()
        .position(|f| f.id == rejection.source_function)
        .ok_or("retained caller absent from original source")?;
    let caller_source = &module.functions[caller_ordinal];
    let caller_lir = plan
        .parts
        .lir_functions
        .iter()
        .find(|(f, _)| f.name == caller_source.name)
        .map(|(f, _)| f)
        .ok_or("retained caller LIR missing")?;
    if !rejection.captured.matches_aarch64_input_with_modules(
        &rejection.machine,
        Some(caller_lir),
        &modules,
    ) {
        return Err(
            "original caller capture does not authenticate exact source/LIR/machine".into(),
        );
    }
    standard_frame(rejection.frame_layout.as_ref(), &rejection.bytes)?;
    let (emitted, fixups, sites) = crate::decode_check::without_telemetry(|| {
        affine_bytes::encode_core_function(module, caller_ordinal, caller_lir, &rejection.machine)
    })
    .map_err(|e| e.to_string())?;
    compare_emission(&rejection.bytes, &rejection.fixup_sites, &emitted, &sites)?;
    validate_core_aarch64_fixup_sites(&rejection.machine, &emitted, &fixups, &sites)
        .map_err(|e| e.to_string())?;
    validate_core_lir_call_order(&rejection.machine, &sites).map_err(|e| e.to_string())?;
    if sites.len() != 1 || fixups.len() != 1 {
        return Err("requires one retained BL fixup occurrence".into());
    }
    let prior = &rejection.prior_functions[0];
    let callee_ordinal = module
        .functions
        .iter()
        .position(|f| f.id == prior.source_function)
        .ok_or("earlier callee source is absent")?;
    if caller_ordinal == callee_ordinal
        || prior.name != module.functions[callee_ordinal].name
        || !prior.certificate.has_checked_semantics()
        || !prior.certificate.replay_check()
        || prior.normalized_code_digest != digest(&prior.code)
        || prior.certificate.function() != prior.name
        || prior
            .certificate
            .core_semantic_digest()
            .map(trust_ir::proof::ProofDigest::sha256)
            != Some(prior.certificate_digest)
    {
        return Err("earlier callee identity, certificate or original bytes differ".into());
    }
    // Reapply original captured Formal and actual byte owner before linking.
    failure
        .reattach_replayed_defined_callee(prior.source_function)
        .map_err(|e| e.to_string())?;
    let site = &sites[0];
    let fixup = fixups.iter().next().ok_or("missing BL fixup")?;
    authenticate_call_site(
        caller_lir,
        &rejection.machine,
        site,
        fixup,
        prior.source_function,
        &prior.name,
    )?;
    let mut image = Vec::new();
    let mut functions = Vec::new();
    for (ordinal, function) in module.functions.iter().enumerate() {
        let (code, alignment) = if ordinal == caller_ordinal {
            (emitted.as_slice(), rejection.machine.text_align_log2)
        } else {
            (prior.code.as_slice(), prior.text_align_log2)
        };
        let range = append_function(&mut image, code, alignment)?;
        functions.push(CoreLinkedFunctionRange {
            function: function.id,
            name: function.name.clone(),
            range,
            normalized_digest: digest(code),
            linked_digest: digest(code),
        });
    }
    let branch_offset = functions[caller_ordinal]
        .range
        .start
        .checked_add(site.offset as usize)
        .ok_or("BL coordinate overflow")?;
    patch_defined_bl(
        &mut image,
        branch_offset,
        functions[callee_ordinal].range.start,
    )?;
    for function in &mut functions {
        function.linked_digest = digest(&image[function.range.clone()]);
    }
    Ok((
        image,
        functions,
        caller_ordinal,
        callee_ordinal,
        u32::try_from(branch_offset).map_err(|_| "BL coordinate overflow")?,
    ))
}

impl CoreAddressFreeMachineCompilationFailure {
    pub fn link_defined_call(
        self,
    ) -> Result<CoreDefinedCallLinkedImage, CoreDefinedCallLinkFailure> {
        let permit = match trust_cg_process_env::artifact_reuse_permit() {
            Some(permit) => permit,
            None => {
                return Err(CoreDefinedCallLinkFailure {
                    reason: "final-link environment permit unavailable".into(),
                    predecessor: self,
                });
            }
        };
        let prepared = prepare(&self);
        let result = prepared.and_then(
            |(image, functions, caller_ordinal, callee_ordinal, branch_offset)| {
                let image_digest = digest(&image);
                let identity = core_address_free_encoded_digest(
                    "trust-cg.core-defined-call-final-link.v1",
                    |sink| {
                        core_identity_digest(sink, self.plan.identity().full_digest())?;
                        core_identity_digest(sink, image_digest)?;
                        core_identity_u32(sink, branch_offset)?;
                        for function in &functions {
                            core_identity_u32(sink, function.function.index())?;
                            core_identity_str(sink, &function.name)?;
                            core_identity_u64(sink, function.range.start as u64)?;
                            core_identity_u64(sink, function.range.end as u64)?;
                            core_identity_digest(sink, function.normalized_digest)?;
                            core_identity_digest(sink, function.linked_digest)?;
                        }
                        Ok(())
                    },
                )
                .map_err(|e| e.to_string())?;
                if !permit.is_valid() {
                    return Err("final-link environment changed".into());
                }
                Ok((
                    image,
                    functions,
                    caller_ordinal,
                    callee_ordinal,
                    branch_offset,
                    image_digest,
                    identity,
                ))
            },
        );
        let (
            image,
            functions,
            caller_ordinal,
            callee_ordinal,
            branch_offset,
            image_digest,
            identity,
        ) = match result {
            Ok(parts) => parts,
            Err(reason) => {
                return Err(CoreDefinedCallLinkFailure {
                    reason,
                    predecessor: self,
                });
            }
        };
        let owner = CoreDefinedCallLinkedImage {
            predecessor: self,
            image,
            functions,
            caller_ordinal,
            callee_ordinal,
            branch_offset,
            image_digest,
            identity,
        };
        let validation = owner
            .verification_endpoints()
            .and_then(|endpoints| endpoints.check_bytes().map(|_| ()));
        if let Err(reason) = validation {
            return Err(CoreDefinedCallLinkFailure {
                reason,
                predecessor: owner.predecessor,
            });
        }
        if !permit.is_valid() {
            return Err(CoreDefinedCallLinkFailure {
                reason: "final-link environment changed".into(),
                predecessor: owner.predecessor,
            });
        }
        Ok(owner)
    }
}

impl CoreDefinedCallLinkedImage {
    pub fn image(&self) -> &[u8] {
        &self.image
    }
    pub fn functions(&self) -> &[CoreLinkedFunctionRange] {
        &self.functions
    }
    pub fn image_digest(&self) -> trust_ir::proof::ProofDigest {
        self.image_digest
    }
    pub fn identity(&self) -> trust_ir::proof::ProofDigest {
        self.identity
    }
    pub fn branch_offset(&self) -> u32 {
        self.branch_offset
    }
    pub fn predecessor(&self) -> &CoreAddressFreeMachineCompilationFailure {
        &self.predecessor
    }
    pub fn into_predecessor(self) -> CoreAddressFreeMachineCompilationFailure {
        self.predecessor
    }
    pub fn verification_endpoints(
        &self,
    ) -> Result<CoreDefinedCallVerificationEndpoints<'_>, String> {
        if digest(&self.image) != self.image_digest {
            return Err("linked image digest changed".into());
        }
        let failure = &self.predecessor;
        let module = &failure.plan.plan.parts.module;
        let rejection = failure
            .machine_rejection
            .as_ref()
            .ok_or("missing original rejection")?;
        let prior = &rejection.prior_functions[0];
        let lir = |ordinal: usize| {
            failure
                .plan
                .plan
                .parts
                .lir_functions
                .iter()
                .find(|(f, _)| f.name == module.functions[ordinal].name)
                .map(|(f, _)| f)
                .ok_or_else(|| "original retained LIR disappeared".to_string())
        };
        let callee_lir = lir(self.callee_ordinal)?;
        let summary = prior
            .defined_callee
            .as_ref()
            .map_err(|e| e.to_string())?
            .as_ref()
            .ok_or("earlier callee has no sealed summary")?;
        let modules = trust_cg_verify::FunctionSourceModules::capture(module, module)
            .map_err(|e| e.to_string())?;
        let callee = summary
            .attach(
                &modules,
                &rejection.request,
                prior.source_function,
                callee_lir,
                &self.image[self.functions[self.callee_ordinal].range.clone()],
            )
            .map_err(|e| e.to_string())?;
        Ok(CoreDefinedCallVerificationEndpoints {
            module,
            caller_lir: lir(self.caller_ordinal)?,
            request: &rejection.request,
            callee,
            image: &self.image,
            caller_ordinal: self.caller_ordinal,
            caller_range: self.functions[self.caller_ordinal].range.clone(),
            callee_offset: self.functions[self.callee_ordinal].range.start,
        })
    }
}

#[cfg(test)]
#[path = "compiler_defined_call_link_tests.rs"]
mod tests;
