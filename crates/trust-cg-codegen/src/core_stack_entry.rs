// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! Source-bound consuming entry over real invocation-owned stack storage.
//!
//! The legacy consumer admits the existing zero-argument affine source/LIR/byte
//! owner. The distinct aggregate route consumes a checked original Source/Core
//! and actual linked CALL/RET trace under replay policy. Both expose only the
//! selected entry through an exclusive owned-stack invocation. The aggregate
//! additionally binds the entire installed image and image/stack disjointness;
//! it creates no per-function caller certificate or new row verdict.
//! A separate private conditional-peer consumer retains its own complete
//! caller/final-link and actual storage obligations.

use super::{CoreAddressFreeMachineArtifact, CoreCompilationSource};
use crate::compile_service::InstalledArtifact;
use crate::jit::entry_stack::{EntryStackError, OwnedEntryStack, SourceEntryStackRequirement};
use crate::jit_contract::{ArtifactManifestV1, SymbolLookupContract};
use sha2::{Digest, Sha256};

/// Installed source/byte entry with no public raw-pointer conversion. Each
/// call requires a fresh exclusive invocation borrow of real RW storage.
pub struct CoreOwnedStackEntry {
    installed: InstalledArtifact,
    manifest: ArtifactManifestV1,
    symbol: String,
    requirement: SourceEntryStackRequirement,
    #[cfg(feature = "source-defined-call")]
    aggregate: Option<super::CoreCheckedDefinedCallImage>,
}

impl std::fmt::Debug for CoreOwnedStackEntry {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("CoreOwnedStackEntry")
            .field("symbol", &self.symbol)
            .field("source_function", &self.requirement.function)
            .field("module_digest", &self.requirement.module_digest)
            .finish_non_exhaustive()
    }
}

pub(super) fn bind_source(
    source: &CoreCompilationSource,
    artifact: &CoreAddressFreeMachineArtifact,
    symbol: &str,
) -> Result<SourceEntryStackRequirement, EntryStackError> {
    let mut matches = artifact.functions.iter().filter(|f| f.name == symbol);
    let function = matches
        .next()
        .ok_or_else(|| EntryStackError::Source("entry is not an actual Core definition".into()))?;
    if matches.next().is_some() {
        return Err(EntryStackError::Source("ambiguous Core entry".into()));
    }
    let mut source_matches = source
        .module
        .functions
        .iter()
        .enumerate()
        .filter(|(_, f)| f.id == function.source_function && f.name == symbol);
    let (ordinal, _) = source_matches
        .next()
        .ok_or_else(|| EntryStackError::Source("entry source identity differs".into()))?;
    if source_matches.next().is_some() {
        return Err(EntryStackError::Source(
            "ambiguous source entry identity".into(),
        ));
    }
    let mut lir_matches = source
        .lir_functions
        .iter()
        .filter(|(lir, _)| lir.name == symbol);
    let (lir, _) = lir_matches
        .next()
        .ok_or_else(|| EntryStackError::Source("entry LIR is absent".into()))?;
    if lir_matches.next().is_some() {
        return Err(EntryStackError::Source("ambiguous entry LIR".into()));
    }
    // The existing independent owner reconstructs the full source/LIR/final
    // word return and effect relation. Public layout or signature metadata is
    // not substituted for that check. The caller already validated all source
    // certificates and actual machine certificates through its original owner.
    let checked = trust_cg_verify::aarch64_affine_lowering::check_aarch64_trust_ir_affine_bytes(
        &source.module,
        ordinal,
        lir,
        &function.code,
    )
    .map_err(|error| EntryStackError::Source(error.to_string()))?;
    SourceEntryStackRequirement::from_checked_affine_entry(
        &checked,
        artifact.module_digest(),
        function.normalized_code_digest,
    )
}

impl CoreOwnedStackEntry {
    pub(super) fn new(
        installed: InstalledArtifact,
        manifest: ArtifactManifestV1,
        symbol: String,
        requirement: SourceEntryStackRequirement,
    ) -> Self {
        Self {
            installed,
            manifest,
            symbol,
            requirement,
            #[cfg(feature = "source-defined-call")]
            aggregate: None,
        }
    }

    #[cfg(feature = "source-defined-call")]
    pub(super) fn new_aggregate(
        installed: InstalledArtifact,
        manifest: ArtifactManifestV1,
        symbol: String,
        requirement: SourceEntryStackRequirement,
        owner: super::CoreCheckedDefinedCallImage,
    ) -> Self {
        Self {
            installed,
            manifest,
            symbol,
            requirement,
            aggregate: Some(owner),
        }
    }

    /// Separate complete source/native replay evidence. Original rejected rows
    /// and genuine per-function certificate counts remain available unchanged.
    #[cfg(feature = "source-defined-call")]
    pub fn aggregate_evidence(&self) -> Option<&super::CoreCheckedDefinedCallImage> {
        self.aggregate.as_ref()
    }

    /// The exact retained function identity; diagnostic, not a permission mint.
    pub fn source_function(&self) -> trust_ir::FuncId {
        trust_ir::FuncId::new(self.requirement.function)
    }

    /// Actual installed proof class and payload binding, including separate
    /// aggregate evidence when present. This is reporting, not a constructor.
    pub fn proof_evidence(&self) -> &crate::jit_contract::ProofEvidenceSummary {
        &self.installed.metadata.proof_evidence_summary
    }

    /// Required private footprint established by the existing byte owner.
    /// The number is not an allocation, lease or permission constructor.
    pub fn required_private_stack_bytes(&self) -> usize {
        self.requirement.private_bytes()
    }

    /// Invoke the exact checked () -> 64-bit entry on a fresh exclusive stack
    /// lease. Bits are returned unchanged, matching the existing I64 ABI carrier.
    pub fn invoke0_u64(&self, stack: &mut OwnedEntryStack) -> Result<u64, EntryStackError> {
        self.invoke_scalar_u64(stack, None)
    }

    pub(crate) fn invoke1_u64(
        &self,
        stack: &mut OwnedEntryStack,
        argument: u64,
    ) -> Result<u64, EntryStackError> {
        self.invoke_scalar_u64(stack, Some(argument))
    }

    fn invoke_scalar_u64(
        &self,
        stack: &mut OwnedEntryStack,
        argument: Option<u64>,
    ) -> Result<u64, EntryStackError> {
        let actual = usize::from(argument.is_some());
        if self.requirement.argument_count != actual {
            return Err(EntryStackError::ArgumentCount {
                expected: self.requirement.argument_count,
                actual,
            });
        }
        let mut symbols = self
            .manifest
            .symbols
            .iter()
            .filter(|s| s.name == self.symbol);
        let symbol = symbols.next().ok_or_else(|| {
            EntryStackError::Publication("installed entry symbol is absent".into())
        })?;
        if symbols.next().is_some() {
            return Err(EntryStackError::Publication(
                "installed entry is ambiguous".into(),
            ));
        }
        let expected_signature = crate::jit_contract::SymbolSignature::extern_c(
            vec![
                crate::jit_contract::AbiValue::new(crate::jit_contract::AbiValueKind::I64);
                actual
            ],
            vec![crate::jit_contract::AbiValue::new(
                crate::jit_contract::AbiValueKind::I64,
            )],
        );
        if symbol.signature != expected_signature {
            return Err(EntryStackError::Source(
                "installed entry scalar signature differs from its sealed source requirement"
                    .into(),
            ));
        }
        let contract = SymbolLookupContract::new(
            &self.symbol,
            symbol.signature.clone(),
            self.manifest.target.checksum(),
            self.manifest.abi.checksum(),
            self.manifest.layout.checksum(),
        )
        .with_invalidation_checksum(self.manifest.invalidation.checksum())
        .with_manifest_checksum(self.manifest.checksum())
        .with_proof_evidence(self.installed.metadata.proof_evidence_summary.clone());
        let target = if argument.is_some() {
            self.installed
                .get_contract_symbol_bound::<extern "C" fn(u64) -> u64>(&self.manifest, &contract)
                .map_err(|error| EntryStackError::Publication(error.to_string()))?
                .as_ptr()
        } else {
            self.installed
                .get_contract_symbol_bound::<extern "C" fn() -> u64>(&self.manifest, &contract)
                .map_err(|error| EntryStackError::Publication(error.to_string()))?
                .as_ptr()
        };
        let range = self
            .installed
            .buffer
            .function_ranges()
            .iter()
            .find(|(name, _)| name == &self.symbol)
            .map(|(_, range)| range)
            .ok_or_else(|| EntryStackError::Publication("entry byte range is absent".into()))?;
        let begin = usize::try_from(range.start).map_err(|_| EntryStackError::Extent)?;
        let end = usize::try_from(range.end).map_err(|_| EntryStackError::Extent)?;
        let bytes = self
            .installed
            .buffer
            .code_slice()
            .get(begin..end)
            .ok_or(EntryStackError::Extent)?;
        if trust_ir::proof::ProofDigest::sha256(Sha256::digest(bytes).into())
            != self.requirement.code_digest
        {
            return Err(EntryStackError::Source(
                "published entry bytes differ from the original checked source binding".into(),
            ));
        }
        let execution = self
            .installed
            .buffer
            .execution_lease()
            .map_err(|error| EntryStackError::Publication(error.to_string()))?;
        execution.prepare_current_thread();
        let mut invocation = stack.borrow_invocation(&self.requirement)?;
        if self.requirement.requires_whole_image() {
            invocation.bind_image(self.installed.buffer.code_slice())?;
        }
        // SAFETY: only this consuming source/byte owner constructs the entry
        // requirement. The actual manifest-backed symbol, exact code digest and
        // execution lease were checked above. The complete admitted byte owner
        // establishes normal return, SP preservation and writes confined below
        // entry SP; the sealed scalar ABI contains at most one word and no externally addressed effects.
        unsafe {
            match argument {
                None => invocation.invoke0_u64(target),
                Some(value) => invocation.invoke1_u64(target, value),
            }
        }
    }
}
