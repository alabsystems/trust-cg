// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! Consuming Core installation retaining the exact source needed by the
//! existing publication, ABI, payload and native-install owners.
//! The initial domain has no imports or symbolic fixups. A source island
//! certificate is required; recorded-comparand TV alone grants no entry here.

use super::*;
use crate::compile_service::{CompileGeneration, InstalledArtifact};
use crate::jit_contract::ArtifactManifestV1;
use sha2::{Digest, Sha256};

/// Non-callable, move-only predecessor of the existing installed-image owner.
/// Only a policy-qualified compile can pair its actual artifact and source.
pub struct CoreInstallationArtifact {
    artifact: CoreAddressFreeMachineArtifact,
    source: CoreCompilationSource,
    verified_proof_reports: usize,
}

impl std::fmt::Debug for CoreInstallationArtifact {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("CoreInstallationArtifact")
            .field("artifact", &self.artifact)
            .finish_non_exhaustive()
    }
}

/// Installation refused without exposing a pointer; the exact predecessor is retained.
pub struct CoreInstallationFailure {
    reason: String,
    predecessor: CoreInstallationArtifact,
}

impl std::fmt::Debug for CoreInstallationFailure {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("CoreInstallationFailure")
            .field("reason", &self.reason)
            .finish_non_exhaustive()
    }
}
impl std::fmt::Display for CoreInstallationFailure {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(&self.reason)
    }
}
impl std::error::Error for CoreInstallationFailure {}
impl CoreInstallationFailure {
    pub fn reason(&self) -> &str {
        &self.reason
    }
    pub fn predecessor(&self) -> &CoreInstallationArtifact {
        &self.predecessor
    }
    pub fn into_predecessor(self) -> CoreInstallationArtifact {
        self.predecessor
    }
}

pub(super) fn source_contract(module: &trust_ir::Module) -> Result<(), String> {
    let environment = trust_cg_process_env::artifact_reuse_environment_safety();
    if !environment.is_reuse_safe() {
        return Err(format!(
            "unkeyed ambient controls: {:?}",
            environment.unkeyed_controls()
        ));
    }
    let config = trust_ir_build::ValidationConfig::pinned()
        .with_bound_certificates(true)
        .with_source_bound_certificates(true)
        .with_gate_evidence(true);
    let report = trust_ir_build::validate_module_with_config(module, &config);
    if !report.is_ok() {
        return Err(format!(
            "source-bound Core validation: {:?}",
            report.into_errors()
        ));
    }
    // Recognition and current-body evidence remain the existing default owner's decision.
    trust_cg_lower::CodegenLicensePolicy::default()
        .enforce_module(module)
        .map_err(|error| error.to_string())?;
    Ok(())
}

impl PolicyQualifiedCoreJitCompilationPlan {
    /// Compile with the ordinary proof gate, retaining the same moved Core/LIR
    /// inputs for typed installation. This changes no ordinary artifact default.
    pub fn compile_for_installation(
        self,
    ) -> Result<CoreInstallationArtifact, CoreAddressFreeMachineCompilationFailure> {
        let mut machine_rejection = None;
        let prepared = (|| {
            source_contract(&self.plan.parts.module).map_err(|reason| {
                CoreAddressFreeMachineCompilationError::Compile(
                    CompileError::CoreInstallationContract(reason),
                )
            })?;
            if !self.plan.native_runtime_catalog.is_empty()
                || !self
                    .plan
                    .parts
                    .declared_import_manifest
                    .imports()
                    .is_empty()
            {
                return Err(CoreAddressFreeMachineCompilationError::Compile(CompileError::CoreInstallationContract("typed runtime providers are not yet admitted by the Core installation owner".into())));
            }
            let compiled = compile_policy_qualified_core_to_address_free_machine(
                &self,
                &mut machine_rejection,
            )?;
            if !compiled.fixup_inventory.entries.is_empty() {
                return Err(CoreAddressFreeMachineCompilationError::Compile(
                    CompileError::CoreInstallationContract(
                        "symbolic Core fixups require a typed final-link transport".into(),
                    ),
                ));
            }
            Ok(compiled)
        })();
        match prepared {
            Err(error) => Err(CoreAddressFreeMachineCompilationFailure {
                error,
                plan: self,
                machine_rejection,
            }),
            Ok(compiled) => {
                let verified_proof_reports = compiled.verified_proof_report_count;
                let (artifact, source) =
                    into_core_address_free_machine_artifact_with_source(self, compiled);
                Ok(CoreInstallationArtifact {
                    artifact,
                    source,
                    verified_proof_reports,
                })
            }
        }
    }
}

impl CoreInstallationArtifact {
    #[cfg(feature = "source-defined-call")]
    pub(super) fn from_physically_bound_context_output(
        artifact: CoreAddressFreeMachineArtifact,
        source: CoreCompilationSource,
        verified_proof_reports: usize,
        storage: &std::sync::Arc<super::core_context_output::CoreBoundContextOutputProof>,
    ) -> Result<Self, String> {
        let owner = Self {
            artifact,
            source,
            verified_proof_reports,
        };
        storage.check_artifact(&owner.artifact, &owner.source)?;
        owner.validate()?;
        Ok(owner)
    }
    #[cfg(feature = "source-defined-call")]
    pub(super) fn from_physically_bound_four_pointer_status(
        artifact: CoreAddressFreeMachineArtifact,
        source: CoreCompilationSource,
        verified_proof_reports: usize,
        storage: &std::sync::Arc<super::core_four_pointer_status::CoreBoundFourPointerStatusProof>,
    ) -> Result<Self, String> {
        let owner = Self {
            artifact,
            source,
            verified_proof_reports,
        };
        storage.check_artifact(&owner.artifact, &owner.source)?;
        owner.validate()?;
        Ok(owner)
    }
    pub fn artifact(&self) -> &CoreAddressFreeMachineArtifact {
        &self.artifact
    }

    /// Publish an exact source/byte-bound entry that can be invoked only with
    /// an exclusive runtime-owned stack. The existing source, proof, fixup,
    /// payload and publication checks all remain mandatory. This initial
    /// consumer admits the existing complete no-call affine domain only;
    /// symbolic peer calls remain refused by their unchanged owners.
    pub fn install_owned_stack_entry(
        self,
        entry: &str,
        manifest: ArtifactManifestV1,
        generation: CompileGeneration,
    ) -> Result<(super::CoreOwnedStackEntry, ArtifactManifestV1), CoreInstallationFailure> {
        let requirement = (|| {
            self.validate()
                .map_err(crate::jit::entry_stack::EntryStackError::Source)?;
            super::core_stack_entry::bind_source(&self.source, &self.artifact, entry)
        })();
        let requirement = match requirement {
            Ok(value) => value,
            Err(error) => {
                return Err(CoreInstallationFailure {
                    reason: error.to_string(),
                    predecessor: self,
                });
            }
        };
        let (installed, manifest) = self.install(manifest, generation)?;
        let owned = super::core_stack_entry::CoreOwnedStackEntry::new(
            installed,
            manifest.clone(),
            entry.to_owned(),
            requirement,
        );
        Ok((owned, manifest))
    }

    fn validate(&self) -> Result<(), String> {
        source_contract(&self.source.module)?;
        let artifact = &self.artifact;
        if !artifact.native_runtime_catalog.is_empty()
            || !artifact.declared_import_manifest.imports().is_empty()
            || !artifact.fixup_inventory.entries.is_empty()
        {
            return Err(
                "Core installation needs complete empty import and fixup inventories".into(),
            );
        }
        self.validate_fields()
    }

    fn validate_fields(&self) -> Result<(), String> {
        let artifact = &self.artifact;
        if self.source.module.stable_digest() != artifact.module_digest()
            || trust_cg_lower::retained_lir_proof_context_digest(&self.source.lir_functions)
                .map_err(|error| error.to_string())?
                != artifact.retained_lir_proof_context_digest
        {
            return Err("retained Core/LIR identity differs from the compiled artifact".into());
        }
        let expected = core_address_free_machine_identity_from_parts(
            artifact.predecessor_identity,
            &artifact.receipt,
            &artifact.target_contract,
            &artifact.native_runtime_catalog,
            &artifact.native_dependency_references,
            &artifact.lir_native_dependency_bindings,
            &artifact.functions,
            &artifact.fixup_inventory,
            artifact.proof_bundle_digest,
            core_address_free_proof_optimization_digest(&artifact.proof_optimization_certificates)
                .map_err(|error| error.to_string())?,
        )
        .map_err(|error| error.to_string())?;
        if artifact.identity != expected
            || !artifact.receipt.is_intact()
            || !artifact.target_contract.is_intact()
            || !artifact.native_runtime_catalog.is_intact()
            || self.verified_proof_reports > artifact.proof_report_count
        {
            return Err("Core artifact identity/contract is not intact".into());
        }
        if artifact.functions.len() != self.source.lir_functions.len() {
            return Err("Core function cardinality differs".into());
        }
        for (function, (lir, _)) in artifact.functions.iter().zip(&self.source.lir_functions) {
            if function.name != lir.name
                || self
                    .source
                    .module
                    .function_by_id(function.source_function)
                    .is_none_or(|source| source.name != function.name)
                || function.certificate.function() != function.name
                || !function.certificate.has_checked_semantics()
                || !function.certificate.replay_check()
                || trust_ir::proof::ProofDigest::sha256(Sha256::digest(&function.code).into())
                    != function.normalized_code_digest
                || function
                    .certificate
                    .core_semantic_digest()
                    .map(trust_ir::proof::ProofDigest::sha256)
                    != Some(function.certificate_digest)
            {
                return Err(format!(
                    "Core function/certificate/bytes binding differs: {}",
                    function.name
                ));
            }
        }
        Ok(())
    }

    /// Publish through the existing shared JIT owner and existing manifest/native
    /// install gates. Returns the exact finalized manifest, completed with the
    /// actual native-payload digest. A supplied digest must match. Import/fixup
    /// support remains closed; failure returns this owner.
    pub fn install(
        self,
        manifest: ArtifactManifestV1,
        generation: CompileGeneration,
    ) -> Result<(InstalledArtifact, ArtifactManifestV1), CoreInstallationFailure> {
        let result = (|| {
            let permit = trust_cg_process_env::artifact_reuse_permit()
                .ok_or_else(|| "Core installation environment permit unavailable".to_owned())?;
            self.validate()?;
            let compiler = Compiler::new_for_target_spec(
                self.artifact.effective_options.compiler_config.clone(),
                self.artifact.target_contract.target_spec(),
            );
            crate::compile_service::preflight_core_publication(
                &compiler,
                &self.source.module,
                &manifest,
                generation,
                self.artifact.effective_options.jit_config.clone(),
            )?;
            let buffer =
                crate::jit::publish_core_artifact(&self).map_err(|error| error.to_string())?;
            let installed = crate::compile_service::finish_core_publication(
                &compiler,
                &self.source.module,
                buffer,
                manifest,
                generation,
                self.artifact.identity.full_digest().to_string(),
                self.artifact.proof_report_count,
                self.verified_proof_reports,
                self.artifact.proof_bundle_digest,
                self.artifact.effective_options.jit_config.clone(),
            )?;
            if !permit.is_valid() {
                return Err("Core installation environment changed".into());
            }
            Ok(installed)
        })();
        result.map_err(|reason| CoreInstallationFailure {
            reason,
            predecessor: self,
        })
    }

    pub(super) fn from_physically_bound_peer(
        artifact: CoreAddressFreeMachineArtifact,
        source: CoreCompilationSource,
        verified_proof_reports: usize,
        storage: &std::sync::Arc<super::core_peer_entry::CoreBoundPeerProof>,
    ) -> Result<Self, String> {
        let owner = Self {
            artifact,
            source,
            verified_proof_reports,
        };
        owner.validate_physically_bound_peer(storage)?;
        Ok(owner)
    }

    pub(crate) fn validate_physically_bound_peer(
        &self,
        storage: &std::sync::Arc<super::core_peer_entry::CoreBoundPeerProof>,
    ) -> Result<(), String> {
        source_contract(&self.source.module)?;
        if !self.artifact.native_runtime_catalog.is_empty()
            || !self.artifact.declared_import_manifest.imports().is_empty()
        {
            return Err("physically bound peers require empty imports/providers".into());
        }
        storage.check_artifact(&self.artifact, &self.source)?;
        self.validate_fields()
    }

    pub(super) fn install_physically_bound_peer(
        self,
        storage: &std::sync::Arc<super::core_peer_entry::CoreBoundPeerProof>,
        manifest: ArtifactManifestV1,
        generation: CompileGeneration,
    ) -> Result<(InstalledArtifact, ArtifactManifestV1), String> {
        let permit = trust_cg_process_env::artifact_reuse_permit()
            .ok_or("Core installation environment permit unavailable")?;
        self.validate_physically_bound_peer(storage)?;
        let compiler = Compiler::new_for_target_spec(
            self.artifact.effective_options.compiler_config.clone(),
            self.artifact.target_contract.target_spec(),
        );
        crate::compile_service::preflight_core_publication(
            &compiler,
            &self.source.module,
            &manifest,
            generation,
            self.artifact.effective_options.jit_config.clone(),
        )?;
        let buffer = crate::jit::publish_physically_bound_core_peer(&self, storage)
            .map_err(|e| e.to_string())?;
        let installed = crate::compile_service::finish_core_publication(
            &compiler,
            &self.source.module,
            buffer,
            manifest,
            generation,
            self.artifact.identity.full_digest().to_string(),
            self.artifact.proof_report_count,
            self.verified_proof_reports,
            self.artifact.proof_bundle_digest,
            self.artifact.effective_options.jit_config.clone(),
        )?;
        if !permit.is_valid() {
            return Err("Core installation environment changed".into());
        }
        Ok(installed)
    }

    pub(crate) fn physically_bound_peer_function(
        &self,
        storage: &std::sync::Arc<super::core_peer_entry::CoreBoundPeerProof>,
        name: &str,
        bytes: &[u8],
    ) -> Result<bool, String> {
        self.validate_physically_bound_peer(storage)?;
        let function = self
            .artifact
            .functions
            .iter()
            .find(|f| f.name == name)
            .ok_or("foreign peer publication function")?;
        if function.source_function != storage.caller() {
            return Ok(false);
        }
        if function.code.as_slice() != bytes {
            return Err("changed physically bound peer code".into());
        }
        Ok(true)
    }

    // The opaque owner, not an unchecked byte vector, is the shared publisher's input.
    pub(crate) fn publication_rows(
        &self,
    ) -> impl Iterator<Item = (&str, &[u8], &crate::jit_cert::JitCertificate, u8)> {
        self.artifact.functions.iter().map(|function| {
            (
                function.name.as_str(),
                function.code.as_slice(),
                &function.certificate,
                function.text_align_log2,
            )
        })
    }
    pub(crate) fn publication_citations(&self) -> Vec<ProofOptimizationCertificateCitation> {
        self.artifact.proof_optimization_certificates.clone()
    }
    pub(crate) fn publication_features(&self) -> TargetFeatureSet<AArch64IsaFeature> {
        self.artifact
            .functions
            .iter()
            .fold(TargetFeatureSet::EMPTY, |features, function| {
                features.union(function.function_target_features)
            })
    }
}

#[cfg(all(test, target_arch = "aarch64", target_os = "macos"))]
mod tests {
    use super::*;
    use crate as cg;
    #[allow(dead_code)]
    mod fixture {
        include!(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/tests/common/core_install_fixture.rs"
        ));
    }

    #[test]
    fn core_install_rejects_changed_source_lir_bytes_identity_fixups_and_provider_inventory() {
        let mut owner = fixture::licensed_plan(true)
            .compile_for_installation()
            .expect("genuine source-authenticated complete-proof predecessor");
        owner.validate().unwrap();

        let source = owner.source.module.clone();
        std::sync::Arc::make_mut(&mut owner.source.module)
            .name
            .push_str("-changed");
        assert!(owner.validate().is_err());
        owner.source.module = source;
        owner.validate().unwrap();

        owner.source.lir_functions[0].0.name.push_str("-changed");
        assert!(owner.validate().is_err());
        owner.source.lir_functions[0].0.name = "answer".into();
        owner.validate().unwrap();

        owner.artifact.functions[0].code[0] ^= 0x80;
        assert!(owner.validate().is_err());
        owner.artifact.functions[0].code[0] ^= 0x80;
        owner.validate().unwrap();

        let identity = owner.artifact.identity;
        owner.artifact.identity.full_digest = trust_ir::proof::ProofDigest::zero();
        assert!(owner.validate().is_err());
        owner.artifact.identity = identity;
        owner.validate().unwrap();

        owner
            .artifact
            .fixup_inventory
            .entries
            .push(CoreAddressFreeFixup {
                caller: owner.artifact.functions[0].source_function,
                function_ordinal: 0,
                offset: 0,
                target: CoreAddressFreeFixupTarget::ExactModuleFunction {
                    function: owner.artifact.functions[0].source_function,
                },
            });
        assert!(owner.validate().unwrap_err().contains("complete empty"));
        owner.artifact.fixup_inventory.entries.clear();
        owner.validate().unwrap();

        // A negative injected inventory row grants no provider implementation
        // authority. Even an unused whole row must refuse, never be filtered.
        use crate::core_admission::{CoreHostGlobalImport, CoreHostImport, CoreRuntimeIdentity};
        let runtime = CoreRuntimeIdentity::try_new(
            "negative-provider-only",
            trust_ir::proof::ProofDigest::sha256_domain("negative-test", b"no callable provider"),
        )
        .unwrap();
        let import = CoreHostGlobalImport::try_new(
            "unused_external",
            trust_ir::Ty::U64,
            false,
            None,
            Some(8),
            "negative-v1",
            runtime,
        )
        .unwrap();
        let imports =
            CoreDeclaredImportManifest::try_new(vec![CoreHostImport::Global(import)]).unwrap();
        let catalog =
            CoreNativeRuntimeCatalog::try_from_declared_import_manifest(&imports).unwrap();
        let original = std::mem::replace(&mut owner.artifact.native_runtime_catalog, catalog);
        assert!(owner.validate().unwrap_err().contains("complete empty"));
        owner.artifact.native_runtime_catalog = original;
        let original = std::mem::replace(&mut owner.artifact.declared_import_manifest, imports);
        assert!(owner.validate().unwrap_err().contains("complete empty"));
        owner.artifact.declared_import_manifest = original;
        owner.validate().unwrap();
    }
}
