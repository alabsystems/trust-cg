// Copyright 2026 Andrew Yates | Apache-2.0

//! The distinct complete aggregate replay publication route. A real checked
//! original Source/Core/native image is mandatory; a policy setting alone
//! creates no evidence. Literal per-function-certificate policy still refuses.

use super::*;
use crate::compile_service::CompileGeneration;
use crate::jit::entry_stack::SourceEntryStackRequirement;
use crate::jit_contract::{ArtifactManifestV1, EvidenceStrength, ProofMode, ProofPolicy};
use sha2::{Digest, Sha256};

pub struct CoreDefinedCallInstallationFailure {
    reason: String,
    predecessor: CoreCheckedDefinedCallImage,
}
impl std::fmt::Debug for CoreDefinedCallInstallationFailure {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("CoreDefinedCallInstallationFailure")
            .field("reason", &self.reason)
            .finish_non_exhaustive()
    }
}
impl std::fmt::Display for CoreDefinedCallInstallationFailure {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(&self.reason)
    }
}
impl std::error::Error for CoreDefinedCallInstallationFailure {}
impl CoreDefinedCallInstallationFailure {
    pub fn reason(&self) -> &str {
        &self.reason
    }
    pub fn predecessor(&self) -> &CoreCheckedDefinedCallImage {
        &self.predecessor
    }
    pub fn into_predecessor(self) -> CoreCheckedDefinedCallImage {
        self.predecessor
    }
}

fn aggregate_policy(policy: &ProofPolicy) -> Result<(), String> {
    if policy.mode != ProofMode::RequireReplay || policy.require_jit_certificate {
        return Err("aggregate image requires replay evidence policy; literal per-function JitCertificate policy remains unsupported".into());
    }
    if !policy
        .required_strength
        .admits(&EvidenceStrength::IndependentReplay {
            checker: "Clean canonical kernel and Clean/Carcara".into(),
        })
    {
        return Err("aggregate independent replay does not assert SMT-solver-only evidence".into());
    }
    Ok(())
}

impl CoreCheckedDefinedCallImage {
    pub(crate) fn publication_features(&self) -> TargetFeatureSet<AArch64IsaFeature> {
        let rejection = self
            .linked()
            .predecessor()
            .machine_rejection()
            .expect("private checked owner retains rejection");
        rejection
            .prior_functions
            .iter()
            .fold(rejection.machine.function_target_features, |features, f| {
                features.union(f.function_target_features)
            })
    }

    pub(crate) fn validate_publication(
        &self,
        module: &trust_ir::Module,
        image: &[u8],
        policy: &ProofPolicy,
    ) -> Result<(), String> {
        aggregate_policy(policy)?;
        let endpoints = self.linked().verification_endpoints()?;
        if !std::ptr::eq(module, endpoints.module())
            || module.stable_digest() != self.linked().predecessor().plan().module_digest()
            || image != self.linked().image()
            || trust_ir::proof::ProofDigest::sha256(Sha256::digest(image).into())
                != self.linked().image_digest()
            || self.replayed_native_parts() == 0
            || self.native_part_provenance().len() != self.replayed_native_parts()
        {
            return Err("checked aggregate original module/image/replay custody differs".into());
        }
        let caller = self
            .linked()
            .functions()
            .iter()
            .find(|f| f.function() == self.caller())
            .ok_or("checked aggregate entry range is absent")?;
        if caller.name() != endpoints.caller_lir().name {
            return Err("checked aggregate selects another original entry".into());
        }
        Ok(())
    }

    /// Install only this proved original entry, callable exclusively through a
    /// real OwnedEntryStack. Genuine aggregate evidence follows the ordinary
    /// manifest/ABI/payload/RX-readback/native-install owners; no raw pointer or
    /// per-row certificate is exposed, and the source/rejected report is kept.
    pub fn install_owned_stack_entry(
        self,
        manifest: ArtifactManifestV1,
        generation: CompileGeneration,
    ) -> Result<(CoreOwnedStackEntry, ArtifactManifestV1), CoreDefinedCallInstallationFailure> {
        let prepared = (|| {
            let permit = trust_cg_process_env::artifact_reuse_permit()
                .ok_or("aggregate publication environment permit unavailable")?;
            let endpoints = self.linked().verification_endpoints()?;
            let module = endpoints.module();
            self.validate_publication(module, self.linked().image(), &manifest.proof_policy)?;
            let options = self.linked().predecessor().plan().effective_options();
            let compiler =
                Compiler::new_for_target_spec(options.compiler_config.clone(), options.target_spec);
            crate::compile_service::preflight_core_publication(
                &compiler,
                module,
                &manifest,
                generation,
                options.jit_config.clone(),
            )?;
            let requirement = SourceEntryStackRequirement::from_checked_defined_call_entry(&self)
                .map_err(|e| e.to_string())?;
            let entry = module
                .function_by_id(self.caller())
                .ok_or("aggregate caller source disappeared")?
                .name
                .clone();
            let buffer =
                crate::jit::publish_checked_defined_call(&self).map_err(|e| e.to_string())?;
            let installed = crate::compile_service::finish_core_defined_call_publication(
                &compiler,
                module,
                buffer,
                manifest,
                generation,
                &self,
                options.jit_config.clone(),
            )?;
            if !permit.is_valid() {
                return Err("aggregate publication environment changed".into());
            }
            Ok::<_, String>((installed, requirement, entry))
        })();
        match prepared {
            Err(reason) => Err(CoreDefinedCallInstallationFailure {
                reason,
                predecessor: self,
            }),
            Ok(((installed, manifest), requirement, entry)) => {
                let owned = super::core_stack_entry::CoreOwnedStackEntry::new_aggregate(
                    installed,
                    manifest.clone(),
                    entry,
                    requirement,
                    self,
                );
                Ok((owned, manifest))
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::jit_contract::RequiredEvidenceStrength;
    #[test]
    fn replay_strength_is_complete_without_claiming_a_solver() {
        let strength = EvidenceStrength::IndependentReplay {
            checker: "Clean canonical kernel and Clean/Carcara".into(),
        };
        assert!(RequiredEvidenceStrength::Complete.admits(&strength));
        assert!(!RequiredEvidenceStrength::Formal.admits(&strength));
        assert_eq!(strength.as_str(), "independent_replay");
    }

    #[test]
    fn aggregate_policy_preserves_literal_certificate_and_solver_only_refusals() {
        let mut policy = ProofPolicy::require_certificates(std::iter::empty::<String>());
        assert!(aggregate_policy(&policy).is_err());
        policy.mode = ProofMode::RequireReplay;
        policy.require_jit_certificate = true;
        assert!(aggregate_policy(&policy).is_err());
        policy.require_jit_certificate = false;
        policy.required_strength = RequiredEvidenceStrength::Complete;
        aggregate_policy(&policy).unwrap();
        policy.required_strength = RequiredEvidenceStrength::Formal;
        assert!(aggregate_policy(&policy).is_err());
    }
}
