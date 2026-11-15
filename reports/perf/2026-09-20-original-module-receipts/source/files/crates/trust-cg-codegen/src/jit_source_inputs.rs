//! Call-local custody of the exact prepared AArch64/LIR pairing.
//!
//! This is not proof evidence. The compiler owns both inputs throughout the
//! call; shared borrows prevent replacement after binding. Source-aware proof
//! checking still requires the existing verifier's independent discharge.

use super::IrMachFunction;
#[cfg(feature = "verify")]
use super::JitError;

pub(super) struct Aarch64JitInputs<'a> {
    machine: &'a [IrMachFunction],
    #[cfg(feature = "verify")]
    source: Option<&'a [(trust_cg_lower::Function, trust_cg_lower::ProofContext)]>,
    #[cfg(feature = "verify")]
    source_modules: Option<trust_cg_verify::FunctionSourceModules<'a>>,
}

impl<'a> Aarch64JitInputs<'a> {
    pub(super) fn raw(machine: &'a [IrMachFunction]) -> Self {
        Self {
            machine,
            #[cfg(feature = "verify")]
            source: None,
            #[cfg(feature = "verify")]
            source_modules: None,
        }
    }

    /// Only the private compiler continuation supplies its replayed LIR here.
    /// Check ordinal pairing before encoding, mapping memory, or cache lookup;
    /// never silently truncate a zip or reconstruct source from machine tags.
    #[cfg(feature = "verify")]
    pub(super) fn with_replayed_lir(
        machine: &'a [IrMachFunction],
        source: &'a [(trust_cg_lower::Function, trust_cg_lower::ProofContext)],
    ) -> Result<Self, JitError> {
        if machine.len() != source.len() {
            return Err(JitError::LirSourceCountMismatch {
                machine: machine.len(),
                lir: source.len(),
            });
        }
        for (ordinal, (machine, (source, _))) in machine.iter().zip(source).enumerate() {
            if machine.name != source.name {
                return Err(JitError::LirSourcePairMismatch {
                    ordinal,
                    machine: machine.name.clone(),
                    lir: source.name.clone(),
                });
            }
        }
        Ok(Self {
            machine,
            source: Some(source),
            source_modules: None,
        })
    }

    #[cfg(feature = "verify")]
    pub(super) fn with_replayed_source_modules(
        machine: &'a [IrMachFunction],
        source: &'a [(trust_cg_lower::Function, trust_cg_lower::ProofContext)],
        original: &'a trust_ir::Module,
        lowered: &'a trust_ir::Module,
    ) -> Result<Self, JitError> {
        let mut inputs = Self::with_replayed_lir(machine, source)?;
        inputs.source_modules = Some(trust_cg_verify::FunctionSourceModules::capture(
            original, lowered,
        ));
        Ok(inputs)
    }

    #[cfg(feature = "verify")]
    pub(super) fn verifier_input_digest(
        &self,
        ordinal: usize,
    ) -> Result<[u8; 32], crate::jit_cert::JitIdentityEncodingError> {
        match &self.source_modules {
            Some(source) => crate::jit_cert::aarch64_verifier_input_digest_with_modules(
                &self.machine[ordinal],
                self.source(ordinal),
                source,
            ),
            None => crate::jit_cert::aarch64_verifier_input_digest_with_lir(
                &self.machine[ordinal],
                self.source(ordinal),
            ),
        }
    }

    #[cfg(feature = "verify")]
    pub(super) fn matches_report(
        &self,
        ordinal: usize,
        report: &trust_cg_verify::CapturedFunctionVerificationReport,
    ) -> bool {
        let machine = &self.machine[ordinal];
        let lir = self.source(ordinal);
        match &self.source_modules {
            Some(source) => report.matches_aarch64_input_with_modules(machine, lir, source),
            None => report.matches_aarch64_input(machine, lir),
        }
    }

    #[cfg(feature = "verify")]
    pub(super) fn verify(
        &self,
        ordinal: usize,
        verifier: &trust_cg_verify::FunctionVerifier,
        request: &trust_cg_verify::FunctionVerificationRequest,
    ) -> trust_cg_verify::CapturedFunctionVerificationReport {
        let machine = &self.machine[ordinal];
        let lir = self.source(ordinal);
        match &self.source_modules {
            Some(source) => verifier.verify_with_request_and_modules(machine, lir, source, request),
            None => verifier.verify_with_request(machine, lir, request),
        }
    }

    pub(super) fn functions(&self) -> &'a [IrMachFunction] {
        self.machine
    }

    #[cfg(feature = "verify")]
    pub(super) fn has_source(&self) -> bool {
        self.source.is_some()
    }

    #[cfg(feature = "verify")]
    pub(super) fn source_verifier(&self) -> Option<&'static trust_cg_verify::FunctionVerifier> {
        self.has_source()
            .then(crate::compiler::shared_aarch64_function_verifier)
    }

    #[cfg(feature = "verify")]
    pub(super) fn source(&self, ordinal: usize) -> Option<&'a trust_cg_lower::Function> {
        // The only producer checked lengths against the machine slice retained
        // in this same owner. An invalid ordinal is an internal bug, not a
        // reason to downgrade a source-bound request to source-less checking.
        self.source.map(|source| &source[ordinal].0)
    }

    #[cfg(feature = "verify")]
    pub(super) fn capture_request(
        &self,
        verifier: &trust_cg_verify::FunctionVerifier,
    ) -> trust_cg_verify::FunctionVerificationRequest {
        if self.has_source() {
            verifier.capture_request_with_mode(
                trust_cg_verify::provenance_xcheck::ProvenanceXCheckMode::Enforce,
            )
        } else {
            // Preserve the standalone raw-MachIR diagnostic/default policy.
            verifier.capture_request()
        }
    }
}

#[cfg(all(test, feature = "verify"))]
#[path = "jit_source_inputs_tests.rs"]
mod tests;
