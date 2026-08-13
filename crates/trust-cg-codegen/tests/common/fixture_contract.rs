//! Test-only bridge for exercising caller-authored manifest fixtures.
//!
//! This deliberately does not model product install authority. Product code
//! must use `InstalledArtifact::get_contract_symbol_bound`, which authenticates
//! the compiler-derived payload binding before delegating to manifest checks.

use trust_cg_codegen::ExecutableBuffer;
use trust_cg_codegen::jit_contract::{
    ArtifactContractError, ArtifactManifestV1, SymbolLookupContract, TypedSymbol,
};

pub trait FixtureContractLookup {
    #[allow(clippy::result_large_err)] // Test bridge mirrors the production contract verbatim.
    fn get_fixture_contract_symbol_bound<'a, F: Copy>(
        &'a self,
        manifest: &'a ArtifactManifestV1,
        contract: &SymbolLookupContract,
    ) -> Result<TypedSymbol<'a, F>, ArtifactContractError>;
}

impl FixtureContractLookup for ExecutableBuffer {
    #[allow(clippy::result_large_err)] // Test bridge mirrors the production contract verbatim.
    fn get_fixture_contract_symbol_bound<'a, F: Copy>(
        &'a self,
        manifest: &'a ArtifactManifestV1,
        contract: &SymbolLookupContract,
    ) -> Result<TypedSymbol<'a, F>, ArtifactContractError> {
        let ptr = self
            .get_fn_ptr_bound(&contract.symbol)
            .map(|pointer| pointer.as_ptr())
            .unwrap_or(std::ptr::null());
        manifest.typed_symbol(contract, ptr)
    }
}
