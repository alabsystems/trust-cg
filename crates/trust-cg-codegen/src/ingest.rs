//! Ingestion admission for the codegen entries (roadmap WS7.3, F-113).
//!
//! Every entry of this crate that receives a trust-ir module and lowers it —
//! [`crate::compiler::Compiler::compile`] (the object and CLI path, and the
//! in-process MIR lane that calls it),
//! [`crate::compiler::Compiler::compile_module_to_jit_with_profile_hooks`] (the
//! host JIT, and the compile service through both), and
//! [`crate::wasm::lower::compile_module_with_policy`] (the wasm lane) — admits
//! it through [`admit_module`] first, and re-admits the module a pre-adapter
//! rewrite produced ([`admit_rewritten`]) before lowering THAT. The rule, and
//! the one consumer-owned exemption (the `DialectOp` namespaces this crate's
//! dialect registry lowers), are stated on [`trust_cg_lower::ingest`].
//!
//! `tests/ingest_admission.rs` holds every public `compile*` / `translate_*`
//! entry that accepts a trust-ir module to this admission, or to a named,
//! shrink-only allowlist of diagnostic entries that are not ingestion
//! authority.

use std::sync::OnceLock;

use trust_cg_lower::{AdmittedModule, CodegenLicensePolicy};

use crate::compiler::CompileError;
use crate::dialect_legalization::{DialectLegalizationRegistry, OpLowering};

/// The `DialectOp` namespaces `registry` declares: a namespace there has a
/// registered lowering in this backend (a legalization rule that rewrites the
/// op into core trust-ir, or an adapter arm for an op the registry admits and
/// keeps), so trust-ir's "no registered lowering" refusal does not apply to
/// it here. A namespace the registry does not declare keeps that refusal —
/// and the legalization pass would refuse it by name anyway.
pub fn registry_dialect_namespaces(registry: &DialectLegalizationRegistry) -> Vec<&str> {
    registry
        .registrations()
        .iter()
        .map(|registration| registration.namespace.as_str())
        .collect()
}

/// [`registry_dialect_namespaces`] of the backend's default registry
/// ([`DialectLegalizationRegistry::trust_cg_default`]), the one a
/// [`crate::compiler::Compiler`] applies unless replaced.
pub fn registered_dialect_namespaces() -> &'static [&'static str] {
    static OWNED: OnceLock<Vec<String>> = OnceLock::new();
    static BORROWED: OnceLock<Vec<&'static str>> = OnceLock::new();
    BORROWED.get_or_init(|| {
        OWNED
            .get_or_init(|| {
                registry_dialect_namespaces(&DialectLegalizationRegistry::trust_cg_default())
                    .into_iter()
                    .map(str::to_owned)
                    .collect()
            })
            .iter()
            .map(String::as_str)
            .collect()
    })
}

/// Admit the module an entry RECEIVED, under `license`, exempting exactly
/// the `DialectOp` namespaces `registry` lowers (see
/// [`trust_cg_lower::ingest`]). Decided before any cache lookup or rewrite.
pub fn admit_module<'m>(
    module: &'m trust_ir::Module,
    license: &CodegenLicensePolicy,
    registry: &DialectLegalizationRegistry,
) -> Result<AdmittedModule<'m>, CompileError> {
    trust_cg_lower::admit_module(module, license, &registry_dialect_namespaces(registry))
        .map_err(CompileError::from_admission)
}

/// The runtime entries `registry` binds (every [`OpLowering::RuntimeCall`]
/// symbol): a legalization may declare each in the module it produces.
pub fn registry_runtime_symbols(registry: &DialectLegalizationRegistry) -> Vec<&str> {
    registry
        .registrations()
        .iter()
        .flat_map(|registration| &registration.ops)
        .flat_map(|rule| &rule.alternatives)
        .filter_map(|alternative| match &alternative.lowering {
            OpLowering::RuntimeCall { symbol } => Some(symbol.as_str()),
            _ => None,
        })
        .collect()
}

/// Re-admit `rewritten`, the module `registry`'s legalization produced from
/// the admitted `received` module, under the same admission. The runtime
/// entries the registry binds are the only declarations the rewrite may add
/// to a target-free module without a pinned target
/// ([`trust_cg_lower::AdmittedModule::readmit_rewritten_with_runtime_bindings`]),
/// the rule the legalization's own re-validation applies.
pub fn admit_rewritten<'r>(
    received: &AdmittedModule<'_>,
    rewritten: &'r trust_ir::Module,
    registry: &DialectLegalizationRegistry,
) -> Result<AdmittedModule<'r>, CompileError> {
    received
        .readmit_rewritten_with_runtime_bindings(rewritten, &registry_runtime_symbols(registry))
        .map_err(CompileError::from_admission)
}
