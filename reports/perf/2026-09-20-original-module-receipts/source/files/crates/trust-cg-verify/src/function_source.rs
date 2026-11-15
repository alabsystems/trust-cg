//! Borrowed original and adapter-input modules for one verification invocation.
//!
//! Identity records custody, not correctness of dialect lowering or of a call
//! contract. Consumers still need the independently checked source relation.

/// Immutable modules retained from before and after dialect lowering.
/// The digest cannot be supplied independently of these borrowed endpoints.
#[derive(Clone, Debug)]
pub struct FunctionSourceModules<'a> {
    original: &'a trust_ir::Module,
    lowered: &'a trust_ir::Module,
    digest: [u8; 32],
}

impl<'a> FunctionSourceModules<'a> {
    /// Hash the exact, lossless binary encodings once, without allocating a
    /// serialized copy of either module. Shared borrows prevent later mutation.
    pub fn capture(original: &'a trust_ir::Module, lowered: &'a trust_ir::Module) -> Self {
        use sha2::{Digest, Sha256};
        let module_digest = |module| {
            trust_ir::binary::ModuleBinaryPlan::new(module)
                .sha256_prefixed(b"trust-cg.function-source-module.v1\0")
        };
        let original_digest = module_digest(original);
        let lowered_digest = if std::ptr::eq(original, lowered) {
            original_digest
        } else {
            module_digest(lowered)
        };
        let mut hash = Sha256::new();
        hash.update(b"trust-cg.function-source-modules.v1\0");
        hash.update(original_digest);
        hash.update(lowered_digest);
        Self {
            original,
            lowered,
            digest: hash.finalize().into(),
        }
    }

    pub fn original(&self) -> &'a trust_ir::Module {
        self.original
    }

    pub fn lowered(&self) -> &'a trust_ir::Module {
        self.lowered
    }

    pub fn digest(&self) -> &[u8; 32] {
        &self.digest
    }
}

#[cfg(test)]
#[path = "function_source_tests.rs"]
mod tests;
