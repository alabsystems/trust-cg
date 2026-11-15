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

/// One module of a pair has no lossless binary encoding, so the pair has no
/// custody digest. The canonical writer owns this census, including constructs
/// ahead of their wire carrier, producer-internal types, bounded ABI records
/// and counts that exceed the binary format. Encoding custody does not validate
/// the module's semantics or authenticate a recorded physical ABI.
#[derive(Clone, Debug, PartialEq, Eq, thiserror::Error)]
#[error("the {side} trust-ir module has no binary wire image ({location}: {construct})")]
pub struct SourceModuleHasNoWireImage {
    /// `"original"` or `"lowered"`.
    pub side: &'static str,
    /// Where the unencodable construct sits.
    pub location: String,
    /// trust-ir's own name for it.
    pub construct: String,
}

#[path = "function_source_wire_refusal.rs"]
mod wire_refusal;
use wire_refusal::wire_image_blocker;

impl<'a> FunctionSourceModules<'a> {
    /// Hash the exact, lossless binary encodings once, without allocating a
    /// serialized copy of either module. Shared borrows prevent later mutation.
    ///
    /// A module with no binary encoding has no custody identity, so it is
    /// refused by name rather than hashed.
    pub fn capture(
        original: &'a trust_ir::Module,
        lowered: &'a trust_ir::Module,
    ) -> Result<Self, SourceModuleHasNoWireImage> {
        use sha2::{Digest, Sha256};
        if let Some(blocker) = wire_image_blocker("original", original) {
            return Err(blocker);
        }
        if !std::ptr::eq(original, lowered)
            && let Some(blocker) = wire_image_blocker("lowered", lowered)
        {
            return Err(blocker);
        }
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
        Ok(Self {
            original,
            lowered,
            digest: hash.finalize().into(),
        })
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

#[cfg(test)]
#[path = "function_source_wire_refusal_tests.rs"]
mod wire_refusal_tests;
