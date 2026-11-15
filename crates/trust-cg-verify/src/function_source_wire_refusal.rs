// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! Writer-backed custody preflight; encoding capacity is not validation.
//!
//! The canonical TrustIR writer owns the encoding census. This adapter keeps
//! historical diagnostics without duplicating that census or changing custody
//! hashes, source borrows, semantic validation or proof authority.

use super::*;
use trust_ir::{BinaryProjectionError, WireNodeSite};

/// Preserve a source function's spelling only when the writer's coordinates
/// identify one actual node. FuncId is not an index into `Module.functions`;
/// malformed duplicate IDs must not manufacture a diagnostic owner.
fn node_location(module: &trust_ir::Module, site: WireNodeSite) -> String {
    let mut owners = module
        .functions
        .iter()
        .filter(|function| function.id.index() == site.function);
    let owner = owners.next();
    if let Some(owner) = owner
        && owners.next().is_none()
        && owner
            .blocks
            .iter()
            .filter(|block| block.id.index() == site.block)
            .count()
            == 1
        && owner
            .blocks
            .iter()
            .any(|block| block.id.index() == site.block && block.body.get(site.index).is_some())
    {
        format!("function '{}' bb{} #{}", owner.name, site.block, site.index)
    } else {
        format!(
            "function #{} bb{} #{}",
            site.function, site.block, site.index
        )
    }
}

/// Keep the old three public diagnostics byte-for-byte for their supported
/// locations. Every other refusal retains the shared writer's own display
/// text, including its ABI detail or full-width count. Future variants stay
/// fail-closed without a duplicated validator or a second construct census.
/// (A fourth, the `CertificateBinding` carrier gap, retired with trust-ir
/// binary v61, which writes the binding: the writer no longer refuses it.)
pub(super) fn map_wire_refusal(
    side: &'static str,
    module: &trust_ir::Module,
    refusal: BinaryProjectionError,
) -> SourceModuleHasNoWireImage {
    let (location, construct) = match refusal {
        BinaryProjectionError::ConstructAheadOfWireTag {
            construct,
            site: Some(site),
        } => (node_location(module, site), construct.to_owned()),
        refusal @ BinaryProjectionError::ConstructAheadOfWireTag { site: None, .. } => {
            ("module".to_owned(), refusal.to_string())
        }
        BinaryProjectionError::InlinedScopeChainUnencodable { function, scope } => (
            format!("function #{function} lexical scope #{scope}"),
            "a ScopeData.inlined_at inlining chain link ahead of its binary carrier".to_owned(),
        ),
        BinaryProjectionError::CompletenessClaimUnencodable => (
            "module".to_owned(),
            "a Module.completeness claim ahead of its binary carrier".to_owned(),
        ),
        refusal @ BinaryProjectionError::SignatureAbiUnencodable { signature, .. } => {
            (format!("signature #{signature}"), refusal.to_string())
        }
        refusal @ BinaryProjectionError::ProducerInternalType => {
            ("module".to_owned(), refusal.to_string())
        }
        refusal @ BinaryProjectionError::CountExceedsFormat { what, .. } => {
            (format!("module field '{what}'"), refusal.to_string())
        }
        // Projection-only errors are not currently returned by the exact
        // writer preflight. If that changes, no unrecognized error is admitted.
        refusal => ("module".to_owned(), refusal.to_string()),
    };
    SourceModuleHasNoWireImage {
        side,
        location,
        construct,
    }
}

/// Check exactly what the canonical writer refuses, before either endpoint
/// is hashed. The shared API checks unused signatures too and inspects no
/// byte payload. A wire image confers neither source nor native authority.
pub(super) fn wire_image_blocker(
    side: &'static str,
    module: &trust_ir::Module,
) -> Option<SourceModuleHasNoWireImage> {
    module
        .wire_image_refusal()
        .map(|refusal| map_wire_refusal(side, module, refusal))
}
