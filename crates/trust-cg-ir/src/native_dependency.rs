// trust-cg-ir/native_dependency.rs - catalog-scoped native dependency identity
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Stable carriers for native dependency identity.
//!
//! A [`NativeDependencyId`] is an ordinal in one separately authenticated
//! runtime catalog.  It is intentionally not a symbol-name hash, address, or
//! authority token: the same ordinal in two catalogs can name different
//! dependencies.  Machine artifacts therefore have to carry the catalog
//! digest alongside every ID-bearing fixup inventory.

use serde::{Deserialize, Serialize};

/// Compact identity of one dependency in an authenticated native-runtime
/// catalog.
///
/// Construction is public because compiler stages in sibling crates must be
/// able to transport IDs.  Constructing an ID grants no binding or execution
/// authority; only lookup in the exact catalog named by an enclosing receipt
/// gives it meaning.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
#[repr(transparent)]
pub struct NativeDependencyId(u32);

impl NativeDependencyId {
    /// Create a catalog-local ID from its canonical zero-based ordinal.
    #[must_use]
    pub const fn new(index: u32) -> Self {
        Self(index)
    }

    /// Canonical zero-based ordinal encoded in receipts and machine IR.
    #[must_use]
    pub const fn index(self) -> u32 {
        self.0
    }
}

impl std::fmt::Display for NativeDependencyId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "native-dependency#{}", self.0)
    }
}

#[cfg(test)]
mod tests {
    use super::NativeDependencyId;

    #[test]
    fn identity_round_trips_through_json_without_symbol_or_address_state() {
        let id = NativeDependencyId::new(17);
        let json = serde_json::to_string(&id).unwrap();
        let decoded: NativeDependencyId = serde_json::from_str(&json).unwrap();

        assert_eq!(json, "17");
        assert_eq!(decoded, id);
        assert_eq!(decoded.index(), 17);
        assert_eq!(decoded.to_string(), "native-dependency#17");
        assert_eq!(std::mem::size_of::<NativeDependencyId>(), 4);
    }
}
