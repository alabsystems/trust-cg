// Author: Andrew Yates | Copyright 2026 Andrew Yates | License: Apache-2.0

//! Compiler-owned memory runtime identities and their real foreign prototypes.
//! A matching spelling alone never supplies a callee or a guessed declaration.

#[cfg(not(rustc_canonical_memory_symbols))]
use crate::lang_items::LangItem;
use rustc_hir::def::DefKind;
use rustc_middle::ty::{self, TyCtxt};
use rustc_span::def_id::DefId;

/// The memory routine an intrinsic site of this lowering calls.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum MemoryLibcall {
    /// `memcpy` (`copy_nonoverlapping`).
    Copy,
    /// `memmove` (`copy`).
    Move,
    /// `memset` (`write_bytes`, and the `[v; N]` fills).
    Set,
}

impl MemoryLibcall {
    pub(crate) const ALL: [Self; 3] = [Self::Copy, Self::Move, Self::Set];

    #[cfg(rustc_canonical_memory_symbols)]
    fn symbol(self) -> &'static str {
        match self {
            Self::Copy => "memcpy",
            Self::Move => "memmove",
            Self::Set => "memset",
        }
    }

    pub(crate) fn label(self) -> &'static str {
        match self {
            Self::Copy => "MemCpy",
            Self::Move => "MemMove",
            Self::Set => "MemSet",
        }
    }

    /// Resolve the actual compiler authority, then authenticate its owner and
    /// prototype before the caller constructs an instance or a declaration.
    pub(crate) fn definition(self, tcx: TyCtxt<'_>) -> Result<DefId, String> {
        #[cfg(not(rustc_canonical_memory_symbols))]
        let did = {
            let item = match self {
                Self::Copy => LangItem::MemCpy,
                Self::Move => LangItem::MemMove,
                Self::Set => LangItem::MemSet,
            };
            tcx.lang_items().get(item).ok_or_else(|| {
                format!(
                    "[TCG-MEM-LIBCALL-ABI] missing genuine runtime lang item {}",
                    self.label()
                )
            })?
        };
        #[cfg(rustc_canonical_memory_symbols)]
        let did = {
            let symbol = rustc_span::Symbol::intern(self.symbol());
            let canonical = tcx.all_canonical_symbols(());
            let mut entries = canonical.iter().filter(|entry| entry.symbol == symbol);
            let first = entries.next().ok_or_else(|| {
                format!(
                    "[TCG-MEM-LIBCALL-ABI] missing genuine runtime canonical symbol {}",
                    self.symbol()
                )
            })?;
            if entries.next().is_some() {
                return Err(format!(
                    "[TCG-MEM-LIBCALL-ABI] conflicting runtime canonical symbols {}",
                    self.symbol()
                ));
            }
            first.def_id
        };
        let core = tcx.lang_items().sized_trait().map(|did| did.krate);
        if Some(did.krate) != core {
            return Err(format!(
                "[TCG-MEM-LIBCALL-ABI] unsupported genuine {} owner {did:?}",
                self.label()
            ));
        }
        self.validate_declaration(tcx, did)?;
        Ok(did)
    }

    /// Check foreign-function kind and the exact prototype, independently of
    /// identity lookup. Success here alone supplies no core-owner authority.
    /// The backend's supported `size_t` mapping is checked by its caller too.
    pub(crate) fn validate_declaration(self, tcx: TyCtxt<'_>, did: DefId) -> Result<(), String> {
        // Authenticate kind before querying a function signature.
        if tcx.def_kind(did) != DefKind::Fn || !tcx.is_foreign_item(did) {
            return Err(format!(
                "[TCG-MEM-LIBCALL-ABI] unsupported genuine {} foreign function {did:?}",
                self.label()
            ));
        }
        let sig = tcx.fn_sig(did).instantiate_identity().skip_binder();
        let inputs = sig.inputs();
        let is_fill = self == Self::Set;
        if inputs.len() != 3
            || sig.c_variadic()
            || sig.abi() != (rustc_abi::ExternAbi::C { unwind: false })
            || !matches!(inputs[0].kind(), ty::RawPtr(_, rustc_hir::Mutability::Mut))
            || sig.output() != inputs[0]
            || inputs[2] != tcx.types.usize
            || (is_fill && inputs[1] != tcx.types.i32)
            || (!is_fill && !matches!(inputs[1].kind(), ty::RawPtr(_, rustc_hir::Mutability::Not)))
        {
            return Err(format!(
                "[TCG-MEM-LIBCALL-ABI] unsupported genuine {} prototype {sig:?}",
                self.label()
            ));
        }
        Ok(())
    }
}
