// trust-cg-ir/tls.rs - Thread-local storage access models
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! TLS access models.
//!
//! Identifies how a thread-local storage reference is resolved to a
//! concrete address. See issues #370 (MRS primitive, landed) and #383
//! (end-to-end wiring) for scope.
//!
//! | Model | Sequence | Runtime cost | JIT? |
//! |-------|----------|--------------|------|
//! | LocalExec | MRS + ADD [+ ADD] | no call | yes |
//! | InitialExec | MRS + LDR (GOT) | GOT fixup | no — needs loader |
//! | GeneralDynamic | TLSDESC resolver call (ELF) | TLSDESC | no |
//! | LocalDynamic | same TLSDESC sequence as GeneralDynamic | TLSDESC | no |
//! | Tlv | call `_tlv_bootstrap` (Darwin) | dyld callback | Darwin AOT only |

use serde::{Deserialize, Serialize};

/// TLS access model used when lowering a `#[thread_local]` reference.
///
/// The JIT currently only supports `LocalExec` — it owns TPIDR_EL0 on the
/// target thread, allocates the TLS block, and resolves offsets at codegen
/// time. AOT ELF supports `LocalExec` (linker-patched TPREL add pair),
/// `InitialExec` (GOT-indirect TPREL via the `R_AARCH64_TLSIE_*` pair) and
/// `GeneralDynamic` through a TLS descriptor (the `R_AARCH64_TLSDESC_*`
/// sequence; `LocalDynamic` reuses it). The ELF relocation model selects among
/// them; AOT Mach-O uses `Tlv`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum TlsModel {
    /// Local-exec — `MRS Xd, TPIDR_EL0` + `ADD Xd, Xd, #tprel_hi12, LSL #12`
    /// (if needed) + `ADD Xd, Xd, #tprel_lo12`. The JIT resolves the TPREL
    /// offset at codegen time. No runtime helper.
    LocalExec,
    /// Initial-exec — `MRS` + GOT load. Requires loader.
    InitialExec,
    /// General-dynamic — TLS-descriptor resolver call (ELF TLSDESC).
    /// Requires loader.
    GeneralDynamic,
    /// Local-dynamic — lowered exactly like `GeneralDynamic` (per-symbol
    /// TLSDESC). Requires loader.
    LocalDynamic,
    /// Darwin TLV descriptor — `ARM64_RELOC_TLVP_LOAD_PAGE21` + LDR TLVP.
    /// Requires `_tlv_bootstrap` from dyld. Only reachable on Mach-O AOT.
    Tlv,
}

impl TlsModel {
    /// True if this model can be lowered without a dynamic loader.
    /// Currently only `LocalExec` qualifies.
    pub fn is_jit_compatible(self) -> bool {
        matches!(self, TlsModel::LocalExec)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn local_exec_is_jit_compatible() {
        assert!(TlsModel::LocalExec.is_jit_compatible());
    }

    #[test]
    fn other_models_are_not_jit_compatible() {
        assert!(!TlsModel::InitialExec.is_jit_compatible());
        assert!(!TlsModel::GeneralDynamic.is_jit_compatible());
        assert!(!TlsModel::LocalDynamic.is_jit_compatible());
        assert!(!TlsModel::Tlv.is_jit_compatible());
    }

    #[test]
    fn tls_model_is_copy() {
        let m = TlsModel::LocalExec;
        let n = m;
        assert_eq!(m, n);
    }
}
