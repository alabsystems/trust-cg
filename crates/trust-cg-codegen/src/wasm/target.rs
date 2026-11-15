// trust-cg-codegen/wasm/target.rs - wasm32 target recognition
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! wasm32 target recognition and dispatch boundary.
//!
//! WebAssembly is a **stack machine**: it has no physical registers, condition
//! flags, calling-convention argument registers, or object-file relocations.
//! The register-machine [`crate::target::Target`] enum
//! (`X86_64`/`Aarch64`/`Riscv64`) exists precisely to describe those things, so
//! wasm deliberately does **not** live there — forcing it in would mean dozens
//! of `unreachable!` arms across regalloc / ISel / JIT and would mis-model the
//! backend.
//!
//! Instead, wasm is recognized at the **dispatch boundary**: a target selector
//! checks [`is_wasm32_target`] first and, when true, routes to the wasm
//! pipeline ([`crate::wasm::compile_module`]) rather than constructing a
//! register `Target`. This module owns that recognition.

/// Returns true if `triple` (a full target triple like
/// `wasm32-unknown-unknown` / `wasm32-wasip1`, or a bare arch like `wasm32`)
/// targets 32-bit WebAssembly and must be routed to the wasm backend.
///
/// 64-bit `wasm64` is intentionally **not** matched: it is not a target the
/// wasm backend handles yet (linear-memory lowering assumes 32-bit addresses).
pub fn is_wasm32_target(triple: &str) -> bool {
    let arch = triple.split('-').next().unwrap_or(triple);
    arch == "wasm32"
}

/// The canonical target triple of the wasm backend's closed-module lane.
pub const WASM32_TRIPLE: &str = "wasm32-unknown-unknown";

/// The canonical [`trust_ir::TargetInfo`] a module must carry to enter the
/// wasm32 lane: 32-bit pointers, little-endian, pinned to [`WASM32_TRIPLE`].
///
/// [`crate::wasm::compile_module`] refuses target-free modules and modules
/// pinned to any other pointer-width/endianness shape (the layout engine would
/// size pointers at 8 bytes while the lowering addresses memory through i32).
/// Callers building modules for this backend stamp
/// `module.target_info = Some(wasm32_target_info())` before compiling.
///
/// `struct_passing` is [`trust_ir::StructPassingPolicy::NativeC`]: the lane
/// passes a by-value aggregate by the WebAssembly Basic C ABI (the classifier
/// in `lower/abi.rs`), so a module stamped with this shape claims exactly the
/// classification the lane applies. A producer that performed no aggregate
/// classification stamps `Unclassified` itself, and the lane refuses such a
/// module once an aggregate crosses a call edge by value
/// (`trust_cg_lower::reject_unconsumed_struct_passing`); `AlwaysMemory` is
/// refused outright.
pub fn wasm32_target_info() -> trust_ir::TargetInfo {
    trust_ir::TargetInfo {
        triple: WASM32_TRIPLE.to_string(),
        pointer_size: 4,
        endianness: trust_ir::Endianness::Little,
        abi: None,
        struct_passing: trust_ir::StructPassingPolicy::NativeC,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn recognizes_wasm32_triples_and_arch() {
        assert!(is_wasm32_target("wasm32"));
        assert!(is_wasm32_target("wasm32-unknown-unknown"));
        assert!(is_wasm32_target("wasm32-wasip1"));
        assert!(is_wasm32_target("wasm32-wasi"));
    }

    #[test]
    fn rejects_non_wasm32() {
        assert!(!is_wasm32_target("aarch64-apple-darwin"));
        assert!(!is_wasm32_target("x86_64-unknown-linux-gnu"));
        assert!(!is_wasm32_target("riscv64"));
        // wasm64 is not handled by this backend yet.
        assert!(!is_wasm32_target("wasm64-unknown-unknown"));
        assert!(!is_wasm32_target(""));
    }

    #[test]
    fn canonical_wasm32_target_info_is_the_wasm32_shape() {
        let ti = wasm32_target_info();
        assert_eq!(ti.triple, WASM32_TRIPLE);
        assert!(is_wasm32_target(&ti.triple));
        assert_eq!(ti.pointer_size, 4);
        assert_eq!(ti.endianness, trust_ir::Endianness::Little);
        assert_eq!(ti.abi, None);
        assert_eq!(ti.struct_passing, trust_ir::StructPassingPolicy::NativeC);
    }
}
