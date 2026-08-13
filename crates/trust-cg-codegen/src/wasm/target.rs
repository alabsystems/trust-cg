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
}
