// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0
//! Pin a test fixture's trust-ir `target_info` to the triple it is compiled
//! for.
//!
//! trust-ir's validator refuses a module with an FFI boundary (a bodyless
//! external declaration) and no `target_info` (`TargetInfoRequired`:
//! cross-object ABI agreement requires a pinned target), and since WS7.3
//! every trust-cg ingestion entry refuses what that validator refuses. A
//! producer pins the target it emitted for; a fixture compiled for several
//! triples pins each compile's own triple through [`pinned`].

// Declared unconditionally; a target whose callers are all cfg'd out for this
// host must not trip the workspace's `warnings = "deny"`.
#![allow(dead_code)]

use trust_ir::{Endianness, Module, StructPassingPolicy, TargetInfo};

/// The trust-ir target metadata of a 64-bit little-endian `triple` (every
/// native triple trust-cg's fixtures compile for).
pub fn target_info(triple: &str) -> TargetInfo {
    TargetInfo {
        triple: triple.to_string(),
        pointer_size: 8,
        endianness: Endianness::Little,
        abi: None,
        struct_passing: StructPassingPolicy::NativeC,
    }
}

/// Pin `module` to `triple` in place. A module that already names `triple`
/// keeps its own `target_info` (its ABI and struct-passing facts included).
pub fn pin(module: &mut Module, triple: &str) {
    if module
        .target_info
        .as_ref()
        .is_some_and(|existing| existing.triple == triple)
    {
        return;
    }
    module.target_info = Some(target_info(triple));
}

/// A copy of `module` pinned to `triple`.
pub fn pinned(module: &Module, triple: &str) -> Module {
    let mut module = module.clone();
    pin(&mut module, triple);
    module
}

/// The triple of the host trust-cg's native tests run on.
pub fn host_triple() -> &'static str {
    match (std::env::consts::ARCH, std::env::consts::OS) {
        ("aarch64", "macos") => "aarch64-apple-darwin",
        ("x86_64", "macos") => "x86_64-apple-darwin",
        ("aarch64", _) => "aarch64-unknown-linux-gnu",
        _ => "x86_64-unknown-linux-gnu",
    }
}
