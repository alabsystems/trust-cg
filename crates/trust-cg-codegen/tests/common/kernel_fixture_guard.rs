// trust-cg-codegen/tests/common/kernel_fixture_guard.rs - the runtime refusal
// that pairs with `cfg(kernel_fixture_layout_lint_only)`.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Second barrier for the layout-sensitive kernel JIT fixtures.
//!
//! `build.rs` emits `kernel_fixture_layout_lint_only` only when the compiler
//! is UNSUPPORTED for the frozen `repr(Rust)` fixtures *and* a lint driver
//! (`clippy-driver`, `tippy-driver`) is in front of it. A lint driver
//! type-checks and emits metadata; it links no test binary, so those targets
//! can be compiled for the lint gate without the `compile_error` that guards
//! every ordinary build.
//!
//! Being compiled is not permission to run. Each JIT entry point in those
//! targets calls this first under the same cfg, so "an uncertified compiler
//! cannot execute a frozen-layout fixture" is a property of the code, not of
//! how the linter happened to be invoked.

/// Refuse to execute a layout-sensitive kernel JIT fixture, naming the JIT
/// entry point (`what`) that tried to run.
///
/// Reachable only from a binary built under `kernel_fixture_layout_lint_only`,
/// which a lint driver never links.
pub fn refuse_uncertified_execution(what: &str) -> ! {
    panic!(
        "refusing to execute `{what}`: a repr(Rust) layout fixture must not execute under an \
         uncertified compiler. This target was compiled lint-only (a `clippy-driver` / \
         `tippy-driver` build, which links no binary); run it under exact Rust 1.95.0, \
         Rust 1.97.1, or the certified Trust compiler."
    );
}
