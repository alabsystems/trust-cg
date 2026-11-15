// trust-cg-irmid/passes/fill_call.rs - withheld unauthenticated fill-call rewrite
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! A helper name and signature do not bind an external declaration to the
//! bridge's store loop. No default pass rewrites those calls until a shared
//! source-bound helper contract can be checked (OD-155).

pub(crate) const FILL_CALL_NAME: &str = "fill_call";
pub(crate) const FILL_CALL_WITHHELD: &str =
    "an external fill-helper declaration has no source-bound helper body or contract";
