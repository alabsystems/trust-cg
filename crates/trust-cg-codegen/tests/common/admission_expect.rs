// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0
//! The refusal a fixture must get when trust-ir itself refuses it.
//!
//! Since WS7.3 every trust-cg ingestion entry runs trust-ir's composed codegen
//! admission first and refuses every finding, before any backend arm is
//! reached. A refusal fixture that trust-ir refuses is therefore refused by
//! trust-ir's finding, named by its `ValidationError` variant (an
//! `InvalidTrustIr` refusal spells it in both `Debug` and `Display`) or, for
//! the findings the adapter maps to a named refusal of its own, by trust-ir's
//! text. A fixture trust-ir admits keeps the backend's own refusal.
//!
//! The admission judges a module under the license policy of the compile
//! that ingests it: trust-ir raises `UnlicensedBodyForCodegen` for a
//! claim-less body exactly when the policy refuses such bodies, which the
//! default policy does (WS7.5, DG-73). Every function here therefore takes
//! that policy as a required argument, and the caller passes the policy its
//! compile states: `Permit` for hand-built claim-less fixtures,
//! `CodegenLicensePolicy::default()` for a compile that states none
//! (LD-55, LD-76). Judged under a policy other than
//! the compile's, a claim-less fixture would report a license finding its
//! compile never raised, or miss one it did.

// Declared unconditionally; a target whose callers are all cfg'd out for this
// host must not trip the workspace's `warnings = "deny"`.
#![allow(dead_code)]

use trust_cg_lower::CodegenLicensePolicy;
use trust_ir::Module;

/// trust-ir's first codegen-admission finding for `module` under `license`,
/// the policy the caller's compile states (no consumer dialects), as
/// `(variant name, text)`, or `None` when trust-ir admits the module.
pub fn first_finding(module: &Module, license: &CodegenLicensePolicy) -> Option<(String, String)> {
    let findings = trust_cg_lower::admission_findings(module, license, &[]);
    let finding = findings.first()?;
    let debug = format!("{finding:?}");
    let variant = debug
        .split(|c: char| !(c.is_ascii_alphanumeric() || c == '_'))
        .next()
        .unwrap_or_default()
        .to_string();
    Some((variant, finding.to_string()))
}

/// Whether `error` — a compile error's `Debug` or `Display` text — names
/// trust-ir's first admission finding for `module` under `license`, the
/// policy the compile that produced `error` stated. `None` when trust-ir
/// admits the module (the backend's own refusal is then the one to check).
pub fn names_first_finding(
    module: &Module,
    error: &str,
    license: &CodegenLicensePolicy,
) -> Option<bool> {
    let (variant, text) = first_finding(module, license)?;
    let escaped = format!("{text:?}");
    Some(
        (!variant.is_empty() && error.contains(&variant))
            || error.contains(&text)
            || error.contains(escaped.trim_matches('"')),
    )
}
