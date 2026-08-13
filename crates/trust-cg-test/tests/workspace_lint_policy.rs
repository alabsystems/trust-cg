//! Regression check for the workspace-wide `deny(warnings)` policy.
//!
//! The root manifest declares `[workspace.lints.rust] warnings = "deny"` and
//! instructs every member to opt in with `[lints] workspace = true`. That opt-in
//! is not automatic, and the failure mode is silent in a way that reads
//! backwards: a member that declares its own `[lints.<tool>]` table **replaces**
//! the inherited set rather than extending it, so adding what looks like a
//! tightening ("this lint should warn") actually drops `deny(warnings)` for the
//! whole crate.
//!
//! That is exactly what `trust-cg-llvm-import` did. It carried
//! `[lints.rust] unused_must_use = "warn"` -- a level that is already rustc's
//! default -- so the table's only net effect was to opt roughly 4500 lines,
//! including the driver-gated `trust-cg-ws2-import` binary, out of the policy.
//! `trust-cg-fuzz` had no `[lints]` table at all.
//!
//! Nothing else catches this. `scripts/check_warnings_ratchet.sh` builds with
//! default features and counts `warning:` lines, so it never compiles
//! feature-gated code and cannot see a crate that silently stopped denying.

use std::fs;
use std::path::{Path, PathBuf};

fn repo_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../..")
        .canonicalize()
        .expect("canonicalize repository root")
}

fn read_toml(relative: &str) -> toml::Value {
    let path = repo_root().join(relative);
    let text = fs::read_to_string(&path)
        .unwrap_or_else(|error| panic!("read {}: {error}", path.display()));
    toml::from_str(&text).unwrap_or_else(|error| panic!("parse {}: {error}", path.display()))
}

/// The policy has to exist before it is worth asserting anyone inherits it.
#[test]
fn workspace_declares_the_deny_warnings_policy() {
    let root = read_toml("Cargo.toml");
    assert_eq!(
        root["workspace"]["lints"]["rust"]["warnings"].as_str(),
        Some("deny"),
        "root manifest must keep `[workspace.lints.rust] warnings = \"deny\"`; \
         every member inherits this and the per-member test below assumes it"
    );
}

#[test]
fn every_workspace_member_inherits_the_lint_policy() {
    let root = read_toml("Cargo.toml");
    let members: Vec<&str> = root["workspace"]["members"]
        .as_array()
        .expect("workspace members array")
        .iter()
        .filter_map(toml::Value::as_str)
        .collect();
    assert!(
        !members.is_empty(),
        "workspace must declare members for this policy to mean anything"
    );

    let mut offenders = Vec::new();
    for member in &members {
        let manifest_path = format!("{member}/Cargo.toml");
        if !repo_root().join(&manifest_path).is_file() {
            continue;
        }
        let manifest = read_toml(&manifest_path);
        let inherits = manifest
            .get("lints")
            .and_then(|lints| lints.get("workspace"))
            .and_then(toml::Value::as_bool)
            == Some(true);
        if !inherits {
            // Report what the member has instead, so the failure names the cause
            // rather than only the symptom.
            let found = manifest.get("lints").map_or_else(
                || "no [lints] table".to_string(),
                |lints| format!("{lints}"),
            );
            offenders.push(format!("  {member}: {found}"));
        }
    }

    assert!(
        offenders.is_empty(),
        "these workspace members do not inherit `[workspace.lints]`, so \
         `warnings = \"deny\"` does not apply to them:\n{}\n\n\
         Add `[lints]` / `workspace = true` to each. Note that Cargo rejects a \
         local `[lints.<tool>]` table alongside `workspace = true` -- the local \
         table replaces inheritance rather than extending it, so a per-crate lint \
         level must move to `[workspace.lints]` at the root or become a scoped \
         `#[allow]` / `#[deny]` in source.",
        offenders.join("\n")
    );
}
