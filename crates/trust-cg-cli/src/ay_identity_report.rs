// trust-cg-cli/ay_identity_report.rs - `--print-ay-identity`
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Report which AY THIS build of trust-cg admits, without running one.
//!
//! The record the AY identity rule compares against
//! (`trust_cg_verify::ay_identity`) is compiled into the binary, so a script
//! cannot see it. A script that wants to run an AY itself (the AArch64 AOT
//! arithmetic gate's independent replay) asks this binary instead: the answer
//! is [`trust_cg_verify::ay_identity::resolve_for_process`] applied to the
//! caller's environment, i.e. exactly the admission the compiler's own solver
//! calls make. Nothing is executed to decide it.
//!
//! Admission also places the admitted bytes in the private, content-addressed
//! copy every solver call starts from (`exec_path`; `0700` directory, `0500`
//! file, owned by this user). AY re-executes itself by its own path at
//! startup, so a script must start THAT file, never the admitted path, or a
//! file swapped in after admission runs instead.
//!
//! `toolchain_overlay` (additive to v2) is `null` for a build from an
//! installed toolchain. For a build from a local overlay toolchain
//! (`scripts/assemble_trust_overlay.py`) it names the overlay manifest's
//! digest and the Clean digest and commit the build is bound to: such a build
//! accepts no other proof checker.

use serde_json::{Value, json};
use trust_cg_verify::ay_identity::{self, PinnedAy};

/// The report object and whether an AY was admitted.
pub(crate) fn report() -> (Value, bool) {
    let recorded = match ay_identity::recorded_toolchain_ay_identity() {
        Ok(identity) => json!({
            "sha256": identity.sha256(),
            "identity": identity.describe(),
        }),
        Err(refusal) => json!({ "refusal": refusal.to_string(), "code": refusal.code() }),
    };
    let record = ay_identity::ToolchainAyRecord::recorded();
    let overlay = match (record.overlay(), record.pinned_clean_sha256()) {
        (Some(overlay), _) => json!({
            "manifest_sha256": overlay.manifest_sha256(),
            "clean_sha256": overlay.clean_sha256(),
            "clean_commit": overlay.clean_commit(),
        }),
        (None, Some(_)) => json!({ "refused": true }),
        (None, None) => Value::Null,
    };
    match ay_identity::resolve_for_process() {
        Ok(pinned) => (admitted(&pinned, recorded, overlay), true),
        Err(refusal) => (
            json!({
                "schema": SCHEMA,
                "admitted": false,
                "code": refusal.code(),
                "detail": refusal.to_string(),
                "recorded": recorded,
                "toolchain_overlay": overlay,
            }),
            false,
        ),
    }
}

/// Stable schema tag for scripts that parse the report.
pub(crate) const SCHEMA: &str = "trust-cg.ay-identity.v2";

fn admitted(pinned: &PinnedAy, recorded: Value, overlay: Value) -> Value {
    json!({
        "schema": SCHEMA,
        "admitted": true,
        "path": pinned.path().display().to_string(),
        "exec_path": pinned.exec_path().display().to_string(),
        "sha256": pinned.sha256(),
        "route": pinned.route().as_str(),
        "identity": pinned.identity().describe(),
        "describe": pinned.describe(),
        "recorded": recorded,
        "toolchain_overlay": overlay,
    })
}
