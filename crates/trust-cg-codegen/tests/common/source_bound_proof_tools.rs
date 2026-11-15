// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0
//! The proof tools a proof-required AArch64 JIT test on the host needs, and
//! the ones this process actually resolved.
//!
//! A source-bound leaf publishes only when its FP/LR frame theorem, each of
//! the six memory-effect parts of its two frame records (`L07-P2`: the save
//! and restore are credited by the frame theorem AND their parts) and each
//! ADD/SUB/LSL ALU theorem are discharged by the identity-admitted AY (UNSAT
//! with an Alethe proof) AND fully replayed by an independent Clean checker
//! built with `carcara-verify`. Neither tool is optional and neither refusal
//! is waived: a test that needs them fails, naming the tools it resolved,
//! instead of skipping. The recorded host outcomes (the pack-9192 pair on
//! aarch64-apple-darwin answers `unknown` on the frame query and certifies no
//! part; an overlay with AY 2657db47c and Clean ed21fee39 discharges the frame
//! query and every part) are in docs/jit-source-custody.md.

#![allow(dead_code)]

/// What these tests require of the proof tools.
pub const REQUIRED_PROOF_TOOLS: &str = "requires the identity-admitted AY to answer \
     UNSAT with an Alethe proof for the source-bound AArch64 frame query, the \
     memory-effect parts of its two frame records and the ALU queries, and a Clean \
     checker built with carcara-verify that fully replays each proof \
     (docs/jit-source-custody.md names the pairs measured on each host)";

/// The AY and Clean this process resolved, in one line.
pub fn resolved_proof_tools() -> String {
    let ay = match trust_cg_verify::ay_identity::resolve_for_process() {
        Ok(ay) => format!("AY {}", ay.describe()),
        Err(refusal) => format!("no AY admitted ({refusal})"),
    };
    let clean = match trust_cg_verify::obligation_cert_store::resolve_proof_checker() {
        Ok((path, sha256)) => format!("Clean {} sha256 {sha256}", path.display()),
        Err(reason) => format!("no Clean checker resolves ({reason})"),
    };
    format!("{ay}; {clean}")
}

/// The diagnostic appended to every unexpected proof refusal.
pub fn proof_tool_context() -> String {
    format!(
        "this test {REQUIRED_PROOF_TOOLS}; resolved: {}",
        resolved_proof_tools()
    )
}

/// Refuse to start without both tools: a missing AY or Clean is a failure
/// naming the missing component, never a skip.
pub fn require_proof_tools() {
    if let Some(reason) = trust_cg_verify::ay_bridge::proof_toolchain_unavailable_reason() {
        panic!(
            "PROOF_TOOLS_MISSING: {reason}; this test {REQUIRED_PROOF_TOOLS}; resolved: {}",
            resolved_proof_tools()
        );
    }
}

/// Whether a proof refusal is the checker's: the frame or ALU theorem the
/// source-bound owner forms, or a memory-effect part of a source-bound frame
/// record, was not discharged by an independently replayed proof (AY
/// `unknown`, or a Clean rejection).
pub fn is_unreplayed_source_bound_refusal(reason: &str) -> bool {
    reason.contains("source-bound frame needs independently replayed proof")
        || reason.contains("source-bound arithmetic needs independently replayed proof")
        || reason.contains(
            trust_cg_verify::aarch64_memory_source_binding::SOURCE_BOUND_MEMORY_NOT_CREDITED,
        )
}
