// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! Optional, untrusted diagnostics at the AOT preparation/certificate boundary.
//! No dump is read by compilation, verification, or publication. Debug text
//! retains transient metadata, but is not an encoding or proof authority.

use std::ffi::OsString;
use std::fmt::Write as _;
use std::path::{Path, PathBuf};
use std::sync::OnceLock;
use std::sync::atomic::{AtomicU64, Ordering};

use crate::compiler::CompilerConfig;
use crate::jit_diagnostics::sha256_hex;
use crate::pipeline::PreparationMetrics;
use crate::target::TargetSpec;

const ENV: &str = "TCG_DUMP_AARCH64_PREPARED";
static DIRECTORY: OnceLock<Option<PathBuf>> = OnceLock::new();
static NEXT: AtomicU64 = AtomicU64::new(0);

/// Install the diagnostic directory from a tracked backend option, once.
/// Equal reinstallation is accepted. An absent/empty tracked value disables
/// the standalone environment fallback. No setting changes a verdict.
pub fn set_directory(directory: Option<PathBuf>) -> bool {
    install(&DIRECTORY, directory)
}

fn install(cell: &OnceLock<Option<PathBuf>>, directory: Option<PathBuf>) -> bool {
    let directory = directory.filter(|p| !p.as_os_str().is_empty());
    match cell.set(directory) {
        Ok(()) => true,
        Err(requested) => cell.get() == Some(&requested),
    }
}

fn resolve(setting: Option<&Option<PathBuf>>, ambient: Option<OsString>) -> Option<PathBuf> {
    setting
        .cloned()
        .unwrap_or_else(|| ambient.map(PathBuf::from))
        .filter(|p| !p.as_os_str().is_empty())
}

/// The exact borrowed endpoints about to enter AArch64 certificate generation.
/// Config is the public compiler configuration, not all ambient/compiler state.
pub(crate) struct PreparedModule<'a> {
    pub module: &'a trust_ir::Module,
    pub lir: &'a [(trust_cg_lower::Function, trust_cg_lower::ProofContext)],
    pub machine: &'a [trust_cg_ir::MachFunction],
    pub metrics: &'a [PreparationMetrics],
    pub config: &'a CompilerConfig,
    pub target: &'a TargetSpec,
}

pub(crate) fn observe(view: PreparedModule<'_>) {
    let Some(directory) = resolve(DIRECTORY.get(), trust_cg_process_env::var_os(ENV)) else {
        return;
    };
    if let Err(error) = write(&directory, view) {
        eprintln!("trust-cg: could not dump prepared AArch64 diagnostics: {error}");
    }
}

fn write(directory: &Path, view: PreparedModule<'_>) -> std::io::Result<PathBuf> {
    if view.lir.len() != view.machine.len() || view.metrics.len() != view.machine.len() {
        return Err(std::io::Error::other("preparation endpoint counts differ"));
    }
    if view
        .lir
        .iter()
        .zip(view.machine)
        .any(|((lir, _), machine)| lir.name != machine.name)
    {
        return Err(std::io::Error::other(
            "preparation function identities differ",
        ));
    }
    let source = trust_ir::binary::serialize_module(view.module).map_err(std::io::Error::other)?;
    std::fs::create_dir_all(directory)?;
    let nonce = format!(
        "{}-{}",
        std::process::id(),
        NEXT.fetch_add(1, Ordering::Relaxed)
    );
    let pending = directory.join(format!(".pending-{nonce}"));
    let complete = directory.join(format!("capture-{nonce}"));
    if complete.exists() {
        return Err(std::io::Error::other(
            "diagnostic destination already exists",
        ));
    }
    std::fs::create_dir(&pending)?;
    let result = (|| {
        std::fs::write(pending.join("source.trust_irbin"), &source)?;
        let mut functions = Vec::new();
        for (ordinal, (((lir, proof_context), machine), metrics)) in view
            .lir
            .iter()
            .zip(view.machine)
            .zip(view.metrics)
            .enumerate()
        {
            // Numeric file names: source/callee names never become path components.
            let prefix = format!("function-{ordinal}");
            let lir_text = format!("{lir:#?}");
            let machine_text = format!("{machine:#?}");
            let mut lir_identity = String::new();
            lir.write_canonical_verifier_identity(&mut lir_identity)
                .map_err(std::io::Error::other)?;
            // Match the verifier's machine rendering, including the IEEE
            // payload bits ordinary Debug spells only as `NaN`.
            let mut machine_identity = format!("{machine:#?}\n");
            for (i, instruction) in machine.insts.iter().enumerate() {
                for (j, operand) in instruction.operands.iter().enumerate() {
                    if let trust_cg_ir::MachOperand::FImm(value) = operand {
                        writeln!(machine_identity, "{i}:{j}:{:016x}", value.to_bits())
                            .map_err(std::io::Error::other)?;
                    }
                }
            }
            let proof_context_text = format!("{proof_context:#?}");
            let frame_text = format!("{:#?}", metrics.frame_layout);
            for (suffix, text) in [
                ("lir.txt", &lir_text),
                ("machine.txt", &machine_text),
                ("lir-identity.txt", &lir_identity),
                ("machine-identity.txt", &machine_identity),
                ("proof-context.txt", &proof_context_text),
                ("frame.txt", &frame_text),
            ] {
                std::fs::write(pending.join(format!("{prefix}.{suffix}")), text)?;
            }
            functions.push(serde_json::json!({
                "ordinal": ordinal,
                "name": machine.name,
                "prefix": prefix,
                "lir_sha256": sha256_hex(lir_text.as_bytes()),
                "machine_sha256": sha256_hex(machine_text.as_bytes()),
                "lir_identity_sha256": sha256_hex(lir_identity.as_bytes()),
                "machine_identity_sha256": sha256_hex(machine_identity.as_bytes()),
                "proof_context_sha256": sha256_hex(proof_context_text.as_bytes()),
                "frame_sha256": sha256_hex(frame_text.as_bytes()),
            }));
        }
        let manifest = serde_json::json!({
            "schema": "trust-cg.aarch64-prepared-dump.v1",
            "stage": "prepared-before-certificate-generation",
            "module": view.module.name,
            "source_sha256": sha256_hex(&source),
            "compiler_config_debug": format!("{:#?}", view.config),
            "target_debug": format!("{:#?}", view.target),
            "proofs_requested": view.config.emit_proofs,
            "proof_or_encoding_authority": false,
            "functions": functions,
        });
        let bytes = serde_json::to_vec_pretty(&manifest).map_err(std::io::Error::other)?;
        std::fs::write(pending.join("snapshot.json"), bytes)?;
        // Readers only consume completed directories after all payloads exist.
        std::fs::rename(&pending, &complete)?;
        Ok(complete)
    })();
    if result.is_err() {
        // This directory was created by this invocation, never a user's existing tree.
        let _ = std::fs::remove_dir_all(&pending);
    }
    result
}

#[cfg(test)]
#[path = "aarch64_prepared_dump_tests.rs"]
mod tests;
