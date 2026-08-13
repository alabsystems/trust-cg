// trust-cg-cli/emit_proofs.rs - Per-proof SMT-LIB2 + certificate emission (#421)
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// Implements the `--emit-proofs=<dir>` CLI flag introduced in issue #421
// (epic #407, task 6). For every verified lowering rule produced by the
// compiler we write two files to `<dir>/<ProofCategory>/<proof_name>`:
//
//   - `.smt2`  : complete SMT-LIB2 query (via `trust_cg_verify::serialize_to_smt2`)
//   - `.cert`  : minimal JSON metadata capturing
//                `{ result, solver, timestamp, hash, proof_name, category }`
//
// The CLI also exposes function-level lowering sidecars for tRust
// trust-proof-cert consumers:
//
//   - `<function>.lowering.json`          : Trust Codegen lowering certificate
//   - `<function>.trust-proof-cert.json`  : trust-proof-cert v2 JSON
//
// Downstream consumers: `ty`, `tRust` (issues #260, #269, #570).
//
// Design notes:
// * Certificates produced by the codegen pipeline (see
//   `trust_cg_codegen::compiler::ProofCertificate`) only carry `rule_name`,
//   `verified`, `category` (String), `strength` (String) and `function_name`
//   fields. To produce real SMT-LIB2 text we need the underlying
//   `ProofObligation` — we reconstruct the mapping by loading the full
//   `ProofDatabase` once and looking up obligations by name.
// * Rules that are verified by codegen but absent from the database (should
//   be rare) are still logged via a `.cert` file with `result: "eval-only"`
//   and no `.smt2`, keeping the audit trail complete.
// * All filenames are sanitized so category variants with spaces or slashes
//   (e.g. "Floating-Point") produce filesystem-safe directory names.

use std::collections::{HashMap, HashSet};
use std::fs;
use std::io;
use std::path::{Path, PathBuf};
use std::time::{SystemTime, UNIX_EPOCH};

use trust_cg_codegen::compiler::ProofCertificate as CodegenCertificate;
use trust_cg_verify::proof_certificate::generate_lowering_certificate;
use trust_cg_verify::{CategorizedProof, ProofDatabase, serialize_to_smt2};

/// Summary of how many proof files were written.
#[derive(Debug, Default, Clone, Copy)]
pub struct EmitSummary {
    pub smt2_written: usize,
    pub cert_written: usize,
    pub lowering_written: usize,
    pub trust_proof_cert_written: usize,
    pub skipped_no_obligation: usize,
}

impl EmitSummary {
    pub fn merge(&mut self, other: EmitSummary) {
        self.smt2_written += other.smt2_written;
        self.cert_written += other.cert_written;
        self.lowering_written += other.lowering_written;
        self.trust_proof_cert_written += other.trust_proof_cert_written;
        self.skipped_no_obligation += other.skipped_no_obligation;
    }
}

/// Stable input bytes needed to build function-level lowering sidecars.
#[derive(Debug, Clone, Copy)]
pub struct LoweringSidecarInputs<'a> {
    pub target: &'a str,
    pub trust_ir_bytes: &'a [u8],
    pub machine_code_bytes: &'a [u8],
    pub compiler_config_bytes: &'a [u8],
}

/// Sanitize a string for use as a filesystem path segment.
fn sanitize_path(s: &str) -> String {
    let mut out = String::with_capacity(s.len());
    for c in s.chars() {
        match c {
            c if c.is_ascii_alphanumeric() => out.push(c),
            '_' | '-' | '.' => out.push(c),
            _ => out.push('_'),
        }
    }
    if out.is_empty() {
        out.push_str("unknown");
    }
    out
}

/// Escape a string for JSON string output.
fn escape_json(s: &str) -> String {
    let mut out = String::with_capacity(s.len());
    for c in s.chars() {
        match c {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            c if (c as u32) < 0x20 => {
                out.push_str(&format!("\\u{:04x}", c as u32));
            }
            c => out.push(c),
        }
    }
    out
}

/// Compute a stable 64-bit FNV-1a hash of a byte slice.
///
/// Chosen over `DefaultHasher` for determinism across Rust versions — the
/// hash lands in the `.cert` JSON and is used downstream for cache
/// invalidation (see `ty` / `tRust` integration).
fn fnv1a_64(bytes: &[u8]) -> u64 {
    let mut h: u64 = 0xcbf2_9ce4_8422_2325;
    for b in bytes {
        h ^= *b as u64;
        h = h.wrapping_mul(0x100_0000_01b3);
    }
    h
}

/// Build a lookup table from proof name to `(ProofObligation, category name)`.
fn build_obligation_index(db: &ProofDatabase) -> HashMap<String, (usize, &'static str)> {
    let mut map = HashMap::with_capacity(db.len());
    for (idx, cp) in db.all().iter().enumerate() {
        let cat_name = category_dir_name(cp);
        map.insert(cp.obligation.name.clone(), (idx, cat_name));
    }
    map
}

/// Return the category's canonical variant name (e.g. "Arithmetic") for
/// use as a directory name. We use `{:?}` so the directory mirrors the
/// Rust enum variant exactly (no spaces, stable across releases).
fn category_dir_name(cp: &CategorizedProof) -> &'static str {
    // `format!("{:?}", cp.category)` would work but allocates — instead we
    // match against `ProofCategory::name()` at leaf level. For simplicity,
    // we leak the debug repr of the variant via a static dispatch table.
    match cp.category {
        trust_cg_verify::ProofCategory::Arithmetic => "Arithmetic",
        trust_cg_verify::ProofCategory::Division => "Division",
        trust_cg_verify::ProofCategory::FloatingPoint => "FloatingPoint",
        trust_cg_verify::ProofCategory::Comparison => "Comparison",
        trust_cg_verify::ProofCategory::Branch => "Branch",
        trust_cg_verify::ProofCategory::Peephole => "Peephole",
        trust_cg_verify::ProofCategory::Optimization => "Optimization",
        trust_cg_verify::ProofCategory::ConstantFolding => "ConstantFolding",
        trust_cg_verify::ProofCategory::CseLicm => "CseLicm",
        trust_cg_verify::ProofCategory::CfgSimplification => "CfgSimplification",
        trust_cg_verify::ProofCategory::Memory => "Memory",
        trust_cg_verify::ProofCategory::LoadStoreLowering => "LoadStoreLowering",
        trust_cg_verify::ProofCategory::SwitchLowering => "SwitchLowering",
        trust_cg_verify::ProofCategory::NeonLowering => "NeonLowering",
        trust_cg_verify::ProofCategory::NeonEncoding => "NeonEncoding",
        trust_cg_verify::ProofCategory::Vectorization => "Vectorization",
        trust_cg_verify::ProofCategory::RegAlloc => "RegAlloc",
        trust_cg_verify::ProofCategory::BitwiseShift => "BitwiseShift",
        trust_cg_verify::ProofCategory::ConstantMaterialization => "ConstantMaterialization",
        trust_cg_verify::ProofCategory::AddressMode => "AddressMode",
        trust_cg_verify::ProofCategory::FrameLayout => "FrameLayout",
        trust_cg_verify::ProofCategory::InstructionScheduling => "InstructionScheduling",
        trust_cg_verify::ProofCategory::MachOEmission => "MachOEmission",
        trust_cg_verify::ProofCategory::LoopOptimization => "LoopOptimization",
        trust_cg_verify::ProofCategory::StrengthReduction => "StrengthReduction",
        trust_cg_verify::ProofCategory::CmpCombine => "CmpCombine",
        trust_cg_verify::ProofCategory::Gvn => "Gvn",
        trust_cg_verify::ProofCategory::IfConversion => "IfConversion",
        trust_cg_verify::ProofCategory::FpConversion => "FpConversion",
        trust_cg_verify::ProofCategory::ExtensionTruncation => "ExtensionTruncation",
        trust_cg_verify::ProofCategory::AtomicOperations => "AtomicOperations",
        trust_cg_verify::ProofCategory::CallLowering => "CallLowering",
        trust_cg_verify::ProofCategory::X8664Lowering => "X8664Lowering",
        trust_cg_verify::ProofCategory::RiscVLowering => "RiscVLowering",
        trust_cg_verify::ProofCategory::WasmLowering => "WasmLowering",
    }
}

/// Write one `.cert` JSON file for a codegen certificate.
fn write_cert_file(
    path: &Path,
    cert: &CodegenCertificate,
    smt2_hash: Option<u64>,
    result_tag: &str,
) -> std::io::Result<()> {
    let timestamp = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .map(|d| d.as_secs())
        .unwrap_or(0);

    let solver = if cert.strength.contains("Statistical") {
        "mock_statistical"
    } else if cert.strength.contains("Exhaustive") {
        "mock_exhaustive"
    } else if cert.strength.contains("Formal") {
        "ay"
    } else {
        "unknown"
    };

    let hash_str = match smt2_hash {
        Some(h) => format!("{}", h),
        None => "null".to_string(),
    };

    let body = format!(
        "{{\n  \"result\": \"{}\",\n  \"solver\": \"{}\",\n  \"timestamp\": {},\n  \"hash\": {},\n  \"proof_name\": \"{}\",\n  \"category\": \"{}\",\n  \"function\": \"{}\",\n  \"strength\": \"{}\",\n  \"verified\": {}\n}}\n",
        escape_json(result_tag),
        solver,
        timestamp,
        hash_str,
        escape_json(&cert.rule_name),
        escape_json(&cert.category),
        escape_json(&cert.function_name),
        escape_json(&cert.strength),
        cert.verified,
    );
    fs::write(path, body)
}

/// Emit `.smt2` and `.cert` files for every certificate in `certs` under
/// `<out_dir>/<Category>/<rule_name>.{smt2,cert}`.
///
/// Returns a summary count. Errors creating directories or writing files
/// are propagated to the caller.
#[allow(dead_code)]
pub fn emit_proof_files(
    out_dir: &Path,
    certs: &[CodegenCertificate],
) -> std::io::Result<EmitSummary> {
    if certs.is_empty() {
        return Ok(EmitSummary::default());
    }

    fs::create_dir_all(out_dir)?;

    // Build the obligation index once per invocation; ProofDatabase::new()
    // is pure construction and not cached, so we avoid rebuilding it per
    // certificate (several thousand entries).
    let db = ProofDatabase::new();
    let index = build_obligation_index(&db);
    let all = db.all();

    emit_per_rule_proof_files(out_dir, certs, &index, all)
}

/// Emit per-rule proof files plus function-level lowering/trust sidecars.
///
/// The sidecar path is intentionally fail-closed: every included codegen
/// certificate must be verified, must resolve to a `ProofDatabase` obligation,
/// and that obligation must carry a typed `check_kind`.
pub fn emit_proof_files_with_lowering_sidecars(
    out_dir: &Path,
    certs: &[CodegenCertificate],
    sidecar: LoweringSidecarInputs<'_>,
) -> io::Result<EmitSummary> {
    if certs.is_empty() {
        return Ok(EmitSummary::default());
    }

    fs::create_dir_all(out_dir)?;

    let db = ProofDatabase::new();
    let index = build_obligation_index(&db);
    let all = db.all();

    let mut summary = emit_per_rule_proof_files(out_dir, certs, &index, all)?;
    let sidecars = build_lowering_sidecars(out_dir, certs, sidecar, &index, all)?;
    for sidecar in sidecars {
        fs::write(&sidecar.lowering_path, sidecar.lowering_json)?;
        summary.lowering_written += 1;
        fs::write(&sidecar.trust_path, sidecar.trust_json)?;
        summary.trust_proof_cert_written += 1;
    }

    Ok(summary)
}

fn emit_per_rule_proof_files(
    out_dir: &Path,
    certs: &[CodegenCertificate],
    index: &HashMap<String, (usize, &'static str)>,
    all: &[CategorizedProof],
) -> io::Result<EmitSummary> {
    let mut summary = EmitSummary::default();
    // Dedup on (category_dir, rule_name) so duplicate certs (same rule
    // applied in multiple functions) do not thrash the filesystem.
    let mut seen: HashSet<(String, String)> = HashSet::new();

    for cert in certs {
        let (category_dir, obligation_idx) = match index.get(&cert.rule_name) {
            Some((idx, cat)) => (sanitize_path(cat), Some(*idx)),
            None => {
                // No obligation in the database — fall back to the string
                // category from the codegen certificate so we still
                // organise the file correctly.
                (sanitize_path(&cert.category), None)
            }
        };

        let file_stem = sanitize_path(&cert.rule_name);
        let key = (category_dir.clone(), file_stem.clone());
        if !seen.insert(key) {
            continue;
        }

        let dir = out_dir.join(&category_dir);
        fs::create_dir_all(&dir)?;

        let smt2_path: PathBuf = dir.join(format!("{}.smt2", file_stem));
        let cert_path: PathBuf = dir.join(format!("{}.cert", file_stem));

        let (smt2_hash, result_tag) = match obligation_idx {
            Some(idx) => {
                let smt2 = serialize_to_smt2(&all[idx].obligation);
                let hash = fnv1a_64(smt2.as_bytes());
                fs::write(&smt2_path, &smt2)?;
                summary.smt2_written += 1;
                let tag = if cert.verified { "verified" } else { "failed" };
                (Some(hash), tag)
            }
            None => {
                // No SMT available — record an eval-only certificate so
                // auditors can see the rule was attempted even without
                // a matching obligation in the database.
                (None, "eval-only")
            }
        };

        write_cert_file(&cert_path, cert, smt2_hash, result_tag)?;
        summary.cert_written += 1;

        if obligation_idx.is_none() {
            summary.skipped_no_obligation += 1;
        }
    }

    Ok(summary)
}

struct LoweringSidecar {
    lowering_path: PathBuf,
    lowering_json: String,
    trust_path: PathBuf,
    trust_json: String,
}

fn build_lowering_sidecars(
    out_dir: &Path,
    certs: &[CodegenCertificate],
    sidecar: LoweringSidecarInputs<'_>,
    index: &HashMap<String, (usize, &'static str)>,
    all: &[CategorizedProof],
) -> io::Result<Vec<LoweringSidecar>> {
    let mut groups: Vec<(String, Vec<trust_cg_verify::ProofObligation>)> = Vec::new();
    let mut group_indices: HashMap<String, usize> = HashMap::new();
    let mut seen_rules_by_function: HashMap<String, HashSet<String>> = HashMap::new();

    for cert in certs {
        if !cert.verified {
            return Err(invalid_data(format!(
                "cannot emit lowering sidecar for unverified codegen proof `{}` in function `{}`",
                cert.rule_name, cert.function_name
            )));
        }

        // Object-level relocation-inventory certificates are not per-function
        // instruction-lowering rules: they certify linker-visible object
        // metadata for a whole module/object, carry the object name (not an
        // trust_ir function) in `function_name`, and have no SMT obligation in
        // the ProofDatabase by design. They are still emitted as per-rule
        // `.cert` audit files by `emit_per_rule_proof_files`, but they must not
        // participate in the function-level lowering sidecars. (An unverified
        // inventory is already rejected above and by the compiler's object
        // proof-promotion gate, so this skip only drops genuinely-verified
        // object metadata certs.)
        if cert.category == "relocation_inventory" {
            continue;
        }

        // Covered-elsewhere structural certificates (indirect/direct branch & call
        // targets, register copy, RET, conditional select, const materialization —
        // see `function_verifier::is_covered_elsewhere_indirect_branch`) have NO
        // ProofDatabase obligation BY DESIGN: their correctness is the surrounding
        // structural argument, not a per-instruction SMT equivalence. (#62 retracted
        // the degenerate X==X proofs that used to back some of these.) They are
        // emitted as positive `.cert` audit files by `emit_per_rule_proof_files`,
        // but must not participate in the function-level SMT lowering sidecars.
        if cert.category == "covered_elsewhere" {
            continue;
        }

        // OPERAND-RECONSTRUCTED certificates (#63/#66) are GENUINE coverage whose
        // obligation is rebuilt on-the-fly from the REAL emitted opcode+operands,
        // so it is NOT a static ProofDatabase entry. They are recorded as positive
        // per-rule `.cert` audit files but, like covered-elsewhere certs, have no
        // static DB obligation to drive an SMT lowering sidecar.
        if cert.rule_name.starts_with("RECONSTRUCTED ") {
            continue;
        }

        let (obligation_idx, _) = index.get(&cert.rule_name).ok_or_else(|| {
            invalid_data(format!(
                "cannot emit lowering sidecar for function `{}`: proof `{}` has no ProofDatabase obligation",
                cert.function_name, cert.rule_name
            ))
        })?;
        let obligation = &all[*obligation_idx].obligation;
        if obligation.category.is_none() {
            return Err(invalid_data(format!(
                "cannot emit lowering sidecar for function `{}`: proof `{}` has no check_kind",
                cert.function_name, cert.rule_name
            )));
        }

        let seen_rules = seen_rules_by_function
            .entry(cert.function_name.clone())
            .or_default();
        if !seen_rules.insert(cert.rule_name.clone()) {
            continue;
        }

        let group_idx = match group_indices.get(&cert.function_name) {
            Some(idx) => *idx,
            None => {
                let idx = groups.len();
                group_indices.insert(cert.function_name.clone(), idx);
                groups.push((cert.function_name.clone(), Vec::new()));
                idx
            }
        };
        groups[group_idx].1.push(obligation.clone());
    }

    let mut sidecars = Vec::with_capacity(groups.len());
    for (function, obligations) in groups {
        let lowering = generate_lowering_certificate(
            &function,
            sidecar.target,
            sidecar.trust_ir_bytes,
            sidecar.machine_code_bytes,
            sidecar.compiler_config_bytes,
            &obligations,
        )
        .map_err(|e| {
            invalid_data(format!(
                "failed to generate lowering certificate for function `{}`: {}",
                function, e
            ))
        })?;

        let lowering_json = lowering.to_json().map_err(|e| {
            invalid_data(format!(
                "failed to serialize lowering certificate for function `{}`: {}",
                function, e
            ))
        })?;
        let trust_json = lowering.to_trust_proof_cert_json().map_err(|e| {
            invalid_data(format!(
                "failed to serialize trust-proof-cert sidecar for function `{}`: {}",
                function, e
            ))
        })?;

        let file_stem = sanitize_path(&function);
        sidecars.push(LoweringSidecar {
            lowering_path: out_dir.join(format!("{}.lowering.json", file_stem)),
            lowering_json,
            trust_path: out_dir.join(format!("{}.trust-proof-cert.json", file_stem)),
            trust_json,
        });
    }

    Ok(sidecars)
}

fn invalid_data(message: String) -> io::Error {
    io::Error::new(io::ErrorKind::InvalidData, message)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn codegen_cert(rule_name: &str, category: &str, verified: bool) -> CodegenCertificate {
        CodegenCertificate {
            rule_name: rule_name.to_string(),
            verified,
            category: category.to_string(),
            strength: "Statistical".to_string(),
            function_name: "_generated_frame_spill".to_string(),
        }
    }

    fn generated_frame_spill_certs() -> Vec<CodegenCertificate> {
        vec![
            codegen_cert(
                "FrameLayout: large negative offset materialization (SUB base, abs_offset)",
                "FrameLayout",
                true,
            ),
            codegen_cert(
                "FrameLayout: FP/SP-relative addressing equivalence",
                "FrameLayout",
                true,
            ),
            codegen_cert(
                "FrameLayout: distinct slots have non-overlapping memory",
                "FrameLayout",
                true,
            ),
            codegen_cert(
                "RegAlloc Phase2: spill/reload semantic roundtrip",
                "RegAlloc",
                true,
            ),
            codegen_cert(
                "RegAlloc Phase2: spill offset non-interference",
                "RegAlloc",
                true,
            ),
        ]
    }

    #[test]
    fn lowering_sidecar_rejects_retracted_degenerate_frame_proofs() {
        for rule_name in [
            "FrameLayout: large offset materialization (ADD base, offset)",
            "FrameLayout: emergency spill slot address via X16",
        ] {
            let tmp = std::env::temp_dir().join(format!(
                "trust_cg_cli_emit_proofs_retracted_frame_{}_{}",
                std::process::id(),
                sanitize_path(rule_name)
            ));
            let _ = fs::remove_dir_all(&tmp);

            let cert = codegen_cert(rule_name, "FrameLayout", true);
            let err = emit_proof_files_with_lowering_sidecars(&tmp, &[cert], sidecar_inputs())
                .expect_err("retracted degenerate proof must not mint a certified sidecar");

            assert_eq!(err.kind(), io::ErrorKind::InvalidData);
            assert!(
                err.to_string().contains("has no ProofDatabase obligation"),
                "retracted proof must fail at the authoritative database boundary: {err}"
            );
            assert!(!tmp.join("_generated_frame_spill.lowering.json").exists());
            assert!(
                !tmp.join("_generated_frame_spill.trust-proof-cert.json")
                    .exists()
            );
            let _ = fs::remove_dir_all(&tmp);
        }
    }

    fn sidecar_inputs() -> LoweringSidecarInputs<'static> {
        LoweringSidecarInputs {
            target: "aarch64",
            trust_ir_bytes: b"trust_ir",
            machine_code_bytes: b"machine",
            compiler_config_bytes: b"config",
        }
    }

    #[test]
    fn sanitize_path_handles_special_chars() {
        assert_eq!(sanitize_path("foo_bar"), "foo_bar");
        assert_eq!(sanitize_path("Floating-Point"), "Floating-Point");
        assert_eq!(sanitize_path("a/b"), "a_b");
        assert_eq!(sanitize_path(""), "unknown");
    }

    #[test]
    fn fnv1a_is_stable() {
        // Known FNV-1a-64 value for the empty string.
        assert_eq!(fnv1a_64(b""), 0xcbf2_9ce4_8422_2325);
        // Deterministic across calls.
        assert_eq!(fnv1a_64(b"hello"), fnv1a_64(b"hello"));
        assert_ne!(fnv1a_64(b"hello"), fnv1a_64(b"world"));
    }

    #[test]
    fn empty_certs_produces_no_files() {
        let tmp = std::env::temp_dir().join(format!(
            "trust_cg_cli_emit_proofs_empty_{}",
            std::process::id()
        ));
        let _ = fs::remove_dir_all(&tmp);
        let s = emit_proof_files(&tmp, &[]).expect("empty ok");
        assert_eq!(s.smt2_written, 0);
        assert_eq!(s.cert_written, 0);
        let _ = fs::remove_dir_all(&tmp);
    }

    #[test]
    fn lowering_sidecar_includes_generated_frame_spill_check_kinds() {
        let tmp = std::env::temp_dir().join(format!(
            "trust_cg_cli_emit_proofs_frame_spill_{}",
            std::process::id()
        ));
        let _ = fs::remove_dir_all(&tmp);

        let certs = generated_frame_spill_certs();
        let summary = emit_proof_files_with_lowering_sidecars(&tmp, &certs, sidecar_inputs())
            .expect("generated frame/spill proofs should emit certified sidecars");
        assert_eq!(summary.lowering_written, 1);
        assert_eq!(summary.trust_proof_cert_written, 1);
        assert_eq!(summary.smt2_written, certs.len());
        assert_eq!(summary.cert_written, certs.len());
        assert_eq!(summary.skipped_no_obligation, 0);

        let lowering_path = tmp.join("_generated_frame_spill.lowering.json");
        let lowering_json = fs::read_to_string(&lowering_path).expect("read lowering sidecar");
        let lowering: serde_json::Value =
            serde_json::from_str(&lowering_json).expect("parse lowering sidecar JSON");
        assert_eq!(lowering["schema"], "trust-cg.lowering_certificate.v1");
        assert_eq!(lowering["function"], "_generated_frame_spill");
        assert_eq!(lowering["target"], "aarch64");
        assert_eq!(lowering["result"], "verified");

        let rule_proofs = lowering["rule_proofs"]
            .as_array()
            .expect("lowering rule_proofs should be an array");
        assert_eq!(rule_proofs.len(), certs.len());

        for cert in &certs {
            let proof = rule_proofs
                .iter()
                .find(|proof| proof["rule_name"] == cert.rule_name)
                .unwrap_or_else(|| {
                    panic!(
                        "missing generated frame/spill proof `{}` in sidecar:\n{}",
                        cert.rule_name, lowering_json
                    )
                });
            assert_eq!(
                proof["check_kind"], "regalloc",
                "generated frame/spill proof should carry a populated check_kind: {proof:?}"
            );
            assert_eq!(proof["result"]["status"], "proved");
        }

        let trust_path = tmp.join("_generated_frame_spill.trust-proof-cert.json");
        let trust_json = fs::read_to_string(&trust_path).expect("read trust-proof-cert sidecar");
        let trust: serde_json::Value =
            serde_json::from_str(&trust_json).expect("parse trust-proof-cert JSON");
        assert_eq!(trust["status"], "Trusted");
        let steps = trust["chain"]["steps"]
            .as_array()
            .expect("trust-proof-cert chain steps should be an array");
        assert!(
            steps
                .iter()
                .any(|step| step["step_type"] == "CodegenLowering"),
            "generated frame/spill trust sidecar should include CodegenLowering: {trust_json}"
        );

        let _ = fs::remove_dir_all(&tmp);
    }

    #[test]
    fn lowering_sidecar_io_error_does_not_publish_trust_sidecar() {
        let tmp = std::env::temp_dir().join(format!(
            "trust_cg_cli_emit_proofs_sidecar_io_{}",
            std::process::id()
        ));
        let _ = fs::remove_dir_all(&tmp);
        fs::create_dir_all(&tmp).expect("create proof output directory");

        let lowering_path = tmp.join("_generated_frame_spill.lowering.json");
        fs::create_dir(&lowering_path).expect("create conflicting lowering-sidecar directory");

        let certs = generated_frame_spill_certs();
        emit_proof_files_with_lowering_sidecars(&tmp, &certs, sidecar_inputs())
            .expect_err("a lowering-sidecar write error must fail closed");

        assert!(
            lowering_path.is_dir(),
            "conflicting path must stay a directory"
        );
        assert!(
            !tmp.join("_generated_frame_spill.trust-proof-cert.json")
                .exists(),
            "trust sidecar must not be published after lowering-sidecar I/O failure"
        );

        let _ = fs::remove_dir_all(&tmp);
    }

    #[test]
    fn lowering_sidecar_rejects_missing_generated_frame_spill_proof() {
        let tmp = std::env::temp_dir().join(format!(
            "trust_cg_cli_emit_proofs_missing_frame_spill_{}",
            std::process::id()
        ));
        let _ = fs::remove_dir_all(&tmp);

        let cert = codegen_cert(
            "FrameLayout: generated frame slot proof missing from ProofDatabase",
            "FrameLayout",
            true,
        );
        let err = emit_proof_files_with_lowering_sidecars(&tmp, &[cert], sidecar_inputs())
            .expect_err("missing generated frame proof must fail closed");

        assert_eq!(err.kind(), io::ErrorKind::InvalidData);
        assert!(
            err.to_string().contains("has no ProofDatabase obligation"),
            "missing generated proof error should name the ProofDatabase gap: {err}"
        );
        assert!(
            !tmp.join("_generated_frame_spill.lowering.json").exists(),
            "lowering sidecar must not be written when a generated proof is missing"
        );
        assert!(
            !tmp.join("_generated_frame_spill.trust-proof-cert.json")
                .exists(),
            "trust-proof-cert sidecar must not be written when a generated proof is missing"
        );
        let _ = fs::remove_dir_all(&tmp);
    }

    #[test]
    fn lowering_sidecar_rejects_unverified_generated_spill_proof() {
        let tmp = std::env::temp_dir().join(format!(
            "trust_cg_cli_emit_proofs_unverified_spill_{}",
            std::process::id()
        ));
        let _ = fs::remove_dir_all(&tmp);

        let cert = codegen_cert(
            "RegAlloc Phase2: spill offset non-interference",
            "RegAlloc",
            false,
        );
        let err = emit_proof_files_with_lowering_sidecars(&tmp, &[cert], sidecar_inputs())
            .expect_err("unverified generated spill proof must fail closed");

        assert_eq!(err.kind(), io::ErrorKind::InvalidData);
        assert!(
            err.to_string()
                .contains("cannot emit lowering sidecar for unverified codegen proof"),
            "unverified generated spill proof error should be explicit: {err}"
        );
        assert!(
            !tmp.join("_generated_frame_spill.lowering.json").exists(),
            "lowering sidecar must not be written for an unverified generated spill proof"
        );
        assert!(
            !tmp.join("_generated_frame_spill.trust-proof-cert.json")
                .exists(),
            "trust-proof-cert sidecar must not be written for an unverified generated spill proof"
        );
        let _ = fs::remove_dir_all(&tmp);
    }

    #[test]
    fn lowering_sidecar_rejects_unverified_codegen_cert() {
        let tmp = std::env::temp_dir().join(format!(
            "trust_cg_cli_emit_proofs_unverified_{}",
            std::process::id()
        ));
        let _ = fs::remove_dir_all(&tmp);

        let cert = CodegenCertificate {
            rule_name: "Iadd_I8 -> ADD (8-bit)".to_string(),
            verified: false,
            category: "Arithmetic".to_string(),
            strength: "Exhaustive".to_string(),
            function_name: "_unverified".to_string(),
        };
        let err = emit_proof_files_with_lowering_sidecars(&tmp, &[cert], sidecar_inputs())
            .expect_err("unverified codegen proof must fail closed");

        assert_eq!(err.kind(), io::ErrorKind::InvalidData);
        assert!(
            !tmp.join("_unverified.trust-proof-cert.json").exists(),
            "trust-proof-cert sidecar must not be written on failed certification"
        );
        let _ = fs::remove_dir_all(&tmp);
    }
}
