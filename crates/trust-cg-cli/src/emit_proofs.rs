// trust-cg-cli/emit_proofs.rs - Per-proof SMT-LIB2 + certificate emission (#421)
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// Implements the `--emit-proofs=<dir>` CLI flag. Verified static rules and
// retained source-bound obligations produce two proof files:
//
//   - `.smt2`  : complete SMT-LIB2 query (via `trust_cg_verify::serialize_to_smt2`)
//   - `.cert`  : minimal JSON metadata capturing
//                `{ result, solver, timestamp, hash, proof_name, category,
//                   covered_span }`
//
// Functions with supported lowering obligations also produce sidecars
// for tRust trust-proof-cert consumers:
//
//   - `<function>.lowering.json`          : Trust Codegen lowering certificate
//   - `<function>.trust-proof-cert.json`  : trust-proof-cert v2 JSON
//
// Downstream consumers: `ty`, `tRust` (issues #260, #269, #570).
//
// Covered span (WS7.2, F-111): every `.cert`, `lowering.json` and
// `trust-proof-cert.json` carries `"covered_span": "lir->machine"`. Each rule
// relates a LIR instruction to its machine code; the trust-ir -> LIR adapter
// is outside every certificate written here, so none of them is a trust-ir ->
// machine claim (that obligation is WS7.16).
//
// Design notes:
// * Static obligations are looked up in ProofDatabase. A source-bound payload
//   (AArch64 ALU/constants on Arithmetic rows, raw AArch64 bodies on their
//   owner-selected Arithmetic/Comparison rows, the frameless AArch64
//   whole-body theorem on each credited row under that row's role category,
//   or x86-64 bodies on X8664Lowering rows) carries the exact immutable theorem
//   retained by the verifier after source, body, proof and provenance checks.
//   Its complete query identifies filenames and deduplication; a rule name
//   alone does not identify actual operands.
// * Frame-bearing and source-bound sidecars re-check every included query
//   against the replay authority before publication: the exact query bytes
//   must hold a Clean-checked AY proof under the admitted solver identity and
//   the currently resolved checker. In the process that compiled them, a
//   query the compile already replayed is served from that process's session
//   memo (keyed by solver identity and the exact query), so this binds the
//   exported bytes to a checked verdict; it is not a second AY + Clean run.
//   Retained metadata cannot grant authority.
// * Verified structural, relocation-inventory, and reconstructed records have
//   no static obligation by design. They produce audit-only `.cert` files with
//   the legacy `result: "eval-only"` tag and no SMT or lowering sidecar. The
//   record's strength remains explicit; serialization cannot upgrade evidence.
// * Filenames are sanitized and checked for collisions and protected-path
//   aliases before publication. Multiple inputs use separate proof directories.

use std::collections::{HashMap, HashSet};
use std::fs;
use std::io;
use std::path::{Path, PathBuf};
use std::time::{SystemTime, UNIX_EPOCH};

use trust_cg_codegen::compiler::ProofCertificate as CodegenCertificate;
use trust_cg_codegen::proof_evidence::CALL_ONLY_BODY_CATEGORY;
use trust_cg_verify::proof_certificate::{
    CoveredSpan, generate_formal_lowering_certificate, generate_lowering_certificate,
};
use trust_cg_verify::source_bound_frame::FRAME_OBLIGATION_NAME;
use trust_cg_verify::{CategorizedProof, ProofDatabase, serialize_to_smt2};

#[cfg(test)]
#[path = "emit_proofs_alu_tests.rs"]
mod arithmetic_tests;

#[cfg(test)]
#[path = "emit_proofs_comparison_tests.rs"]
mod comparison_tests;

#[cfg(test)]
#[path = "emit_proofs_select_tests.rs"]
mod select_tests;

#[cfg(test)]
#[path = "emit_proofs_x86_tests.rs"]
mod x86_body_tests;

#[cfg(test)]
#[path = "emit_proofs_a64_body_tests.rs"]
mod a64_body_tests;

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
    /// Source, profile, object, and auxiliary output paths this emission may
    /// not overwrite, including their symlink and hard-link aliases.
    pub protected_paths: &'a [PathBuf],
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
    if out == "." || out == ".." {
        out = out.replace('.', "_");
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

/// Dynamic source-bound evidence carries its original theorem, not a lookup by display
/// name. Validate the immutable payload against the public report before any
/// audit-only categorization or publication can discard it.
fn resolve_obligation<'a>(
    cert: &'a CodegenCertificate,
    index: &HashMap<String, (usize, &'static str)>,
    all: &'a [CategorizedProof],
) -> io::Result<Option<&'a trust_cg_verify::ProofObligation>> {
    if let Some(bound) = &cert.source_bound_obligation {
        // Each sealed owner's payload retains its exact proof category. A
        // report string cannot select a category, including for a raw A64
        // comparison body whose live copy rows share the comparison theorem.
        match bound.kind() {
            trust_cg_verify::SourceBoundObligationKind::A64Alu
            | trust_cg_verify::SourceBoundObligationKind::A64Constant
            | trust_cg_verify::SourceBoundObligationKind::A64Body
            | trust_cg_verify::SourceBoundObligationKind::X86Body => {}
            // The ABI envelope is a JIT-only, function-level theorem over
            // final bytes. No AOT route emits it, and this emitter has no
            // category or file layout for it, so it refuses rather than
            // guessing one.
            trust_cg_verify::SourceBoundObligationKind::X86Envelope => {
                return Err(invalid_data(format!(
                    "source-bound x86-64 ABI envelope export for `{}` in `{}` is JIT-only; the \
                     AOT proof emitter does not accept it",
                    cert.rule_name, cert.function_name
                )));
            }
        }
        if !cert.verified
            || cert.strength != "Formal"
            || cert.category != bound.proof_category().to_string()
            || cert.function_name != bound.function_name()
            || cert.rule_name != bound.obligation().name
            || index.contains_key(&cert.rule_name)
        {
            return Err(invalid_data(format!(
                "source-bound {:?} export payload does not match proof `{}` in function `{}`",
                bound.kind(),
                cert.rule_name,
                cert.function_name
            )));
        }
        return Ok(Some(bound.obligation()));
    }
    Ok(index
        .get(&cert.rule_name)
        .map(|(idx, _)| &all[*idx].obligation))
}

fn rule_file_stem(cert: &CodegenCertificate) -> String {
    let stem = sanitize_path(&cert.rule_name);
    match &cert.source_bound_obligation {
        Some(bound) => format!("{stem}--{}", bound.query_sha256()),
        None => stem,
    }
}

/// Each per-rule file of a certificate: its stem and the obligation its
/// `.smt2` holds (none for an eval-only record). Slice 16: an x86-64 body
/// theorem stated in parts publishes its parts, one file each (stem: the
/// part's name and query digest), and only once its part inventory checks
/// against the statement; the statement itself is never published. Slice 19
/// (OD-197): a theorem or part credited claim by claim publishes its claims
/// in its place, once they check as its claim split. Slice 23 (OD-205): a
/// paired theorem is published only once its pairing record re-derives its
/// pairing and its statement.
fn rule_files<'a>(
    cert: &'a CodegenCertificate,
    index: &HashMap<String, (usize, &'static str)>,
    all: &'a [CategorizedProof],
) -> io::Result<Vec<(String, Option<&'a trust_cg_verify::ProofObligation>)>> {
    let obligation = resolve_obligation(cert, index, all)?;
    let Some(parts) = cert.source_bound_obligation.as_ref().filter(|bound| {
        bound.x86_body_parts().is_some()
            || bound.x86_body_claims().is_some()
            || bound.is_x86_body_paired()
    }) else {
        return Ok(vec![(rule_file_stem(cert), obligation)]);
    };
    let replayed = parts.replayed_obligations().map_err(|why| {
        invalid_data(format!(
            "source-bound x86-64 body theorem `{}` in function `{}` is stated in parts, claims \
             or a pairing whose record does not check: {why}",
            cert.rule_name, cert.function_name
        ))
    })?;
    Ok(replayed
        .into_iter()
        .map(|part| {
            let digest = format!(
                "{:x}",
                <sha2::Sha256 as sha2::Digest>::digest(serialize_to_smt2(part).as_bytes())
            );
            (
                format!("{}--{digest}", sanitize_path(&part.name)),
                Some(part),
            )
        })
        .collect())
}

/// Return the category's canonical variant name (e.g. "Arithmetic") for
/// use as a directory name. The explicit table avoids allocation and keeps
/// directory names independent of the category's human-readable label.
fn category_dir_name(cp: &CategorizedProof) -> &'static str {
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

/// The `--link` sidecar (WS7.9): `<dir>/linked_dependencies.json`, every
/// import row of the compiled module that `trust_ir_build::validate_linked_module`
/// authenticated against a supplied dependency module.
///
/// The digest authenticates the dependency MODULE, not an object file; the
/// sidecar exists so a link step (or a human) can bind each object it links to
/// the module it was compiled from. Nothing here claims that binding.
pub fn write_linked_dependencies(
    out_dir: &Path,
    rows: &[trust_cg_codegen::LinkedDependency],
    protected_paths: &[PathBuf],
) -> io::Result<PathBuf> {
    let path = out_dir.join("linked_dependencies.json");
    let refusals =
        super::output_alias_refusals(&[("--emit-proofs", path.as_path())], protected_paths);
    if !refusals.is_empty() {
        return Err(invalid_data(refusals.join("\n")));
    }
    let linked_dependencies: Vec<_> = rows
        .iter()
        .map(|dependency| {
            serde_json::json!({
                "import": dependency.import.index(),
                "name": dependency.row.name,
                "digest": dependency.row.digest.to_string(),
                "scheme": format!("{:?}", dependency.row.scheme),
                "producer": dependency.row.producer.as_ref().map(|producer| format!("{producer:?}")),
            })
        })
        .collect();
    let mut body = serde_json::to_vec_pretty(&serde_json::json!({
        "schema": "trust-cg.linked_dependencies.v1",
        "authenticates": "dependency trust_ir module (stable digest), not an object file",
        "linked_dependencies": linked_dependencies,
    }))
    .map_err(io::Error::other)?;
    body.push(b'\n');
    fs::create_dir_all(out_dir)?;
    fs::write(&path, body)?;
    Ok(path)
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

    let mut body = serde_json::to_vec_pretty(&serde_json::json!({
        "result": result_tag,
        "solver": solver,
        "timestamp": timestamp,
        "hash": smt2_hash,
        "proof_name": cert.rule_name,
        "category": cert.category,
        "function": cert.function_name,
        "strength": cert.strength,
        "verified": cert.verified,
        // WS7.2: the rule relates LIR to machine code; the trust-ir -> LIR
        // adapter is outside every certificate trust-cg writes.
        "covered_span": CoveredSpan::LirToMachine.as_str(),
    }))
    .map_err(io::Error::other)?;
    body.push(b'\n');
    fs::write(path, body)
}

/// Emit per-rule proof files plus function-level lowering/trust sidecars.
///
/// Every codegen certificate must be verified. Records included in a function's
/// lowering sidecar must resolve to a static or verifier-retained obligation
/// with a typed `check_kind`. The named audit-only categories have no such obligation
/// and are retained only as per-rule `.cert` records.
pub fn emit_proof_files_with_lowering_sidecars(
    out_dir: &Path,
    certs: &[CodegenCertificate],
    sidecar: LoweringSidecarInputs<'_>,
) -> io::Result<EmitSummary> {
    if certs.is_empty() {
        return Ok(EmitSummary::default());
    }

    let db = ProofDatabase::new();
    let index = build_obligation_index(&db);
    let all = db.all();

    // Validate every certificate and destination before publishing any files.
    let sidecars = build_lowering_sidecars(out_dir, certs, sidecar, &index, all)?;
    let mut rule_paths = std::collections::BTreeSet::new();
    for cert in certs {
        let category = index
            .get(&cert.rule_name)
            .map_or(cert.category.as_str(), |(_, category)| *category);
        let directory = out_dir.join(sanitize_path(category));
        for (stem, obligation) in rule_files(cert, &index, all)? {
            rule_paths.insert(directory.join(format!("{stem}.cert")));
            if obligation.is_some() {
                rule_paths.insert(directory.join(format!("{stem}.smt2")));
            }
        }
    }
    let destinations: Vec<_> = rule_paths
        .iter()
        .chain(
            sidecars
                .iter()
                .flat_map(|sidecar| [&sidecar.lowering_path, &sidecar.trust_path]),
        )
        .map(|path| ("--emit-proofs", path.as_path()))
        .collect();
    let refusals = super::output_alias_refusals(&destinations, sidecar.protected_paths);
    if !refusals.is_empty() {
        return Err(invalid_data(refusals.join("\n")));
    }
    let mut summary = emit_per_rule_proof_files(out_dir, certs, &index, all)?;
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
    let mut paths = HashMap::new();
    for cert in certs {
        let category = index
            .get(&cert.rule_name)
            .map_or(cert.category.as_str(), |(_, category)| *category);
        for (stem, _) in rule_files(cert, index, all)? {
            let path = out_dir.join(sanitize_path(category)).join(stem);
            if let Some(previous) = paths.insert(path, &cert.rule_name)
                && previous != &cert.rule_name
            {
                return Err(invalid_data(format!(
                    "proof names `{previous}` and `{}` resolve to the same output path",
                    cert.rule_name
                )));
            }
        }
    }

    for cert in certs {
        let category_dir = match index.get(&cert.rule_name) {
            Some((_, cat)) => sanitize_path(cat),
            None => {
                // No obligation in the database — fall back to the string
                // category from the codegen certificate so we still
                // organise the file correctly.
                sanitize_path(&cert.category)
            }
        };

        for (file_stem, obligation) in rule_files(cert, index, all)? {
            let key = (category_dir.clone(), file_stem.clone());
            if !seen.insert(key) {
                continue;
            }

            let dir = out_dir.join(&category_dir);
            fs::create_dir_all(&dir)?;

            let smt2_path: PathBuf = dir.join(format!("{}.smt2", file_stem));
            let cert_path: PathBuf = dir.join(format!("{}.cert", file_stem));

            let (smt2_hash, result_tag) = match obligation {
                Some(obligation) => {
                    let smt2 = serialize_to_smt2(obligation);
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

            if obligation.is_none() {
                summary.skipped_no_obligation += 1;
            }
        }
    }

    Ok(summary)
}

/// A FRAME RECORD (L07-P2) is credited by the frame theorem AND a
/// Clean-checked certificate of every memory-effect part of its word, bound to
/// the theorem's record. When a function's group carries the frame theorem,
/// append the parts of both records (save, then restore; the frame owner
/// admits one spelling of each, so they are exactly the parts its credit
/// replayed) so that the formal sidecar replays everything that credit needed,
/// not the theorem alone. Returns whether the group carries the frame theorem.
fn with_frame_record_parts(obligations: &mut Vec<trust_cg_verify::ProofObligation>) -> bool {
    if !obligations
        .iter()
        .any(|obligation| obligation.name == FRAME_OBLIGATION_NAME)
    {
        return false;
    }
    for part in trust_cg_verify::aarch64_memory_source_binding::frame_record_part_obligations() {
        if !obligations.contains(&part) {
            obligations.push(part);
        }
    }
    true
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
    let mut seen_rules_by_function: HashMap<String, HashSet<trust_cg_verify::ProofObligation>> =
        HashMap::new();
    let mut formal_functions = HashSet::new();
    let mut function_paths = HashMap::new();

    for cert in certs {
        let resolved = resolve_obligation(cert, index, all)?;
        if cert.source_bound_obligation.is_some() {
            formal_functions.insert(cert.function_name.clone());
        }
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

        // The x86-64 CALL-ONLY-BODY structural certificate (every verifier row a
        // trap skip or a by-design unverified control transfer, AND a LIR source
        // that is a bare diverging transfer; LIMITATIONS.md, x86-64) has NO
        // ProofDatabase obligation BY DESIGN: it states that the function has no
        // value-semantics row to discharge, so there is no SMT theorem to put in
        // a lowering sidecar. It is emitted as an `eval-only` per-rule `.cert`
        // audit file by `emit_per_rule_proof_files` (an unverified one is already
        // rejected above), and the function gets no lowering sidecar unless
        // another certificate of its supplies one.
        if cert.category == CALL_ONLY_BODY_CATEGORY {
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

        // A SOURCE-BOUND MEMORY ACCESS (L07-P2) is credited by the live,
        // Clean-checked replay of every part of its word's memory-effect
        // decomposition, bound to its source access by the memory-leaf
        // checker. Those parts are several obligations per row and travel in
        // no export payload yet, so a formal sidecar cannot carry this row:
        // refuse the function by name rather than emit a partial record.
        if cert.rule_name.starts_with(
            trust_cg_verify::aarch64_memory_source_binding::SOURCE_BOUND_MEMORY_PROOF_PREFIX,
        ) {
            return Err(invalid_data(format!(
                "cannot emit lowering sidecar for function `{}`: `{}` is credited by live, \
                 Clean-checked replays of its memory-effect parts, which no sidecar export \
                 carries yet",
                cert.function_name, cert.rule_name
            )));
        }

        if resolved.is_none() {
            return Err(invalid_data(format!(
                "cannot emit lowering sidecar for function `{}`: proof `{}` has no ProofDatabase obligation",
                cert.function_name, cert.rule_name
            )));
        }
        // Slice 16: a theorem stated in parts replays its parts (the
        // inventory checked against the statement), never the statement.
        let replayed: Vec<&trust_cg_verify::ProofObligation> = rule_files(cert, index, all)?
            .into_iter()
            .filter_map(|(_, obligation)| obligation)
            .collect();
        for obligation in &replayed {
            if obligation.category.is_none() {
                return Err(invalid_data(format!(
                    "cannot emit lowering sidecar for function `{}`: proof `{}` has no check_kind",
                    cert.function_name, cert.rule_name
                )));
            }
        }

        let seen_rules = seen_rules_by_function
            .entry(cert.function_name.clone())
            .or_default();
        let fresh: Vec<trust_cg_verify::ProofObligation> = replayed
            .into_iter()
            .filter(|obligation| seen_rules.insert((*obligation).clone()))
            .cloned()
            .collect();
        if fresh.is_empty() {
            continue;
        }

        let group_idx = match group_indices.get(&cert.function_name) {
            Some(idx) => *idx,
            None => {
                let file_stem = sanitize_path(&cert.function_name);
                if let Some(previous) = function_paths.insert(file_stem, &cert.function_name) {
                    return Err(invalid_data(format!(
                        "function names `{previous}` and `{}` resolve to the same lowering sidecar path",
                        cert.function_name
                    )));
                }
                let idx = groups.len();
                group_indices.insert(cert.function_name.clone(), idx);
                groups.push((cert.function_name.clone(), Vec::new()));
                idx
            }
        };
        groups[group_idx].1.extend(fresh);
    }

    let mut sidecars = Vec::with_capacity(groups.len());
    for (function, mut obligations) in groups {
        let framed = with_frame_record_parts(&mut obligations);
        // The frame theorem quantifies arbitrary memory. Replaying the whole
        // group preserves that requirement in the exported sidecar; neither
        // sampling nor a codegen report's positive label can replace it.
        let generate = if formal_functions.contains(&function) || framed {
            generate_formal_lowering_certificate
        } else {
            generate_lowering_certificate
        };
        let lowering = generate(
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

    /// This module's fixtures are hand-built and carry no codegen license
    /// (`body_gate: None`), which trust-cg REFUSES by default (roadmap WS7.5,
    /// decision gate DG-73). Its compiles state `Permit` explicitly, so none
    /// of them passes (or is refused) because it was silently refused.
    fn permit_unlicensed() -> trust_cg_codegen::CodegenLicensePolicy {
        trust_cg_codegen::CodegenLicensePolicy::default()
            .with_unlicensed(trust_cg_codegen::UnlicensedBodyPolicy::Permit)
    }

    fn codegen_cert(rule_name: &str, category: &str, verified: bool) -> CodegenCertificate {
        CodegenCertificate {
            ay_refusal_note: None,
            source_bound_obligation: None,
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

    /// A source-bound memory access is credited by live part replays that no
    /// export carries: the formal sidecar refuses its function by name and
    /// writes nothing, rather than certify the rest of the function.
    #[test]
    fn lowering_sidecar_refuses_a_source_bound_memory_access_by_name() {
        let rule_name = format!(
            "{}: LdrRI 0xf9400001 bound to source access 0, LIR instruction lir0.0",
            trust_cg_verify::aarch64_memory_source_binding::SOURCE_BOUND_MEMORY_PROOF_PREFIX
        );
        let mut cert = codegen_cert(&rule_name, "Memory", true);
        cert.strength = "Formal".into();
        let directory = tempfile::tempdir().unwrap();
        let err =
            emit_proof_files_with_lowering_sidecars(directory.path(), &[cert], sidecar_inputs())
                .expect_err("a source-bound memory row has no sidecar export");
        assert_eq!(err.kind(), io::ErrorKind::InvalidData);
        assert!(
            err.to_string()
                .contains("Clean-checked replays of its memory-effect parts, which no sidecar"),
            "{err}"
        );
        assert!(
            !directory
                .path()
                .join("_generated_frame_spill.lowering.json")
                .exists()
        );
    }

    /// A group that carries the frame theorem gains the twelve frame-record
    /// parts, once each and in order, so the formal sidecar replays every
    /// obligation the frame records' credit needed; any other group is
    /// unchanged.
    #[test]
    fn a_framed_sidecar_group_carries_the_frame_record_parts() {
        use trust_cg_verify::aarch64_memory_source_binding::frame_record_part_obligations;
        use trust_cg_verify::source_bound_frame::frame_obligation;
        let parts = frame_record_part_obligations();
        assert_eq!(parts.len(), 12, "six parts per record");
        assert!(
            parts[..6].iter().all(|part| part
                .name
                .starts_with("A64 memory effect StpPreIndex 0xa9bf7bfd"))
                && parts[6..].iter().all(|part| part
                    .name
                    .starts_with("A64 memory effect LdpPostIndex 0xa8c17bfd")),
            "{:?}",
            parts.iter().map(|part| &part.name).collect::<Vec<_>>()
        );
        let mut group = vec![frame_obligation()];
        assert!(with_frame_record_parts(&mut group));
        assert_eq!(group[0], frame_obligation());
        assert_eq!(group[1..], parts[..]);
        assert!(with_frame_record_parts(&mut group));
        assert_eq!(group.len(), 13, "appended once");
        let mut unframed = parts[..1].to_vec();
        assert!(!with_frame_record_parts(&mut unframed));
        assert_eq!(unframed.len(), 1);
    }

    fn sidecar_inputs() -> LoweringSidecarInputs<'static> {
        LoweringSidecarInputs {
            target: "aarch64",
            trust_ir_bytes: b"trust_ir",
            machine_code_bytes: b"machine",
            compiler_config_bytes: b"config",
            protected_paths: &[],
        }
    }

    /// The x86-64 `call_only_body` certificate has no ProofDatabase obligation
    /// by design, so a bundle that carries it (with the covered-elsewhere
    /// entries the same body co-emits) must publish per-rule `.cert` audit files
    /// and no lowering sidecar, instead of failing at the "has no ProofDatabase
    /// obligation" boundary; a forged UNVERIFIED copy is still refused before
    /// any file is written.
    #[test]
    fn call_only_body_certificate_emits_audit_file_without_sidecar() {
        let mut call_only = codegen_cert(CALL_ONLY_BODY_CATEGORY, CALL_ONLY_BODY_CATEGORY, true);
        call_only.strength = "no value-semantics row: 1 control transfer(s) [Call] left \
                              unverified by design (CFG edge and relocation covered elsewhere) \
                              and 1 trap(s) [Ud2] skipped; the LIR source is a bare diverging \
                              transfer ([Call, Trap]); no instruction theorem was discharged"
            .to_string();
        call_only.function_name = "panic_const_add_overflow".to_string();
        let mut covered =
            codegen_cert("covered_elsewhere_instruction_0", "covered_elsewhere", true);
        covered.strength = "x86_64::Call: direct call/branch".to_string();
        covered.function_name = call_only.function_name.clone();
        let certs = [call_only.clone(), covered];

        let directory = tempfile::tempdir().unwrap();
        let summary = emit_proof_files_with_lowering_sidecars(
            directory.path(),
            &certs,
            LoweringSidecarInputs {
                target: "x86_64-unknown-linux-gnu",
                ..sidecar_inputs()
            },
        )
        .expect("a call-only body must be publishable");
        assert_eq!(summary.cert_written, 2);
        assert_eq!(summary.smt2_written, 0);
        assert_eq!(summary.skipped_no_obligation, 2);
        assert_eq!(summary.lowering_written, 0);
        assert_eq!(summary.trust_proof_cert_written, 0);
        let audit = directory
            .path()
            .join(CALL_ONLY_BODY_CATEGORY)
            .join(format!("{CALL_ONLY_BODY_CATEGORY}.cert"));
        let body: serde_json::Value =
            serde_json::from_str(&fs::read_to_string(&audit).unwrap()).unwrap();
        assert_eq!(body["result"], "eval-only");
        assert_eq!(body["category"], CALL_ONLY_BODY_CATEGORY);
        assert_eq!(body["verified"], true);
        assert!(
            !directory
                .path()
                .join("panic_const_add_overflow.lowering.json")
                .exists(),
            "a structural certificate must not mint a lowering sidecar"
        );

        let mut forged = call_only;
        forged.verified = false;
        let refused = tempfile::tempdir().unwrap();
        let err = emit_proof_files_with_lowering_sidecars(
            refused.path(),
            &[forged],
            LoweringSidecarInputs {
                target: "x86_64-unknown-linux-gnu",
                ..sidecar_inputs()
            },
        )
        .unwrap_err();
        assert!(err.to_string().contains("unverified"), "{err}");
        assert_eq!(fs::read_dir(refused.path()).unwrap().count(), 0);
    }

    /// The real x86-64 AOT certificate bundle for a module whose functions are a
    /// trap-only body, a `call; unreachable` panic helper in both its one-block
    /// and its O0 two-block shape, and an empty callee — the population the
    /// census measured under `[TCG-PROOF-465]` — publishes through
    /// `--emit-proofs`: the bundle carries `call_only_body` for the three
    /// diverging bodies, and the sidecar builder accepts it.
    ///
    /// A `call f; ret` WRAPPER is the negative control in the same test. Its
    /// emitted rows are indistinguishable from the exempt ones, but it returns
    /// to its caller, so nothing here says what the callee received: the whole
    /// module must be REFUSED at the promotion boundary, and the refusal must
    /// name the function and the source half of the gate.
    #[test]
    fn x86_64_call_only_bodies_publish_through_emit_proofs() {
        use trust_cg_codegen::compiler::{Compiler, CompilerConfig};
        use trust_cg_codegen::pipeline::{OptLevel, encode_tmbc};
        use trust_cg_codegen::target::TargetSpec;
        use trust_ir::FuncId;
        use trust_ir_build::ModuleBuilder;

        let build = |with_wrapper: bool| -> trust_ir::Module {
            let mut mb = ModuleBuilder::new("call_only_bodies_export");
            let void_ty = mb.add_func_type(vec![], vec![]);
            {
                let mut fb = mb.function("callee", void_ty);
                let entry = fb.create_block();
                fb.switch_to_block(entry);
                fb.ret(vec![]);
                fb.build();
            }
            {
                let mut fb = mb.function("trap_only", void_ty);
                let entry = fb.create_block();
                fb.switch_to_block(entry);
                fb.unreachable();
                fb.build();
            }
            {
                let mut fb = mb.function("call_then_trap", void_ty);
                let entry = fb.create_block();
                fb.switch_to_block(entry);
                fb.call_void(FuncId::new(0), vec![]);
                fb.unreachable();
                fb.build();
            }
            {
                let mut fb = mb.function("jump_then_call_then_trap", void_ty);
                let entry = fb.create_block();
                let panic_block = fb.create_block();
                fb.switch_to_block(entry);
                fb.br(panic_block, vec![]);
                fb.switch_to_block(panic_block);
                fb.call_void(FuncId::new(0), vec![]);
                fb.unreachable();
                fb.build();
            }
            if with_wrapper {
                let mut fb = mb.function("call_then_ret", void_ty);
                let entry = fb.create_block();
                fb.switch_to_block(entry);
                fb.call_void(FuncId::new(0), vec![]);
                fb.ret(vec![]);
                fb.build();
            }
            mb.build().expect("ModuleBuilder::build: test fixture")
        };
        let compiler = || {
            Compiler::new_for_target_spec(
                CompilerConfig {
                    opt_level: OptLevel::O0,
                    emit_proofs: true,
                    parallel: false,
                    ..Default::default()
                },
                TargetSpec::parse("x86_64-unknown-linux-gnu").unwrap(),
            )
            .with_codegen_license(permit_unlicensed())
        };

        // NEGATIVE CONTROL first: the wrapper must block the whole module.
        let refused = compiler()
            .compile(&build(true))
            .expect_err("a call-then-RETURN body must not promote on a structural exemption");
        let text = format!("{refused:?}");
        assert!(
            text.contains("non_vacuous_function_evidence")
                && text.contains("call_then_ret")
                && text.contains("not a bare diverging transfer"),
            "the refusal must name the function and the source half: {text}"
        );

        let module = build(false);
        let bytes = encode_tmbc(&module).unwrap();
        let result = compiler()
            .compile(&module)
            .expect("call-only bodies compile with proofs on");
        let certs = result.proofs.expect("proofs requested");
        let call_only: Vec<_> = certs
            .iter()
            .filter(|c| c.category == CALL_ONLY_BODY_CATEGORY)
            .map(|c| c.function_name.as_str())
            .collect();
        assert_eq!(
            call_only,
            ["trap_only", "call_then_trap", "jump_then_call_then_trap"],
            "{certs:?}"
        );
        assert!(certs.iter().all(|c| c.verified), "{certs:?}");

        let directory = tempfile::tempdir().unwrap();
        let out = directory.path().join("proofs");
        let summary = emit_proof_files_with_lowering_sidecars(
            &out,
            &certs,
            LoweringSidecarInputs {
                target: "x86_64-unknown-linux-gnu",
                trust_ir_bytes: &bytes,
                machine_code_bytes: &result.object_code,
                compiler_config_bytes: b"call-only-export-test/O0",
                protected_paths: &[],
            },
        )
        .expect("the real call-only bundle must publish");
        assert!(summary.cert_written >= 3, "{summary:?}");
        assert!(
            out.join(CALL_ONLY_BODY_CATEGORY)
                .join(format!("{CALL_ONLY_BODY_CATEGORY}.cert"))
                .exists()
        );
        for function in ["trap_only", "call_then_trap", "jump_then_call_then_trap"] {
            assert!(
                !out.join(format!("{function}.lowering.json")).exists(),
                "{function}: a call-only body has no lowering theorem to export"
            );
        }
    }

    #[test]
    fn sanitize_path_handles_special_chars() {
        assert_eq!(sanitize_path("foo_bar"), "foo_bar");
        assert_eq!(sanitize_path("Floating-Point"), "Floating-Point");
        assert_eq!(sanitize_path("a/b"), "a_b");
        assert_eq!(sanitize_path(""), "unknown");
        assert_eq!(sanitize_path("."), "_");
        assert_eq!(sanitize_path(".."), "__");
    }

    #[test]
    fn colliding_function_sidecars_are_rejected_before_any_files_are_written() {
        let directory = tempfile::tempdir().unwrap();
        let mut certs = generated_frame_spill_certs();
        certs.truncate(1);
        certs[0].function_name = "a/b".into();
        let mut collision = certs[0].clone();
        collision.function_name = "a_b".into();
        certs.push(collision);
        let error =
            emit_proof_files_with_lowering_sidecars(directory.path(), &certs, sidecar_inputs())
                .unwrap_err();
        assert!(error.to_string().contains("same lowering sidecar path"));
        assert_eq!(fs::read_dir(directory.path()).unwrap().count(), 0);
    }

    #[test]
    fn invalid_certificates_do_not_publish_per_rule_audit_files() {
        let directory = tempfile::tempdir().unwrap();
        let cert = codegen_cert("missing proof", "..", false);
        let error =
            emit_proof_files_with_lowering_sidecars(directory.path(), &[cert], sidecar_inputs())
                .unwrap_err();
        assert!(error.to_string().contains("unverified"));
        assert_eq!(fs::read_dir(directory.path()).unwrap().count(), 0);
    }

    #[test]
    fn proof_destinations_cannot_overwrite_protected_artifacts() {
        let directory = tempfile::tempdir().unwrap();
        let destination = directory
            .path()
            .join("_generated_frame_spill.lowering.json");
        fs::write(&destination, b"protected input or object bytes").unwrap();
        let protected = [destination.clone()];
        let error = emit_proof_files_with_lowering_sidecars(
            directory.path(),
            &generated_frame_spill_certs(),
            LoweringSidecarInputs {
                protected_paths: &protected,
                ..sidecar_inputs()
            },
        )
        .unwrap_err();
        assert!(error.to_string().contains("--emit-proofs"));
        assert_eq!(
            fs::read(&destination).unwrap(),
            b"protected input or object bytes"
        );
        assert_eq!(fs::read_dir(directory.path()).unwrap().count(), 1);
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
        let s = emit_proof_files_with_lowering_sidecars(
            &tmp,
            &[],
            LoweringSidecarInputs {
                target: "x86_64-unknown-linux-gnu",
                trust_ir_bytes: &[],
                machine_code_bytes: &[],
                compiler_config_bytes: &[],
                protected_paths: &[],
            },
        )
        .expect("empty ok");
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

    /// LA-11 leaves AOT export of the AArch64 scalar-cell caller theorem as
    /// remaining work (L09-P11): a row it credits carries no export payload,
    /// so the AOT route refuses the function at the authoritative database
    /// boundary, by the theorem's name, in every role category it reports.
    #[test]
    fn lowering_sidecar_refuses_a_scalar_cell_caller_row() {
        for category in [
            trust_cg_verify::proof_database::ProofCategory::FrameLayout,
            trust_cg_verify::proof_database::ProofCategory::CallLowering,
            trust_cg_verify::proof_database::ProofCategory::ConstantMaterialization,
            trust_cg_verify::proof_database::ProofCategory::Branch,
        ] {
            let tmp = std::env::temp_dir().join(format!(
                "trust_cg_cli_emit_proofs_scalar_cell_caller_{}_{}",
                std::process::id(),
                sanitize_path(&category.to_string())
            ));
            let _ = fs::remove_dir_all(&tmp);
            let mut cert = codegen_cert(
                trust_cg_verify::source_bound_frame::SCALAR_CELL_CALLER_OBLIGATION_NAME,
                &category.to_string(),
                true,
            );
            cert.strength = "Formal".to_string();
            let err = emit_proof_files_with_lowering_sidecars(&tmp, &[cert], sidecar_inputs())
                .expect_err("a scalar-cell caller row has no export payload");
            assert_eq!(err.kind(), io::ErrorKind::InvalidData);
            assert!(
                err.to_string().contains("has no ProofDatabase obligation")
                    && err.to_string().contains(
                        trust_cg_verify::source_bound_frame::SCALAR_CELL_CALLER_OBLIGATION_NAME
                    ),
                "{err}"
            );
            assert!(!tmp.join("_generated_frame_spill.lowering.json").exists());
            let _ = fs::remove_dir_all(&tmp);
        }
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
            ay_refusal_note: None,
            source_bound_obligation: None,
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
