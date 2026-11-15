// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! Bounded test-only inspection of a fresh raw proof before query RAII cleanup.
//! This diagnostic rerun yields no replay receipt, promotion or cache entry.

use super::*;
use std::io::Read;

const MAX_QUERY_BYTES: usize = 1 << 20;
const MAX_PROOF_BYTES: usize = 16 << 20;
const MAX_TRANSCRIPT_BYTES: usize = 1 << 20;

#[derive(Debug, serde::Serialize)]
pub(crate) struct RawProofDiagnostic {
    /// Exact original independently checked problem, never the producer view.
    pub(crate) smt2: String,
    /// Exact actual solver input, retained independently from checker identity.
    pub(crate) producer_smt2: String,
    pub(crate) producer_compact: bool,
    pub(crate) argv: Vec<String>,
    pub(crate) stdout: String,
    pub(crate) stderr: String,
    /// False when the unchanged supervisor returned an error without transcripts.
    pub(crate) output_available: bool,
    pub(crate) solve_error: Option<String>,
    pub(crate) proof: Option<String>,
    pub(crate) proof_error: Option<String>,
    pub(crate) candidate_debug: String,
    pub(crate) checker_accepted: Option<bool>,
    pub(crate) checker_error: Option<String>,
    pub(crate) solver_path: String,
    pub(crate) solver_sha256: String,
    pub(crate) checker_path: Option<String>,
    pub(crate) checker_sha256: Option<String>,
    pub(crate) timeout_ms: u64,
}

/// An untrusted constructive candidate inspected against the original problem.
/// No solver is launched, and no certificate, cache entry or receipt is minted.
// Built only by the AArch64-macOS diagnostic tests' inspection.
#[cfg(all(target_arch = "aarch64", target_os = "macos"))]
#[derive(Debug, serde::Serialize)]
pub(crate) struct ClosedDefinitionProofDiagnostic {
    pub(crate) smt2: String,
    pub(crate) proof: Option<String>,
    pub(crate) compose_error: Option<String>,
    pub(crate) premises: usize,
    pub(crate) definitions: usize,
    pub(crate) steps: usize,
    pub(crate) checker_accepted: Option<bool>,
    pub(crate) checker_error: Option<String>,
    pub(crate) checker_path: Option<String>,
    pub(crate) checker_sha256: Option<String>,
    pub(crate) timeout_ms: u64,
}

enum TextCaptureError {
    Oversized,
    Unreadable(String),
}

fn read_capped_text(reader: impl Read, limit: usize) -> Result<String, TextCaptureError> {
    let bound = u64::try_from(limit)
        .ok()
        .and_then(|limit| limit.checked_add(1))
        .ok_or_else(|| TextCaptureError::Unreadable("invalid capture bound".into()))?;
    let mut bytes = Vec::new();
    reader
        .take(bound)
        .read_to_end(&mut bytes)
        .map_err(|error| TextCaptureError::Unreadable(error.to_string()))?;
    if bytes.len() > limit {
        return Err(TextCaptureError::Oversized);
    }
    String::from_utf8(bytes).map_err(|error| TextCaptureError::Unreadable(error.to_string()))
}

fn capture_text(reader: impl Read, limit: usize, name: &str) -> Result<String, String> {
    read_capped_text(reader, limit).map_err(|error| match error {
        TextCaptureError::Oversized => format!("raw diagnostic {name} exceeds {limit} bytes"),
        TextCaptureError::Unreadable(reason) => {
            format!("raw diagnostic {name} is unreadable: {reason}")
        }
    })
}

fn check_policy() -> Result<(), String> {
    if crate::verdict_db::recording_active() {
        return Err("raw diagnostic refused: the tier-0 recorder is armed".into());
    }
    if crate::env_lock::var_os("TCG_REFINE_SOLVER").is_some_and(|value| value == "0") {
        return Err("raw diagnostic refused: TCG_REFINE_SOLVER=0".into());
    }
    Ok(())
}

/// Preflight BOTH retained problem texts before selecting/cloning the actual
/// solver input. These are the existing per-query capture bounds, not a new
/// solver/process budget or an admission of another independently checked input.
fn check_query_texts(original: &str, producer: Option<&str>) -> Result<(), String> {
    if original.len() > MAX_QUERY_BYTES {
        return Err(format!(
            "raw diagnostic query exceeds {MAX_QUERY_BYTES} bytes"
        ));
    }
    if producer.is_some_and(|text| text.len() > MAX_QUERY_BYTES) {
        return Err(format!(
            "raw diagnostic producer query exceeds {MAX_QUERY_BYTES} bytes"
        ));
    }
    Ok(())
}

fn solve_failure(error: &SolverInvocationError) -> (String, String) {
    let candidate = match error {
        SolverInvocationError::Timeout(_) => format!("{:?}", AYResult::Timeout),
        SolverInvocationError::Io(reason) => format!("{:?}", AYResult::Error(reason.clone())),
    };
    (
        candidate,
        format!(
            "{error:?}; stdout/stderr unavailable: the unchanged process supervisor \
             returned no captured output for this failed invocation"
        ),
    )
}

impl FunctionAyAuthority {
    /// Compose an untrusted proof and inspect it using THIS request's captured
    /// checker, environment and unchanged deadline. This diagnostic lane never
    /// reports AY execution or converts acceptance to native/reuse authority.
    // Its only callers are the AArch64-macOS diagnostic tests.
    #[cfg(all(target_arch = "aarch64", target_os = "macos"))]
    pub(crate) fn inspect_source_bound_closed_definitions<O>(
        &self,
        owner: &O,
        config: &AYConfig,
    ) -> Result<ClosedDefinitionProofDiagnostic, String>
    where
        O: crate::source_bound_replay::SourceBoundReplay + ?Sized,
    {
        check_policy()?;
        let obligation = owner.replayed_obligation();
        let smt2 = generate_smt2_query_raw(obligation, config);
        check_query_texts(&smt2, None)?;
        let (proof, compose_error, premises, definitions, steps) =
            match crate::closed_definition_alethe::compose(obligation) {
                Ok(candidate) => (
                    Some(candidate.text),
                    None,
                    candidate.premises,
                    candidate.definitions,
                    candidate.steps,
                ),
                Err(error) => (None, Some(error.to_string()), 0, 0, 0),
            };
        let (checker_accepted, checker_error) = match proof.as_deref() {
            Some(proof) => self.inspect_source_bound_definition_proof(owner, config, proof)?,
            None => (None, None),
        };
        let authority = self.authority.as_ref().ok_or_else(|| {
            format!(
                "no captured definition-proof authority: {}",
                self.selection.detail()
            )
        })?;
        Ok(ClosedDefinitionProofDiagnostic {
            smt2,
            proof,
            compose_error,
            premises,
            definitions,
            steps,
            checker_accepted,
            checker_error,
            checker_path: authority
                .checker()
                .map(|checker| checker.path().to_string_lossy().into_owned()),
            checker_sha256: authority
                .checker()
                .map(|checker| checker.sha256().to_owned()),
            timeout_ms: config.timeout_ms,
        })
    }

    /// Reinspect candidate DATA against a sealed owner's complete original
    /// script. Used for changed-proof controls; no proof-positive promotion.
    // Its only callers are the AArch64-macOS diagnostic tests.
    #[cfg(all(target_arch = "aarch64", target_os = "macos"))]
    pub(crate) fn inspect_source_bound_definition_proof<O>(
        &self,
        owner: &O,
        config: &AYConfig,
        proof: &str,
    ) -> Result<(Option<bool>, Option<String>), String>
    where
        O: crate::source_bound_replay::SourceBoundReplay + ?Sized,
    {
        check_policy()?;
        let smt2 = generate_smt2_query_raw(owner.replayed_obligation(), config);
        check_query_texts(&smt2, None)?;
        if proof.len() > MAX_PROOF_BYTES {
            return Err(format!(
                "definition diagnostic proof exceeds {MAX_PROOF_BYTES} bytes"
            ));
        }
        let authority = self.authority.as_ref().ok_or_else(|| {
            format!(
                "no captured definition-proof authority: {}",
                self.selection.detail()
            )
        })?;
        let Some(checker) = authority.checker() else {
            return Ok((
                None,
                Some(format!(
                    "no captured checker: {:?}",
                    authority.checker_resolution_error()
                )),
            ));
        };
        match crate::obligation_cert_store::carcara_verify_with_expected_checker_with_env(
            checker.path(),
            checker.sha256(),
            &smt2,
            proof,
            authority.child_env(),
            config.timeout_ms,
        ) {
            Ok(accepted) => Ok((Some(accepted), None)),
            Err(error) => Ok((None, Some(error.to_string()))),
        }
    }

    /// Inspect a fresh diagnostic rerun under THIS captured authority. The caller
    /// must enter the original request's policy scope, reject its captured recorder
    /// state and derive the actual source-bound configuration in that scope.
    /// Same raw script and ordinary Alethe arguments; no debug option is added.
    /// The process supervisor's existing deadline/capture behavior is unchanged;
    /// these caps bound retained diagnostic text, not child process allocations.
    pub(crate) fn inspect_fresh_source_bound<O>(
        &self,
        owner: &O,
        config: &AYConfig,
    ) -> Result<super::RawProofDiagnostic, String>
    where
        O: crate::source_bound_replay::SourceBoundReplay + ?Sized,
    {
        check_policy()?;
        let obligation = owner.replayed_obligation();
        let smt2 = generate_smt2_query_raw(obligation, config);
        self.inspect_fresh_source_bound_texts(obligation, config, smt2, None)
    }

    /// Inspect the production-selected bounded producer print view (or its
    /// unchanged raw fallback) under THIS captured authority. The proof is
    /// independently checked ONLY against the original raw problem. Capturing
    /// SAT/unknown/missing proof is diagnostic, never promotion, receipt, cache
    /// authority, or another problem's model evidence.
    // Its only callers are the AArch64-macOS diagnostic tests.
    #[cfg(all(target_arch = "aarch64", target_os = "macos"))]
    pub(crate) fn inspect_fresh_source_bound_producer<O>(
        &self,
        owner: &O,
        config: &AYConfig,
    ) -> Result<RawProofDiagnostic, String>
    where
        O: crate::source_bound_replay::SourceBoundReplay + ?Sized,
    {
        check_policy()?;
        let obligation = owner.replayed_obligation();
        let (original, producer) = source_bound_query_scripts(obligation, config);
        self.inspect_fresh_source_bound_texts(obligation, config, original, producer)
    }

    /// Historical-form migration control only. Both solver and independent
    /// checker receive the SAME legacy query, under this capture and deadline.
    /// Never a producer substitute for a canonical query or proof admission.
    pub(crate) fn inspect_legacy_right_spine_for_test<O>(
        &self,
        owner: &O,
        config: &AYConfig,
    ) -> Result<RawProofDiagnostic, String>
    where
        O: crate::source_bound_replay::SourceBoundReplay + ?Sized,
    {
        check_policy()?;
        let obligation = owner.replayed_obligation();
        let legacy = super::legacy_right_spine_query_for_test(obligation, config);
        self.inspect_fresh_source_bound_texts(obligation, config, legacy, None)
    }

    fn inspect_fresh_source_bound_texts(
        &self,
        obligation: &ProofObligation,
        config: &AYConfig,
        smt2: String,
        producer: Option<String>,
    ) -> Result<RawProofDiagnostic, String> {
        let authority = self.authority.as_ref().ok_or_else(|| {
            format!(
                "no captured raw diagnostic authority: {}",
                self.selection.detail()
            )
        })?;
        check_query_texts(&smt2, producer.as_deref())?;
        let producer_compact = producer.is_some();
        let producer_smt2 = producer.unwrap_or_else(|| smt2.clone());
        let query = write_temp_smt2(&producer_smt2)
            .map_err(|error| format!("cannot write raw diagnostic query: {error}"))?;
        let solver_path = authority.solver_path().to_string_lossy().into_owned();
        let mut argv = vec![solver_path.clone()];
        argv.extend(
            solver_evidence_args(query.path(), &SolverEvidenceRequest::Alethe)
                .into_iter()
                .map(|argument| argument.to_string_lossy().into_owned()),
        );
        let (stdout, stderr, candidate_debug, solve_error, output_available) =
            match run_solver_command_with_authority(authority, query.path(), config.timeout_ms) {
                Ok(completed) => (
                    capture_text(&completed.output.stdout[..], MAX_TRANSCRIPT_BYTES, "stdout")?,
                    capture_text(&completed.output.stderr[..], MAX_TRANSCRIPT_BYTES, "stderr")?,
                    format!(
                        "{:?}",
                        parse_solver_process_output(&completed.output, &obligation.inputs)
                    ),
                    None,
                    true,
                ),
                Err(error) => {
                    let (candidate, reason) = solve_failure(&error);
                    let reason =
                        capture_text(reason.as_bytes(), MAX_TRANSCRIPT_BYTES, "solve error")?;
                    (String::new(), String::new(), candidate, Some(reason), false)
                }
            };
        let (proof, proof_error) = if solve_error.is_some() {
            // Even a partial file left by a terminated producer is not evidence
            // for this invocation. Retain the exact problem and error instead.
            (
                None,
                Some("proof not inspected: solver invocation failed".into()),
            )
        } else {
            match std::fs::File::open(default_alethe_path(query.path())) {
                Ok(file) => match read_capped_text(file, MAX_PROOF_BYTES) {
                    Ok(proof) => (Some(proof), None),
                    Err(TextCaptureError::Oversized) => {
                        return Err(format!(
                            "raw diagnostic proof exceeds {MAX_PROOF_BYTES} bytes"
                        ));
                    }
                    Err(TextCaptureError::Unreadable(reason)) => (None, Some(reason)),
                },
                Err(error) => (None, Some(error.to_string())),
            }
        };
        let (checker_accepted, checker_error) = match (authority.checker(), proof.as_deref()) {
            (Some(checker), Some(proof)) => {
                match crate::obligation_cert_store::carcara_verify_with_expected_checker_with_env(
                    checker.path(),
                    checker.sha256(),
                    &smt2,
                    proof,
                    authority.child_env(),
                    config.timeout_ms,
                ) {
                    Ok(accepted) => (Some(accepted), None),
                    Err(error) => (None, Some(error.to_string())),
                }
            }
            (None, _) => (
                None,
                Some(format!(
                    "no captured checker: {:?}",
                    authority.checker_resolution_error()
                )),
            ),
            (_, None) => (None, Some("no readable exact proof to inspect".into())),
        };
        Ok(RawProofDiagnostic {
            smt2,
            producer_smt2,
            producer_compact,
            argv,
            stdout,
            stderr,
            output_available,
            solve_error,
            proof,
            proof_error,
            candidate_debug,
            checker_accepted,
            checker_error,
            solver_path,
            solver_sha256: authority.solver().sha256().to_owned(),
            checker_path: authority
                .checker()
                .map(|checker| checker.path().to_string_lossy().into_owned()),
            checker_sha256: authority
                .checker()
                .map(|checker| checker.sha256().to_owned()),
            timeout_ms: config.timeout_ms,
        })
    }
}

#[test]
fn bounded_text_capture_accepts_exact_limit_and_refuses_excess_or_invalid_utf8() {
    assert_eq!(capture_text(&b"abcd"[..], 4, "test").unwrap(), "abcd");
    assert!(matches!(
        read_capped_text(&b"abcde"[..], 4),
        Err(TextCaptureError::Oversized)
    ));
    assert!(matches!(
        read_capped_text(&[0xff][..], 4),
        Err(TextCaptureError::Unreadable(_))
    ));
    assert_eq!(capture_text(&b""[..], 0, "test").unwrap(), "");
    assert!(matches!(
        read_capped_text(&b"x"[..], 0),
        Err(TextCaptureError::Oversized)
    ));
}

#[test]
fn diagnostic_policy_refuses_disabled_solver_without_a_process() {
    crate::env_lock::with_env_overrides(&[("TCG_REFINE_SOLVER", "0")], || {
        assert_eq!(
            check_policy().unwrap_err(),
            "raw diagnostic refused: TCG_REFINE_SOLVER=0"
        );
    });
}

#[test]
fn diagnostic_alethe_arguments_are_the_ordinary_unchanged_command_arguments() {
    let arguments = solver_evidence_args(Path::new("Q.smt2"), &SolverEvidenceRequest::Alethe);
    assert_eq!(
        arguments,
        [
            "-smt2",
            "Q.smt2",
            "--strict-proofs",
            "--proof",
            "Q.smt2.alethe",
            "--proof-format",
            "alethe"
        ]
        .map(std::ffi::OsString::from)
    );
}

#[test]
fn diagnostic_original_and_producer_texts_keep_the_same_capture_bounds() {
    let exact = "x".repeat(MAX_QUERY_BYTES);
    assert!(check_query_texts(&exact, None).is_ok());
    assert!(check_query_texts(&exact, Some(&exact)).is_ok());
    let excessive = "x".repeat(MAX_QUERY_BYTES + 1);
    assert_eq!(
        check_query_texts(&excessive, None).unwrap_err(),
        format!("raw diagnostic query exceeds {MAX_QUERY_BYTES} bytes")
    );
    assert_eq!(
        check_query_texts("original", Some(&excessive)).unwrap_err(),
        format!("raw diagnostic producer query exceeds {MAX_QUERY_BYTES} bytes")
    );
    assert!(check_query_texts("original", Some("producer")).is_ok());
}

#[test]
fn diagnostic_producer_preparation_keeps_the_original_problem_and_raw_fallback() {
    let config = AYConfig {
        solver: None,
        timeout_ms: 30_000,
        produce_models: true,
    };
    let mut shared = SmtExpr::var("diagnostic_shared_x", 64);
    for _ in 0..10 {
        shared = shared.clone().bvadd(shared);
    }
    let obligation = ProofObligation {
        name: "bounded diagnostic shared raw query".into(),
        trust_ir_expr: shared.clone(),
        aarch64_expr: shared.bvadd(SmtExpr::bv_const(1, 64)),
        inputs: vec![("diagnostic_shared_x".into(), 64)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: None,
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
    };
    let (original, producer) = source_bound_query_scripts(&obligation, &config);
    assert_eq!(original, generate_smt2_query_raw(&obligation, &config));
    let producer = producer.expect("large shared DAG has production compact print view");
    check_query_texts(&original, Some(&producer)).unwrap();
    assert_ne!(producer, original);
    assert!(producer.contains("(assert (let ("));
    assert_eq!(
        original.split_once("\n(assert ").unwrap().0,
        producer.split_once("\n(assert ").unwrap().0,
        "all original declarations/options stay untouched"
    );
    assert!(original.ends_with(")\n(check-sat)\n(exit)"));
    assert!(producer.ends_with(")\n(check-sat)\n(exit)"));

    let small = ProofObligation {
        trust_ir_expr: SmtExpr::bv_const(1, 64),
        aarch64_expr: SmtExpr::bv_const(2, 64),
        inputs: vec![],
        ..obligation
    };
    let (raw, producer) = source_bound_query_scripts(&small, &config);
    assert_eq!(raw, generate_smt2_query_raw(&small, &config));
    assert!(producer.is_none(), "ordinary small input retains raw route");
}

#[test]
fn diagnostic_deadline_and_io_refusals_are_not_missing_query_or_fake_output() {
    let expiry = crate::subprocess::DeadlineExpiry {
        limit: Duration::from_millis(30_000),
        cpu: Some(Duration::from_millis(17)),
    };
    let (candidate, reason) = solve_failure(&SolverInvocationError::Timeout(expiry));
    assert_eq!(candidate, "Timeout");
    assert!(reason.contains("Timeout"));
    assert!(reason.contains("stdout/stderr unavailable"));
    let (candidate, reason) = solve_failure(&SolverInvocationError::Io(
        "actual transport refusal".into(),
    ));
    assert_eq!(candidate, "Error(\"actual transport refusal\")");
    assert!(reason.contains("actual transport refusal"));
    assert!(reason.contains("no captured output"));
}

/// Primitive capability qualification, NOT original model/compiler admission.
/// The one captured checker receives each complete original component query;
/// no AY run, receipt, cache, source-owner or native authority is produced.
#[test]
fn definition_literal_components_independently_replay_and_reject_missing_refutations() {
    use crate::lowering_proof::MachineSideProvenance;
    use crate::provenance_xcheck::ProvenanceXCheckMode;
    use crate::smt::SmtSort;
    use crate::{FunctionVerifier, VerificationConfig};
    use sha2::{Digest, Sha256};

    let _serial = formal_solver_test_lock();
    crate::env_lock::with_env_overrides(
        &[
            ("TCG_REFINE_SOLVER", "1"),
            ("TCG_NO_PROOF_CACHE", "1"),
            ("TCG_BLOCKING_IDENTITY", "1"),
        ],
        || {
            let verifier = FunctionVerifier::with_config(VerificationConfig::for_proof_promotion());
            let request = verifier.capture_request_with_mode(ProvenanceXCheckMode::Enforce);
            assert!(!request.recording_active());
            request.with_policy(|| {
                let config = crate::verdict_db::live_source_bound_config();
                let authority = request.ay().authority.as_ref()
                    .expect("genuine captured checker authority is mandatory");
                let checker = authority.checker().expect("actual capable checker is mandatory");
                let low = SmtExpr::uf("low_word", vec![], SmtSort::BitVec(64));
                let packed = SmtExpr::uf("assembled_word", vec![], SmtSort::BitVec(64));
                let source = SmtExpr::uf("stated_word", vec![], SmtSort::BitVec(64));
                let mask = SmtExpr::bv_const(18_446_462_603_027_808_255, 64);
                let shifted = SmtExpr::bv_const(4_294_967_296, 64);
                let definitions = vec![
                    source.clone().eq_expr(SmtExpr::bv_const(4_294_967_297, 64)),
                    low.clone().eq_expr(SmtExpr::bv_const(1, 64)),
                    packed.clone().eq_expr(low.bvand(mask).bvor(shifted)),
                ];
                let narrow = SmtExpr::uf("narrow_word", vec![], SmtSort::BitVec(32));
                let narrow_result = SmtExpr::uf("narrow_result", vec![], SmtSort::BitVec(32));
                let boolean = SmtExpr::uf("literal_predicate", vec![], SmtSort::Bool);
                let cases = [
                    ("full-width assembled status", source, packed, definitions),
                    ("modular i32 alias", SmtExpr::bv_const(u32::MAX as u64, 32),
                        narrow_result.clone(), vec![
                            narrow.clone().eq_expr(SmtExpr::bv_const(1, 32)),
                            narrow_result.clone().eq_expr(narrow.bvneg()),
                        ]),
                    ("Boolean alias equality", SmtExpr::BoolConst(true), boolean.clone(), vec![
                        narrow_result.clone().eq_expr(SmtExpr::bv_const(u32::MAX as u64, 32)),
                        boolean.eq_expr(narrow_result.eq_expr(SmtExpr::bv_const(u32::MAX as u64, 32))),
                    ]),
                ];
                for (name, trust_ir_expr, aarch64_expr, preconditions) in cases {
                    let original = ProofObligation {
                        name: name.into(), trust_ir_expr, aarch64_expr,
                        inputs: vec![], fp_inputs: vec![], preconditions, category: None,
                        machine_side_provenance: MachineSideProvenance::StaticDb,
                    };
                    let before = original.clone();
                    let smt2 = generate_smt2_query_raw(&original, &config);
                    let candidate = crate::closed_definition_alethe::compose(&original)
                        .expect("construct the grounded original component, not a substitute");
                    assert_eq!(original, before);
                    assert_eq!(candidate.premises, original.preconditions.len());
                    assert_eq!(candidate.text.matches("(assume ").count(), 1);
                    let accepted = crate::obligation_cert_store::carcara_verify_with_expected_checker_with_env(
                        checker.path(), checker.sha256(), &smt2, &candidate.text,
                        authority.child_env(), config.timeout_ms,
                    ).expect("checker I/O failure is not proof acceptance");
                    assert!(accepted, "genuine original component {name} must independently replay");
                    let last = candidate.text.rfind("(step ").expect("final refutation step");
                    let truncated = &candidate.text[..last];
                    let rejected = crate::obligation_cert_store::carcara_verify_with_expected_checker_with_env(
                        checker.path(), checker.sha256(), &smt2, truncated,
                        authority.child_env(), config.timeout_ms,
                    ).expect("checker I/O failure is not mutation rejection");
                    assert!(!rejected, "missing final refutation must not certify {name}");
                    println!("DEFINITION_LITERAL_PRIMITIVE_REPLAY {}", serde_json::to_string(
                        &serde_json::json!({
                            "name": name, "smt2": smt2, "proof": candidate.text,
                            "query_sha256": format!("{:x}", Sha256::digest(smt2.as_bytes())),
                            "premises": candidate.premises, "definitions": candidate.definitions,
                            "steps": candidate.steps, "checker_sha256": checker.sha256(),
                            "checker_accepted": accepted, "missing_refutation_accepted": rejected,
                            "ay_ran": false, "model_admission": false, "native_credit": false,
                        })).unwrap());
                }
            });
        },
    );
}

#[test]
fn guarded_components_independently_replay_and_modular_diagnostics_retain_actual_verdicts() {
    use crate::lowering_proof::MachineSideProvenance;
    use crate::provenance_xcheck::ProvenanceXCheckMode;
    use crate::smt::SmtSort;
    use crate::{FunctionVerifier, VerificationConfig};
    use sha2::{Digest, Sha256};

    let _serial = formal_solver_test_lock();
    crate::env_lock::with_env_overrides(
        &[
            ("TCG_REFINE_SOLVER", "1"),
            ("TCG_NO_PROOF_CACHE", "1"),
            ("TCG_BLOCKING_IDENTITY", "1"),
        ],
        || {
            let verifier = FunctionVerifier::with_config(VerificationConfig::for_proof_promotion());
            let request = verifier.capture_request_with_mode(ProvenanceXCheckMode::Enforce);
            assert!(!request.recording_active());
            request.with_policy(|| {
                let config = crate::verdict_db::live_source_bound_config();
                let authority = request.ay().authority.as_ref()
                    .expect("genuine captured checker authority is mandatory");
                let checker = authority.checker().expect("actual capable checker is mandatory");
                let check_case = |original: ProofObligation, expected_rule: &str| {
                    let modular_candidate = expected_rule.starts_with(":rule poly_simp");
                    let before = original.clone();
                    let smt2 = generate_smt2_query_raw(&original, &config);
                    let candidate = if modular_candidate {
                        crate::closed_definition_alethe::compose_modular_candidate(&original)
                    } else {
                        crate::closed_definition_alethe::compose(&original)
                    }
                        .expect("construct the exact original component");
                    assert_eq!(original, before);
                    assert_eq!(candidate.premises, original.preconditions.len());
                    assert_eq!(candidate.text.matches("(assume ").count(), 1);
                    assert!(candidate.text.contains(expected_rule));
                    let accepted = crate::obligation_cert_store::carcara_verify_with_expected_checker_with_env(
                        checker.path(), checker.sha256(), &smt2, &candidate.text,
                        authority.child_env(), config.timeout_ms,
                    ).expect("checker I/O failure is not proof acceptance");
                    let last = candidate.text.rfind("(step ").expect("final refutation step");
                    let rejected = crate::obligation_cert_store::carcara_verify_with_expected_checker_with_env(
                        checker.path(), checker.sha256(), &smt2, &candidate.text[..last],
                        authority.child_env(), config.timeout_ms,
                    ).expect("checker I/O failure is not mutation rejection");
                    println!("CLOSED_DEFINITION_EXTENDED_PRIMITIVE_REPLAY {}", serde_json::to_string(
                        &serde_json::json!({
                            "name": original.name, "expected_rule": expected_rule,
                            "test_only_modular_candidate": modular_candidate,
                            "production_route": !modular_candidate,
                            "smt2": smt2, "proof": candidate.text,
                            "query_sha256": format!("{:x}", Sha256::digest(smt2.as_bytes())),
                            "premises": candidate.premises, "definitions": candidate.definitions,
                            "steps": candidate.steps, "checker_sha256": checker.sha256(),
                            "checker_accepted": accepted, "missing_refutation_accepted": rejected,
                            "timeout_ms": config.timeout_ms,
                            "ay_ran": false, "model_admission": false, "native_credit": false,
                        })).unwrap());
                    if !modular_candidate {
                        assert!(accepted, "exact guarded component {} must independently replay", original.name);
                    }
                    assert!(!rejected, "missing final refutation must not certify {}", original.name);
                };
                for width in [8, 32, 64] {
                    for positive in [true, false] {
                        let condition = SmtExpr::uf("condition", vec![], SmtSort::Bool);
                        let alias = SmtExpr::uf("condition_alias", vec![], SmtSort::Bool);
                        let symbolic = SmtExpr::var("symbolic", width);
                        let selected = SmtExpr::bv_const(17, width);
                        let guard = if positive { alias.clone() } else { alias.clone().not_expr() };
                        let ite = if positive {
                            SmtExpr::ite(condition.clone(), selected.clone(), symbolic)
                        } else {
                            SmtExpr::ite(condition.clone(), symbolic, selected.clone())
                        };
                        let original = ProofObligation {
                            name: format!("ordinary guarded ITE {width} {positive}"),
                            trust_ir_expr: SmtExpr::BoolConst(true),
                            aarch64_expr: guard.not_expr().or_expr(ite.eq_expr(selected)),
                            inputs: vec![("symbolic".into(), width)],
                            fp_inputs: vec![], preconditions: vec![alias.eq_expr(condition)], category: None,
                            machine_side_provenance: MachineSideProvenance::StaticDb,
                        };
                        check_case(original, ":rule ite_intro");
                    }
                }
                for positive in [true, false] {
                    let condition = SmtExpr::uf("condition", vec![], SmtSort::Bool);
                    let other = SmtExpr::uf("symbolic_boolean", vec![], SmtSort::Bool);
                    let guard = if positive { condition.clone() } else { condition.clone().not_expr() };
                    let selected = SmtExpr::BoolConst(true);
                    let ite = if positive {
                        SmtExpr::ite(condition, selected.clone(), other)
                    } else {
                        SmtExpr::ite(condition, other, selected.clone())
                    };
                    check_case(ProofObligation {
                        name: format!("ordinary Boolean guarded ITE {positive}"),
                        trust_ir_expr: SmtExpr::BoolConst(true),
                        aarch64_expr: guard.not_expr().or_expr(ite.eq_expr(selected)),
                        inputs: vec![], fp_inputs: vec![], preconditions: vec![], category: None,
                        machine_side_provenance: MachineSideProvenance::StaticDb,
                    }, ":rule ite_intro");
                }
                for width in [1, 8, 32, 64] {
                    let input = SmtExpr::var("ordinary_input", width);
                    let zero = SmtExpr::bv_const(0, width);
                    let constant = SmtExpr::bv_const(1, width);
                    for (name, trust_ir_expr, aarch64_expr, rule) in [
                        ("modular additive identity", input.clone().bvadd(zero.clone()), input.clone(), ":rule poly_simp)"),
                        ("modular zero comparison", input.clone().bvsub(constant.clone()).eq_expr(zero), input.eq_expr(constant), ":rule poly_simp_rel "),
                    ] {
                        check_case(ProofObligation {
                            name: format!("{name} {width}"), trust_ir_expr, aarch64_expr,
                            inputs: vec![("ordinary_input".into(), width)], fp_inputs: vec![],
                            preconditions: vec![], category: None,
                            machine_side_provenance: MachineSideProvenance::StaticDb,
                        }, rule);
                    }
                }
            });
        },
    );
}
