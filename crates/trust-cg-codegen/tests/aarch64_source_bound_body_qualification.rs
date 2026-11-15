// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0
//! Opt-in qualification of the AArch64 whole-body owner with the admitted
//! proof tools (`TCG_A64_BODY_QUALIFY=1`): the body theorem of every family
//! in both preparations (AOT and JIT) is put to the identity-admitted AY and
//! replayed by Clean, every corruption's theorem must be refuted by AY, and
//! the proof-required JIT and AOT routes publish only bodies whose own
//! theorems certified (the JIT's then run natively; the AOT route exports the
//! theorem). Unrequested, it prints SKIP and supplies no evidence; it is not a
//! floor target. Records: `reports/2026-10-01-aarch64-source-bound-body`.
#![cfg(all(target_arch = "aarch64", feature = "verify"))]

use std::collections::HashMap;
use trust_cg_codegen::compiler::{Compiler, CompilerConfig};
use trust_cg_codegen::target::{Target, TargetSpec};
use trust_cg_verify::source_bound_a64_body::{
    A64_BODY_NEEDS_REPLAY, A64_BODY_OBLIGATION_NAME, a64_body_row_categories,
    diagnostic_a64_body_obligation, source_bound_a64_body,
};

#[path = "common/source_bound_body_cases.rs"]
mod cases;
#[path = "common/source_bound_proof_tools.rs"]
mod source_bound_proof_tools;
use cases::{
    CASES, LEVELS, PREPS, Prep, Sig, call, grid, lir, module, mutants, on_big_stack, prepare_as,
    symbol,
};

/// The opcodes a proof-promotion refusal lists as uncovered.
fn listed_opcodes(text: &str) -> Vec<&str> {
    text.split_once("distinct opcode(s) [")
        .and_then(|(_, rest)| rest.split_once(']'))
        .map_or(Vec::new(), |(list, _)| list.split(", ").collect())
}

/// Whether a refusal of a body whose theorem certified names only what this
/// owner leaves without a credit route: E0.2 copies and constants, or (when
/// the compile's own replay of the same theorem did not certify it, as with
/// an AY whose self-check is not deterministic) the body rows' named need.
/// Returns `false` for an E0.2-only refusal and `true` for an unreplayed
/// theorem (a replay disagreement); panics on anything else.
fn classify_certified_refusal(label: &str, text: &str) -> bool {
    let listed = listed_opcodes(text);
    let copies_or_constants = !listed.is_empty()
        && listed.iter().all(|opcode| {
            matches!(
                *opcode,
                "AArch64::Movz"
                    | "AArch64::Movn"
                    | "AArch64::Movk"
                    | "AArch64::MovI"
                    | "AArch64::MovR"
                    | "AArch64::MOVWrr"
                    | "AArch64::MOVXrr"
            )
        });
    if copies_or_constants {
        return false;
    }
    assert!(
        text.contains(A64_BODY_NEEDS_REPLAY),
        "{label}: a certified body refused on more than E0.2 copies/constants or its \
         unreplayed theorem: {text}"
    );
    true
}

/// Opt-in qualification with the admitted proof tools. For every family and
/// level, the body theorem of each preparation (the AOT route's and the
/// JIT's; one query when the bodies agree) is put to AY and replayed by
/// Clean, and every corruption of each distinct body must be refuted by AY.
/// The proof-required JIT must publish only bodies whose JIT-preparation
/// theorem certified, which then run over their input grids; the
/// proof-required AOT route must emit only objects whose AOT-preparation
/// theorem certified, exporting that theorem on every credited row. Every
/// other refusal of a certified body names only an E0.2 copy/constant or the
/// unreplayed theorem.
#[test]
fn qualification_with_the_admitted_proof_tools() {
    use trust_cg_verify::ay_bridge::{AYConfig, AYResult, verify_with_ay_cli};
    if std::env::var_os("TCG_A64_BODY_QUALIFY").is_none() {
        println!("SKIP A64_BODY_QUALIFY (set TCG_A64_BODY_QUALIFY=1 with admitted AY and Clean)");
        return;
    }
    on_big_stack(|| {
        if let Some(reason) = trust_cg_verify::ay_bridge::proof_toolchain_unavailable_reason() {
            panic!("PROOF_TOOLS_MISSING: {reason}");
        }
        println!(
            "A64_BODY_QUALIFY_TOOLS {}",
            source_bound_proof_tools::resolved_proof_tools()
        );
        // AY's verdict per distinct query.
        let mut verdicts: HashMap<String, bool> = HashMap::new();
        let mut certified = 0usize;
        let mut refuted = 0usize;
        let mut mutants_total = 0usize;
        let mut jit_published = 0usize;
        let mut aot_exported = 0usize;
        let mut replay_disagreements = 0usize;
        let mut bodies = 0usize;
        let mut lines = Vec::new();
        for case in CASES {
            let module = module(case);
            let lir = lir(&module);
            for level in LEVELS {
                let mut certified_by_prep = HashMap::new();
                for prep in PREPS {
                    let machine = prepare_as(prep, &lir, level);
                    let owner = source_bound_a64_body(&lir, &machine).unwrap();
                    let query = trust_cg_verify::serialize_to_smt2(owner.obligation());
                    let sha = format!(
                        "{:x}",
                        <sha2::Sha256 as sha2::Digest>::digest(query.as_bytes())
                    );
                    let known = verdicts.get(&sha).copied();
                    let verified = match known {
                        Some(verified) => verified,
                        None => {
                            let verdict =
                                verify_with_ay_cli(owner.obligation(), &AYConfig::default());
                            assert!(
                                !matches!(verdict, AYResult::CounterExample(_)),
                                "{}/{level:?}/{prep:?}: the body theorem is refuted: {verdict}",
                                case.name
                            );
                            let verified = matches!(verdict, AYResult::Verified);
                            certified += usize::from(verified);
                            verdicts.insert(sha.clone(), verified);
                            lines.push(format!(
                                "A64_BODY_QUALIFY {}/{level:?}/{prep:?} theorem={verdict} \
                                 query_sha256={sha}",
                                case.name
                            ));
                            // Corruptions of each distinct body.
                            for (class, mutant) in mutants(&machine, owner.covered()) {
                                let obligation = diagnostic_a64_body_obligation(&lir, &mutant)
                                    .unwrap_or_else(|r| {
                                        panic!("{}/{level:?}/{prep:?} {class}: {r}", case.name)
                                    });
                                mutants_total += 1;
                                match verify_with_ay_cli(&obligation, &AYConfig::default()) {
                                    AYResult::CounterExample(_) => refuted += 1,
                                    other => panic!(
                                        "{}/{level:?}/{prep:?} {class}: the solver lane did not \
                                         refute: {other}",
                                        case.name
                                    ),
                                }
                            }
                            verified
                        }
                    };
                    if known.is_some() {
                        lines.push(format!(
                            "A64_BODY_QUALIFY {}/{level:?}/{prep:?} same query as above \
                             query_sha256={sha}",
                            case.name
                        ));
                    }
                    bodies += 1;
                    certified_by_prep.insert(prep, verified);
                }
                // The proof-required JIT judges its own preparation.
                let label = format!("{}/{level:?}", case.name);
                let compiler = Compiler::new(CompilerConfig {
                    opt_level: level,
                    emit_proofs: true,
                    parallel: false,
                    ..CompilerConfig::jit_fast(Target::Aarch64)
                })
                .with_codegen_license(permit_unlicensed());
                match compiler.compile_module_to_jit(&module, &HashMap::new()) {
                    Ok(result) => {
                        assert!(
                            certified_by_prep[&Prep::Jit],
                            "{label}: the JIT published without a certified theorem"
                        );
                        jit_published += 1;
                        for row in grid(case.sig) {
                            let Some(expected) = (case.reference)(&row) else {
                                continue;
                            };
                            let mask = if case.sig == Sig::Ww {
                                u64::from(u32::MAX)
                            } else {
                                u64::MAX
                            };
                            assert_eq!(
                                call(&result.buffer, &symbol(case), case.sig, &row),
                                expected & mask
                            );
                        }
                        lines.push(format!("A64_BODY_QUALIFY {label} jit published"));
                    }
                    Err(error) => {
                        let text = error.to_string();
                        if certified_by_prep[&Prep::Jit] {
                            replay_disagreements +=
                                usize::from(classify_certified_refusal(&label, &text));
                        }
                        lines.push(format!("A64_BODY_QUALIFY {label} jit refused: {text}"));
                    }
                }
                // The proof-required AOT route judges its own preparation and
                // exports the same theorem on every credited row, under the
                // row's role category.
                let aot = Compiler::new_for_target_spec(
                    CompilerConfig {
                        opt_level: level,
                        emit_proofs: true,
                        parallel: false,
                        ..Default::default()
                    },
                    TargetSpec::host_for_architecture(Target::Aarch64),
                )
                .with_codegen_license(permit_unlicensed());
                match aot.compile(&module) {
                    Ok(compiled) => {
                        assert!(
                            certified_by_prep[&Prep::Aot],
                            "{label}: the AOT route emitted without a certified theorem"
                        );
                        let certs = compiled.proofs.expect("emit_proofs certificates");
                        let body: Vec<_> = certs
                            .iter()
                            .filter(|cert| cert.rule_name == A64_BODY_OBLIGATION_NAME)
                            .collect();
                        assert!(!body.is_empty(), "{label}: {certs:?}");
                        for cert in &body {
                            let payload = cert
                                .source_bound_obligation
                                .as_ref()
                                .unwrap_or_else(|| panic!("{label}: no exported theorem"));
                            assert!(cert.verified && cert.strength == "Formal", "{cert:?}");
                            assert_eq!(
                                payload.kind(),
                                trust_cg_verify::SourceBoundObligationKind::A64Body
                            );
                            assert_eq!(payload.function_name(), symbol(case));
                            assert_eq!(payload.obligation().name, A64_BODY_OBLIGATION_NAME);
                            assert!(
                                a64_body_row_categories()
                                    .iter()
                                    .any(|category| category.to_string() == cert.category),
                                "{cert:?}"
                            );
                        }
                        aot_exported += 1;
                        lines.push(format!(
                            "A64_BODY_QUALIFY {label} aot exported certificates={}",
                            body.len()
                        ));
                    }
                    Err(error) => {
                        let text = error.to_string();
                        if certified_by_prep[&Prep::Aot] {
                            replay_disagreements +=
                                usize::from(classify_certified_refusal(&label, &text));
                        }
                        lines.push(format!("A64_BODY_QUALIFY {label} aot refused: {text}"));
                    }
                }
            }
        }
        for line in &lines {
            println!("{line}");
        }
        println!(
            "A64_BODY_QUALIFY_SUMMARY families={} bodies={bodies} theorems={} \
             certified={certified} mutants={mutants_total} refuted={refuted} \
             jit_published={jit_published} aot_exported={aot_exported} \
             replay_disagreements={replay_disagreements}",
            CASES.len(),
            verdicts.len()
        );
        assert_eq!(refuted, mutants_total);
    });
}

/// This file's fixtures are hand-built and carry no codegen license
/// (`body_gate: None`), which trust-cg REFUSES by default (roadmap WS7.5,
/// decision gate DG-73). Its compiles state `Permit` explicitly, so none of
/// them passes (or is refused) because the license silently refused it.
fn permit_unlicensed() -> trust_cg_codegen::CodegenLicensePolicy {
    trust_cg_codegen::CodegenLicensePolicy::default()
        .with_unlicensed(trust_cg_codegen::UnlicensedBodyPolicy::Permit)
}
