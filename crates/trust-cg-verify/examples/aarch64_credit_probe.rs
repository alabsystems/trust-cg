// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0
//! OD-35 feasibility probe for raw whole-body and ground constant queries.
//! This measures the admitted AY and independent checker, without granting
//! source correspondence, instruction credit or publication authority.
//!
//! Run through scripts/trust_cargo.sh with TCG_NO_PROOF_CACHE=1 and
//! TCG_NO_SOLVER_SERVER=1 to require fresh solves. The output directory retains
//! each raw query and a result manifest, including refuting controls.

use std::path::PathBuf;
use std::time::Instant;

use serde_json::json;
use sha2::{Digest, Sha256};
use trust_cg_ir::cc::OperandSize;
use trust_cg_verify::ay_bridge::{
    AYConfig, AYResult, generate_smt2_query_raw, verify_with_cli_raw_attributed,
};
use trust_cg_verify::lowering_proof::{MachineSideProvenance, ProofObligation, TransvalCheckKind};
use trust_cg_verify::smt::SmtExpr as E;

fn main() {
    let mut args = std::env::args().skip(1);
    let (Some(out), None) = (args.next(), args.next()) else {
        eprintln!("usage: aarch64_credit_probe <out-dir>");
        std::process::exit(2);
    };
    let out = PathBuf::from(out);
    std::fs::create_dir_all(&out).expect("create probe directory");
    let config = AYConfig::default();
    let mut rows = Vec::new();
    let mut failures = 0;
    for bits in [32, 64] {
        let size = if bits == 32 {
            OperandSize::S32
        } else {
            OperandSize::S64
        };
        let a = E::var("arg0", bits);
        let b = E::var("arg1", bits);
        // LIR Isub has the independent widened wrapping spelling. Thread
        // MOVXrr/MOVWrr, SUB and the return move over the machine registers
        // without simplifying the residual expression into an affine form.
        let source = a
            .clone()
            .zero_ext(1)
            .bvsub(b.clone().zero_ext(1))
            .extract(bits - 1, 0);
        let r9 = trust_cg_verify::aarch64_semantics::encode_mov_rr(size, a);
        let r10 = trust_cg_verify::aarch64_semantics::encode_mov_rr(size, b);
        let r9 = trust_cg_verify::aarch64_semantics::encode_sub_rr(size, r9, r10.clone());
        let returned = trust_cg_verify::aarch64_semantics::encode_mov_rr(size, r9);
        let cases = [
            (
                "body",
                source.clone(),
                returned,
                vec![("arg0".into(), bits), ("arg1".into(), bits)],
                true,
            ),
            (
                "wrong_return_route",
                source,
                r10,
                vec![("arg0".into(), bits), ("arg1".into(), bits)],
                false,
            ),
            (
                "constant",
                E::bv_const(3, bits),
                E::bv_const(3, bits).bvshl(E::bv_const(0, bits)),
                Vec::new(),
                true,
            ),
            (
                "wrong_immediate",
                E::bv_const(3, bits),
                E::bv_const(4, bits).bvshl(E::bv_const(0, bits)),
                Vec::new(),
                false,
            ),
            (
                "wrong_halfword",
                E::bv_const(3, bits),
                E::bv_const(3, bits).bvshl(E::bv_const(16, bits)),
                Vec::new(),
                false,
            ),
        ];
        for (name, trust_ir_expr, aarch64_expr, inputs, should_verify) in cases {
            let obligation = ProofObligation {
                name: format!("AArch64 credit probe {name} i{bits}"),
                trust_ir_expr,
                aarch64_expr,
                inputs,
                preconditions: Vec::new(),
                fp_inputs: Vec::new(),
                category: Some(TransvalCheckKind::InstructionLowering),
                machine_side_provenance: MachineSideProvenance::StaticDb,
            };
            assert!(!obligation.is_degenerate());
            let query = generate_smt2_query_raw(&obligation, &config);
            let file = format!("{name}-{bits}.smt2");
            std::fs::write(out.join(&file), &query).expect("write raw query");
            let start = Instant::now();
            let verdict = verify_with_cli_raw_attributed(&obligation, &config);
            let passed = if should_verify {
                verdict.result == AYResult::Verified
            } else {
                matches!(verdict.result, AYResult::CounterExample(_))
            };
            failures += usize::from(!passed);
            rows.push(json!({
                "name": obligation.name,
                "query": file,
                "query_sha256": format!("{:x}", Sha256::digest(query.as_bytes())),
                "expected": if should_verify { "Verified" } else { "CounterExample" },
                "result": verdict.result.to_string(),
                "attribution": verdict.provenance(),
                "passed": passed,
                "elapsed_ms": start.elapsed().as_millis(),
            }));
            println!("{}: {}", obligation.name, verdict.result);
        }
    }
    let manifest = json!({
        "schema": "trust-cg.aarch64-credit-probe.v1",
        "publication_credit": false,
        "failures": failures,
        "rows": rows,
    });
    std::fs::write(
        out.join("results.json"),
        serde_json::to_string_pretty(&manifest).unwrap(),
    )
    .expect("write probe results");
    if failures != 0 {
        std::process::exit(1);
    }
}
