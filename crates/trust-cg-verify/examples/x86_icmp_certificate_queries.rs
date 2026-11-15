// trust-cg-verify/examples/x86_icmp_certificate_queries.rs - dump every x86-64
// vector-compare cell's lowering-obligation query, with its rule ground, its
// spec side and its certified pin, and the certificate rule itself, for the
// certificate gate.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
//   targo --unverified run -p trust-cg-verify --example x86_icmp_certificate_queries -- <out-dir>
//
// Writes `<out-dir>/<SHAPE>_<Cond>.smt2` (the exact `generate_smt2_query`
// bytes `tests/x86_icmp_manifest_cells.rs` digests) for every covered cell
// with exactly one registered obligation, and `<out-dir>/manifest.json`:
//
// - `certificate_rule`: `trust_ir::CHC_X86_ICMP_CERTIFICATE_RULE`, field for
//   field, as the trust-ir this build compiled against defines it (the gate
//   reads the rule HERE, through the compiled dependency, and parses no
//   prose);
// - for every cell trust-ir's reader answers (every `chc_x86` descriptor x
//   every `ICmpOp`): the reader's verdict, the ground trust-ir answers for it
//   (`trust_ir::chc_x86_vector_icmp_cell_ground`), the obligation's name and
//   degeneracy, the pin from the table the test reads
//   (`tests/support/x86_icmp_cells.rs`), and, for a cell with a registered
//   obligation, trust-ir's spec side of the cell as SMT-LIB text
//   (`trust_ir::chc_x86_vector_icmp_spec`, printed by `SmtAlgebra`).
//
// It decides nothing: `scripts/check_x86_icmp_certificates.py` checks
// coverage, the pins and the spec subterm, and re-runs AY and Clean on the
// certificate-ground queries under the rule.

#[path = "../tests/support/x86_icmp_cells.rs"]
mod cells;

use std::path::PathBuf;

use serde_json::{Value, json};
use sha2::{Digest, Sha256};
use trust_cg_verify::ay_bridge::DEFAULT_AY_TIMEOUT_MS;
use trust_cg_verify::smt::SmtExpr;
use trust_cg_verify::x86_64_lowering_proofs::all_x86_64_proofs;
use trust_ir::{CHC_X86_ICMP_CERTIFICATE_RULE, ChcX86IcmpCertifyingBuild};

const SCHEMA: &str = "trust-cg.x86-icmp-cell-queries.v2";

fn certifying_build(build: &ChcX86IcmpCertifyingBuild) -> Value {
    json!({
        "package": build.package,
        "rev": build.rev,
        "version": build.version,
        "build_args": build.build_args,
        "certifying_sha256": build.certifying_sha256,
    })
}

/// `trust_ir::CHC_X86_ICMP_CERTIFICATE_RULE`, field for field.
fn certificate_rule() -> Value {
    let rule = CHC_X86_ICMP_CERTIFICATE_RULE;
    json!({
        "ay": certifying_build(&rule.ay),
        "ay_args": rule.ay_args,
        "ay_verdict": rule.ay_verdict,
        "ay_certificate_report": rule
            .ay_certificate_report
            .iter()
            .map(|(field, value)| json!([field, value]))
            .collect::<Vec<_>>(),
        "unchecked_proof_rules": rule.unchecked_proof_rules,
        "clean": certifying_build(&rule.clean),
        "clean_args": rule.clean_args,
        "clean_proof_status": rule.clean_proof_status,
    })
}

fn sha256_hex(text: &str) -> String {
    Sha256::digest(text.as_bytes())
        .iter()
        .map(|byte| format!("{byte:02x}"))
        .collect()
}

fn operand(prefix: &str) -> SmtExpr {
    SmtExpr::var(format!("{prefix}_hi"), 64).concat(SmtExpr::var(format!("{prefix}_lo"), 64))
}

fn main() {
    let mut args = std::env::args().skip(1);
    let (Some(out), None) = (args.next(), args.next()) else {
        eprintln!("usage: x86_icmp_certificate_queries <out-dir>");
        std::process::exit(2);
    };
    let out = PathBuf::from(out);
    std::fs::create_dir_all(&out)
        .unwrap_or_else(|error| panic!("create {}: {error}", out.display()));
    let proofs = all_x86_64_proofs();
    let (lhs, rhs) = (operand("lhs"), operand("rhs"));
    let mut descriptors = Vec::new();
    let mut rows = Vec::new();
    for descriptor in trust_ir::chc_x86_hardware_vector_contract_descriptors() {
        let (bits, lanes) = (descriptor.element_bits, descriptor.lane_count);
        let shape = cells::shape_name(bits, lanes);
        descriptors.push(json!({ "shape": shape, "lane_bits": bits, "lanes": lanes }));
        let Some(shape) = shape else {
            continue;
        };
        for op in cells::OPS {
            let cond = cells::cond_name(op);
            let reader = trust_ir::chc_x86_vector_icmp_cell_status(bits, lanes, op)
                .expect("every chc_x86 descriptor covers every ICmpOp");
            let ground = cells::rule_ground(bits, lanes, op);
            let found = cells::obligations(&proofs, shape, cond);
            let mut row = json!({
                "shape": shape,
                "lane_bits": bits,
                "lanes": lanes,
                "cond": cond,
                "operation": cells::manifest_operation(op),
                "reader": {
                    "status": reader.status.code(),
                    "reason": reader.reason.code(),
                    "fail_closed": reader.fail_closed(),
                    "feature_guard": reader.feature_guard,
                },
                "ground": ground.name(),
                "obligation_count": found.len(),
                "obligation": Value::Null,
                "degenerate": Value::Null,
                "query_file": Value::Null,
                "spec": Value::Null,
                "certified_sha256": cells::certified_pin(shape, cond),
            });
            if let [ob] = found.as_slice() {
                let file = format!("{shape}_{cond}.smt2");
                let path = out.join(&file);
                std::fs::write(&path, cells::query_text(ob))
                    .unwrap_or_else(|error| panic!("write {}: {error}", path.display()));
                let spec = trust_cg_verify::trust_ir_bv::chc_x86_vector_icmp_spec(
                    bits, lanes, op, &lhs, &rhs,
                )
                .expect("every chc_x86 descriptor governs every ICmpOp")
                .to_string();
                row["obligation"] = json!(ob.name);
                row["degenerate"] = json!(ob.is_degenerate());
                row["query_file"] = json!(file);
                row["spec"] = json!({
                    "fn": "trust_ir::chc_x86_vector_icmp_spec",
                    "trust_ir_build": trust_ir::BUILD_IDENTITY.version,
                    "sha256": sha256_hex(&spec),
                    "text": spec,
                });
            }
            rows.push(row);
        }
    }
    let manifest = json!({
        "schema": SCHEMA,
        "trust_ir_build": trust_ir::BUILD_IDENTITY.version,
        "certificate_rule": certificate_rule(),
        "ay_query_timeout_ms": DEFAULT_AY_TIMEOUT_MS,
        "operations": cells::OPS.map(cells::cond_name),
        "descriptors": descriptors,
        "certified_pins": cells::CERTIFIED_QUERY_SHA256,
        "reviewed_fail_closed": cells::REVIEWED_FAIL_CLOSED_CELLS,
        "measured_not_admitted": cells::MEASURED_NOT_ADMITTED_QUERY_SHA256,
        "cells": rows,
    });
    let path = out.join("manifest.json");
    let text = serde_json::to_string_pretty(&manifest).expect("the manifest serializes");
    std::fs::write(&path, text + "\n")
        .unwrap_or_else(|error| panic!("write {}: {error}", path.display()));
    eprintln!(
        "wrote {} cells to {}",
        manifest["cells"].as_array().map_or(0, Vec::len),
        out.display()
    );
}
