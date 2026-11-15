// trust-cg-verify/tests/x86_icmp_manifest_cells.rs — every x86-64 vector
// compare cell trust-ir's `chc_x86` manifest publishes as AVAILABLE rests on
// exactly the ground the manifest names for it.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! trust-ir `docs/dialects.md` ("Vector compares on x86-64 follow one per-cell
//! rule"): an available `icmp.<op>` cell of a `chc_x86` descriptor rests on
//! exactly one of two grounds, which trust-ir answers per cell
//! (`trust_ir::chc_x86_vector_icmp_cell_ground`; this crate never re-derives
//! it).
//!
//! 1. INSTRUCTION MODEL — `icmp.eq` and `icmp.sgt`
//!    (`trust_ir::CHC_X86_ICMP_INSTRUCTION_MODEL_OPERATIONS`): the lowering is
//!    one `pcmpeq*` / `pcmpgt*` whose semantic model IS the lane predicate, so
//!    this backend's registered obligation is degenerate by construction
//!    (both sides structurally equal; its query is `(assert false)`). No
//!    certificate is claimed for such a cell; it rests on the instruction
//!    model, a trusted-base fact.
//! 2. CERTIFICATE — every other available cell: the registered obligation is
//!    NON-degenerate, and its exact SMT-LIB query (sha256 pinned in
//!    `support/x86_icmp_cells.rs`) is one the AY named by
//!    `trust_ir::CHC_X86_ICMP_CERTIFICATE_RULE` answers `unsat` under
//!    `--strict-proofs` with an Alethe proof the rule's Clean
//!    `cert verify-external` accepts in full. This test does NOT run AY or
//!    Clean: it holds that the query has not changed since it was certified —
//!    any edit to an obligation changes its digest and fails here until it is
//!    re-certified. The certificate itself is re-run on exactly these bytes by
//!    `scripts/check_x86_icmp_certificates.py`, a `scripts/soundness_check.sh`
//!    leg, which builds both tools by the revisions the rule names and reads
//!    the rule and this table through `examples/x86_icmp_certificate_queries.rs`.
//!
//! The SPEC side of every cell is trust-ir's statement
//! (`trust_ir::chc_x86_vector_icmp_spec`, printed by
//! `trust_cg_verify::trust_ir_bv::SmtAlgebra`), never a copy kept here
//! (`spec_side_is_trust_irs_statement`), and the MACHINE side applies exactly
//! the instruction models trust-ir publishes for the cell
//! (`certificate_cells_use_exactly_the_published_instruction_models`), which
//! stay independent of the spec statement
//! (`x86_instruction_models_do_not_share_the_spec_statement`).
//!
//! This test pins the partition in BOTH directions, so neither ground can
//! silently absorb the other: a composite cell whose obligation turns
//! degenerate fails, and so does an eq/sgt obligation replaced by a
//! non-degenerate one. Every available cell must also be registered exactly
//! once in `all_x86_64_proofs()` and hold under exhaustive/sampled evaluation,
//! and the descriptor table must be exactly trust-ir's. Test rung (digest pins,
//! structural equality and evaluation), not proof.

use std::collections::BTreeMap;

use trust_cg_verify::lowering_proof::verify_by_evaluation;
use trust_cg_verify::smt::SmtExpr;
use trust_cg_verify::trust_ir_bv::chc_x86_vector_icmp_spec;
use trust_cg_verify::verify::VerificationResult;
use trust_cg_verify::x86_64_lowering_proofs::{
    all_x86_64_proofs, x86_vector_icmp_cell_composition,
};

#[path = "support/x86_icmp_cells.rs"]
mod cells;

use cells::{
    CERTIFIED_QUERY_SHA256, Ground, MEASURED_NOT_ADMITTED_QUERY_SHA256, OPS,
    REVIEWED_FAIL_CLOSED_CELLS, SHAPES, cond_name, obligation, query_sha256, rule_ground,
};

#[test]
fn available_icmp_cells_rest_on_their_named_ground() {
    let proofs = all_x86_64_proofs();
    let pinned: BTreeMap<(&str, &str), &str> = CERTIFIED_QUERY_SHA256
        .iter()
        .map(|(shape, cond, digest)| ((*shape, *cond), *digest))
        .collect();
    let mut computed = Vec::new();
    let mut failures = Vec::new();
    let mut used_pins = 0usize;
    for (bits, lanes, shape) in SHAPES {
        for op in OPS {
            let cell = trust_ir::chc_x86_vector_icmp_cell_status(bits, lanes, op)
                .expect("every chc_x86 descriptor covers every ICmpOp");
            if cell.fail_closed() {
                continue;
            }
            let cond = cond_name(op);
            let ob = match obligation(&proofs, shape, cond) {
                Ok(ob) => ob,
                Err(why) => {
                    failures.push(why);
                    continue;
                }
            };
            match verify_by_evaluation(ob) {
                VerificationResult::Valid => {}
                other => failures.push(format!("{shape} {cond}: evaluation {other:?}")),
            }
            let lowering = ob.name.split(" -> ").nth(1).unwrap_or_default();
            let ground = rule_ground(bits, lanes, op);
            if ground == Ground::FailClosed {
                failures.push(format!(
                    "{shape} {cond}: the reader answers the cell available, yet trust-ir answers \
                     no ground for it"
                ));
                continue;
            }
            if ground == Ground::InstructionModel {
                // Ground (a): one instruction whose model IS the predicate.
                if !ob.is_degenerate() {
                    failures.push(format!(
                        "{shape} {cond}: an instruction-model cell's obligation is not degenerate; \
                         it now claims evidence the manifest does not publish for it"
                    ));
                }
                if lowering.contains('+') || lowering.contains('(') {
                    failures.push(format!(
                        "{shape} {cond}: an instruction-model cell lowers to a composition \
                         (`{lowering}`), not one instruction"
                    ));
                }
                continue;
            }
            // Ground (b): a non-degenerate obligation over the certified query.
            if ob.is_degenerate() {
                failures.push(format!(
                    "{shape} {cond}: a certificate-ground cell's obligation is DEGENERATE; a \
                     tautology is never a certificate"
                ));
            }
            let digest = query_sha256(ob);
            computed.push(format!("(\"{shape}\", \"{cond}\", \"{digest}\")"));
            match pinned.get(&(shape, cond)) {
                Some(want) if *want == digest => used_pins += 1,
                Some(want) => failures.push(format!(
                    "{shape} {cond}: query sha256 {digest} is not the certified {want}; a changed \
                     query must be re-certified before its row stays available"
                )),
                None => failures.push(format!(
                    "{shape} {cond}: certificate-ground cell with no pinned certified query \
                     (computed {digest})"
                )),
            }
        }
    }
    if used_pins != pinned.len() {
        failures.push(format!(
            "{} pinned digest(s) name no available certificate-ground cell (a cell left the \
             manifest's available set: delete its pin)",
            pinned.len() - used_pins
        ));
    }
    assert!(
        failures.is_empty(),
        "{} finding(s):\n  {}\ncomputed certificate-ground digests:\n  {}",
        failures.len(),
        failures.join("\n  "),
        computed.join(",\n  ")
    );
}

/// The cells this file and the certificate gate enumerate are exactly
/// trust-ir's: `SHAPES` names every `chc_x86` descriptor the reader answers
/// for, and no other. A descriptor trust-ir adds would otherwise be a reader
/// cell no ground is checked for.
#[test]
fn shapes_are_exactly_the_chc_x86_descriptors() {
    let mut published: Vec<(u32, u32)> = trust_ir::chc_x86_hardware_vector_contract_descriptors()
        .iter()
        .map(|descriptor| (descriptor.element_bits, descriptor.lane_count))
        .collect();
    let mut named: Vec<(u32, u32)> = SHAPES
        .iter()
        .map(|(bits, lanes, _)| (*bits, *lanes))
        .collect();
    published.sort_unstable();
    named.sort_unstable();
    assert_eq!(
        named, published,
        "SHAPES must name exactly trust-ir's chc_x86 descriptors (lane bits, lanes)"
    );
}

/// The deferred side's one rule, over the reader's fail-closed set: that set
/// is exactly `reviewed`, and every `measured` row names a member of it.
/// Pure, so a synthetic set witnesses it while the pinned manifest has none
/// (`deferred_cell_rule_admits_a_reviewed_measured_cell`).
fn deferred_cell_findings(
    fail_closed: &[(&str, &str)],
    reviewed: &[(&str, &str)],
    measured: &[(&str, &str, &str)],
) -> Vec<String> {
    let mut findings = Vec::new();
    for (shape, cond) in fail_closed {
        if !reviewed.contains(&(*shape, *cond)) {
            findings.push(format!(
                "{shape} {cond}: newly fail-closed in the manifest; review it and list it in \
                 REVIEWED_FAIL_CLOSED_CELLS"
            ));
        }
    }
    for (shape, cond) in reviewed {
        if !fail_closed.contains(&(*shape, *cond)) {
            findings.push(format!(
                "{shape} {cond}: listed in REVIEWED_FAIL_CLOSED_CELLS, but the manifest makes it \
                 available; delete the row"
            ));
        }
    }
    for (shape, cond, _) in measured {
        if !fail_closed.contains(&(*shape, *cond)) {
            findings.push(format!(
                "{shape} {cond}: measured-not-admitted row names a cell the manifest makes \
                 available; move it into CERTIFIED_QUERY_SHA256"
            ));
        }
    }
    findings
}

/// A cell the pinned manifest does NOT make available keeps a registered,
/// evaluation-valid obligation (the backend still lowers it on the
/// function-level entries and on AArch64), but no certified-query pin: the
/// manifest names no certificate for it, and trust-cg's x86-64 module entry
/// refuses it (`VectorCompareCellFailClosed`). The fail-closed set must be
/// exactly [`REVIEWED_FAIL_CLOSED_CELLS`]; such a cell may carry a
/// [`MEASURED_NOT_ADMITTED_QUERY_SHA256`] row, which must still name its exact
/// query; and every such row must name a cell that is still fail-closed
/// ([`deferred_cell_findings`]).
///
/// At the pinned trust-ir the reader answers no covered cell fail-closed (the
/// four unsigned `v16_i8` compares were the last, published available at
/// trust-ir `72dee4b6`), so the per-cell loop has no subject and both tables
/// are empty; this test is what holds that at each pin move. A newly deferred
/// cell fails here until it is reviewed.
/// None of this exercises a real-cell rejection while the manifest has none.
#[test]
fn fail_closed_icmp_cells_carry_no_certificate_pin() {
    let proofs = all_x86_64_proofs();
    let mut fail_closed_cells = Vec::new();
    for (bits, lanes, shape) in SHAPES {
        for op in OPS {
            let cell = trust_ir::chc_x86_vector_icmp_cell_status(bits, lanes, op)
                .expect("every chc_x86 descriptor covers every ICmpOp");
            if !cell.fail_closed() {
                continue;
            }
            let cond = cond_name(op);
            fail_closed_cells.push((shape, cond));
            assert!(
                !CERTIFIED_QUERY_SHA256
                    .iter()
                    .any(|(s, c, _)| *s == shape && *c == cond),
                "{shape} {cond}: a fail-closed cell must carry no certified-query pin"
            );
            let ob = obligation(&proofs, shape, cond).unwrap_or_else(|why| panic!("{why}"));
            assert!(
                !ob.is_degenerate(),
                "{shape} {cond}: the composition obligation is not a tautology"
            );
            assert!(
                matches!(verify_by_evaluation(ob), VerificationResult::Valid),
                "{shape} {cond}: the composition obligation does not hold under evaluation"
            );
            if let Some((_, _, measured)) = MEASURED_NOT_ADMITTED_QUERY_SHA256
                .iter()
                .find(|(s, c, _)| *s == shape && *c == cond)
            {
                let digest = query_sha256(ob);
                assert_eq!(
                    digest, *measured,
                    "{shape} {cond}: the query changed since its certificate was measured; \
                     re-certify it or delete the row"
                );
            }
        }
    }
    let findings = deferred_cell_findings(
        &fail_closed_cells,
        REVIEWED_FAIL_CLOSED_CELLS,
        MEASURED_NOT_ADMITTED_QUERY_SHA256,
    );
    assert!(
        findings.is_empty(),
        "{} finding(s):\n  {}",
        findings.len(),
        findings.join("\n  ")
    );
}

/// The tables are usable: the state they exist for (a reviewed fail-closed
/// cell, with or without a measured certificate) passes the rule, and each
/// way out of it is named. No real cell is fail-closed at this pin, so this
/// synthetic set is the witness (test rung).
#[test]
fn deferred_cell_rule_admits_a_reviewed_measured_cell() {
    let cell = [("V16I8", "Ugt")];
    let measured = [("V16I8", "Ugt", "digest")];
    assert_eq!(
        deferred_cell_findings(&cell, &cell, &measured),
        Vec::<String>::new()
    );
    assert_eq!(
        deferred_cell_findings(&cell, &cell, &[]),
        Vec::<String>::new()
    );
    let named = |findings: Vec<String>, needle: &str| {
        assert!(
            findings.len() == 1 && findings[0].contains(needle),
            "expected one finding naming `{needle}`, got {findings:?}"
        );
    };
    named(deferred_cell_findings(&cell, &[], &[]), "newly fail-closed");
    named(deferred_cell_findings(&[], &cell, &[]), "delete the row");
    named(
        deferred_cell_findings(&[], &[], &measured),
        "move it into CERTIFIED_QUERY_SHA256",
    );
}

/// The obligations' operands: a 128-bit vector as two 64-bit variables, high
/// half first (`x86_v128_from_u64_halves` in the lowering proofs).
fn operand(prefix: &str) -> SmtExpr {
    SmtExpr::var(format!("{prefix}_hi"), 64).concat(SmtExpr::var(format!("{prefix}_lo"), 64))
}

/// B-T3a: the SPEC side of every registered cell obligation is trust-ir's
/// statement of the cell (`trust_ir::chc_x86_vector_icmp_spec`, printed by
/// `SmtAlgebra`), compared structurally, for all 40 cells, available or not.
/// The obligation is found by its name (`<shape>Icmp_<cond>`), so a cell whose
/// spec states another predicate than its name fails here. Mutation (measured
/// in the commit that adds it): building the `Ult` obligation's spec with
/// `Ugt` turns it red.
#[test]
fn spec_side_is_trust_irs_statement() {
    let proofs = all_x86_64_proofs();
    let (lhs, rhs) = (operand("lhs"), operand("rhs"));
    let mut failures = Vec::new();
    let mut checked = 0usize;
    for (bits, lanes, shape) in SHAPES {
        for op in OPS {
            let cond = cond_name(op);
            let ob = match obligation(&proofs, shape, cond) {
                Ok(ob) => ob,
                Err(why) => {
                    failures.push(why);
                    continue;
                }
            };
            let spec = chc_x86_vector_icmp_spec(bits, lanes, op, &lhs, &rhs)
                .expect("every chc_x86 descriptor governs every ICmpOp");
            if ob.trust_ir_expr != spec {
                failures.push(format!(
                    "{shape} {cond}: the obligation's spec side is not trust-ir's statement of \
                     icmp.{}",
                    cond.to_ascii_lowercase()
                ));
            }
            checked += 1;
        }
    }
    assert!(
        failures.is_empty(),
        "{} finding(s):\n  {}",
        failures.len(),
        failures.join("\n  ")
    );
    assert_eq!(checked, SHAPES.len() * OPS.len(), "every cell checked");
}

/// The published bias materialization of an unsigned cell: a constant, outside
/// the certificate (trust-ir `docs/dialects.md`, the per-cell rule's clause 2),
/// so it is not a model application of the composition.
const BIAS_MATERIALIZATION: [&str; 3] = ["mov_imm_sign_bit", "movd_to_xmm", "pshufd"];

/// The instruction models trust-ir publishes for an available cell's lowering
/// (`native_instructions`), without the bias materialization, sorted.
fn published_models(native_instructions: &str) -> Vec<&str> {
    let mut models: Vec<&str> = native_instructions.split(';').collect();
    if models.starts_with(&BIAS_MATERIALIZATION) {
        models.drain(..BIAS_MATERIALIZATION.len());
    }
    models.sort_unstable();
    models
}

/// B-T3d: for every AVAILABLE cell, the registered machine side is the cell's
/// composition, and the multiset of x86 instruction models that composition
/// applies is exactly the cell's published `native_instructions`
/// (`trust_ir::chc_x86_vector_icmp_lowering_row`) less the bias
/// materialization: trust-ir's row is the one list of the models a cell's
/// certificate trusts, and no model the composition uses goes unlisted. The
/// composition is not tied to the published `composition` term as a tree.
/// Mutations (measured in the commit that adds it): dropping one `pshufd` from
/// the `v2_i64` unsigned sequence, or adding a `pand` to a `v4_i32` row, turns
/// it red.
#[test]
fn certificate_cells_use_exactly_the_published_instruction_models() {
    let proofs = all_x86_64_proofs();
    let mut failures = Vec::new();
    let mut checked = 0usize;
    for (bits, lanes, shape) in SHAPES {
        for op in OPS {
            let cond = cond_name(op);
            let Some(row) = trust_ir::chc_x86_vector_icmp_lowering_row(bits, lanes, op) else {
                continue;
            };
            let ob = match obligation(&proofs, shape, cond) {
                Ok(ob) => ob,
                Err(why) => {
                    failures.push(why);
                    continue;
                }
            };
            let (composition, mut applied) = x86_vector_icmp_cell_composition(bits, lanes, op)
                .expect("every chc_x86 descriptor has a composition");
            if composition != ob.aarch64_expr {
                failures.push(format!(
                    "{shape} {cond}: the registered machine side is not the cell's composition"
                ));
            }
            applied.sort_unstable();
            let published = published_models(row.native_instructions);
            if applied != published {
                failures.push(format!(
                    "{shape} {cond}: the composition applies {applied:?}; trust-ir publishes \
                     {published:?} (`{}`)",
                    row.native_instructions
                ));
            }
            checked += 1;
        }
    }
    assert!(
        failures.is_empty(),
        "{} finding(s):\n  {}",
        failures.len(),
        failures.join("\n  ")
    );
    assert_eq!(
        checked,
        SHAPES.len() * OPS.len(),
        "every cell is available at this pin, so every cell is checked"
    );
}

/// The source text of the item that starts at `start` in `source`: from
/// `start` to the first line that is exactly `}` after it.
fn item<'a>(source: &'a str, start: &str) -> &'a str {
    let from = source
        .find(start)
        .unwrap_or_else(|| panic!("`{start}` is not in the source"));
    let rest = &source[from..];
    let to = rest
        .find("\n}\n")
        .unwrap_or_else(|| panic!("`{start}` has no closing line"));
    &rest[..to]
}

/// B-T3g: this backend's x86 INSTRUCTION models, and the production
/// compositions over them, never route through trust-ir's spec statement.
/// Were they to, the eight instruction-model cells (`icmp.eq` / `icmp.sgt`)
/// would be degenerate because the two sides share code, not because the
/// instruction model equals the format's meaning. A token scan (test rung) of
/// `x86_64_semantics.rs` and of the production model application and
/// compositions in `x86_64_lowering_proofs.rs`. Mutation (measured in the
/// commit that adds it): routing `packed_lane_mask` through
/// `trust_ir::physical_mask_lane` turns it red.
#[test]
fn x86_instruction_models_do_not_share_the_spec_statement() {
    let semantics = include_str!("../src/x86_64_semantics.rs");
    let proofs = include_str!("../src/x86_64_lowering_proofs.rs");
    let scanned = [
        ("x86_64_semantics.rs", semantics),
        (
            "X86EncodeModels",
            item(proofs, "impl X86IcmpModels for X86EncodeModels"),
        ),
        (
            "encode_x86_v128_compare_mask_lowering_with_bias",
            item(
                proofs,
                "fn encode_x86_v128_compare_mask_lowering_with_bias(",
            ),
        ),
        (
            "encode_x86_v2i64_unsigned_sse2_compare_mask_with_bias",
            item(
                proofs,
                "fn encode_x86_v2i64_unsigned_sse2_compare_mask_with_bias(",
            ),
        ),
        (
            "x86_vector_icmp_lowering",
            item(proofs, "fn x86_vector_icmp_lowering("),
        ),
    ];
    let mut failures = Vec::new();
    for (name, text) in scanned {
        for token in [
            "bv_meaning",
            "physical_mask_lane",
            "chc_x86_vector_icmp_spec",
            "trust_ir_bv",
            "SmtAlgebra",
            "x86_vector_icmp_spec",
        ] {
            if text.contains(token) {
                failures.push(format!("{name} names `{token}`"));
            }
        }
    }
    assert!(
        failures.is_empty(),
        "the x86 instruction models must stay independent of trust-ir's spec statement:\n  {}",
        failures.join("\n  ")
    );
}
