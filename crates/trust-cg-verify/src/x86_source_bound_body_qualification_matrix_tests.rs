// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! Solver-free export of the complete raw-query qualification matrix. These
//! diagnostics neither admit a replayer nor exercise production proof credit.
//! The host qualification tests retain their recorded identities and outcomes.

use super::slice22::fixture_owner;
use super::*;
use serde_json::{Value, json};
use sha2::{Digest, Sha256};

const PREFIX: &str = "X86_BODY_MATRIX\t";
type BodyCase = (String, Function, X86ISelFunction);
type FamilyCases = (&'static str, usize, Vec<BodyCase>);

fn query_record(family: &str, label: &str, class: &str, source_bound: bool, smt2: String) -> Value {
    json!({
        "kind": "query", "family": family, "label": label, "class": class,
        "source_bound": source_bound,
        "expected": if class == "wrong-lowering" { "sat" } else { "unsat" },
        "smt2": smt2,
    })
}

fn raw_record(family: &str, label: &str, class: &str, theorem: &ProofObligation) -> Value {
    query_record(
        family,
        label,
        class,
        false,
        generate_smt2_query_raw(theorem, &replay_config()),
    )
}

fn cases() -> Vec<FamilyCases> {
    vec![
        ("body", all_shapes().len(), qualification_cases()),
        (
            "memory",
            memory::MEMORY_SHAPES.len(),
            memory::MEMORY_SHAPES
                .iter()
                .map(|shape| {
                    let (source, machine) = memory::memory_pair(*shape);
                    (format!("{shape:?}"), source, machine)
                })
                .collect(),
        ),
        (
            "slice5",
            slice5::SLICE_FIVE.len(),
            slice5_qualification::slice_five_qualification_cases(),
        ),
        (
            "slice6",
            slice6::SLICE_SIX.len(),
            slice6_qualification::slice_six_qualification_cases(),
        ),
        (
            "slice7",
            slice7::SLICE_SEVEN.len(),
            slice7::SLICE_SEVEN
                .iter()
                .map(|shape| {
                    let (source, machine) = slice7::slice7_pair(*shape);
                    (format!("{shape:?}"), source, machine)
                })
                .collect(),
        ),
        (
            "slice8",
            slice8::SLICE_EIGHT.len(),
            slice8::SLICE_EIGHT
                .iter()
                .map(|shape| {
                    let (source, machine) = slice8::slice8_pair(*shape);
                    (format!("{shape:?}"), source, machine)
                })
                .collect(),
        ),
        (
            "slice9",
            slice9::SLICE_NINE.len(),
            slice9::SLICE_NINE
                .iter()
                .map(|shape| {
                    let (source, machine) = slice9::slice9_pair(*shape);
                    (format!("{shape:?}"), source, machine)
                })
                .collect(),
        ),
        (
            "slice10",
            slice10::SLICE_TEN.len(),
            slice10::SLICE_TEN
                .iter()
                .map(|shape| {
                    let (source, machine) = slice10::slice10_pair(*shape);
                    (format!("{shape:?}"), source, machine)
                })
                .collect(),
        ),
        (
            "slice11",
            slice11::SLICE_ELEVEN.len(),
            slice11::SLICE_ELEVEN
                .iter()
                .map(|shape| {
                    let (source, machine) = slice11::slice11_pair(*shape);
                    (format!("{shape:?}"), source, machine)
                })
                .collect(),
        ),
        (
            "slice12",
            slice12::SLICE_TWELVE.len(),
            slice12::SLICE_TWELVE
                .iter()
                .map(|shape| {
                    let (source, machine) = slice12::slice12_pair(*shape);
                    (format!("{shape:?}"), source, machine)
                })
                .collect(),
        ),
        (
            "slice13",
            slice13::SLICE_THIRTEEN.len(),
            slice13::SLICE_THIRTEEN
                .iter()
                .map(|shape| {
                    let (source, machine) = slice13::slice13_pair(*shape);
                    (format!("{shape:?}"), source, machine)
                })
                .collect(),
        ),
        (
            "slice14",
            slice14::SLICE_FOURTEEN.len(),
            slice14::SLICE_FOURTEEN
                .iter()
                .map(|shape| {
                    let (source, machine) = slice14::slice14_pair(*shape);
                    (format!("{shape:?}"), source, machine)
                })
                .collect(),
        ),
        (
            "slice15",
            slice15::SLICE_FIFTEEN.len(),
            slice15::SLICE_FIFTEEN
                .iter()
                .map(|shape| {
                    let (source, machine) = slice15::slice15_pair(*shape);
                    (format!("{shape:?}"), source, machine)
                })
                .collect(),
        ),
        (
            "arraygep",
            arraygep::ARRAY_GEP.len(),
            arraygep::ARRAY_GEP
                .iter()
                .map(|shape| {
                    let (source, machine) = arraygep::arraygep_pair(*shape);
                    (format!("{shape:?}"), source, machine)
                })
                .collect(),
        ),
    ]
}

fn matrix() -> Vec<Value> {
    let mut records = Vec::new();
    for (family, canonical_count, cases) in cases() {
        for (index, (label, source, machine)) in cases.into_iter().enumerate() {
            let owner = fixture_owner(&source, &machine)
                .unwrap_or_else(|refusal| panic!("{family}/{label}: {refusal}"));
            let canonical = generate_smt2_query_raw(owner.obligation(), &replay_config());
            records.push(query_record(
                family,
                &label,
                if index < canonical_count {
                    "canonical"
                } else {
                    "machine-variant"
                },
                true,
                canonical.clone(),
            ));
            if family == "body" {
                if ["U8Ident", "Add/commuted"].contains(&label.as_str()) {
                    let mut tailed =
                        theorem_without_affine_refusal(&source, &machine, SYSV).unwrap();
                    append_preserved_tail(&mut tailed);
                    records.push(raw_record(
                        family,
                        &format!("{label}/preserved-tail"),
                        "encoding",
                        &tailed,
                    ));
                }
                // The UF + world form and the concatenation restate the plain
                // spelling (the claims as built).
                if CALLS.iter().any(|shape| format!("{shape:?}") == label) {
                    let theorem = plain_theorem(&source, &machine);
                    records.push(raw_record(
                        family,
                        &format!("{label}/uf-world"),
                        "encoding",
                        &uf_world_form(&source, &theorem),
                    ));
                }
                let theorem = plain_theorem(&source, &machine);
                if observable_items(&theorem).len() >= 2 {
                    records.push(raw_record(
                        family,
                        &format!("{label}/concatenated"),
                        "encoding",
                        &concatenated_form(&theorem),
                    ));
                }
            }
            // The encodings below re-spell the plain spelling (the claims as
            // built; slice 18's canonical spelling value-numbers them).
            let plain = plain_theorem(&source, &machine);
            if family == "slice6"
                && plain.trust_ir_expr == E::bool_const(true)
                && matches!(&plain.aarch64_expr, E::And { lhs, .. }
                    if matches!(lhs.as_ref(), E::Or { .. }))
            {
                records.push(query_record(
                    family,
                    &format!("{label}/implies"),
                    "encoding",
                    false,
                    slice6_qualification::implies_spelling(&generate_smt2_query_raw(
                        &plain,
                        &replay_config(),
                    )),
                ));
                let every = theorem_with_path_encoding(
                    &source,
                    &machine,
                    SYSV,
                    PathEncoding {
                        elide_aliases: false,
                        cone_of_influence: false,
                        merge_at_observation: false,
                        dag: None,
                        bool_guards: false,
                        trim_long_chains: false,
                        inline_single_use: false,
                        value_number: ValueNumbering::Off,
                        bit_moves: false,
                        fold: false,
                        normal: normal::Groups::NONE,
                        pair_arithmetic: ArithPairs::Off,
                    },
                )
                .unwrap();
                records.push(raw_record(
                    family,
                    &format!("{label}/every-definition"),
                    "encoding",
                    &every,
                ));
                records.push(raw_record(
                    family,
                    &format!("{label}/case-split"),
                    "encoding",
                    &slice6_qualification::case_split(&plain),
                ));
                match theorem_with_path_encoding(
                    &source,
                    &machine,
                    SYSV,
                    PathEncoding {
                        merge_at_observation: true,
                        ..PathEncoding::CANONICAL
                    },
                ) {
                    Ok(form) => records.push(raw_record(
                        family,
                        &format!("{label}/merged"),
                        "encoding",
                        &form,
                    )),
                    Err(refusal) => records.push(json!({
                        "kind": "refusal", "family": family, "label": format!("{label}/merged"),
                        "class": "encoding", "source_bound": false, "reason": refusal.to_string(),
                    })),
                }
            }
        }
    }
    for (label, encoding, _) in memory::MEMORY_ENCODING_OUTCOMES {
        records.push(raw_record(
            "memory",
            &format!("{label}/{encoding:?}"),
            "encoding",
            &memory::encoding_evidence(label, *encoding),
        ));
    }
    for (family, refutations) in [
        ("body", qualification_refutations()),
        ("memory", memory::memory_refutations()),
        ("slice5", slice5::slice_five_refutations()),
        ("slice6", slice6::slice_six_refutations()),
        ("slice7", slice7::slice_seven_refutations()),
        ("slice8", slice8::slice_eight_refutations()),
        ("slice9", slice9::slice_nine_refutations()),
        ("slice10", slice10::slice_ten_refutations()),
        ("slice11", slice11::slice_eleven_refutations()),
        ("slice12", slice12::slice_twelve_refutations()),
        ("slice13", slice13::slice_thirteen_refutations()),
        ("slice14", slice14::slice_fourteen_refutations()),
        ("slice15", slice15::slice_fifteen_refutations()),
        ("arraygep", arraygep::arraygep_refutations()),
    ] {
        for (label, source, machine) in refutations {
            let theorem = theorem_without_affine_refusal(&source, &machine, SYSV)
                .unwrap_or_else(|refusal| panic!("{family}/{label}: {refusal}"));
            records.push(raw_record(family, label, "wrong-lowering", &theorem));
            if family == "body" && label == "swapped call arguments" {
                records.push(raw_record(
                    family,
                    "swapped call arguments/uf-world",
                    "wrong-lowering",
                    &uf_world_form(&source, &plain_theorem(&source, &machine)),
                ));
            }
        }
    }
    records
}

/// JSON lines with a completion footer bind all record bytes. The existing
/// ignored fixture printer calls this only under an explicit diagnostic flag.
pub(super) fn print_matrix() {
    let records = matrix();
    println!(
        "\n{PREFIX}{}",
        json!({
            "kind": "header", "format": "trust-cg-x86-body-qualification-matrix-v1",
            "proof_credit": false, "verifier_source_sha256": env!("VERIFIER_SOURCE_SHA256"),
        })
    );
    let mut hash = Sha256::new();
    for (sequence, record) in records.iter().enumerate() {
        let mut record = record.clone();
        record["sequence"] = json!(sequence);
        let text = record.to_string();
        hash.update(text.as_bytes());
        hash.update(b"\n");
        println!("{PREFIX}{text}");
    }
    println!(
        "{PREFIX}{}",
        json!({
            "kind": "footer", "records": records.len(),
            "queries": records.iter().filter(|record| record["kind"] == "query").count(),
            "refusals": records.iter().filter(|record| record["kind"] == "refusal").count(),
            "records_sha256": format!("{:x}", hash.finalize()),
        })
    );
}

#[test]
fn exported_matrix_binds_canonical_snapshots_and_negative_families() {
    let records = matrix();
    let mut keys = std::collections::BTreeSet::new();
    for record in &records {
        assert!(
            keys.insert((
                record["family"].to_string(),
                record["class"].to_string(),
                record["label"].to_string()
            )),
            "duplicate matrix record: {record}"
        );
    }
    for (family, golden) in [
        (
            "body",
            include_str!("../tests/fixtures/x86_source_bound_body/snapshots.smt2"),
        ),
        (
            "memory",
            include_str!("../tests/fixtures/x86_source_bound_body/memory_snapshots.smt2"),
        ),
        (
            "slice5",
            include_str!("../tests/fixtures/x86_source_bound_body/slice5_snapshots.smt2"),
        ),
        (
            "slice6",
            include_str!("../tests/fixtures/x86_source_bound_body/slice6_snapshots.smt2"),
        ),
        (
            "slice7",
            include_str!("../tests/fixtures/x86_source_bound_body/slice7_snapshots.smt2"),
        ),
        (
            "slice8",
            include_str!("../tests/fixtures/x86_source_bound_body/slice8_snapshots.smt2"),
        ),
        (
            "slice9",
            include_str!("../tests/fixtures/x86_source_bound_body/slice9_snapshots.smt2"),
        ),
        (
            "slice10",
            include_str!("../tests/fixtures/x86_source_bound_body/slice10_snapshots.smt2"),
        ),
        (
            "slice11",
            include_str!("../tests/fixtures/x86_source_bound_body/slice11_snapshots.smt2"),
        ),
        (
            "slice12",
            include_str!("../tests/fixtures/x86_source_bound_body/slice12_snapshots.smt2"),
        ),
        (
            "slice13",
            include_str!("../tests/fixtures/x86_source_bound_body/slice13_snapshots.smt2"),
        ),
        (
            "slice14",
            include_str!("../tests/fixtures/x86_source_bound_body/slice14_snapshots.smt2"),
        ),
        (
            "slice15",
            include_str!("../tests/fixtures/x86_source_bound_body/slice15_snapshots.smt2"),
        ),
        (
            "arraygep",
            include_str!("../tests/fixtures/x86_source_bound_body/arraygep_snapshots.smt2"),
        ),
    ] {
        let rendered: String = records
            .iter()
            .filter(|record| record["family"] == family && record["class"] == "canonical")
            .map(|record| {
                format!(
                    ";;;; {}\n{}\n",
                    record["label"].as_str().unwrap(),
                    record["smt2"].as_str().unwrap()
                )
            })
            .collect();
        assert_eq!(
            rendered, golden,
            "{family}: diagnostic bytes differ from canonical snapshots"
        );
        assert!(
            records
                .iter()
                .any(|record| record["family"] == family && record["class"] == "wrong-lowering"),
            "{family}: missing actual wrong-lowering controls"
        );
    }
}
