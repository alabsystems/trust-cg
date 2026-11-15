// Dump a selected obligation family's strict-gate queries into a directory:
// `<dir>/<idx>.smt2` plus `<dir>/index.tsv` (idx, name, category, degenerate),
// the lowered rounds (`.fpbv`, `.fpbv-facts`) and the definitional ones (`.def<k>`).
//
//   targo --unverified run -p trust-cg-verify --example dump_gate_corpus -- <dir> [family]
//
// family: database (default), checked-add-sub-i128, wasm-value-domain.
// Exports queries only; no solver, proof acceptance, certificate or credit.
//
// The query is the one `verify_with_ay_attributed` sends: the simplified
// rendering, or the raw one when the simplifier alone folded it to `false`.

use std::io::Write as _;

use trust_cg_verify::ay_bridge::{
    AYConfig, generate_definitional_queries, generate_lowered_queries, lane_smt2_query,
};
use trust_cg_verify::proof_database::ProofDatabase;

fn main() {
    let dir = std::path::PathBuf::from(std::env::args().nth(1).expect("usage: <dir> [family]"));
    let family = std::env::args().nth(2).unwrap_or_else(|| "database".into());
    let (proofs, timeout_ms) = match family.as_str() {
        "database" => (
            ProofDatabase::new()
                .all()
                .iter()
                .map(|p| (p.obligation.clone(), format!("{:?}", p.category)))
                .collect::<Vec<_>>(),
            120_000,
        ),
        "checked-add-sub-i128" => (
            trust_cg_verify::checked_overflow_proofs::all_checked_overflow_add_sub_i128_proofs()
                .into_iter()
                .map(|p| (p, "InstructionLowering".into()))
                .collect(),
            120_000,
        ),
        "wasm-value-domain" => (
            trust_cg_verify::wasm_value_domain::all_value_domain_obligations()
                .into_iter()
                .map(|p| (p, "Reconstructed".into()))
                .collect(),
            180_000,
        ),
        other => {
            eprintln!(
                "unknown family {other:?}; expected database, checked-add-sub-i128 or wasm-value-domain"
            );
            std::process::exit(2);
        }
    };
    std::fs::create_dir_all(&dir).expect("create dir");
    let config = AYConfig::default().with_timeout(timeout_ms);
    let mut index = std::fs::File::create(dir.join("index.tsv")).expect("index");
    for (idx, (obligation, category)) in proofs.iter().enumerate() {
        let query = lane_smt2_query(obligation, &config);
        std::fs::write(dir.join(format!("{idx:04}.smt2")), query).expect("write");
        for (round, (lowered, _)) in generate_lowered_queries(obligation, &config)
            .into_iter()
            .enumerate()
        {
            let suffix = if round == 0 { "fpbv" } else { "fpbv-facts" };
            std::fs::write(dir.join(format!("{idx:04}.{suffix}.smt2")), lowered).expect("write");
        }
        // The definitional round `verify_with_ay_attributed` tries after the
        // exact query: derived operators spelled by their SMT-LIB definitions.
        for (round, (definitional, _)) in generate_definitional_queries(obligation, &config)
            .into_iter()
            .enumerate()
        {
            std::fs::write(dir.join(format!("{idx:04}.def{round}.smt2")), definitional)
                .expect("write");
        }
        writeln!(
            index,
            "{idx:04}\t{}\t{}\t{}",
            obligation.name,
            category,
            obligation.is_degenerate()
        )
        .expect("index row");
    }
    eprintln!("dumped {} obligations", proofs.len());
}
