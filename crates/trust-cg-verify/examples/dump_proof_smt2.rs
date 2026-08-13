// Dump the SMT2 query for any ProofDatabase obligation whose name contains a
// given substring, so we can study AY's behavior on it directly.
//
//   cargo run -p trust-cg-verify --example dump_proof_smt2 -- "Umul_I32"
//
// Prints, for each match: a header line `;; <name>` then the SMT2 query.

use trust_cg_verify::ay_bridge::{AYConfig, generate_smt2_query};
use trust_cg_verify::proof_database::ProofDatabase;

fn main() {
    let needle = std::env::args().nth(1).unwrap_or_default();
    if needle.is_empty() {
        eprintln!("usage: dump_proof_smt2 <name-substring>");
        std::process::exit(2);
    }
    let db = ProofDatabase::new();
    let config = AYConfig::default();
    let mut found = 0;
    for proof in db.all() {
        if proof.obligation.name.contains(&needle) {
            found += 1;
            println!(";; ===== {} =====", proof.obligation.name);
            print!("{}", generate_smt2_query(&proof.obligation, &config));
            println!();
        }
    }
    if found == 0 {
        eprintln!("no proof matched substring {needle:?}");
        std::process::exit(1);
    }
    eprintln!("matched {found} proof(s) for {needle:?}");
}
