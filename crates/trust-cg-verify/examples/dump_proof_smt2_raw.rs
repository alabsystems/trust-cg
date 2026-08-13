// Dump the RAW (un-simplified) SMT2 query for any ProofDatabase obligation whose
// name contains a given substring.
//
//   cargo run -p trust-cg-verify --example dump_proof_smt2_raw -- "Imul_I32"
//
// The default `dump_proof_smt2` uses `generate_smt2_query`, which runs the
// solver-oriented bitvector simplifier. For commutative-reconstructed ALU
// lowerings (e.g. IMUL: bvmul(a,b) == imul(a,b)), that simplifier folds the
// negated equivalence to constant `false`, emitting `(assert false)` — trivially
// unsat but with NO bit-blasted content (it would be a vacuous B-cert).
//
// This raw variant uses `generate_smt2_query_raw`, the exact generator the bridge
// itself routes such obligations through (see `simplifier_alone_proved_unsat` in
// ay_bridge.rs): it applies only the SOUND bounded-quantifier expansion and emits
// the REAL negated-equivalence formula, so the solver must genuinely refute the
// 32x32 multiply equivalence. This is the formula we want for a non-vacuous,
// production-scale B-cert.

use trust_cg_verify::ay_bridge::{AYConfig, generate_smt2_query_raw};
use trust_cg_verify::proof_database::ProofDatabase;

fn main() {
    let needle = std::env::args().nth(1).unwrap_or_default();
    if needle.is_empty() {
        eprintln!("usage: dump_proof_smt2_raw <name-substring>");
        std::process::exit(2);
    }
    let db = ProofDatabase::new();
    let config = AYConfig::default();
    let mut found = 0;
    let all = needle == "*";
    for proof in db.all() {
        if all || proof.obligation.name.contains(&needle) {
            found += 1;
            println!(";; ===== {} =====", proof.obligation.name);
            print!("{}", generate_smt2_query_raw(&proof.obligation, &config));
            println!();
        }
    }
    if found == 0 {
        eprintln!("no proof matched substring {needle:?}");
        std::process::exit(1);
    }
    eprintln!("matched {found} proof(s) for {needle:?}");
}
