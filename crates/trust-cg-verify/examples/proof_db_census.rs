//! Census: obligation counts per category in the full ProofDatabase.
use trust_cg_verify::proof_database::ProofDatabase;
fn main() {
    let db = ProofDatabase::new();
    let all = db.all();
    let mut counts: std::collections::BTreeMap<String, usize> = Default::default();
    for p in all {
        *counts.entry(format!("{:?}", p.category)).or_default() += 1;
    }
    let mut v: Vec<_> = counts.into_iter().collect();
    v.sort_by_key(|(_, c)| std::cmp::Reverse(*c));
    println!("total {}", all.len());
    for (cat, c) in &v {
        println!(
            "{:34} {:6} {:5.1}%",
            cat,
            c,
            100.0 * *c as f64 / all.len() as f64
        );
    }
}
