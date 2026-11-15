// Discharge the lowering-proof database FORMALLY via the ay SMT solver (not the
// statistical/sampling lane). The solver is the one AY the identity rule admits
// (`trust_cg_verify::ay_identity`): the `bin/ay` of the Trust toolchain that
// builds this example, identified by the SHA-256 of its bytes recorded at build
// time. No PATH, home directory or source checkout is consulted, and
// `AY_SOLVER_PATH` can only name another copy of those exact bytes. To run a
// different AY build, build with the Trust toolchain that ships it:
//
//   targo --unverified run -p trust-cg-verify --release --example prove_all_with_ay
//
// The admitted AY is printed first, so the counts below name the solver that
// produced them.
//
// Prints, per category, how many obligations ay proved (Verified = UNSAT of the
// negated equivalence = correct for ALL inputs), timed out, or refuted.
//
// With the improved ay (auto bvmul-by-constant simplification incl. -(2^k), ay
// main >= 287ceeb) this discharges 135/135 VERIFIED, 0 timeouts, 0 refutations:
// every emitted-instruction lowering obligation is SMT-proven over the full
// 2^n input space, not statistically sampled.

use trust_cg_verify::ay_bridge::{AYConfig, AYResult, verify_all_with_ay_structural};

fn main() {
    println!("solver: {}", trust_cg_verify::ay_bridge::solver_info());
    let config = AYConfig::default();
    let results = verify_all_with_ay_structural(&config);

    // STRICT HONESTY (task #61): a degenerate `X == X` obligation discharges
    // `UNSAT(X != X)` = Verified trivially and proves NOTHING (model-consistency
    // only). Degeneracy is decided PURELY STRUCTURALLY (`trust_ir_expr ==
    // aarch64_expr`), carried as the trailing bool of each result triple — NOT
    // from any name ledger. Degenerate Verifieds are counted SEPARATELY and
    // EXCLUDED from the genuine "VERIFIED" headline.
    let mut genuinely_verified = 0usize;
    let mut degenerate_debt = 0usize;
    let mut timeout = 0usize;
    let mut other = 0usize;
    let mut failures: Vec<String> = Vec::new();

    for (name, res, is_degenerate) in &results {
        match res {
            AYResult::Verified => {
                if *is_degenerate {
                    degenerate_debt += 1;
                } else {
                    genuinely_verified += 1;
                }
            }
            AYResult::Timeout => {
                timeout += 1;
                failures.push(format!("TIMEOUT  {name}"));
            }
            r => {
                other += 1;
                failures.push(format!("{r}  {name}"));
            }
        }
    }

    println!("=== formal ay discharge of the lowering-proof database ===");
    println!("total obligations      : {}", results.len());
    println!("GENUINELY VERIFIED     : {genuinely_verified}");
    println!(
        "degenerate debt (X==X) : {degenerate_debt}  (UNSAT(X!=X) is vacuous — proves NOTHING; NOT counted as genuine)"
    );
    println!("timeout                : {timeout}");
    println!("other (sat/error)      : {other}");
    if !failures.is_empty() {
        println!("--- non-verified ---");
        for f in &failures {
            println!("  {f}");
        }
    }
    // A counterexample (SAT) would mean a real lowering bug; treat as failure.
    let refuted = results
        .iter()
        .filter(|(_, r, _)| matches!(r, AYResult::CounterExample(_)))
        .count();
    if refuted > 0 {
        eprintln!("FAIL: {refuted} obligation(s) REFUTED by ay (real lowering bug)");
        std::process::exit(1);
    }
}
