// Emit a read-only inventory of ProofDatabase::new() obligations.
//
// This example is intentionally small so scripts can use the runtime
// denominator without depending on verifier integration tests.

use trust_cg_verify::proof_database::{ProofCategory, ProofDatabase};

fn max_bv_width(inputs: &[(String, u32)]) -> u32 {
    inputs.iter().map(|(_, width)| *width).max().unwrap_or(0)
}

fn escape_tsv(value: &str) -> String {
    value
        .replace('\\', "\\\\")
        .replace('\t', "\\t")
        .replace('\n', "\\n")
}

fn print_tsv() {
    let db = ProofDatabase::new();
    println!("category\tname\tmax_bv_width\tbv_inputs\tfp_inputs\tpreconditions\tcheck_kind");
    for proof in db.all() {
        let obligation = &proof.obligation;
        let check_kind = obligation
            .category
            .map(|kind| kind.to_string())
            .unwrap_or_else(|| "uncategorized".to_string());
        println!(
            "{}\t{}\t{}\t{}\t{}\t{}\t{}",
            escape_tsv(proof.category.name()),
            escape_tsv(&obligation.name),
            max_bv_width(&obligation.inputs),
            obligation.inputs.len(),
            obligation.fp_inputs.len(),
            obligation.preconditions.len(),
            escape_tsv(&check_kind)
        );
    }
}

fn print_markdown() {
    let db = ProofDatabase::new();
    let summary = db.summary();

    println!("# ProofDatabase Inventory");
    println!();
    println!("- Total obligations: {}", summary.total);
    println!("- FP obligations: {}", summary.fp_proof_count);
    println!("- Preconditions: {}", summary.preconditioned_count);
    println!();
    println!("## Categories");
    println!();
    println!("| Category | Obligations |");
    println!("| --- | ---: |");
    for category in ProofCategory::all_categories() {
        let count = db.count_by_category(*category);
        if count > 0 {
            println!("| {} | {} |", category.name(), count);
        }
    }
    println!();
    println!("## Obligations");
    println!();
    println!(
        "| Category | Name | Max BV Width | BV Inputs | FP Inputs | Preconditions | Check Kind |"
    );
    println!("| --- | --- | ---: | ---: | ---: | ---: | --- |");
    for proof in db.all() {
        let obligation = &proof.obligation;
        let check_kind = obligation
            .category
            .map(|kind| kind.to_string())
            .unwrap_or_else(|| "uncategorized".to_string());
        println!(
            "| {} | `{}` | {} | {} | {} | {} | {} |",
            proof.category.name(),
            obligation.name.replace('|', "\\|"),
            max_bv_width(&obligation.inputs),
            obligation.inputs.len(),
            obligation.fp_inputs.len(),
            obligation.preconditions.len(),
            check_kind
        );
    }
}

fn main() {
    let mut format = String::from("markdown");
    let mut args = std::env::args().skip(1);
    while let Some(arg) = args.next() {
        match arg.as_str() {
            "--format" => {
                format = args
                    .next()
                    .unwrap_or_else(|| panic!("--format requires markdown or tsv"));
            }
            "--help" | "-h" => {
                println!(
                    "usage: cargo run -p trust-cg-verify --example proof_database_inventory -- --format <markdown|tsv>"
                );
                return;
            }
            other => panic!("unknown argument: {other}"),
        }
    }

    match format.as_str() {
        "markdown" => print_markdown(),
        "tsv" => print_tsv(),
        other => panic!("unknown format: {other}"),
    }
}
