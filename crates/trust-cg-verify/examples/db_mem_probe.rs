//! Measures what a `ProofDatabase` actually COSTS in resident memory, and where
//! that cost sits, full vs scoped to the one category an x86-64 compile
//! consults.
//!
//! Written because "the compile-memory gap is `ProofDatabase::new()`" was an
//! INFERENCE (from a cert-path A/B), never a direct measurement.
use trust_cg_verify::proof_database::{ProofCategory, ProofDatabase};

fn main() {
    let mode = std::env::args().nth(1).unwrap_or_else(|| "none".into());
    match mode.as_str() {
        "full" => {
            let db = ProofDatabase::new();
            println!("full: {} obligations", db.all().len());
            std::hint::black_box(&db);
        }
        "x86" => {
            let db = ProofDatabase::for_categories(&[ProofCategory::X8664Lowering]);
            println!("x86: {} obligations", db.all().len());
            std::hint::black_box(&db);
        }
        // Rank obligations by rendered tree size, a proxy for heap footprint,
        // so we can see whether a few monsters dominate or the cost is spread.
        "rank" => {
            let db = ProofDatabase::new();
            let mut rows: Vec<(usize, String, String)> = db
                .all()
                .iter()
                .map(|p| {
                    let n = format!("{:?}", p.obligation.trust_ir_expr).len()
                        + format!("{:?}", p.obligation.aarch64_expr).len();
                    (n, p.category.name().to_string(), p.obligation.name.clone())
                })
                .collect();
            rows.sort_by(|a, b| b.0.cmp(&a.0));
            let total: usize = rows.iter().map(|r| r.0).sum();
            let x86: usize = rows
                .iter()
                .filter(|r| r.1 == ProofCategory::X8664Lowering.name())
                .map(|r| r.0)
                .sum();
            println!(
                "total rendered bytes {total}  x86 share {:.1}%",
                100.0 * x86 as f64 / total as f64
            );
            println!("--- top 15 ---");
            for (n, cat, name) in rows.iter().take(15) {
                println!("{n:>10}  {cat:<16} {}", name);
            }
            let top50: usize = rows.iter().take(50).map(|r| r.0).sum();
            println!(
                "top 50 obligations = {:.1}% of all rendered bytes",
                100.0 * top50 as f64 / total as f64
            );
        }
        // Where does a 2MB obligation COME FROM? Build the cmpxchg pieces in
        // the same order the proof does and measure each stage, so the
        // multiplication is observed rather than assumed.
        "blowup" => {
            use trust_cg_verify::memory_proofs::{encode_load_le, encode_store_le, zeroed_memory};
            use trust_cg_verify::smt::SmtExpr;
            use trust_cg_verify::x86_64_semantics::encode_cmpxchg;
            let sz = |e: &SmtExpr| format!("{e:?}").len();
            for size_bytes in [4u32, 8] {
                let addr = SmtExpr::var("addr", 64);
                let matched = SmtExpr::var("matched", size_bytes * 8);
                let desired = SmtExpr::var("desired", size_bytes * 8);
                let zero = zeroed_memory();
                let mem = encode_store_le(&zero, &addr, &matched, size_bytes);
                let (_r, mem_after, _f) =
                    encode_cmpxchg(&mem, &addr, &matched, &desired, size_bytes);
                let loaded = encode_load_le(&mem_after, &addr, size_bytes);
                println!(
                    "{size_bytes}B: seeded_mem {:>9}  after_cmpxchg {:>9} (x{:.1})  load_le {:>9} (x{:.1})",
                    sz(&mem),
                    sz(&mem_after),
                    sz(&mem_after) as f64 / sz(&mem) as f64,
                    sz(&loaded),
                    sz(&loaded) as f64 / sz(&mem_after) as f64,
                );
            }
        }
        // Per-family RSS: build ONE family, hold it, report. Run once per
        // family name so each measurement starts from a clean process — the
        // point is where the 4.7 MB of the x86 database actually SITS after
        // MEM-2's Arc sharing, which need not match the pre-sharing
        // rendered-bytes ranking.
        "family" => {
            use trust_cg_verify::x86_64_lowering_proofs as p;
            let which = std::env::args().nth(2).unwrap_or_default();
            let v: Vec<_> = match which.as_str() {
                "atomic_rmw" => p::all_x86_64_atomic_rmw_cas_loop_proofs(),
                "cmpxchg" => p::all_x86_64_cmpxchg_proofs(),
                "atomic_lsf" => p::all_x86_64_atomic_load_store_fence_proofs(),
                "packed_arith" => p::all_x86_64_v128_packed_arithmetic_proofs(),
                "bitfield" => p::all_x86_64_scalar_bitfield_proofs(),
                "fp_conv" => p::all_x86_64_fp_conversion_proofs(),
                "bit_manip" => p::all_x86_64_bit_manip_proofs(),
                "all" => p::all_x86_64_proofs(),
                _ => Vec::new(),
            };
            println!("{which}: {} obligations", v.len());
            std::hint::black_box(&v);
        }
        _ => println!("baseline: no database built"),
    }
}
