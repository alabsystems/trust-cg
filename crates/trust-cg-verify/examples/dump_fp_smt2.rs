// Dump the exact SMT2 query the bridge sends the solver for each failing
// FP int<->fp roundtrip obligation, so we can study AY's behavior directly.
//
//   cargo run -p trust-cg-verify --example dump_fp_smt2 -- <which>
//
// where <which> is one of: i32 i16 i64 u32 u16 u64 (default: i32)

use trust_cg_verify::ay_bridge::{AYConfig, generate_smt2_query};
use trust_cg_verify::fp_convert_proofs;

fn main() {
    let which = std::env::args().nth(1).unwrap_or_else(|| "i32".to_string());
    let obligation = match which.as_str() {
        "i32" => fp_convert_proofs::proof_roundtrip_scvtf_fcvtzs(),
        "i16" => fp_convert_proofs::proof_roundtrip_scvtf_fcvtzs_i16(),
        "i64" => fp_convert_proofs::proof_roundtrip_scvtf_fcvtzs_i64(),
        "u32" => fp_convert_proofs::proof_roundtrip_ucvtf_fcvtzu(),
        "u16" => fp_convert_proofs::proof_roundtrip_ucvtf_fcvtzu_i16(),
        "u64" => fp_convert_proofs::proof_roundtrip_ucvtf_fcvtzu_i64(),
        other => {
            eprintln!("unknown obligation '{other}'");
            std::process::exit(2);
        }
    };
    let config = AYConfig::default();
    print!("{}", generate_smt2_query(&obligation, &config));
}
