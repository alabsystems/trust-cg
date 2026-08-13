// trust-cg-cli/ty_replay_jit_probe.rs - TY replay JIT publication probe
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

use std::collections::HashMap;
use std::error::Error;
use std::path::PathBuf;
use std::process;

use clap::Parser;
use serde_json::json;
use trust_cg_codegen::pipeline::OptLevel;
use trust_cg_codegen::{Compiler, CompilerConfig, FormatMode, load_module_as};

const TY_PARENT_SUMMARY_SLOTS: usize = 5;
const DEFAULT_TY_PARENT_INPUTS: &[u64] = &[2, 5, 8, 13, 21, 34];

/// Compile a linked TY replay trust_ir JSON artifact through the host JIT and
/// print the public allocation size alongside publication-proof evidence.
#[derive(Debug, Parser)]
#[command(
    name = "ty_replay_jit_probe",
    about = "Probe Trust Codegen JIT publication state for a linked TY replay trust_ir JSON artifact"
)]
struct Cli {
    /// Linked TY replay module, usually `*.compile_module_native.linked-*.trust_ir.json`.
    #[arg(long = "trust_ir-json", value_name = "PATH")]
    trust_ir_json: PathBuf,

    /// Symbol to resolve and diagnose from the compiled JIT buffer.
    #[arg(long, value_name = "NAME")]
    symbol: String,

    /// Optimization level to use while compiling the replay module.
    #[arg(
        short = 'O',
        long = "opt-level",
        value_parser = parse_opt_level,
        default_value = "O3"
    )]
    opt_level: OptLevel,

    /// Invoke the resolved symbol as TY parent-loop ABI: (ptr, u64, ptr) -> u64.
    #[arg(long)]
    invoke_ty_parent_loop: bool,

    /// Comma-separated parent inputs for `--invoke-ty-parent-loop`.
    #[arg(long, value_delimiter = ',', value_name = "CSV")]
    parent_inputs: Vec<u64>,
}

fn main() {
    if let Err(err) = run() {
        eprintln!("error: {err}");
        process::exit(1);
    }
}

fn run() -> Result<(), Box<dyn Error>> {
    let cli = Cli::parse();
    let module = load_module_as(&cli.trust_ir_json, FormatMode::Json)?;

    let mut config = CompilerConfig::for_host_jit();
    config.opt_level = cli.opt_level;

    let extern_symbols: HashMap<String, *const u8> = HashMap::new();
    let result = Compiler::new(config).compile_module_to_jit(&module, &extern_symbols)?;
    let public_allocated_size = result.buffer.allocated_size();
    let pointer = result
        .buffer
        .get_fn_ptr_bound(&cli.symbol)
        .ok_or_else(|| boxed_error(format!("JIT buffer does not export `{}`", cli.symbol)))?
        .as_ptr();
    let proof = result
        .buffer
        .diagnose_published_symbol_ptr(&cli.symbol, pointer)?;
    let replay_metadata = result.buffer.replay_report_metadata();
    let function_ranges: Vec<_> = replay_metadata
        .symbols
        .iter()
        .map(|symbol| {
            json!({
                "name": symbol.name.as_str(),
                "start_offset": symbol.range.start_offset,
                "end_offset": symbol.range.end_offset,
                "byte_len": symbol.range.byte_len(),
            })
        })
        .collect();
    let invocation = if cli.invoke_ty_parent_loop {
        let parents = if cli.parent_inputs.is_empty() {
            DEFAULT_TY_PARENT_INPUTS.to_vec()
        } else {
            cli.parent_inputs.clone()
        };
        let func = unsafe {
            result
                .buffer
                .get_fn_bound::<extern "C" fn(*const u64, u64, *mut u64) -> u64>(&cli.symbol)
        }
        .ok_or_else(|| boxed_error(format!("JIT buffer does not export `{}`", cli.symbol)))?;
        let mut summary = [u64::MAX; TY_PARENT_SUMMARY_SLOTS];
        let return_value =
            (*func.as_ref())(parents.as_ptr(), parents.len() as u64, summary.as_mut_ptr());
        Some(json!({
            "shape": "ty_parent_loop_u64_return",
            "parent_inputs": parents,
            "parent_count": summary[0],
            "generated_count": summary[1],
            "parent_digest": summary[2],
            "fingerprint": summary[3],
            "status": summary[4],
            "return_value": return_value,
            "summary": summary,
        }))
    } else {
        None
    };

    let output = json!({
        "symbol": proof.symbol,
        "allocated_size": public_allocated_size,
        "proof_allocation_len": proof.allocation_len,
        "public_matches_proof": public_allocated_size == proof.allocation_len,
        "exact_symbol_match": proof.exact_symbol_match,
        "code_len": proof.code_len,
        "function_count": result.metrics.function_count,
        "function_ranges": function_ranges,
        "invocation": invocation,
    });
    println!("{}", serde_json::to_string(&output)?);

    Ok(())
}

fn boxed_error(message: String) -> Box<dyn Error> {
    Box::new(std::io::Error::new(std::io::ErrorKind::NotFound, message))
}

fn parse_opt_level(value: &str) -> Result<OptLevel, String> {
    match value.to_ascii_lowercase().as_str() {
        "o0" | "0" => Ok(OptLevel::O0),
        "o1" | "1" => Ok(OptLevel::O1),
        "o2" | "2" => Ok(OptLevel::O2),
        "o3" | "3" => Ok(OptLevel::O3),
        _ => Err(format!(
            "invalid optimization level '{value}': expected O0, O1, O2, O3, 0, 1, 2, or 3"
        )),
    }
}
