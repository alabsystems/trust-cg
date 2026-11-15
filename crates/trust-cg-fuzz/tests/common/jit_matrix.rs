// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

use std::collections::HashMap;
use std::panic::{AssertUnwindSafe, catch_unwind};
use trust_cg_codegen::compiler::{Compiler, CompilerConfig};
use trust_cg_codegen::pipeline::OptLevel;
use trust_ir::{CallingConv, Module, Ty};

pub const OPTS: [OptLevel; 4] = [OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::O3];
pub type Config = (bool, OptLevel);
pub type MatrixResults = Vec<(Config, Vec<i64>)>;

/// Compile one exact fixture/configuration, keeping its executable owner alive
/// across every input row. Fixture functions must have the declared C ABI.
pub fn run_jit_config(
    module: &Module,
    entry: &str,
    opt: OptLevel,
    jit_fast: bool,
    rows: &[[i64; 4]],
) -> Result<Vec<i64>, String> {
    let result = catch_unwind(AssertUnwindSafe(|| {
        if rows.is_empty() {
            return Err("NO_ROWS: no native executions requested".into());
        }
        let mut functions = module
            .functions
            .iter()
            .filter(|function| function.name == entry);
        let function = functions
            .next()
            .ok_or_else(|| format!("SYMBOL_MISSING: {entry}"))?;
        if functions.next().is_some()
            || function.blocks.is_empty()
            || function.calling_conv != CallingConv::C
            || !module
                .func_types
                .get(function.ty.as_usize())
                .is_some_and(|ty| {
                    ty.params.len() == 4
                        && ty.params.iter().all(|param| *param == Ty::I64)
                        && ty.returns == [Ty::I64]
                        && !ty.is_vararg
                })
        {
            return Err(format!(
                "ENTRY_ABI_MISMATCH: {entry} must be one defined C (i64,i64,i64,i64)->i64 function"
            ));
        }
        let mut config = if jit_fast {
            CompilerConfig::jit_fast(trust_cg_codegen::Target::host())
        } else {
            let mut config = CompilerConfig::for_host_jit();
            config.enable_jit_fast_regalloc = false;
            config
        };
        config.opt_level = opt;
        let buffer = Compiler::new(config)
            .with_codegen_license(permit_unlicensed())
            .compile_module_to_jit(module, &HashMap::new())
            .map_err(|error| format!("COMPILE_ERR: {error:?}"))?
            .buffer;
        type Fn4 = extern "C" fn(i64, i64, i64, i64) -> i64;
        // The exact fixture signature was checked above; buffer owns the code
        // until every call below has completed.
        let function = unsafe { buffer.get_fn_bound::<Fn4>(entry) }
            .ok_or_else(|| format!("SYMBOL_MISSING: compiled {entry}"))?
            .into_inner();
        Ok(rows
            .iter()
            .map(|row| function(row[0], row[1], row[2], row[3]))
            .collect())
    }));
    result.unwrap_or_else(|payload| {
        let message = payload
            .downcast_ref::<String>()
            .map(String::as_str)
            .or_else(|| payload.downcast_ref::<&str>().copied())
            .unwrap_or("non-string panic payload");
        Err(format!("JIT_PANIC: {message}"))
    })
}

/// No configuration failure is excused by an unavailable reference result.
pub fn run_jit_matrix(
    module: &Module,
    entry: &str,
    rows: &[[i64; 4]],
    label: &str,
    defects: &mut Vec<String>,
) -> MatrixResults {
    let mut results = Vec::new();
    for jit_fast in [true, false] {
        for opt in OPTS {
            match run_jit_config(module, entry, opt, jit_fast, rows) {
                Ok(values) => results.push(((jit_fast, opt), values)),
                Err(error) => defects.push(format!("{label} fast={jit_fast} opt={opt:?}: {error}")),
            }
        }
    }
    results
}

/// This file's fixtures are hand-built and carry no codegen license
/// (`body_gate: None`), which trust-cg REFUSES by default (roadmap WS7.5,
/// decision gate DG-73). Its compiles state `Permit` explicitly, so none of
/// them passes because it was silently refused.
fn permit_unlicensed() -> trust_cg_lower::CodegenLicensePolicy {
    trust_cg_lower::CodegenLicensePolicy::default()
        .with_unlicensed(trust_cg_lower::UnlicensedBodyPolicy::Permit)
}
