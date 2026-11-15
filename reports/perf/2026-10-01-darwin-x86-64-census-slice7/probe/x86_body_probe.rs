// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! Probe: read a bridge `dump-trust-ir` module, translate it to LIR, select
//! each function whose name contains the filter as the AOT compiler does,
//! and print the LIR, the pre-RA machine rows and the body-theorem verdict.
//! A copy kept with the report, not compiled in the crate: to run it, place
//! it in `crates/trust-cg-verify/examples/` and build it with
//! `scripts/trust_cargo.sh build -p trust-cg-verify --example x86_body_probe`.
//! The slice-7 design read the bridge's real LIR of `fails-before/
//! probe_callee.rs` (`probe_run.sh` dumps it) through it, and `--census`
//! judged the census's dumped `core` modules offline (`census/`).
//!
//! usage: x86_body_probe <module.trust_irbin> [name-filter] [--smt]
//!        x86_body_probe --census <dump dir> <out.tsv> [<smt2 dir>] [<names>]

use trust_cg_lower::Function;
use trust_cg_lower::x86_64_isel::{X86CallAbi, X86ISelFunction, X86InstructionSelector};
use trust_cg_verify::x86_source_bound_body::{X86SourceBoundAbi, source_bound_x86_body};

fn select(source: &Function) -> Result<X86ISelFunction, String> {
    let signature = trust_cg_lower::function::Signature {
        params: source.signature.params.clone(),
        returns: source.signature.returns.clone(),
    };
    let mut isel = X86InstructionSelector::with_abi(
        source.name.clone(),
        signature.clone(),
        X86CallAbi::SystemV,
    );
    isel.set_stack_slots(source.stack_slots.clone());
    isel.seed_value_types(&source.value_types);
    isel.seed_function_value_use_counts(source);
    isel.seed_pure_callees(&source.pure_callees);
    isel.seed_sret_param(source.abi_sret_param)
        .map_err(|e| format!("{e:?}"))?;
    isel.seed_sret_arg_callees(&source.sret_arg_callees);
    isel.seed_sret_arg_indirect_callees(&source.sret_arg_indirect_callees);
    let order = source.layout_order();
    isel.seed_iconst_origins(
        order
            .iter()
            .map(|block| source.blocks[block].instructions.as_slice()),
    );
    for block in &order {
        isel.ensure_block(*block);
    }
    isel.lower_formal_arguments(&signature, source.entry_block)
        .map_err(|e| format!("{e:?}"))?;
    for block in &order {
        let body = &source.blocks[block];
        if *block != source.entry_block && !body.params.is_empty() {
            isel.define_block_params(&body.params);
        }
        isel.select_block(*block, &body.instructions)
            .map_err(|e| format!("{e:?}"))?;
    }
    isel.finalize_with_eh_info(&source.eh_info)
        .map_err(|e| format!("{e:?}"))
}

/// `--census <dump dir> <out.tsv> [<smt2 dir>] [<names file>]`: every
/// function of every dumped module (first definition of a name wins), one
/// TSV row each (name, verdict, bound rows, whether a call passes a private
/// slot or the source has an sret-arg callee); with an SMT-LIB directory,
/// each built theorem's query as the live replay renders it, restricted to
/// the names file's functions when one is given.
fn census(args: &[String]) {
    use std::io::Write as _;
    let dir = &args[2];
    let mut out = std::fs::File::create(&args[3]).expect("out.tsv");
    let smt2_dir = args.get(4).filter(|dir| !dir.is_empty());
    let names: Option<std::collections::HashSet<String>> = args.get(5).map(|path| {
        std::fs::read_to_string(path)
            .expect("names")
            .lines()
            .map(str::to_owned)
            .collect()
    });
    let config = trust_cg_verify::ay_bridge::AYConfig {
        solver: None,
        timeout_ms: 30_000,
        produce_models: true,
    };
    let mut files: Vec<_> = std::fs::read_dir(dir)
        .expect("dump dir")
        .filter_map(|entry| entry.ok().map(|entry| entry.path()))
        .filter(|path| path.extension().is_some_and(|ext| ext == "trust_irbin"))
        .collect();
    files.sort();
    let mut seen = std::collections::HashSet::new();
    for file in files {
        let Ok(module) = trust_ir::binary::deserialize_module(&std::fs::read(&file).unwrap())
        else {
            eprintln!("undecodable {}", file.display());
            continue;
        };
        let Ok(lir) = trust_cg_lower::translate_module_for_arch(
            &module,
            trust_cg_lower::GuardCarrierArch::X86_64,
        ) else {
            eprintln!("untranslatable {}", file.display());
            continue;
        };
        for (function, _) in lir {
            if !seen.insert(function.name.clone()) {
                continue;
            }
            let through_memory = !function.sret_arg_callees.is_empty();
            let (verdict, rows) = match select(&function) {
                Err(error) => (format!("SELECT {}", error.replace('\t', " ")), 0),
                Ok(machine) => match source_bound_x86_body(
                    &function,
                    &machine,
                    Some(X86SourceBoundAbi::SystemV),
                ) {
                    Ok(body) => {
                        if let Some(dir) = smt2_dir
                            && names.as_ref().is_none_or(|names| names.contains(&function.name))
                        {
                            std::fs::create_dir_all(dir).unwrap();
                            let query = trust_cg_verify::ay_bridge::generate_smt2_query_raw(
                                body.obligation(),
                                &config,
                            );
                            std::fs::write(
                                std::path::Path::new(dir).join(format!(
                                    "{}.smt2",
                                    &function.name[..function.name.len().min(200)]
                                )),
                                query,
                            )
                            .unwrap();
                        }
                        ("OWNER".to_owned(), body.bound_rows().len())
                    }
                    Err(refusal) => (refusal.to_string().replace('\t', " "), 0),
                },
            };
            writeln!(out, "{}\t{verdict}\t{rows}\t{through_memory}", function.name).unwrap();
        }
    }
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    if args.get(1).is_some_and(|arg| arg == "--census") {
        census(&args);
        return;
    }
    let bytes = std::fs::read(&args[1]).expect("module");
    let filter = args.get(2).cloned().unwrap_or_default();
    let smt = args.iter().any(|a| a == "--smt");
    let module = trust_ir::binary::deserialize_module(&bytes).expect("deserialize");
    let lir = trust_cg_lower::translate_module_for_arch(
        &module,
        trust_cg_lower::GuardCarrierArch::X86_64,
    )
    .expect("translate");
    for (function, _) in lir {
        if !function.name.contains(&filter) {
            continue;
        }
        println!("==== {}", function.name);
        println!(
            "sig {:?} -> {:?}; sret={:?}; sret_arg_callees={:?}; slots={:?}",
            function.signature.params,
            function.signature.returns,
            function.abi_sret_param,
            function.sret_arg_callees,
            function
                .stack_slots
                .iter()
                .map(|s| s.size)
                .collect::<Vec<_>>()
        );
        for block in function.layout_order() {
            let body = &function.blocks[&block];
            println!("  {block:?} params {:?}", body.params);
            for inst in &body.instructions {
                println!("    {:?} = {:?} {:?}", inst.results, inst.opcode, inst.args);
            }
        }
        let mut value_types: Vec<_> = function.value_types.iter().collect();
        value_types.sort_by_key(|(v, _)| v.0);
        println!("  value_types {value_types:?}");
        let machine = match select(&function) {
            Ok(machine) => machine,
            Err(error) => {
                println!("  SELECT ERROR {error}");
                continue;
            }
        };
        let mut ordinal = 0;
        for block in &machine.block_order {
            println!("  M{block:?} succ {:?}", machine.blocks[block].successors);
            for inst in &machine.blocks[block].insts {
                println!(
                    "    {ordinal:3} {:?} {:?} args={:?} results={:?}",
                    inst.opcode, inst.operands, inst.call_arg_regs, inst.call_result_regs
                );
                ordinal += 1;
            }
        }
        match source_bound_x86_body(&function, &machine, Some(X86SourceBoundAbi::SystemV)) {
            Ok(body) => {
                println!("  BODY OK bound rows {}", body.bound_rows().len());
                if smt {
                    let o = body.obligation();
                    for p in o.preconditions.iter().rev() {
                        println!("    pre {p}");
                    }
                    println!("    src {}", o.trust_ir_expr);
                    println!("    mach {}", o.aarch64_expr);
                }
            }
            Err(refusal) => println!("  BODY {refusal}"),
        }
    }
}
