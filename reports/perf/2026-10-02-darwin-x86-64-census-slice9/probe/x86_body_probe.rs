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
//!        x86_body_probe --cf <dump dir> <out.tsv> [<smt2 dir>] [<names>]
//!
//! Slice 9 adds `--cf`: per function, the verdict and the control-flow
//! shape (LIR blocks, a loop, entry-to-end paths, the longest path and all
//! instructions, machine blocks and rows), the sampled check of a built
//! theorem, and its query when an SMT-LIB directory is given.

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
                            && names
                                .as_ref()
                                .is_none_or(|names| names.contains(&function.name))
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
            writeln!(
                out,
                "{}\t{verdict}\t{rows}\t{through_memory}",
                function.name
            )
            .unwrap();
        }
    }
}

/// Whether the theorem's two sides agree at `samples` sampled assignments of
/// its free inputs (premises evaluated in order): random words, small
/// values, and every input 0 except one byte boundary, so zero tags beside
/// nonzero payloads occur. Diagnostic only, never credit: `Some(seed)` is the
/// first sample that refutes it.
fn refuting_sample(
    obligation: &trust_cg_verify::lowering_proof::ProofObligation,
    samples: u64,
) -> Option<u64> {
    use trust_cg_verify::smt::{EvalEnv, EvalResult, SmtExpr as E};
    let defined: std::collections::HashSet<String> = obligation
        .preconditions
        .iter()
        .filter_map(|premise| match premise {
            E::Eq { lhs, .. } => match lhs.as_ref() {
                E::Var { name, .. } => Some(name.clone()),
                _ => None,
            },
            _ => None,
        })
        .collect();
    for seed in 0..samples {
        let mut env = EvalEnv::default();
        let mut state = seed.wrapping_mul(0x9e37_79b9_7f4a_7c15).wrapping_add(17);
        for (index, (name, width)) in obligation.inputs.iter().enumerate() {
            if defined.contains(name) {
                continue;
            }
            state = state
                .wrapping_mul(6_364_136_223_846_793_005)
                .wrapping_add(1_442_695_040_888_963_407);
            let value = match seed % 5 {
                0 => state ^ (state >> 29),
                1 => (state >> 33) % 7,
                2 => 0,
                3 if (index as u64) == (seed / 5) % (obligation.inputs.len() as u64).max(1) => {
                    state
                }
                3 => 0,
                _ => (state >> 17) & 0x1ff,
            };
            let masked = if *width >= 64 {
                value
            } else {
                value & ((1u64 << width) - 1)
            };
            env.insert(name.clone(), masked);
        }
        for premise in obligation.preconditions.iter().rev() {
            let E::Eq { lhs, rhs } = premise else {
                return Some(u64::MAX);
            };
            let E::Var { name, .. } = lhs.as_ref() else {
                return Some(u64::MAX);
            };
            let EvalResult::Bv(value) = rhs.eval(&env) else {
                return Some(u64::MAX);
            };
            env.insert(name.clone(), value);
        }
        if obligation.trust_ir_expr.eval(&env) != obligation.aarch64_expr.eval(&env) {
            return Some(seed);
        }
    }
    None
}

/// `--clean <in.trust_irbin> <out.trust_irbin>`: the module with the body of
/// every function the current adapter refuses dropped, written once so later
/// probes translate it in one pass.
fn clean(args: &[String]) {
    let mut module =
        trust_ir::binary::deserialize_module(&std::fs::read(&args[2]).unwrap()).unwrap();
    for _ in 0..4096 {
        match trust_cg_lower::translate_module_for_arch(
            &module,
            trust_cg_lower::GuardCarrierArch::X86_64,
        ) {
            Ok(_) => break,
            Err(error) => {
                let text = format!("{error:?}");
                let name = text.split("fn ").nth(1).unwrap().split(':').next().unwrap();
                let function = module
                    .functions
                    .iter_mut()
                    .find(|f| f.name == name)
                    .unwrap();
                assert!(!function.blocks.is_empty(), "{text}");
                eprintln!("dropped {name}");
                function.blocks.clear();
            }
        }
    }
    std::fs::write(&args[3], trust_ir::binary::serialize_module(&module)).unwrap();
}

/// Translate `module`, dropping the body of every function the current
/// adapter refuses by name (a dump made before a trust-ir pin move), so the
/// rest of the module can still be judged. The dropped names go to stderr.
fn translate_dropping_refused(
    mut module: trust_ir::Module,
) -> Option<Vec<(Function, trust_cg_lower::adapter::ProofContext)>> {
    // The bridge's private copies are hidden definitions, which only the
    // Mach-O module path admits; the generic entry the probe uses refuses
    // them. Visibility does not change a body.
    for function in &mut module.functions {
        function.visibility = trust_ir::Visibility::Default;
    }
    for _ in 0..4096 {
        match trust_cg_lower::translate_module_for_arch(
            &module,
            trust_cg_lower::GuardCarrierArch::X86_64,
        ) {
            Ok(lir) => return Some(lir),
            Err(error) => {
                let text = format!("{error:?}");
                let Some(name) = text
                    .split("fn ")
                    .nth(1)
                    .and_then(|rest| rest.split(':').next())
                    .map(str::to_owned)
                else {
                    eprintln!("untranslatable: {}", &text[..text.len().min(400)]);
                    return None;
                };
                let Some(function) = module.functions.iter_mut().find(|f| f.name == name) else {
                    eprintln!(
                        "untranslatable (no function {name}): {}",
                        &text[..text.len().min(400)]
                    );
                    return None;
                };
                if function.blocks.is_empty() {
                    eprintln!(
                        "untranslatable (already dropped {name}): {}",
                        &text[..text.len().min(400)]
                    );
                    return None;
                }
                eprintln!("dropped {name}");
                function.blocks.clear();
            }
        }
    }
    None
}

/// `--sig <dump dir> <out.tsv>`: every function (first definition of a name
/// wins), one TSV row each: name, verdict, LIR params, LIR returns, sret
/// param, and the non-scalar call results (callee and result value types).
fn sig_census(args: &[String]) {
    use std::io::Write as _;
    let dir = &args[2];
    let mut out = std::fs::File::create(&args[3]).expect("out.tsv");
    let mut files: Vec<_> = std::fs::read_dir(dir)
        .expect("dump dir")
        .filter_map(|entry| entry.ok().map(|entry| entry.path()))
        .filter(|path| path.extension().is_some_and(|ext| ext == "trust_irbin"))
        .collect();
    files.sort();
    let mut seen = std::collections::HashSet::new();
    let scalar = |ty: &trust_cg_lower::Type| {
        matches!(
            ty,
            trust_cg_lower::Type::B1
                | trust_cg_lower::Type::I8
                | trust_cg_lower::Type::I16
                | trust_cg_lower::Type::I32
                | trust_cg_lower::Type::I64
        )
    };
    for file in files {
        let Ok(module) = trust_ir::binary::deserialize_module(&std::fs::read(&file).unwrap())
        else {
            continue;
        };
        let Some(lir) = translate_dropping_refused(module) else {
            eprintln!("untranslatable {}", file.display());
            continue;
        };
        for (function, _) in lir {
            if !seen.insert(function.name.clone()) {
                continue;
            }
            let mut call_results = Vec::new();
            for block in function.layout_order() {
                for inst in &function.blocks[&block].instructions {
                    if let trust_cg_lower::instructions::Opcode::Call { name, .. } = &inst.opcode {
                        let tys: Vec<_> = inst
                            .results
                            .iter()
                            .map(|r| function.value_types.get(r).cloned())
                            .collect();
                        if tys.iter().any(|t| t.as_ref().is_none_or(|t| !scalar(t))) {
                            call_results.push(format!("{name}:{tys:?}"));
                        }
                    }
                }
            }
            let verdict = match select(&function) {
                Err(error) => format!("SELECT {}", error.replace(['\t', '\n'], " ")),
                Ok(machine) => match source_bound_x86_body(
                    &function,
                    &machine,
                    Some(X86SourceBoundAbi::SystemV),
                ) {
                    Ok(body) => match refuting_sample(body.obligation(), 2000) {
                        None => format!("OWNER {}", body.bound_rows().len()),
                        Some(seed) => {
                            format!("OWNER {} REFUTED-AT-SAMPLE {seed}", body.bound_rows().len())
                        }
                    },
                    Err(refusal) => refusal.to_string().replace(['\t', '\n'], " "),
                },
            };
            writeln!(
                out,
                "{}\t{verdict}\t{:?}\t{:?}\t{:?}\t{}",
                function.name,
                function.signature.params,
                function.signature.returns,
                function.abi_sret_param,
                call_results.join(" | ")
            )
            .unwrap();
        }
    }
}

/// The control-flow shape of a LIR function: blocks, whether a back edge
/// exists, entry-to-end paths (saturating), the longest path and all
/// instructions.
fn cf_shape(function: &Function) -> (usize, bool, u128, usize, usize) {
    use std::collections::HashMap;
    use trust_cg_lower::instructions::{Block, Opcode};
    let successors: HashMap<Block, Vec<Block>> = function
        .blocks
        .iter()
        .map(|(id, block)| {
            let targets = match block.instructions.last().map(|inst| &inst.opcode) {
                Some(Opcode::Jump { dest }) => vec![*dest],
                Some(Opcode::Brif {
                    then_dest,
                    else_dest,
                    ..
                }) => vec![*then_dest, *else_dest],
                Some(Opcode::Switch { cases, default }) => cases
                    .iter()
                    .map(|(_, target)| *target)
                    .chain(std::iter::once(*default))
                    .collect(),
                _ => Vec::new(),
            };
            (*id, targets)
        })
        .collect();
    let mut colour: HashMap<Block, u8> = HashMap::new();
    let mut postorder = Vec::new();
    let mut looped = false;
    let mut stack = vec![(function.entry_block, 0usize)];
    colour.insert(function.entry_block, 1);
    while let Some((block, next)) = stack.pop() {
        let targets = successors.get(&block).cloned().unwrap_or_default();
        match targets.get(next) {
            None => {
                colour.insert(block, 2);
                postorder.push(block);
            }
            Some(target) => {
                stack.push((block, next + 1));
                match colour.get(target) {
                    Some(1) => looped = true,
                    Some(_) => {}
                    None if successors.contains_key(target) => {
                        colour.insert(*target, 1);
                        stack.push((*target, 0));
                    }
                    None => {}
                }
            }
        }
    }
    let instructions: usize = function
        .blocks
        .values()
        .map(|block| block.instructions.len())
        .sum();
    if looped {
        return (function.blocks.len(), true, 0, 0, instructions);
    }
    let mut counts: HashMap<Block, (u128, usize)> = HashMap::new();
    for block in &postorder {
        let length = function.blocks[block].instructions.len();
        let mut paths = 0u128;
        let mut longest = 0usize;
        for target in &successors[block] {
            if let Some((p, l)) = counts.get(target) {
                paths = paths.saturating_add(*p);
                longest = longest.max(*l);
            }
        }
        if successors[block].is_empty() {
            paths = 1;
        }
        counts.insert(*block, (paths, length + longest));
    }
    let (paths, longest) = counts.get(&function.entry_block).copied().unwrap_or((0, 0));
    (function.blocks.len(), false, paths, longest, instructions)
}

/// `--cf <dump dir> <out.tsv> [<smt2 dir>] [<names file>]`: every function
/// of every dumped module (first definition of a name wins), one TSV row
/// each: name, verdict (`OWNER <bound rows>`, with `REFUTED-AT-SAMPLE` when
/// the sampler refutes it, or the refusal), LIR blocks, loop, paths, the
/// longest path, instructions, machine blocks, machine rows; with an SMT-LIB
/// directory, each built theorem's query, restricted to the names file's
/// functions when one is given.
fn cf_census(args: &[String]) {
    use std::io::Write as _;
    let dir = &args[2];
    let mut out = std::fs::File::create(&args[3]).expect("out.tsv");
    let smt2_dir = args.get(4).filter(|dir| !dir.is_empty());
    let names: Option<std::collections::HashSet<String>> = args.get(5).map(|path| {
        std::fs::read_to_string(path)
            .expect("names")
            .lines()
            .map(|line| line.split('\t').next().unwrap_or_default().to_owned())
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
        let Some(lir) = translate_dropping_refused(module) else {
            eprintln!("untranslatable {}", file.display());
            continue;
        };
        for (function, _) in lir {
            if !seen.insert(function.name.clone()) {
                continue;
            }
            let (blocks, looped, paths, longest, instructions) = cf_shape(&function);
            let (verdict, machine_blocks, machine_rows) = match select(&function) {
                Err(error) => (format!("SELECT {}", error.replace(['\t', '\n'], " ")), 0, 0),
                Ok(machine) => {
                    let rows: usize = machine.blocks.values().map(|b| b.insts.len()).sum();
                    let verdict = match source_bound_x86_body(
                        &function,
                        &machine,
                        Some(X86SourceBoundAbi::SystemV),
                    ) {
                        Ok(body) => {
                            if let Some(dir) = smt2_dir
                                && names
                                    .as_ref()
                                    .is_none_or(|names| names.contains(&function.name))
                            {
                                std::fs::create_dir_all(dir).unwrap();
                                let query = trust_cg_verify::ay_bridge::generate_smt2_query_raw(
                                    body.obligation(),
                                    &config,
                                );
                                // Long symbols share long prefixes: name the
                                // file by a hash of the whole name (the
                                // `.names` file maps it back).
                                let hash = function
                                    .name
                                    .bytes()
                                    .fold(0xcbf2_9ce4_8422_2325u64, |h, b| {
                                        (h ^ u64::from(b)).wrapping_mul(0x0100_0000_01b3)
                                    });
                                let file = format!("{hash:016x}");
                                std::fs::write(
                                    std::path::Path::new(dir).join(format!("{file}.smt2")),
                                    query,
                                )
                                .unwrap();
                                use std::io::Write as _;
                                let mut index = std::fs::OpenOptions::new()
                                    .create(true)
                                    .append(true)
                                    .open(std::path::Path::new(dir).join("index.tsv"))
                                    .unwrap();
                                writeln!(index, "{file}\t{}", function.name).unwrap();
                            }
                            match refuting_sample(body.obligation(), 600) {
                                None => format!(
                                    "OWNER {} defs={}",
                                    body.bound_rows().len(),
                                    body.obligation().preconditions.len()
                                ),
                                Some(seed) => format!(
                                    "OWNER {} REFUTED-AT-SAMPLE {seed}",
                                    body.bound_rows().len()
                                ),
                            }
                        }
                        Err(refusal) => refusal.to_string().replace(['\t', '\n'], " "),
                    };
                    (verdict, machine.blocks.len(), rows)
                }
            };
            writeln!(
                out,
                "{}\t{verdict}\t{blocks}\t{looped}\t{paths}\t{longest}\t{instructions}\t{machine_blocks}\t{machine_rows}",
                function.name
            )
            .unwrap();
        }
    }
}

fn main() {
    // The verifier runs the body theorem on a large stack
    // (`resource_limits::run_on_proof_verifier_stack`); the probe runs
    // everything on a larger one still, so a deep theorem is measured, not
    // a crash.
    std::thread::Builder::new()
        .stack_size(512 << 20)
        .spawn(probe_main)
        .unwrap()
        .join()
        .unwrap();
}

fn probe_main() {
    let args: Vec<String> = std::env::args().collect();
    if args.get(1).is_some_and(|arg| arg == "--cf") {
        cf_census(&args);
        return;
    }
    if args.get(1).is_some_and(|arg| arg == "--census") {
        census(&args);
        return;
    }
    if args.get(1).is_some_and(|arg| arg == "--sig") {
        sig_census(&args);
        return;
    }
    if args.get(1).is_some_and(|arg| arg == "--clean") {
        clean(&args);
        return;
    }
    // `--tir <module> <name filter>`: the trust-ir text of each function
    // whose name contains the filter.
    if args.get(1).is_some_and(|arg| arg == "--tir") {
        let module =
            trust_ir::binary::deserialize_module(&std::fs::read(&args[2]).unwrap()).unwrap();
        for function in &module.functions {
            if function.name.contains(&args[3]) {
                println!("{function}");
            }
        }
        return;
    }
    let bytes = std::fs::read(&args[1]).expect("module");
    let filter = args.get(2).cloned().unwrap_or_default();
    let smt = args.iter().any(|a| a == "--smt");
    let module = trust_ir::binary::deserialize_module(&bytes).expect("deserialize");
    let lir = translate_dropping_refused(module).expect("translate");
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
