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

/// The loop structure of a LIR function (slice 12): successors, dominators,
/// back edges and natural loops, from the LIR alone.
struct LoopProfile {
    blocks: usize,
    instructions: usize,
    reducible: bool,
    /// Each loop header: its natural loop's blocks (merged over its back
    /// edges), its back-edge sources, and its exit edges.
    loops: Vec<(
        trust_cg_lower::instructions::Block,
        std::collections::BTreeSet<trust_cg_lower::instructions::Block>,
        Vec<trust_cg_lower::instructions::Block>,
        usize,
    )>,
    max_depth: usize,
}

fn lir_successors(
    function: &Function,
) -> std::collections::HashMap<
    trust_cg_lower::instructions::Block,
    Vec<trust_cg_lower::instructions::Block>,
> {
    use trust_cg_lower::instructions::Opcode;
    function
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
        .collect()
}

fn loop_profile(function: &Function) -> LoopProfile {
    use std::collections::{BTreeSet, HashMap, HashSet};
    use trust_cg_lower::instructions::Block;
    let successors = lir_successors(function);
    // Reverse postorder from the entry; retreating edges by DFS colour.
    let mut colour: HashMap<Block, u8> = HashMap::new();
    let mut postorder = Vec::new();
    let mut retreating: Vec<(Block, Block)> = Vec::new();
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
                    Some(1) => retreating.push((block, *target)),
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
    let rpo: Vec<Block> = postorder.iter().rev().copied().collect();
    let index: HashMap<Block, usize> = rpo.iter().enumerate().map(|(i, b)| (*b, i)).collect();
    let mut predecessors: HashMap<Block, Vec<Block>> = HashMap::new();
    for block in &rpo {
        for target in &successors[block] {
            predecessors.entry(*target).or_default().push(*block);
        }
    }
    // Cooper-Harvey-Kennedy dominators.
    let mut idom: HashMap<Block, Block> = HashMap::new();
    idom.insert(function.entry_block, function.entry_block);
    let mut changed = true;
    while changed {
        changed = false;
        for block in rpo.iter().skip(1) {
            let mut new: Option<Block> = None;
            for pred in predecessors.get(block).cloned().unwrap_or_default() {
                if !idom.contains_key(&pred) {
                    continue;
                }
                new = Some(match new {
                    None => pred,
                    Some(mut a) => {
                        let mut b = pred;
                        while a != b {
                            while index[&a] > index[&b] {
                                a = idom[&a];
                            }
                            while index[&b] > index[&a] {
                                b = idom[&b];
                            }
                        }
                        a
                    }
                });
            }
            if let Some(new) = new
                && idom.get(block) != Some(&new)
            {
                idom.insert(*block, new);
                changed = true;
            }
        }
    }
    let dominates = |a: Block, mut b: Block| loop {
        if a == b {
            return true;
        }
        let up = idom[&b];
        if up == b {
            return false;
        }
        b = up;
    };
    let reducible = retreating.iter().all(|(from, to)| dominates(*to, *from));
    let mut loops: HashMap<Block, (BTreeSet<Block>, Vec<Block>)> = HashMap::new();
    for (latch, header) in &retreating {
        let entry = loops.entry(*header).or_default();
        entry.1.push(*latch);
        entry.0.insert(*header);
        let mut work = vec![*latch];
        while let Some(block) = work.pop() {
            if entry.0.insert(block) {
                work.extend(predecessors.get(&block).cloned().unwrap_or_default());
            }
        }
    }
    let mut loops: Vec<(Block, BTreeSet<Block>, Vec<Block>, usize)> = loops
        .into_iter()
        .map(|(header, (body, latches))| {
            let exits = body
                .iter()
                .flat_map(|block| successors[block].iter())
                .filter(|target| !body.contains(target))
                .count();
            (header, body, latches, exits)
        })
        .collect();
    loops.sort_by_key(|(header, ..)| index.get(header).copied().unwrap_or(usize::MAX));
    let max_depth = rpo
        .iter()
        .map(|block| {
            loops
                .iter()
                .filter(|(_, body, ..)| body.contains(block))
                .count()
        })
        .max()
        .unwrap_or(0);
    let _ = HashSet::<Block>::new();
    LoopProfile {
        blocks: function.blocks.len(),
        instructions: function.blocks.values().map(|b| b.instructions.len()).sum(),
        reducible,
        loops,
        max_depth,
    }
}

/// `--loops <dump dir> <names file> <out.tsv>` (slice 12): for each named
/// function, its current verdict and its loop profile: blocks, LIR
/// instructions, reducibility, loops and nesting depth, and per loop its
/// blocks, back edges, exits, header parameters (types), calls, incoming
/// and private loads and stores, the header parameters updated by a
/// constant step, and the opcodes it runs; machine blocks and rows, and
/// whether the TV-1 provenance gives the one-to-one block correspondence.
fn loops_census(args: &[String]) {
    use std::collections::{BTreeMap, HashMap, HashSet};
    use std::io::Write as _;
    use trust_cg_lower::instructions::{Opcode, Value};
    let dir = &args[2];
    let names: HashSet<String> = std::fs::read_to_string(&args[3])
        .expect("names")
        .lines()
        .map(str::to_owned)
        .collect();
    let mut out = std::fs::File::create(&args[4]).expect("out.tsv");
    let mut files: Vec<_> = std::fs::read_dir(dir)
        .expect("dump dir")
        .filter_map(|entry| entry.ok().map(|entry| entry.path()))
        .filter(|path| path.extension().is_some_and(|ext| ext == "trust_irbin"))
        .collect();
    files.sort();
    let mut seen = HashSet::new();
    for file in files {
        let Ok(module) = trust_ir::binary::deserialize_module(&std::fs::read(&file).unwrap())
        else {
            eprintln!("undecodable {}", file.display());
            continue;
        };
        if !module.functions.iter().any(|f| names.contains(&f.name)) {
            continue;
        }
        let Some(lir) = translate_dropping_refused(module) else {
            eprintln!("untranslatable {}", file.display());
            continue;
        };
        for (function, _) in lir {
            if !names.contains(&function.name) || !seen.insert(function.name.clone()) {
                continue;
            }
            let profile = loop_profile(&function);
            // Values derived from a private stack address (StackAddr, then
            // Copy/Iadd/StructGep/Bitcast of one), over the whole function.
            let mut frame: HashSet<Value> = HashSet::new();
            let mut changed = true;
            while changed {
                changed = false;
                for block in function.blocks.values() {
                    for inst in &block.instructions {
                        let derived = match &inst.opcode {
                            Opcode::StackAddr { .. } => true,
                            Opcode::Copy
                            | Opcode::Bitcast { .. }
                            | Opcode::StructGep { .. }
                            | Opcode::Iadd => inst.args.iter().any(|a| frame.contains(a)),
                            _ => false,
                        };
                        if derived {
                            for result in &inst.results {
                                changed |= frame.insert(*result);
                            }
                        }
                    }
                }
            }
            let short = |opcode: &Opcode| {
                let text = format!("{opcode:?}");
                text.split([' ', '{', '('])
                    .next()
                    .unwrap_or_default()
                    .to_owned()
            };
            let mut per_loop = Vec::new();
            for (header, body, latches, exits) in &profile.loops {
                let params: Vec<String> = function.blocks[header]
                    .params
                    .iter()
                    .map(|(_, ty)| format!("{ty:?}"))
                    .collect();
                let (mut calls, mut incoming, mut private) = (0, 0, 0);
                let mut opcodes: BTreeMap<String, usize> = BTreeMap::new();
                // Header parameters a block of the loop redefines by `p +/- k`.
                let header_params: HashSet<Value> = function.blocks[header]
                    .params
                    .iter()
                    .map(|(v, _)| *v)
                    .collect();
                let mut defs: HashMap<Value, (Opcode, Vec<Value>)> = HashMap::new();
                for block in body {
                    for inst in &function.blocks[block].instructions {
                        for result in &inst.results {
                            defs.insert(*result, (inst.opcode.clone(), inst.args.clone()));
                        }
                    }
                }
                let mut stepped = 0;
                for param in &header_params {
                    // The latch's copy into the parameter, then its source.
                    let mut cursor = *param;
                    for _ in 0..4 {
                        match defs.get(&cursor) {
                            Some((Opcode::Copy, args)) if args.len() == 1 => cursor = args[0],
                            Some((Opcode::Iadd | Opcode::Isub, args)) if args.contains(param) => {
                                stepped += 1;
                                break;
                            }
                            _ => break,
                        }
                    }
                }
                for block in body {
                    for inst in &function.blocks[block].instructions {
                        *opcodes.entry(short(&inst.opcode)).or_default() += 1;
                        match &inst.opcode {
                            Opcode::Call { .. } | Opcode::CallIndirect => calls += 1,
                            Opcode::Load { .. } => {
                                if frame.contains(&inst.args[0]) {
                                    private += 1;
                                } else {
                                    incoming += 1;
                                }
                            }
                            Opcode::Store { .. } => {
                                if frame.contains(&inst.args[1]) {
                                    private += 1;
                                } else {
                                    incoming += 1;
                                }
                            }
                            _ => {}
                        }
                    }
                }
                let ops: Vec<String> = opcodes
                    .iter()
                    .map(|(name, count)| format!("{name}:{count}"))
                    .collect();
                per_loop.push(format!(
                    "h{}[blocks={} latches={} exits={} params=({}) stepped={} calls={} incoming={} private={} ops={}]",
                    header.0,
                    body.len(),
                    latches.len(),
                    exits,
                    params.join(","),
                    stepped,
                    calls,
                    incoming,
                    private,
                    ops.join(",")
                ));
            }
            let (verdict, machine_blocks, machine_rows, correspondence) = match select(&function) {
                Err(error) => (
                    format!("SELECT {}", error.replace(['\t', '\n'], " ")),
                    0,
                    0,
                    false,
                ),
                Ok(machine) => {
                    let rows: usize = machine.blocks.values().map(|b| b.insts.len()).sum();
                    // TV-1 provenance: each laid-out block lowers one LIR block,
                    // one to one, every LIR block lowered.
                    let mut lowered: HashMap<u32, usize> = HashMap::new();
                    let mut ok = true;
                    for block in &machine.block_order {
                        let named: std::collections::BTreeSet<u32> = machine.blocks[block]
                            .insts
                            .iter()
                            .filter_map(|inst| inst.lowering_provenance.source_id())
                            .map(|id| id.block)
                            .collect();
                        if named.len() != 1 {
                            ok = false;
                            continue;
                        }
                        *lowered.entry(*named.iter().next().unwrap()).or_default() += 1;
                    }
                    ok &= lowered.len() == function.blocks.len()
                        && lowered.values().all(|count| *count == 1);
                    let verdict = match source_bound_x86_body(
                        &function,
                        &machine,
                        Some(X86SourceBoundAbi::SystemV),
                    ) {
                        Ok(body) => match refuting_sample(body.obligation(), 600) {
                            None => format!(
                                "OWNER {} defs={}",
                                body.bound_rows().len(),
                                body.obligation().preconditions.len()
                            ),
                            Some(seed) => format!(
                                "OWNER {} REFUTED-AT-SAMPLE {seed}",
                                body.bound_rows().len()
                            ),
                        },
                        Err(refusal) => refusal.to_string().replace(['\t', '\n'], " "),
                    };
                    (verdict, machine.blocks.len(), rows, ok)
                }
            };
            writeln!(
                out,
                "{}\t{verdict}\t{}\t{}\t{}\t{}\t{}\t{machine_blocks}\t{machine_rows}\t{correspondence}\t{}",
                function.name,
                profile.blocks,
                profile.instructions,
                profile.reducible,
                profile.loops.len(),
                profile.max_depth,
                per_loop.join(" ")
            )
            .unwrap();
        }
    }
}

/// Slice 14: `--dump <dump dir> <names file> <out dir>`: for each named
/// function (first definition of a name wins), its LIR, its pre-RA machine
/// rows and tables, the owner's verdict and which machine-function cause of
/// the slice-1..13 "constant pool, jump tables, EH, guard obligations or an
/// outgoing call area" refusal it hits; one summary row per function in
/// `<out dir>/summary.tsv`.
fn dump_named(args: &[String]) {
    use std::fmt::Write as _;
    use std::io::Write as _;
    let dir = &args[2];
    let names: std::collections::HashSet<String> = std::fs::read_to_string(&args[3])
        .expect("names")
        .lines()
        .map(|line| line.split('\t').next().unwrap_or_default().to_owned())
        .filter(|line| !line.is_empty())
        .collect();
    let out = std::path::Path::new(&args[4]);
    std::fs::create_dir_all(out).unwrap();
    let mut summary = std::fs::File::create(out.join("summary.tsv")).unwrap();
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
            continue;
        };
        if !module.functions.iter().any(|f| names.contains(&f.name)) {
            continue;
        }
        let Some(lir) = translate_dropping_refused(module) else {
            continue;
        };
        for (function, _) in lir {
            if !names.contains(&function.name) || !seen.insert(function.name.clone()) {
                continue;
            }
            let mut text = String::new();
            writeln!(text, "==== {}", function.name).unwrap();
            writeln!(
                text,
                "sig {:?} -> {:?}; sret={:?}; slots={:?}",
                function.signature.params,
                function.signature.returns,
                function.abi_sret_param,
                function
                    .stack_slots
                    .iter()
                    .map(|s| s.size)
                    .collect::<Vec<_>>()
            )
            .unwrap();
            for block in function.layout_order() {
                let body = &function.blocks[&block];
                writeln!(text, "  {block:?} params {:?}", body.params).unwrap();
                for inst in &body.instructions {
                    writeln!(
                        text,
                        "    {:?} = {:?} {:?}",
                        inst.results, inst.opcode, inst.args
                    )
                    .unwrap();
                }
            }
            let (verdict, causes) = match select(&function) {
                Err(error) => (format!("SELECT {error}"), String::new()),
                Ok(machine) => {
                    let mut ordinal = 0;
                    for block in &machine.block_order {
                        writeln!(
                            text,
                            "  M{block:?} succ {:?}",
                            machine.blocks[block].successors
                        )
                        .unwrap();
                        for inst in &machine.blocks[block].insts {
                            writeln!(
                                text,
                                "    {ordinal:3} {:?} {:?} args={:?} results={:?} src={:?}",
                                inst.opcode,
                                inst.operands,
                                inst.call_arg_regs,
                                inst.call_result_regs,
                                inst.lowering_provenance.source_id()
                            )
                            .unwrap();
                            ordinal += 1;
                        }
                    }
                    for (i, table) in machine.jump_tables.iter().enumerate() {
                        writeln!(
                            text,
                            "  JT{i} min={} targets={:?}",
                            table.min_val, table.targets
                        )
                        .unwrap();
                    }
                    for (i, entry) in machine.const_pool_entries.iter().enumerate() {
                        writeln!(text, "  CP{i} {:02x?} align {}", entry.data, entry.align)
                            .unwrap();
                    }
                    let mut causes = Vec::new();
                    if !machine.jump_tables.is_empty() {
                        causes.push(format!("jump_tables={}", machine.jump_tables.len()));
                    }
                    if !machine.eh_info.is_empty() {
                        causes.push("eh".to_owned());
                    }
                    if !machine.guard_obligations.is_empty() {
                        causes.push(format!(
                            "guard_obligations={}",
                            machine.guard_obligations.len()
                        ));
                    }
                    if machine.max_outgoing_call_bytes != 0 {
                        causes.push(format!("outgoing={}", machine.max_outgoing_call_bytes));
                    }
                    let pool_rows: Vec<String> = machine
                        .blocks
                        .values()
                        .flat_map(|b| b.insts.iter())
                        .filter(|inst| {
                            inst.operands.iter().any(|o| {
                                matches!(
                                    o,
                                    trust_cg_lower::x86_64_isel::X86ISelOperand::ConstPoolEntry(_)
                                )
                            })
                        })
                        .map(|inst| format!("{:?}", inst.opcode))
                        .collect();
                    if !pool_rows.is_empty() {
                        causes.push(format!("const_pool_rows={}", pool_rows.join("+")));
                    }
                    let verdict = match source_bound_x86_body(
                        &function,
                        &machine,
                        Some(X86SourceBoundAbi::SystemV),
                    ) {
                        Ok(body) => {
                            let hash = function
                                .name
                                .bytes()
                                .fold(0xcbf2_9ce4_8422_2325u64, |h, b| {
                                    (h ^ u64::from(b)).wrapping_mul(0x0100_0000_01b3)
                                });
                            let config = trust_cg_verify::ay_bridge::AYConfig {
                                solver: None,
                                timeout_ms: 30_000,
                                produce_models: true,
                            };
                            let query = trust_cg_verify::ay_bridge::generate_smt2_query_raw(
                                body.obligation(),
                                &config,
                            );
                            std::fs::create_dir_all(out.join("smt2")).unwrap();
                            std::fs::write(
                                out.join("smt2").join(format!("{hash:016x}.smt2")),
                                query,
                            )
                            .unwrap();
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
                        Err(refusal) => refusal.to_string(),
                    };
                    (verdict, causes.join(","))
                }
            };
            writeln!(text, "  VERDICT {verdict}").unwrap();
            writeln!(text, "  CAUSES {causes}").unwrap();
            let hash = function
                .name
                .bytes()
                .fold(0xcbf2_9ce4_8422_2325u64, |h, b| {
                    (h ^ u64::from(b)).wrapping_mul(0x0100_0000_01b3)
                });
            std::fs::write(out.join(format!("{hash:016x}.txt")), text).unwrap();
            writeln!(
                summary,
                "{}\t{hash:016x}\t{}\t{}",
                function.name,
                verdict.replace(['\t', '\n'], " "),
                causes
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
    if args.get(1).is_some_and(|arg| arg == "--dump") {
        dump_named(&args);
        return;
    }
    if args.get(1).is_some_and(|arg| arg == "--cf") {
        cf_census(&args);
        return;
    }
    if args.get(1).is_some_and(|arg| arg == "--loops") {
        loops_census(&args);
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
