// Offline analysis probe used for the slice-6 design and encoding choice
// (a copy kept with the report; it is not compiled in the crate). To run it,
// register it as a submodule of `x86_source_bound_body_tests.rs`
// (`#[path = "x86_source_bound_body_census_probe.rs"] mod census_probe;`)
// and see `probe.sh`. It translates every function of a dumped `core`
// trust-ir module set (`-Ztrust-ir-cg-args=dump-trust-ir=DIR`, O0), selects
// it with the real x86-64 selector, runs the slice-6 owner, and writes one
// TSV row per function (CFG class, admission, refusal or `OWNER`); with
// TCG_PROBE_SMT2=DIR it also writes each built theorem's SMT-LIB query, which
// `replay_dir.py` replays on AY and Clean.

use super::*;
use std::collections::BTreeMap;
use std::io::Write as _;

fn load_functions() -> Vec<Function> {
    let dir = std::env::var("TCG_PROBE_DUMP").expect("TCG_PROBE_DUMP");
    let mut files: Vec<_> = std::fs::read_dir(&dir)
        .unwrap()
        .filter_map(|entry| entry.ok().map(|e| e.path()))
        .filter(|path| path.extension().is_some_and(|ext| ext == "trust_irbin"))
        .collect();
    files.sort();
    let mut out = Vec::new();
    let mut seen = HashSet::new();
    for file in files {
        let bytes = std::fs::read(&file).unwrap();
        let Ok(module) = trust_ir::binary::deserialize_module(&bytes) else {
            eprintln!("PROBE undecodable {}", file.display());
            continue;
        };
        match trust_cg_lower::translate_module_for_arch(
            &module,
            trust_cg_lower::GuardCarrierArch::X86_64,
        ) {
            Ok(functions) => {
                for (function, _) in functions {
                    if seen.insert(function.name.clone()) {
                        out.push(function);
                    }
                }
            }
            Err(error) => eprintln!("PROBE untranslatable {}: {error:?}", file.display()),
        }
    }
    out
}

fn opcode_name(opcode: &L) -> String {
    format!("{opcode:?}")
        .split([' ', '{', '('])
        .next()
        .unwrap_or_default()
        .to_owned()
}

fn successors(inst: &trust_cg_lower::instructions::Instruction) -> Vec<Block> {
    match &inst.opcode {
        L::Jump { dest } => vec![*dest],
        L::Brif {
            then_dest,
            else_dest,
            ..
        } => vec![*then_dest, *else_dest],
        L::Switch { cases, default } => {
            let mut s: Vec<Block> = cases.iter().map(|(_, b)| *b).collect();
            s.push(*default);
            s
        }
        _ => vec![],
    }
}

/// (has back edge, number of entry-to-exit paths (saturating), reachable blocks)
fn cfg_shape(function: &Function) -> (bool, u64, usize) {
    let succ = |b: Block| -> Vec<Block> {
        function.blocks[&b]
            .instructions
            .last()
            .map(successors)
            .unwrap_or_default()
    };
    // DFS colouring.
    let mut state: HashMap<Block, u8> = HashMap::new();
    let mut back = false;
    fn dfs(
        b: Block,
        succ: &dyn Fn(Block) -> Vec<Block>,
        state: &mut HashMap<Block, u8>,
        back: &mut bool,
        function: &Function,
    ) {
        state.insert(b, 1);
        for s in succ(b) {
            if !function.blocks.contains_key(&s) {
                continue;
            }
            match state.get(&s) {
                Some(1) => *back = true,
                Some(_) => {}
                None => dfs(s, succ, state, back, function),
            }
        }
        state.insert(b, 2);
    }
    dfs(function.entry_block, &succ, &mut state, &mut back, function);
    let reachable = state.len();
    if back {
        return (true, 0, reachable);
    }
    let mut memo: HashMap<Block, u64> = HashMap::new();
    fn paths(
        b: Block,
        succ: &dyn Fn(Block) -> Vec<Block>,
        memo: &mut HashMap<Block, u64>,
    ) -> u64 {
        if let Some(n) = memo.get(&b) {
            return *n;
        }
        let s = succ(b);
        let n = if s.is_empty() {
            1
        } else {
            s.iter()
                .map(|x| paths(*x, succ, memo))
                .fold(0u64, |a, b| a.saturating_add(b))
        };
        memo.insert(b, n);
        n
    }
    (false, paths(function.entry_block, &succ, &mut memo), reachable)
}

/// [`super::select`] without panicking.
fn try_select(source: &Function) -> Option<X86ISelFunction> {
    let signature = trust_cg_lower::function::Signature {
        params: source.signature.params.clone(),
        returns: source.signature.returns.clone(),
    };
    let mut isel = X86InstructionSelector::with_abi(source.name.clone(), signature.clone(), X86CallAbi::SystemV);
    isel.set_stack_slots(source.stack_slots.clone());
    isel.seed_value_types(&source.value_types);
    isel.seed_function_value_use_counts(source);
    isel.seed_pure_callees(&source.pure_callees);
    isel.seed_sret_param(source.abi_sret_param).ok()?;
    isel.seed_sret_arg_callees(&source.sret_arg_callees);
    isel.seed_sret_arg_indirect_callees(&source.sret_arg_indirect_callees);
    let order = source.layout_order();
    isel.seed_iconst_origins(order.iter().map(|block| source.blocks[block].instructions.as_slice()));
    for block in &order {
        isel.ensure_block(*block);
    }
    isel.lower_formal_arguments(&signature, source.entry_block).ok()?;
    for block in &order {
        let body = &source.blocks[block];
        if *block != source.entry_block && !body.params.is_empty() {
            isel.define_block_params(&body.params);
        }
        isel.select_block(*block, &body.instructions).ok()?;
    }
    isel.finalize_with_eh_info(&source.eh_info).ok()
}

#[test]
#[ignore]
fn census_probe_shapes() {
    let names: Option<HashSet<String>> = std::env::var("TCG_PROBE_NAMES").ok().map(|file| {
        std::fs::read_to_string(file)
            .unwrap()
            .lines()
            .map(str::to_owned)
            .collect()
    });
    let functions = load_functions();
    eprintln!("PROBE translated {} functions", functions.len());
    let out_path = std::env::var("TCG_PROBE_OUT").unwrap_or("/dev/stderr".into());
    let mut out = std::fs::File::create(out_path).unwrap();
    let mut histogram: BTreeMap<String, usize> = BTreeMap::new();
    let mut found = 0usize;
    for function in &functions {
        if names.as_ref().is_some_and(|names| !names.contains(&function.name)) {
            continue;
        }
        found += 1;
        if std::env::var("TCG_PROBE_LIR").is_ok_and(|name| function.name.contains(&name)) {
            eprintln!("PROBE-LIR {} sig={:?} slots={:?} sret={:?}", function.name, function.signature, function.stack_slots.iter().map(|s| s.size).collect::<Vec<_>>(), function.abi_sret_param);
            for block in function.layout_order() {
                let body = &function.blocks[&block];
                eprintln!("PROBE-LIR   {block:?} params={:?}", body.params);
                for inst in &body.instructions {
                    eprintln!("PROBE-LIR     {:?} {:?} -> {:?}", inst.opcode, inst.args, inst.results);
                }
            }
            if let Some(machine) = try_select(function) {
                for block in &machine.block_order {
                    eprintln!("PROBE-MIR   {block:?} succ={:?}", machine.blocks[block].successors);
                    for inst in &machine.blocks[block].insts {
                        eprintln!("PROBE-MIR     {:?} {:?}", inst.opcode, inst.operands);
                    }
                }
            }
        }
        let (back, npaths, reachable) = cfg_shape(function);
        let mut terms: BTreeMap<String, usize> = BTreeMap::new();
        let mut mids: BTreeMap<String, usize> = BTreeMap::new();
        for block in function.blocks.values() {
            if let Some(last) = block.instructions.last() {
                *terms.entry(opcode_name(&last.opcode)).or_default() += 1;
            }
            for inst in &block.instructions[..block.instructions.len().saturating_sub(1)] {
                let name = opcode_name(&inst.opcode);
                if matches!(
                    name.as_str(),
                    "GuardBoundsCheck"
                        | "GuardBoundsCheckDyn"
                        | "GuardDivZero"
                        | "GuardNull"
                        | "GuardShiftRange"
                        | "GuardOverflow"
                        | "Assert"
                        | "Select"
                        | "Switch"
                        | "Brif"
                        | "Trap"
                        | "Return"
                        | "Jump"
                ) {
                    *mids.entry(name).or_default() += 1;
                }
            }
        }
        let class = if back {
            "loop".to_owned()
        } else if terms.contains_key("Switch") {
            "dag+switch".to_owned()
        } else if terms.keys().any(|t| !matches!(t.as_str(), "Jump" | "Brif" | "Return" | "Trap")) {
            format!("dag+other-term:{:?}", terms.keys().collect::<Vec<_>>())
        } else if npaths <= 1 {
            "chain".to_owned()
        } else {
            "dag".to_owned()
        };
        *histogram.entry(class.clone()).or_default() += 1;
        let admitted = source_admits_x86_body_owner(function, Some(X86SourceBoundAbi::SystemV));
        let refusal = if !admitted {
            match admitted_body(function) {
                Ok(_) => "admitted?".to_owned(),
                Err(refusal) => refusal.to_string(),
            }
        } else {
            match try_select(function) {
                None => "selection failed".to_owned(),
                Some(machine) => match source_bound_x86_body(function, &machine, SYSV) {
                    Ok(owner) => {
                        if let Ok(dir) = std::env::var("TCG_PROBE_SMT2") {
                            let name: String = function.name.chars().map(|c| if c.is_ascii_alphanumeric() || c == '_' { c } else { '-' }).take(200).collect();
                            std::fs::create_dir_all(&dir).unwrap();
                            std::fs::write(
                                std::path::Path::new(&dir).join(format!("{name}.smt2")),
                                crate::ay_bridge::generate_smt2_query_raw(owner.obligation(), &crate::ay_bridge::AYConfig { solver: None, timeout_ms: 30_000, produce_models: true }),
                            ).unwrap();
                        }
                        format!("OWNER bound_rows={}", owner.bound_rows().len())
                    }
                    Err(refusal) => refusal.to_string(),
                },
            }
        };
        writeln!(
            out,
            "{}\t{class}\tblocks={}\treach={reachable}\tpaths={npaths}\tterms={terms:?}\tmids={mids:?}\tadmitted={admitted}\t{refusal}",
            function.name,
            function.blocks.len(),
        )
        .unwrap();
    }
    eprintln!("PROBE found {found} functions; classes {histogram:?}");
}
