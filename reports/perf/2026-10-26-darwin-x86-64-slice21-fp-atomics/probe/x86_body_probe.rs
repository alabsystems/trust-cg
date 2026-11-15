// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! Probe (slice 21: the verdict names an FP-abstract theorem): read a bridge `dump-trust-ir` module, translate it to LIR, select
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


/// S20 local, with `S20_DIV128=1` only: the slice-20 design's runtime-call
/// reading of an `I128` division, measured without an owner change. Every
/// machine `call` the selector emits for an `I128` `Udiv`/`Sdiv`/`Urem`/
/// `Srem` (`__udivti3`, `__divti3`, `__umodti3`, `__modti3`, stamped with the
/// LIR instruction it lowers) makes the owner's copy of that instruction a
/// direct call to the same symbol (`Interposable`, an `I128` result), and the
/// row declares the System V argument registers of two `I128` arguments
/// (RDI, RSI, RDX, RCX at 64 bits), which the selector's libcall leaves
/// undeclared today. Each rewrite is named on stderr (`S20-DIV128`).
fn s20_prepare(source: &Function, mut machine: X86ISelFunction) -> (Function, X86ISelFunction) {
    let mut owner = source.clone();
    if std::env::var_os("S20_DIV128").is_none() {
        return (owner, machine);
    }
    use trust_cg_lower::x86_64_isel::{X86CallArgReg, X86ISelOperand};
    const ROUTINES: [&str; 4] = ["__udivti3", "__divti3", "__umodti3", "__modti3"];
    for block in machine.blocks.values_mut() {
        for inst in &mut block.insts {
            let Some(X86ISelOperand::Symbol(symbol)) = inst.operands.first() else {
                continue;
            };
            if !ROUTINES.contains(&symbol.as_str()) || !inst.call_arg_regs.is_empty() {
                continue;
            }
            let symbol = symbol.clone();
            let Some(id) = inst.lowering_provenance.source_id() else {
                eprintln!("S20-DIV128\t{}\tunattributed {symbol}", source.name);
                continue;
            };
            let lir_block = trust_cg_lower::instructions::Block(id.block);
            let Some(lir) = owner
                .blocks
                .get_mut(&lir_block)
                .and_then(|b| b.instructions.get_mut(id.index as usize))
            else {
                continue;
            };
            use trust_cg_lower::instructions::Opcode as L;
            if !matches!(lir.opcode, L::Udiv | L::Sdiv | L::Urem | L::Srem) {
                eprintln!("S20-DIV128\t{}\t{symbol} stamped with {:?}", source.name, lir.opcode);
                continue;
            }
            eprintln!("S20-DIV128\t{}\t{:?}:{}\t{:?} -> {symbol}", source.name, lir_block, id.index, lir.opcode);
            lir.opcode = L::Call {
                name: symbol,
                binding: trust_cg_lower::instructions::DirectCallBinding::Interposable,
            };
            let result = lir.results[0];
            owner
                .value_types
                .insert(result, trust_cg_lower::types::Type::I128);
            inst.call_arg_regs = [
                trust_cg_ir::x86_64_regs::RDI,
                trust_cg_ir::x86_64_regs::RSI,
                trust_cg_ir::x86_64_regs::RDX,
                trust_cg_ir::x86_64_regs::RCX,
            ]
            .into_iter()
            .map(|reg| X86CallArgReg::new(reg, 64))
            .collect();
        }
    }
    (owner, machine)
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
        // A bridge dump carries no codegen license (WS7.5 refuses an
        // unlicensed body by default); the probe measures the owner, so it
        // states `Permit`, as the crate's own fixtures do.
        match trust_cg_lower::translate_module_for_arch_with_tls_with_license(
            &module,
            trust_cg_lower::GuardCarrierArch::X86_64,
            trust_cg_lower::TlsDialect::default(),
            &trust_cg_lower::CodegenLicensePolicy::default()
                .with_unlicensed(trust_cg_lower::UnlicensedBodyPolicy::Permit),
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
    std::fs::write(
        &args[3],
        trust_ir::binary::serialize_module(&module).expect("serialize"),
    )
    .unwrap();
}

/// An integer constant `value` of a `bits`-wide type outside the type's
/// range, re-spelled with the same low `bits` bits inside it (an unsigned bit
/// pattern of a signed type, or the reverse); `None` when it already fits or
/// its bits do not fit in `bits`.
fn same_bits_in_range(value: i128, bits: u32, signed: bool) -> Option<i128> {
    let full = 1i128 << bits;
    let half = 1i128 << (bits - 1);
    if signed {
        (half..full).contains(&value).then(|| value - full)
    } else {
        (-half..0).contains(&value).then(|| value + full)
    }
}

/// See `translate_dropping_refused`: the S16 local re-spelling of an older
/// dump's `bool` and thin-reference constants.
fn respell_old_constants(module: &mut trust_ir::Module) {
    use trust_ir::inst::{CastOp, Inst};
    use trust_ir::{Constant, Ty};
    // A function item's declared type, by id (an id defined twice is left
    // alone: the validator refuses it on its own).
    let mut item_ty = std::collections::HashMap::new();
    for function in &module.functions {
        item_ty
            .entry(function.id.index())
            .and_modify(|ty: &mut Option<trust_ir::FuncTyId>| *ty = None)
            .or_insert(Some(function.ty));
    }
    for function in &mut module.functions {
        let mut fresh = function.fresh_value_ids();
        let (mut bools, mut refs, mut fndefs, mut ints) = (0usize, 0usize, 0usize, 0usize);
        // A `fndef` constant typed with another function type than its item
        // declares: retyped to the item's, and so is the `reify_fn_pointer`
        // that reads it (both lower to the item's symbol address).
        let mut retyped = std::collections::HashMap::new();
        for block in &mut function.blocks {
            for node in &mut block.body {
                if let Inst::Const {
                    ty: Ty::Func(signature),
                    value: Constant::FnDef(target),
                } = &mut node.inst
                    && let Some(Some(declared)) = item_ty.get(&target.index())
                    && *declared != *signature
                {
                    for result in &node.results {
                        retyped.insert(*result, (*signature, *declared));
                    }
                    *signature = *declared;
                    fndefs += 1;
                }
            }
        }
        for block in &mut function.blocks {
            for node in &mut block.body {
                if let Inst::Cast {
                    op: CastOp::ReifyFnPointer,
                    src_ty: src_ty @ Ty::Func(_),
                    operand,
                    ..
                } = &mut node.inst
                    && let Some((old, new)) = retyped.get(operand)
                    && *src_ty == Ty::Func(*old)
                {
                    *src_ty = Ty::Func(*new);
                }
            }
        }
        for block in &mut function.blocks {
            let mut body = Vec::with_capacity(block.body.len());
            for mut node in std::mem::take(&mut block.body) {
                match &mut node.inst {
                    Inst::Const {
                        ty: Ty::Bool,
                        value,
                    } if matches!(value, Constant::Int(0 | 1)) => {
                        let one = matches!(value, Constant::Int(1));
                        *value = Constant::Bool(one);
                        bools += 1;
                        body.push(node);
                    }
                    Inst::Const {
                        ty,
                        value: Constant::Int(v),
                    } if ty.is_integer()
                        && let Some(bits @ 1..=64) = ty.bit_width_with(64)
                        && let Some(wrapped) = same_bits_in_range(*v, bits, ty.is_signed()) =>
                    {
                        *v = wrapped;
                        ints += 1;
                        body.push(node);
                    }
                    Inst::Const {
                        ty: ty @ (Ty::Ref(_) | Ty::RefMut(_)),
                        value: Constant::Int(n),
                    } => {
                        // The 64-bit address, as the signed `i64` spelling.
                        let (ty, n) = (ty.clone(), same_bits_in_range(*n, 64, true).unwrap_or(*n));
                        let int = fresh.take().expect("fresh value id");
                        let mut constant = trust_ir::InstrNode::new(Inst::Const {
                            ty: Ty::I64,
                            value: Constant::Int(n),
                        })
                        .with_result(int);
                        constant.span = node.span.clone();
                        constant.scope = node.scope;
                        body.push(constant);
                        let raw = fresh.take().expect("fresh value id");
                        let mut cast = trust_ir::InstrNode::new(Inst::Cast {
                            op: CastOp::IntToPtr,
                            src_ty: Ty::I64,
                            dst_ty: Ty::Ptr,
                            operand: int,
                        })
                        .with_result(raw);
                        cast.span = node.span.clone();
                        cast.scope = node.scope;
                        body.push(cast);
                        node.inst = Inst::Cast {
                            op: CastOp::PtrToPtr,
                            src_ty: Ty::Ptr,
                            dst_ty: ty,
                            operand: raw,
                        };
                        refs += 1;
                        body.push(node);
                    }
                    _ => body.push(node),
                }
            }
            block.body = body;
        }
        if bools + refs + fndefs + ints > 0 {
            eprintln!(
                "respelled {}\tbool={bools}\tref={refs}\tfndef={fndefs}\tint={ints}",
                function.name
            );
        }
    }
}

/// S16 local, with `S16_RESPELL=1` only: the older bridge's STORE-FORM
/// `insertfield` (its aggregate operand a pointer to the aggregate, its
/// result never read), which the pinned adapter refuses by name
/// (`AggregateInsertNotValueForm`, WS7.1 (b)) after giving it the meaning
/// of a store of the value at the field through that pointer, becomes that
/// store as today's bridge spells it (`emit_aggregate_field_store`): a byte
/// offset `GEP` from the pointer to the field (the adapter's own layout of
/// the aggregate type) and a `Store` of the field's type. Only a tuple or
/// array field over an operand defined as a pointer here (an `alloca`, a
/// pointer cast, a `GEP`, a pointer parameter) is re-spelled; anything
/// else is left for the adapter to refuse. Each re-spelled function is
/// named on stderr.
fn respell_store_form_inserts(module: &mut trust_ir::Module) {
    use trust_ir::Constant;
    use trust_ir::Ty;
    use trust_ir::inst::Inst;
    use trust_ir::value::ValueId;
    let pointerish = |ty: &Ty| {
        matches!(
            ty,
            Ty::Ptr | Ty::PtrMut(_) | Ty::PtrConst(_) | Ty::Ref(_) | Ty::RefMut(_)
        )
    };
    let types = module.types.clone();
    let structs = module.structs.clone();
    for function in &mut module.functions {
        let mut fresh = function.fresh_value_ids();
        let mut pointers: std::collections::HashSet<ValueId> = std::collections::HashSet::new();
        for block in &function.blocks {
            for (value, ty) in &block.params {
                if pointerish(ty) {
                    pointers.insert(*value);
                }
            }
            for node in &block.body {
                let defines_pointer = match &node.inst {
                    Inst::Alloca { .. } | Inst::GEP { .. } => true,
                    Inst::Cast { dst_ty, .. } => pointerish(dst_ty),
                    Inst::Load { ty, .. } => pointerish(ty),
                    _ => false,
                };
                if defines_pointer {
                    pointers.extend(node.results.iter().copied());
                }
            }
        }
        let mut respelled = 0usize;
        for block in &mut function.blocks {
            let mut body = Vec::with_capacity(block.body.len());
            for node in std::mem::take(&mut block.body) {
                let Inst::InsertField {
                    ty,
                    aggregate,
                    field,
                    value,
                } = &node.inst
                else {
                    body.push(node);
                    continue;
                };
                let field_ty = match ty {
                    Ty::Tuple(fields) => fields.get(*field as usize).cloned(),
                    Ty::Array(element, _) => types.get(element.as_usize()).cloned(),
                    _ => None,
                };
                let offset =
                    trust_cg_lower::adapter::translate_type_with_tables(ty, &structs, &types)
                        .ok()
                        .and_then(|lir| lir.offset_of(*field as usize));
                let (Some(field_ty), Some(offset), true) =
                    (field_ty, offset, pointers.contains(aggregate))
                else {
                    body.push(node);
                    continue;
                };
                let (pointer, stored) = (*aggregate, *value);
                let index = fresh.take().expect("fresh value id");
                let mut constant = trust_ir::InstrNode::new(Inst::Const {
                    ty: Ty::I64,
                    value: Constant::Int(i128::from(offset)),
                })
                .with_result(index);
                constant.span = node.span.clone();
                constant.scope = node.scope;
                let at = fresh.take().expect("fresh value id");
                let mut gep = trust_ir::InstrNode::new(Inst::GEP {
                    pointee_ty: Ty::I8,
                    base: pointer,
                    indices: vec![index],
                    inbounds: false,
                })
                .with_result(at);
                gep.span = node.span.clone();
                gep.scope = node.scope;
                let mut store = trust_ir::InstrNode::new(Inst::Store {
                    ty: field_ty,
                    ptr: at,
                    value: stored,
                    volatile: false,
                    align: None,
                });
                store.span = node.span.clone();
                store.scope = node.scope;
                body.push(constant);
                body.push(gep);
                body.push(store);
                respelled += 1;
            }
            block.body = body;
        }
        if respelled > 0 {
            eprintln!(
                "respelled-store-form {}\tinserts={respelled}",
                function.name
            );
        }
    }
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
    // S16 local, with `S16_RESPELL=1` only: re-spell four constant forms of
    // a dump older than the pinned trust-ir, which its validator now refuses
    // as `const type mismatch`: a `bool` constant spelled `Int(0|1)` becomes
    // `Bool(..)` (the same value); an integer constant outside its type's
    // range takes the in-range spelling of the same bits; a thin reference
    // constant spelled `Int(n)` becomes `const i64 n`, `inttoptr` to `ptr`
    // and `ptrtoptr` to the reference type (two extra copies); a `fndef`
    // constant takes its item's declared function type. Each re-spelled
    // function is named on stderr.
    if std::env::var_os("S16_RESPELL").is_some() {
        respell_old_constants(&mut module);
        respell_store_form_inserts(&mut module);
    }
    for _ in 0..4096 {
        // A bridge dump carries no codegen license (WS7.5 refuses an
        // unlicensed body by default); the probe measures the owner, so it
        // states `Permit`, as the crate's own fixtures do.
        match trust_cg_lower::translate_module_for_arch_with_tls_with_license(
            &module,
            trust_cg_lower::GuardCarrierArch::X86_64,
            trust_cg_lower::TlsDialect::default(),
            &trust_cg_lower::CodegenLicensePolicy::default()
                .with_unlicensed(trust_cg_lower::UnlicensedBodyPolicy::Permit),
        ) {
            Ok(lir) => return Some(lir),
            Err(error) => {
                let text = format!("{error:?}");
                // S16 local: the pinned trust-ir now names a refused
                // function as `function '<name>'`; the older text used `fn <name>:`.
                let quoted = text
                    .split("function '")
                    .nth(1)
                    .and_then(|rest| rest.split('\'').next())
                    .map(str::to_owned);
                // S16 local: a structured adapter refusal names it as
                // `function: "<name>"`.
                let structured = text
                    .split("function: \"")
                    .nth(1)
                    .and_then(|rest| rest.split('"').next())
                    .map(str::to_owned);
                let Some(name) = quoted.or(structured).or_else(|| {
                    text.split("fn ")
                        .nth(1)
                        .and_then(|rest| rest.split(':').next())
                        .map(str::to_owned)
                }) else {
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
                // S16 local: the refusal text too, so a drop is classified.
                eprintln!(
                    "dropped {name}\t{}",
                    text[..text.len().min(600)].replace(['\t', '\n'], " ")
                );
                function.blocks.clear();
                // A body-less function must be a declaration.
                function.linkage = trust_ir::Linkage::External;
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
        // S16 local, with `S16_ONLY_NAMES=1` and a names file only: every
        // other function becomes a declaration before translation, so a
        // dump the pinned adapter refuses in many functions is translated
        // once per refused NAMED function, not once per refused function.
        let mut module = module;
        if std::env::var_os("S16_ONLY_NAMES").is_some()
            && let Some(names) = names.as_ref()
        {
            for function in &mut module.functions {
                if !names.contains(&function.name) {
                    function.blocks.clear();
                    function.linkage = trust_ir::Linkage::External;
                }
            }
        }
        let Some(lir) = translate_dropping_refused(module) else {
            eprintln!("untranslatable {}", file.display());
            continue;
        };
        for (function, _) in lir {
            if !seen.insert(function.name.clone()) {
                continue;
            }
            if std::env::var_os("S16_ONLY_NAMES").is_some()
                && names
                    .as_ref()
                    .is_some_and(|names| !names.contains(&function.name))
            {
                continue;
            }
            let (blocks, looped, paths, longest, instructions) = cf_shape(&function);
            if std::env::var_os("S16_TRACE_NAMES").is_some() {
                eprintln!("judging {}", function.name);
            }
            let (verdict, machine_blocks, machine_rows) = match select(&function) {
                Err(error) => (format!("SELECT {}", error.replace(['\t', '\n'], " ")), 0, 0),
                Ok(machine) => {
                    let rows: usize = machine.blocks.values().map(|b| b.insts.len()).sum();
                    let (owner_fn, machine) = s20_prepare(&function, machine);
                    let verdict = match source_bound_x86_body(
                        &owner_fn,
                        &machine,
                        Some(X86SourceBoundAbi::SystemV),
                    ) {
                        Ok(body) if body.is_stated_in_parts() => {
                            // Slice 16: a theorem stated in parts, one query
                            // per part (`<hash>.part<k>.smt2`).
                            let hash = function
                                .name
                                .bytes()
                                .fold(0xcbf2_9ce4_8422_2325u64, |h, b| {
                                    (h ^ u64::from(b)).wrapping_mul(0x0100_0000_01b3)
                                });
                            if let Some(dir) = smt2_dir
                                && names
                                    .as_ref()
                                    .is_none_or(|names| names.contains(&function.name))
                            {
                                std::fs::create_dir_all(dir).unwrap();
                                for (k, part) in body.parts().iter().enumerate() {
                                    let query = trust_cg_verify::ay_bridge::generate_smt2_query_raw(
                                        part, &config,
                                    );
                                    std::fs::write(
                                        std::path::Path::new(dir)
                                            .join(format!("{hash:016x}.part{}.smt2", k + 1)),
                                        query,
                                    )
                                    .unwrap();
                                }
                                use std::io::Write as _;
                                let mut index = std::fs::OpenOptions::new()
                                    .create(true)
                                    .append(true)
                                    .open(std::path::Path::new(dir).join("index.tsv"))
                                    .unwrap();
                                writeln!(
                                    index,
                                    "{hash:016x}\t{}\t{}",
                                    function.name,
                                    body.parts().len()
                                )
                                .unwrap();
                            }
                            let shapes: Vec<String> = body
                                .parts()
                                .iter()
                                .map(|part| {
                                    let claims = {
                                        let mut n = 1;
                                        let mut rest = &part.aarch64_expr;
                                        while let trust_cg_verify::smt::SmtExpr::And {
                                            rhs, ..
                                        } = rest
                                        {
                                            n += 1;
                                            rest = rhs.as_ref();
                                        }
                                        n
                                    };
                                    let bytes =
                                        trust_cg_verify::ay_bridge::generate_smt2_query_raw(
                                            part, &config,
                                        )
                                        .len();
                                    format!("{}/{claims}/{bytes}", part.preconditions.len())
                                })
                                .collect();
                            let refuted: Vec<usize> = body
                                .parts()
                                .iter()
                                .enumerate()
                                .filter(|(_, part)| refuting_sample(part, 600).is_some())
                                .map(|(k, _)| k + 1)
                                .collect();
                            if refuted.is_empty() {
                                format!(
                                    "OWNER {} PARTS {} defs/claims/bytes={}",
                                    body.bound_rows().len(),
                                    body.parts().len(),
                                    shapes.join(",")
                                )
                            } else {
                                format!(
                                    "OWNER {} PARTS {} REFUTED-PARTS {refuted:?}",
                                    body.bound_rows().len(),
                                    body.parts().len()
                                )
                            }
                        }
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
                                    "OWNER {} defs={}{}",
                                    body.bound_rows().len(),
                                    body.obligation().preconditions.len(),
                                    if body.is_fp_abstract() { " FP-ABSTRACT" } else { "" }
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
    // S20 local: `@<file>` names the functions exactly, one per line (the
    // first TSV field), so one translation serves a whole class.
    let named: Option<std::collections::HashSet<String>> = filter.strip_prefix('@').map(|path| {
        std::fs::read_to_string(path)
            .expect("names")
            .lines()
            .map(|line| line.split('\t').next().unwrap_or_default().to_owned())
            .collect()
    });
    for (function, _) in lir {
        let wanted = match &named {
            Some(names) => names.contains(&function.name),
            None => function.name.contains(&filter),
        };
        if !wanted {
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
        let (owner_fn, machine) = s20_prepare(&function, machine);
        match source_bound_x86_body(&owner_fn, &machine, Some(X86SourceBoundAbi::SystemV)) {
            Ok(body) => {
                println!("  BODY OK bound rows {}", body.bound_rows().len());
                // S20 local: parts, and the sampler on each query.
                if body.is_stated_in_parts() {
                    let refuted: Vec<usize> = body
                        .parts()
                        .iter()
                        .enumerate()
                        .filter(|(_, part)| refuting_sample(part, 600).is_some())
                        .map(|(k, _)| k + 1)
                        .collect();
                    println!("  BODY PARTS {} refuted-parts {refuted:?}", body.parts().len());
                } else {
                    println!(
                        "  BODY SINGLE refuted-at-sample {:?}",
                        refuting_sample(body.obligation(), 600)
                    );
                }
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
