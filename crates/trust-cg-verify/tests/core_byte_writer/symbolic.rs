// Copyright 2026 Andrew Yates | Apache-2.0

//! Candidate assembly for all five canonical input words, with actual fetched
//! execution and independent whole-world replay. No native authority.

use super::*;
use std::collections::HashMap;
use trust_ir::{BinOp, CastOp, Constant};
use trust_ir_build::core_execution::{
    Assembler, ByteEightCodec, ByteStoreEight, ByteStoreEightPremises, Catalog, Coordinate,
    EntryTarget, Limits, MemoryPremises, PendingEquality, PendingProof, ScalarPremises,
};
use trust_ir_build::scoped_local::{LocalScope, ScopedLocal};

#[path = "caller.rs"]
mod caller;

fn eq(ty: Expr, left: Expr, right: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
        [ty, left, right],
    )
}
fn refl(ty: Expr, value: Expr) -> Expr {
    Expr::apps(
        Expr::const_(
            Name::from_string("Eq.refl"),
            vec![Level::succ(Level::zero())],
        ),
        [ty, value],
    )
}
fn conversion(ty: Expr, left: Expr, right: Expr) -> PendingEquality {
    PendingEquality::candidate(ty.clone(), left, right.clone(), refl(ty, right))
}
fn truth(guard: Expr) -> PendingEquality {
    conversion(c("Bool"), guard, c("Bool.true"))
}
fn some(ty: &str, value: Expr) -> Expr {
    app("IROption.some", [c(ty), value])
}
fn scalar(word: Expr) -> Expr {
    app("IRScalar.int_", [word])
}
fn pointer(address: u64) -> Expr {
    app("IRScalar.ptr_", [nat(address)])
}
fn limits() -> Limits {
    Limits {
        max_operations: 50_000,
        max_locals: 5_000,
        max_list_items: 1_000,
        max_lookup_candidates: 128,
        lookup_heartbeats: 5_000_000,
        lookup_cache_entries: 100_000,
    }
}
fn world_source(address: u64) -> WriterCall {
    let mut source = invocation();
    source.address = address;
    source
}
fn arguments(address: u64, words: &[Expr]) -> Expr {
    let mut values = vec![pointer(address)];
    values.extend(words.iter().cloned().map(scalar));
    list("IRScalar", &values)
}
fn initial(model: &MachineModel, address: u64, words: &[Expr], bytes: Expr) -> Expr {
    app(
        "ir_byte_init_v1",
        [
            c("Nat"),
            model.context().clone(),
            nat(0),
            arguments(address, words),
            memory(&world_source(address), bytes),
            nat(37),
        ],
    )
}
fn terminal(address: u64, words: &[Expr], mut bytes: Expr) -> Expr {
    for (index, word) in words.iter().enumerate() {
        bytes = app(
            "ir_byte_write_word_v1",
            [bytes, nat(address + 8 * index as u64), nat(8), word.clone()],
        );
    }
    app(
        "IRByteConfigV1.halted",
        [
            c("Nat"),
            app("IROutcome.ret", [list("IRScalar", &[])]),
            app(
                "IRByteWorldV1.mk",
                [
                    c("Nat"),
                    memory(&world_source(address), bytes),
                    nat(37),
                    list("Nat", &[]),
                    nat(9),
                ],
            ),
        ],
    )
}
fn locals(scope: &mut LocalScope) -> (Vec<ScopedLocal>, Vec<ScopedLocal>, ScopedLocal) {
    let words: Vec<_> = (0..5).map(|_| scope.try_local(c("Nat")).unwrap()).collect();
    let bounds: Vec<_> = words
        .iter()
        .map(|word| {
            scope
                .try_local(app("Nat.lt", [word.term().clone(), c("ir_byte_limit_v1")]))
                .unwrap()
        })
        .collect();
    let bytes = scope.try_local(bytes_type()).unwrap();
    (words, bounds, bytes)
}
struct SymbolicWriter;
impl SourceTranslationModel for SymbolicWriter {
    type Source = u64;
    fn build_environment() -> Result<Environment, String> {
        WriterModel::build_environment()
    }
    fn reconstruct(address: &u64, target: &Module) -> Result<Expr, String> {
        if ![80, 88].contains(address)
            || target.functions.len() != 1
            || target.functions[0].blocks.len() != 1
        {
            return Err("bounded symbolic writer profile".into());
        }
        let function = &target.functions[0];
        let mut params = vec![Ty::RefMut(Box::new(Ty::Tuple(vec![Ty::U64; 5])))];
        params.extend(vec![Ty::U64; 5]);
        let signature = target.func_type(function.ty).ok_or("signature")?;
        if function.id != FuncId::new(0)
            || function.blocks[0].body.len() != 51
            || signature.params != params
            || !signature.returns.is_empty()
        {
            return Err("captured writer signature and length required".into());
        }
        let reflected =
            reflect_core_module_v1(target, &[(function.id, 4096)]).map_err(|e| e.to_string())?;
        let model = MachineModel::new(c("Nat"), &reflected, providers());
        let mut scope = LocalScope::new();
        let (words, bounds, bytes) = locals(&mut scope);
        let values: Vec<_> = words.iter().map(|w| w.term().clone()).collect();
        let mut claim = eq(
            model.config_type(),
            model.run(
                &NatTerm::literal(51),
                initial(&model, *address, &values, bytes.term().clone()),
            ),
            terminal(*address, &values, bytes.term().clone()),
        );
        claim = bytes.pi(claim);
        for local in bounds.iter().rev().chain(words.iter().rev()) {
            claim = local.pi(claim);
        }
        scope.close(&claim).map_err(|e| e.to_string())
    }
}
fn conjunction(a: PendingEquality, b: PendingEquality) -> PendingEquality {
    PendingEquality::candidate(
        c("Bool"),
        app("Bool.and", [a.left().clone(), b.left().clone()]),
        c("Bool.true"),
        app(
            "ir_byte_function_and_true_v1",
            [
                a.left().clone(),
                b.left().clone(),
                a.term().clone(),
                b.term().clone(),
            ],
        ),
    )
}
fn fits(context: &Expr, word: &Expr, bound: &ScopedLocal) -> PendingEquality {
    PendingEquality::candidate(
        c("Bool"),
        app(
            "ir_byte_value_matches_v1",
            [
                context.clone(),
                app("IRTy.uint_", [nat(64)]),
                scalar(word.clone()),
            ],
        ),
        c("Bool.true"),
        app(
            "ir_byte_u64_value_fits_v1",
            [
                context.clone(),
                word.clone(),
                app(
                    "ir_byte_ltb_of_lt_v1",
                    [word.clone(), c("ir_byte_limit_v1"), bound.term().clone()],
                ),
            ],
        ),
    )
}
fn uint_codec(context: &Expr, word: &Expr, bound: &ScopedLocal) -> ByteEightCodec {
    let ty = app("IRTy.uint_", [nat(64)]);
    let value = scalar(word.clone());
    let layout = app(
        "IRByteLayoutV1.mk",
        [
            ty.clone(),
            nat(8),
            nat(8),
            list("IRTy", &[]),
            list("Nat", &[]),
        ],
    );
    ByteEightCodec {
        context: context.clone(),
        ty: ty.clone(),
        value: value.clone(),
        word: word.clone(),
        layout: layout.clone(),
        lane: conversion(
            app("IROption", [c("Nat")]),
            app("ir_byte_lane_size_v1", [ty.clone()]),
            some("Nat", nat(8)),
        ),
        layout_found: conversion(
            app("IROption", [c("IRByteLayoutV1")]),
            app("ir_byte_layout_v1", [context.clone(), ty.clone()]),
            some("IRByteLayoutV1", layout.clone()),
        ),
        valid_layout: truth(app(
            "Bool.and",
            [
                app(
                    "ir_nat_eqb",
                    [nat(8), app("ir_byte_layout_size_v1", [layout.clone()])],
                ),
                app(
                    "ir_byte_alignment_v1",
                    [app("ir_byte_layout_align_v1", [layout])],
                ),
            ],
        )),
        fits: fits(context, word, bound),
        encoded: conversion(
            app("IROption", [c("Nat")]),
            app("ir_byte_scalar_word_v1", [context.clone(), value.clone()]),
            some("Nat", word.clone()),
        ),
        decoded: conversion(
            app("IROption", [c("IRScalar")]),
            app(
                "ir_byte_decode_word_v1",
                [context.clone(), ty, word.clone()],
            ),
            some("IRScalar", value),
        ),
        bounded: PendingProof::candidate(
            app("Nat.lt", [word.clone(), c("ir_byte_limit_v1")]),
            bound.term().clone(),
        ),
    }
}

#[derive(Clone, Copy)]
enum Fault {
    None,
    WrongWordBound,
    UnwrittenByte,
}

fn assemble(module: &Module, address: u64, fault: Fault) -> Vec<u8> {
    let function = &module.functions[0];
    let reflected = reflect_core_module_v1(module, &[(function.id, 4096)]).unwrap();
    let model = MachineModel::new(c("Nat"), &reflected, providers());
    let mut catalog = Catalog::new(
        shared_specification_with_stack(EvalIrVocabulary::ByteV1)
            .unwrap()
            .env(),
        &reflected,
        limits(),
    )
    .unwrap();
    let entry = catalog.entry(function.id).unwrap();
    let mut scope = LocalScope::new();
    let (words, bounds, bytes) = locals(&mut scope);
    let values: Vec<_> = words.iter().map(|w| w.term().clone()).collect();
    let mut assembler = Assembler::new(&mut scope, limits()).unwrap();
    let mut argument_fits = truth(c("Bool.true"));
    for (word, bound) in values.iter().zip(&bounds).rev() {
        argument_fits = conjunction(fits(model.context(), word, bound), argument_fits);
    }
    // The pointer carrier is concrete and independently checked at init.
    argument_fits = conjunction(truth(c("Bool.true")), argument_fits);
    let args = arguments(address, &values);
    let mem = memory(&world_source(address), bytes.term().clone());
    let initialized = entry
        .initialize(
            &mut assembler,
            &model,
            args.clone(),
            mem.clone(),
            nat(37),
            truth(EntryTarget::memory_admission(mem)),
            PendingEquality::candidate(
                c("Bool"),
                entry.admission(&model, args).unwrap(),
                c("Bool.true"),
                argument_fits.term().clone(),
            ),
        )
        .unwrap();
    let mut current = initialized.current().clone();
    let mut valid = initialized.valid().clone();
    let mut run = assembler.zero(&model, current.running(&model)).unwrap();
    let mut concrete = HashMap::from([(1_u32, address)]);
    let mut symbolic = HashMap::new();
    for index in 0..5 {
        symbolic.insert(index as u32 + 2, index);
    }
    for (pc, node) in function.blocks[0].body.iter().enumerate() {
        let site = catalog
            .fetch(Coordinate {
                function: function.id,
                block: function.entry,
                instruction: pc,
            })
            .unwrap();
        if let Inst::Store {
            ptr, value, align, ..
        } = &node.inst
        {
            let index = symbolic[&value.index()];
            let bound = if matches!(fault, Fault::WrongWordBound) && index == 4 {
                &bounds[0]
            } else {
                &bounds[index]
            };
            let codec = uint_codec(model.context(), &values[index], bound);
            let ptr = app("ir_getd", [current.machine(), nat(u64::from(ptr.index()))]);
            let mem = app("ir_byte_world_memory_v1", [c("Nat"), current.world.clone()]);
            let align = nat(align.unwrap_or(0));
            let dest = address + 8 * index as u64;
            let stored = assembler
                .byte_store_eight(
                    &codec,
                    ByteStoreEight {
                        pointer: ptr.clone(),
                        address: nat(dest),
                        requested_align: align.clone(),
                        memory: mem.clone(),
                    },
                    ByteStoreEightPremises {
                        pointer: conversion(
                            app("IROption", [c("Nat")]),
                            app("ir_byte_pointer_address_v1", [ptr]),
                            some("Nat", nat(dest)),
                        ),
                        accessible: truth(app(
                            "ir_byte_accessible_v1",
                            [
                                app("ir_byte_mem_allocs_v1", [mem]),
                                nat(dest),
                                nat(8),
                                app(
                                    "ir_byte_effective_align_v1",
                                    [
                                        align,
                                        app("ir_byte_layout_align_v1", [codec.layout.clone()]),
                                    ],
                                ),
                            ],
                        )),
                    },
                )
                .unwrap();
            let checks = site
                .memory_checks(&model, &current, &stored.result)
                .unwrap();
            let bridge = assembler
                .conversion(
                    c("IRByteMemoryResultV1"),
                    checks.evaluation,
                    stored.evaluated.left().clone(),
                )
                .unwrap();
            let evaluated = assembler.compose(bridge, stored.evaluated).unwrap();
            let transfer = site
                .memory_value(
                    &mut assembler,
                    &model,
                    &current,
                    stored.result,
                    MemoryPremises {
                        evaluated,
                        allocations: stored.allocations,
                        result: truth(checks.result),
                        before: valid,
                    },
                )
                .unwrap();
            run = assembler.concatenate(run, transfer.run().clone()).unwrap();
            current = transfer.current().clone();
            valid = transfer.valid().clone();
            continue;
        }
        if matches!(node.inst, Inst::Return { .. }) {
            let step = site
                .step(&mut assembler, &model, &current, valid.clone())
                .unwrap();
            let end = assembler
                .conversion(
                    model.config_type(),
                    step.right().clone(),
                    terminal(
                        address,
                        &values,
                        if matches!(fault, Fault::UnwrittenByte) {
                            app(
                                "ir_byte_write_word_v1",
                                [bytes.term().clone(), nat(200), nat(1), nat(9)],
                            )
                        } else {
                            bytes.term().clone()
                        },
                    ),
                )
                .unwrap();
            let step = assembler.compose(step, end).unwrap();
            let returned = assembler
                .one_step(&model, current.running(&model), step)
                .unwrap();
            run = assembler.concatenate(run, returned).unwrap();
            continue;
        }
        let result = node.results[0].index();
        let value = match &node.inst {
            Inst::Const {
                value: Constant::Int(n),
                ..
            } => {
                let n = u64::try_from(*n).unwrap();
                concrete.insert(result, n);
                scalar(nat(n))
            }
            Inst::Copy { operand, .. } if symbolic.contains_key(&operand.index()) => {
                let index = symbolic[&operand.index()];
                symbolic.insert(result, index);
                scalar(values[index].clone())
            }
            Inst::Copy { operand, .. } => {
                let n = concrete[&operand.index()];
                concrete.insert(result, n);
                scalar(nat(n))
            }
            Inst::Cast { op, operand, .. } => {
                let n = concrete[&operand.index()];
                concrete.insert(result, n);
                match op {
                    CastOp::PtrToPtr | CastOp::IntToPtr => pointer(n),
                    CastOp::PtrToInt => scalar(nat(n)),
                    _ => panic!("cast"),
                }
            }
            Inst::BinOp { op, lhs, rhs, .. } => {
                let a = concrete[&lhs.index()];
                let b = concrete[&rhs.index()];
                let n = match op {
                    BinOp::Add => a.checked_add(b).unwrap(),
                    BinOp::Mul => a.checked_mul(b).unwrap(),
                    _ => panic!("binop"),
                };
                concrete.insert(result, n);
                scalar(nat(n))
            }
            _ => panic!("captured scalar"),
        };
        let checks = site.scalar_checks(&model, &current, value.clone()).unwrap();
        let (evaluated, result_fits) = if let Some(index) = symbolic.get(&result) {
            let fit = fits(model.context(), &values[*index], &bounds[*index]);
            let choose = Expr::apps(
                Expr::const_(
                    Name::from_string("Bool.rec"),
                    vec![Level::succ(Level::zero())],
                ),
                [
                    Expr::lam(BinderInfo::Default, c("Bool"), c("IRStepResult")),
                    app(
                        "IRStepResult.fault",
                        [app("IROutcome.type_error", [c("IRFault.bad_field")])],
                    ),
                    app("IRStepResult.value", [value.clone()]),
                    Expr::bvar(0),
                ],
            );
            let proof = app(
                "ir_eq_cong",
                [
                    c("Bool"),
                    c("IRStepResult"),
                    Expr::lam(BinderInfo::Default, c("Bool"), choose),
                    fit.left().clone(),
                    c("Bool.true"),
                    fit.term().clone(),
                ],
            );
            let result_fit = conjunction(
                truth(c("Bool.true")),
                conjunction(fit, truth(c("Bool.true"))),
            );
            (
                PendingEquality::candidate(
                    c("IRStepResult"),
                    checks.evaluation,
                    app("IRStepResult.value", [value.clone()]),
                    proof,
                ),
                PendingEquality::candidate(
                    c("Bool"),
                    checks.result,
                    c("Bool.true"),
                    result_fit.term().clone(),
                ),
            )
        } else {
            (
                conversion(
                    c("IRStepResult"),
                    checks.evaluation,
                    app("IRStepResult.value", [value.clone()]),
                ),
                truth(checks.result),
            )
        };
        let transfer = site
            .scalar_value(
                &mut assembler,
                &model,
                &current,
                value,
                ScalarPremises {
                    evaluated,
                    operands: truth(checks.operands),
                    result: result_fits,
                    before: valid,
                },
            )
            .unwrap();
        run = assembler.concatenate(run, transfer.run().clone()).unwrap();
        current = transfer.current().clone();
        valid = transfer.valid().clone();
    }
    let mapped = assembler
        .congruence(
            initialized.equality().clone(),
            model.config_type(),
            |state| model.run(run.fuel(), state),
        )
        .unwrap();
    let before = assembler
        .conversion(
            model.config_type(),
            model.run(
                &NatTerm::literal(51),
                initial(&model, address, &values, bytes.term().clone()),
            ),
            mapped.left().clone(),
        )
        .unwrap();
    let after = assembler
        .conversion(
            model.config_type(),
            mapped.right().clone(),
            run.equality().left().clone(),
        )
        .unwrap();
    let proof = assembler.compose(before, mapped).unwrap();
    let proof = assembler.compose(proof, after).unwrap();
    let proof = assembler.compose(proof, run.equality().clone()).unwrap();
    let mut term = bytes.lam(proof.term().clone());
    for local in bounds.iter().rev().chain(words.iter().rev()) {
        term = local.lam(term);
    }
    let term = scope.close(&term).unwrap();
    trust_ir::proof::encode_clean_expr_dag_v2(&term).unwrap()
}

fn reject_symbolic(
    checker: &TranslationRechecker<SymbolicWriter>,
    label: &str,
    address: u64,
    module: &Module,
    proof: &[u8],
) {
    let error = checker
        .recheck_dag_v2(&address, module, proof)
        .expect_err(label);
    assert_eq!(error.stage(), "kernel audit", "{label}: {error}");
    assert!(error.reason().contains("TypeMismatch"), "{label}: {error}");
    for resource in [
        "heartbeat",
        "budget",
        "timeout",
        "fuel exhausted",
        "recursion limit",
    ] {
        assert!(
            !error.reason().to_ascii_lowercase().contains(resource),
            "{label}: {error}"
        );
    }
    if let Some(directory) = std::env::var_os("TCG_CORE_BYTE_WRITER_EXPORT") {
        let directory = std::path::Path::new(&directory);
        std::fs::write(
            directory.join(format!("reject-{label}.json")),
            serde_json::to_vec_pretty(&serde_json::json!({
                "label":label,"stage":error.stage(),"reason":error.reason()
            }))
            .unwrap(),
        )
        .unwrap();
        std::fs::write(directory.join(format!("{label}.rejected-dag")), proof).unwrap();
    }
}

#[test]
fn writer_replays_all_canonical_input_words() {
    let module = module();
    let checker = TranslationRechecker::<SymbolicWriter>::new(Default::default()).unwrap();
    let mut retained = None;
    for address in [80, 88] {
        let proof = assemble(&module, address, Fault::None);
        let checked = checker.recheck_dag_v2(&address, &module, &proof).unwrap();
        assert!(std::ptr::eq(checked.target(), &module));
        assert_eq!(checked.source(), &address);
        assert_eq!(checked.proof_term(), proof);
        if let Some(directory) = std::env::var_os("TCG_CORE_BYTE_WRITER_EXPORT") {
            let directory = std::path::Path::new(&directory);
            std::fs::write(
                directory.join(format!("symbolic-writer-{address}.dag")),
                &proof,
            )
            .unwrap();
            std::fs::write(directory.join(format!("symbolic-writer-{address}.json")), serde_json::to_vec_pretty(&serde_json::json!({
                "address":address,"proof_bytes":proof.len(),
                "instructions":51,"stores":5,"quantified":"five independent words below 2^64 and all initial byte maps"
            })).unwrap()).unwrap();
        }
        if address == 80 {
            retained = Some(proof);
        }
    }
    let proof = retained.unwrap();
    reject_symbolic(&checker, "symbolic-reused-address", 88, &module, &proof);
    let mut changed = module.clone();
    let Inst::Store { value, .. } = &mut changed.functions[0].blocks[0].body[49].inst else {
        panic!("last captured store")
    };
    *value = ValueId::new(2);
    reject_symbolic(&checker, "symbolic-changed-store", 80, &changed, &proof);
    for (fault, label) in [
        (Fault::WrongWordBound, "symbolic-wrong-word-bound"),
        (Fault::UnwrittenByte, "symbolic-unwritten-byte"),
    ] {
        let wrong = assemble(&module, 80, fault);
        reject_symbolic(&checker, label, 80, &module, &wrong);
    }
}
