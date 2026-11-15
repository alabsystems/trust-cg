// Copyright 2026 Andrew Yates | Apache-2.0

//! Whole captured execution for arbitrary caller memory and positive addresses.
//! The premises are the actual entry ownership, word range and access guards.
//! They are not inferred from RefMut and supply no native frame authority.

use super::*;

#[path = "retirement.rs"]
mod retirement;

#[path = "private_frame.rs"]
mod private_frame;

#[derive(Clone, Copy, Debug)]
enum CallerFault {
    None,
    WrongAddressBound,
    WrongWordBound,
    WrongAccess,
    Host,
    UnwrittenByte,
}

struct Caller {
    binders: Vec<ScopedLocal>,
    predecessor: Expr,
    words: Vec<Expr>,
    rows: Expr,
    bytes: Expr,
    cursor: Expr,
    host: Expr,
    address_bounds: Vec<ScopedLocal>,
    word_bounds: Vec<ScopedLocal>,
    admitted: ScopedLocal,
    accesses: Vec<ScopedLocal>,
}

impl Caller {
    fn new(scope: &mut LocalScope) -> Self {
        let mut binders = Vec::new();
        let mut local = |ty| {
            let value = scope.try_local(ty).unwrap();
            binders.push(value.clone());
            value
        };
        let predecessor = local(c("Nat")).term().clone();
        let words: Vec<_> = (0..5).map(|_| local(c("Nat")).term().clone()).collect();
        let rows = local(app("IRList", [c("IRByteAllocationV1")]))
            .term()
            .clone();
        let bytes = local(bytes_type()).term().clone();
        let cursor = local(c("Nat")).term().clone();
        let host = local(c("Nat")).term().clone();
        let address_bounds = (0..5)
            .map(|i| {
                local(app(
                    "Nat.lt",
                    [address(&predecessor, i), c("ir_byte_limit_v1")],
                ))
            })
            .collect();
        let word_bounds = words
            .iter()
            .map(|word| local(app("Nat.lt", [word.clone(), c("ir_byte_limit_v1")])))
            .collect();
        let memory = app(
            "IRByteMemoryV1.mk",
            [rows.clone(), bytes.clone(), cursor.clone()],
        );
        let admitted = local(eq(
            c("Bool"),
            EntryTarget::memory_admission(memory),
            c("Bool.true"),
        ));
        let accesses = (0..5)
            .map(|i| {
                local(eq(
                    c("Bool"),
                    access(rows.clone(), address(&predecessor, i)),
                    c("Bool.true"),
                ))
            })
            .collect();
        Self {
            binders,
            predecessor,
            words,
            rows,
            bytes,
            cursor,
            host,
            address_bounds,
            word_bounds,
            admitted,
            accesses,
        }
    }
    fn address(&self, index: usize) -> Expr {
        address(&self.predecessor, index)
    }
    fn memory(&self, bytes: Expr) -> Expr {
        app(
            "IRByteMemoryV1.mk",
            [self.rows.clone(), bytes, self.cursor.clone()],
        )
    }
    fn arguments(&self) -> Expr {
        let mut args = vec![ptr(self.address(0))];
        args.extend(self.words.iter().cloned().map(scalar));
        list("IRScalar", &args)
    }
    fn initial(&self, model: &MachineModel) -> Expr {
        app(
            "ir_byte_init_v1",
            [
                c("Nat"),
                model.context().clone(),
                nat(0),
                self.arguments(),
                self.memory(self.bytes.clone()),
                self.host.clone(),
            ],
        )
    }
    fn terminal(&self) -> Expr {
        self.terminal_with(CallerFault::None)
    }
    fn terminal_with(&self, fault: CallerFault) -> Expr {
        self.terminal_with_rows(self.rows.clone(), fault)
    }
    fn terminal_with_rows(&self, rows: Expr, fault: CallerFault) -> Expr {
        let mut bytes = self.bytes.clone();
        for i in 0..5 {
            bytes = app(
                "ir_byte_write_word_v1",
                [bytes, self.address(i), nat(8), self.words[i].clone()],
            );
        }
        if matches!(fault, CallerFault::UnwrittenByte) {
            bytes = app("ir_byte_write_word_v1", [bytes, nat(1), nat(1), nat(9)]);
        }
        let owner = app("ir_byte_fresh_owner_v1", [self.memory(self.bytes.clone())]);
        let memory = app("IRByteMemoryV1.mk", [rows, bytes, self.cursor.clone()]);
        app(
            "IRByteConfigV1.halted",
            [
                c("Nat"),
                app("IROutcome.ret", [list("IRScalar", &[])]),
                app(
                    "IRByteWorldV1.mk",
                    [
                        c("Nat"),
                        memory,
                        if matches!(fault, CallerFault::Host) {
                            app("Nat.succ", [self.host.clone()])
                        } else {
                            self.host.clone()
                        },
                        list("Nat", &[]),
                        app("Nat.succ", [owner]),
                    ],
                ),
            ],
        )
    }
    fn close(&self, mut body: Expr, proof: bool) -> Expr {
        for local in self.binders.iter().rev() {
            body = if proof {
                local.lam(body)
            } else {
                local.pi(body)
            };
        }
        body
    }
    fn bounded(&self, index: usize) -> PendingEquality {
        let word = self.address(index);
        PendingEquality::candidate(
            c("Bool"),
            app("ir_nat_ltb", [word.clone(), c("ir_byte_limit_v1")]),
            c("Bool.true"),
            app(
                "ir_byte_ltb_of_lt_v1",
                [
                    word,
                    c("ir_byte_limit_v1"),
                    self.address_bounds[index].term().clone(),
                ],
            ),
        )
    }
    fn pointer_fit(&self, context: &Expr, index: usize) -> PendingEquality {
        let predecessor = app("Nat.add", [self.predecessor.clone(), nat(8 * index as u64)]);
        PendingEquality::candidate(
            c("Bool"),
            app(
                "ir_byte_value_matches_v1",
                [context.clone(), c("IRTy.ptr_"), ptr(self.address(index))],
            ),
            c("Bool.true"),
            app(
                "ir_byte_pointer_value_fits_v1",
                [
                    context.clone(),
                    predecessor,
                    self.address_bounds[index].term().clone(),
                ],
            ),
        )
    }
    fn address_fit(&self, context: &Expr, index: usize) -> PendingEquality {
        PendingEquality::candidate(
            c("Bool"),
            app(
                "ir_byte_value_matches_v1",
                [
                    context.clone(),
                    app("IRTy.int_", [nat(64)]),
                    scalar(self.address(index)),
                ],
            ),
            c("Bool.true"),
            app(
                "ir_byte_i64_value_fits_v1",
                [
                    context.clone(),
                    self.address(index),
                    self.bounded(index).term().clone(),
                ],
            ),
        )
    }
}

fn address(predecessor: &Expr, index: usize) -> Expr {
    app(
        "Nat.add",
        [
            app("Nat.succ", [predecessor.clone()]),
            nat(8 * index as u64),
        ],
    )
}
fn ptr(word: Expr) -> Expr {
    app("IRScalar.ptr_", [word])
}
fn access(rows: Expr, address: Expr) -> Expr {
    app("ir_byte_accessible_v1", [rows, address, nat(8), nat(8)])
}

struct CallerWriter;
impl SourceTranslationModel for CallerWriter {
    type Source = ();
    fn build_environment() -> Result<Environment, String> {
        WriterModel::build_environment()
    }
    fn reconstruct(_: &(), target: &Module) -> Result<Expr, String> {
        // Reuse the established captured-module/signature profile, not its
        // concrete invocation claim. This model quantifies its own caller state.
        let _ = SymbolicWriter::reconstruct(&80, target)?;
        let reflected =
            reflect_core_module_v1(target, &[(FuncId::new(0), 4096)]).map_err(|e| e.to_string())?;
        let model = MachineModel::new(c("Nat"), &reflected, providers());
        let mut scope = LocalScope::new();
        let caller = Caller::new(&mut scope);
        let claim = eq(
            model.config_type(),
            model.run(&NatTerm::literal(51), caller.initial(&model)),
            caller.terminal(),
        );
        scope
            .close(&caller.close(claim, false))
            .map_err(|e| e.to_string())
    }
}

fn case_true(
    guard: &PendingEquality,
    failure: Expr,
    success: Expr,
    expected: Expr,
    step: Expr,
) -> Expr {
    app(
        "ir_byte_case_true_v1",
        [
            c("IRStepResult"),
            guard.left().clone(),
            failure,
            success,
            expected,
            guard.term().clone(),
            step,
        ],
    )
}
fn type_fault() -> Expr {
    app(
        "IRStepResult.fault",
        [app("IROutcome.type_error", [c("IRFault.bad_field")])],
    )
}
fn value(word: Expr) -> Expr {
    app("IRStepResult.value", [word])
}

fn cast_equality(
    assembler: &mut Assembler<'_>,
    evaluation: Expr,
    result: Expr,
    source_fits: PendingEquality,
    destination_fits: PendingEquality,
    computed: PendingEquality,
) -> PendingEquality {
    let args = evaluation.get_app_args();
    let context = args[0].clone();
    let destination = args[3].clone();
    drop(args);
    let complete = value(result);
    let mapped = assembler
        .congruence(computed, c("IRStepResult"), |step| {
            app(
                "ir_byte_cast_result_v1",
                [context.clone(), destination.clone(), step],
            )
        })
        .unwrap();
    let finished = PendingEquality::candidate(
        c("IRStepResult"),
        mapped.right().clone(),
        complete.clone(),
        case_true(
            &destination_fits,
            type_fault(),
            complete.clone(),
            complete.clone(),
            refl(c("IRStepResult"), complete.clone()),
        ),
    );
    let inner = assembler.compose(mapped, finished).unwrap();
    let proof = case_true(
        &source_fits,
        type_fault(),
        inner.left().clone(),
        complete.clone(),
        inner.term().clone(),
    );
    PendingEquality::candidate(c("IRStepResult"), evaluation, complete, proof)
}

#[derive(Clone, Copy)]
enum Known {
    Literal(u64),
    Address(usize),
    Input(usize),
}

fn assemble_caller(module: &Module, fault: CallerFault) -> Vec<u8> {
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
    let mut caller = Caller::new(&mut scope);
    if matches!(fault, CallerFault::WrongAddressBound) {
        caller.address_bounds[0] = caller.address_bounds[1].clone();
    }
    let mut assembler = Assembler::new(&mut scope, limits()).unwrap();
    let mut arguments_fit = truth(c("Bool.true"));
    for (word, bound) in caller.words.iter().zip(&caller.word_bounds).rev() {
        arguments_fit = conjunction(fits(model.context(), word, bound), arguments_fit);
    }
    arguments_fit = conjunction(caller.pointer_fit(model.context(), 0), arguments_fit);
    let memory = caller.memory(caller.bytes.clone());
    let initialized = entry
        .initialize(
            &mut assembler,
            &model,
            caller.arguments(),
            memory.clone(),
            caller.host.clone(),
            PendingEquality::candidate(
                c("Bool"),
                EntryTarget::memory_admission(memory),
                c("Bool.true"),
                caller.admitted.term().clone(),
            ),
            PendingEquality::candidate(
                c("Bool"),
                entry.admission(&model, caller.arguments()).unwrap(),
                c("Bool.true"),
                arguments_fit.term().clone(),
            ),
        )
        .unwrap();
    let mut current = initialized.current().clone();
    let mut valid = initialized.valid().clone();
    let mut run = assembler.zero(&model, current.running(&model)).unwrap();
    let mut known = HashMap::from([(1_u32, Known::Address(0))]);
    for i in 0..5 {
        known.insert(i as u32 + 2, Known::Input(i));
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
            let Known::Address(dest) = known[&ptr.index()] else {
                panic!("address")
            };
            let Known::Input(index) = known[&value.index()] else {
                panic!("word")
            };
            let bound = if matches!(fault, CallerFault::WrongWordBound) && index == 0 {
                1
            } else {
                index
            };
            let codec = uint_codec(
                model.context(),
                &caller.words[index],
                &caller.word_bounds[bound],
            );
            let pointer = app("ir_getd", [current.machine(), nat(u64::from(ptr.index()))]);
            let mem = app("ir_byte_world_memory_v1", [c("Nat"), current.world.clone()]);
            let stored = assembler
                .byte_store_eight(
                    &codec,
                    ByteStoreEight {
                        pointer: pointer.clone(),
                        address: caller.address(dest),
                        requested_align: nat(align.unwrap_or(0)),
                        memory: mem.clone(),
                    },
                    ByteStoreEightPremises {
                        pointer: PendingEquality::candidate(
                            app("IROption", [c("Nat")]),
                            app("ir_byte_pointer_address_v1", [pointer]),
                            some("Nat", caller.address(dest)),
                            app(
                                "ir_byte_pointer_address_bounded_v1",
                                [
                                    caller.address(dest),
                                    caller.address_bounds[dest].term().clone(),
                                ],
                            ),
                        ),
                        accessible: PendingEquality::candidate(
                            c("Bool"),
                            app(
                                "ir_byte_accessible_v1",
                                [
                                    app("ir_byte_mem_allocs_v1", [mem]),
                                    caller.address(dest),
                                    nat(8),
                                    app(
                                        "ir_byte_effective_align_v1",
                                        [
                                            nat(align.unwrap_or(0)),
                                            app("ir_byte_layout_align_v1", [codec.layout.clone()]),
                                        ],
                                    ),
                                ],
                            ),
                            c("Bool.true"),
                            caller.accesses[if matches!(fault, CallerFault::WrongAccess)
                                && dest == 0
                            {
                                1
                            } else {
                                dest
                            }]
                            .term()
                            .clone(),
                        ),
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
            let owner = app(
                "ir_byte_fresh_owner_v1",
                [caller.memory(caller.bytes.clone())],
            );
            let retired_rows = app(
                "ir_byte_retire_allocs_v1",
                [owner.clone(), caller.rows.clone()],
            );
            let end = assembler
                .conversion(
                    model.config_type(),
                    step.right().clone(),
                    caller.terminal_with_rows(retired_rows.clone(), fault),
                )
                .unwrap();
            let preserved_rows = PendingEquality::candidate(
                app("IRList", [c("IRByteAllocationV1")]),
                retired_rows,
                caller.rows.clone(),
                Expr::apps(
                    retirement::proof_term(),
                    [
                        caller.rows.clone(),
                        caller.bytes.clone(),
                        caller.cursor.clone(),
                        owner,
                        caller.admitted.term().clone(),
                    ],
                ),
            );
            let preserved_world = assembler
                .congruence(preserved_rows, model.config_type(), |rows| {
                    caller.terminal_with_rows(rows, fault)
                })
                .unwrap();
            // Congruence retains a lambda application at each endpoint. The
            // assembler requires explicit checked conversion to the raw state.
            let before_preservation = assembler
                .conversion(
                    model.config_type(),
                    end.right().clone(),
                    preserved_world.left().clone(),
                )
                .unwrap();
            let after_preservation = assembler
                .conversion(
                    model.config_type(),
                    preserved_world.right().clone(),
                    caller.terminal_with(fault),
                )
                .unwrap();
            let step = assembler.compose(step, end).unwrap();
            let step = assembler.compose(step, before_preservation).unwrap();
            let step = assembler.compose(step, preserved_world).unwrap();
            let step = assembler.compose(step, after_preservation).unwrap();
            let returned = assembler
                .one_step(&model, current.running(&model), step)
                .unwrap();
            run = assembler.concatenate(run, returned).unwrap();
            continue;
        }
        let (kind, pointer) = match &node.inst {
            Inst::Const {
                value: Constant::Int(n),
                ..
            } => (Known::Literal(u64::try_from(*n).unwrap()), false),
            Inst::Copy { operand, .. } => (known[&operand.index()], false),
            Inst::Cast { op, operand, .. } => (known[&operand.index()], *op != CastOp::PtrToInt),
            Inst::BinOp { op, lhs, rhs, .. } => {
                match (op, known[&lhs.index()], known[&rhs.index()]) {
                    (BinOp::Mul, Known::Literal(a), Known::Literal(b)) => {
                        (Known::Literal(a.checked_mul(b).unwrap()), false)
                    }
                    (BinOp::Add, Known::Address(0), Known::Literal(offset))
                        if offset % 8 == 0 && offset <= 32 =>
                    {
                        (Known::Address(offset as usize / 8), false)
                    }
                    _ => panic!("captured arithmetic"),
                }
            }
            _ => panic!("captured scalar"),
        };
        let word = match kind {
            Known::Literal(n) => nat(n),
            Known::Address(i) => caller.address(i),
            Known::Input(i) => caller.words[i].clone(),
        };
        let output = if pointer {
            ptr(word.clone())
        } else {
            scalar(word.clone())
        };
        let checks = site
            .scalar_checks(&model, &current, output.clone())
            .unwrap();
        let fit = match kind {
            Known::Literal(_) => truth(app(
                "ir_byte_value_matches_v1",
                [
                    model.context().clone(),
                    app("IRTy.int_", [nat(64)]),
                    output.clone(),
                ],
            )),
            Known::Address(i) if pointer => caller.pointer_fit(model.context(), i),
            Known::Address(i) => caller.address_fit(model.context(), i),
            Known::Input(i) => fits(model.context(), &caller.words[i], &caller.word_bounds[i]),
        };
        let evaluated = match &node.inst {
            Inst::Copy { .. } if matches!(kind, Known::Input(_)) => PendingEquality::candidate(
                c("IRStepResult"),
                checks.evaluation.clone(),
                value(output.clone()),
                case_true(
                    &fit,
                    type_fault(),
                    value(output.clone()),
                    value(output.clone()),
                    refl(c("IRStepResult"), value(output.clone())),
                ),
            ),
            Inst::BinOp { op: BinOp::Add, .. } => {
                let Known::Address(index) = kind else {
                    panic!("sum")
                };
                PendingEquality::candidate(
                    c("IRStepResult"),
                    checks.evaluation.clone(),
                    value(output.clone()),
                    app(
                        "ir_byte_add_int_below_v1",
                        [
                            nat(64),
                            caller.address(0),
                            nat(8 * index as u64),
                            caller.bounded(index).term().clone(),
                        ],
                    ),
                )
            }
            Inst::Cast { op, .. } => {
                let Known::Address(index) = kind else {
                    panic!("cast address")
                };
                let args = checks.evaluation.get_app_args();
                let compute = app(
                    "ir_byte_cast_compute_v1",
                    [
                        args[1].clone(),
                        args[2].clone(),
                        args[3].clone(),
                        args[4].clone(),
                    ],
                );
                let computed = if *op == CastOp::PtrToInt {
                    let address_eq = app(
                        "ir_byte_pointer_address_bounded_v1",
                        [word.clone(), caller.address_bounds[index].term().clone()],
                    );
                    PendingEquality::candidate(
                        c("IRStepResult"),
                        compute,
                        value(output.clone()),
                        app(
                            "ir_byte_case_some_v1",
                            [
                                c("Nat"),
                                c("IRStepResult"),
                                app("ir_byte_pointer_address_v1", [ptr(word.clone())]),
                                word.clone(),
                                type_fault(),
                                Expr::lam(
                                    BinderInfo::Default,
                                    c("Nat"),
                                    value(scalar(Expr::bvar(0))),
                                ),
                                value(output.clone()),
                                address_eq,
                                refl(c("IRStepResult"), value(output.clone())),
                            ],
                        ),
                    )
                } else {
                    conversion(c("IRStepResult"), compute, value(output.clone()))
                };
                let source_fit = if *op == CastOp::IntToPtr {
                    caller.address_fit(model.context(), index)
                } else {
                    caller.pointer_fit(model.context(), index)
                };
                cast_equality(
                    &mut assembler,
                    checks.evaluation.clone(),
                    output.clone(),
                    source_fit,
                    fit.clone(),
                    computed,
                )
            }
            _ => conversion(
                c("IRStepResult"),
                checks.evaluation.clone(),
                value(output.clone()),
            ),
        };
        let operands = if let Inst::BinOp { op: BinOp::Add, .. } = node.inst {
            let both = conjunction(
                caller.address_fit(model.context(), 0),
                truth(c("Bool.true")),
            );
            PendingEquality::candidate(
                c("Bool"),
                checks.operands,
                c("Bool.true"),
                both.term().clone(),
            )
        } else {
            truth(checks.operands)
        };
        let result_fits = conjunction(
            truth(c("Bool.true")),
            conjunction(fit, truth(c("Bool.true"))),
        );
        let transfer = site
            .scalar_value(
                &mut assembler,
                &model,
                &current,
                output,
                ScalarPremises {
                    evaluated,
                    operands,
                    result: PendingEquality::candidate(
                        c("Bool"),
                        checks.result,
                        c("Bool.true"),
                        result_fits.term().clone(),
                    ),
                    before: valid,
                },
            )
            .unwrap();
        run = assembler.concatenate(run, transfer.run().clone()).unwrap();
        current = transfer.current().clone();
        valid = transfer.valid().clone();
        known.insert(node.results[0].index(), kind);
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
            model.run(&NatTerm::literal(51), caller.initial(&model)),
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
    let term = scope
        .close(&caller.close(proof.term().clone(), true))
        .unwrap();
    trust_ir::proof::encode_clean_expr_dag_v2(&term).unwrap()
}

#[test]
fn writer_replays_arbitrary_caller_memory() {
    let module = module();
    let checker = TranslationRechecker::<CallerWriter>::new(Default::default()).unwrap();
    let proof = assemble_caller(&module, CallerFault::None);
    let checked = checker.recheck_dag_v2(&(), &module, &proof).unwrap();
    export(
        "caller-writer",
        checked.proof_term(),
        serde_json::json!({
            "proof_bytes":proof.len(), "instructions":51,
            "quantified":"positive address, five canonical words, allocation history, initial bytes, cursor and host",
            "premises":"actual entry ownership, five address bounds, five word bounds and five actual live access guards",
            "terminal":"five writes, unchanged allocation history/cursor/host, empty active owner list and actual next-owner counter; root retirement preservation kernel-proved"
        }),
    );
    // Apply this same universal proof to genuinely different valid caller
    // histories, including a store ending at the last 64-bit byte address.
    let mut boundary = invocation();
    boundary.address = u64::MAX - 39;
    boundary.allocations[0].base = boundary.address;
    boundary.allocations[0].size = 40;
    boundary.allocations[1].owner = 41;
    boundary.allocations.swap(0, 2);
    boundary.cursor = 0;
    boundary.host = 123;
    boundary.words = [42, 17, 0, u64::MAX, 1];
    for call in [invocation(), boundary] {
        let instance = instantiate(&proof, &call);
        let checked = super::super::checker()
            .recheck_dag_v2(&call, &module, &instance)
            .unwrap();
        export(
            &format!("caller-{}", call.address),
            checked.proof_term(),
            serde_json::json!({
                "address":call.address,"proof_bytes":instance.len(),
                "instructions":51,"instantiated_universal_proof":true,"all_initial_bytes":true
            }),
        );
    }
    for fault in [
        CallerFault::WrongAddressBound,
        CallerFault::WrongWordBound,
        CallerFault::WrongAccess,
        CallerFault::Host,
        CallerFault::UnwrittenByte,
    ] {
        let wrong = assemble_caller(&module, fault);
        reject_caller(&checker, &format!("caller-{fault:?}"), &module, &wrong);
    }
    let mut wrong = module.clone();
    let Inst::Store { value, .. } = &mut wrong.functions[0].blocks[0].body[49].inst else {
        panic!("store")
    };
    *value = ValueId::new(2);
    reject_caller(&checker, "caller-changed-store", &wrong, &proof);
    let mut wrong = module.clone();
    let Inst::Const { value, .. } = &mut wrong.functions[0].blocks[0].body[40].inst else {
        panic!("offset")
    };
    *value = Constant::Int(5);
    reject_caller(&checker, "caller-changed-offset", &wrong, &proof);
    for (label, retired) in [
        ("caller-retired-instance", true),
        ("caller-short-instance", false),
    ] {
        let mut call = invocation();
        if retired {
            call.allocations[0].live = false;
        } else {
            call.allocations[0].size = 32;
        }
        let wrong = instantiate(&proof, &call);
        super::super::reject(label, &call, &module, &wrong, "kernel audit");
        if let Some(directory) = std::env::var_os("TCG_CORE_BYTE_WRITER_EXPORT") {
            std::fs::write(
                std::path::Path::new(&directory).join(format!("{label}.rejected-dag")),
                wrong,
            )
            .unwrap();
        }
    }
}

fn export(label: &str, proof: &[u8], record: serde_json::Value) {
    if let Some(directory) = std::env::var_os("TCG_CORE_BYTE_WRITER_EXPORT") {
        let directory = std::path::Path::new(&directory);
        std::fs::write(directory.join(format!("{label}.dag")), proof).unwrap();
        std::fs::write(
            directory.join(format!("{label}.json")),
            serde_json::to_vec_pretty(&record).unwrap(),
        )
        .unwrap();
    }
}

fn instantiate(proof: &[u8], call: &WriterCall) -> Vec<u8> {
    let proof = trust_ir::proof::decode_clean_expr_dag_v2(proof).unwrap();
    let mut scope = LocalScope::new();
    let bytes = scope.try_local(bytes_type()).unwrap();
    let mut arguments = vec![nat(call.address.checked_sub(1).unwrap())];
    arguments.extend(call.words.iter().copied().map(nat));
    arguments.extend([
        allocation_rows(call),
        bytes.term().clone(),
        nat(call.cursor),
        nat(call.host),
    ]);
    // Nat.lt word 2^64 is Nat.le (succ word) 2^64. This checked standard
    // arithmetic law supplies the bound with a compact concrete addend.
    let bound = |word| {
        app(
            "Nat.le_add_right",
            [app("Nat.succ", [nat(word)]), nat(u64::MAX - word)],
        )
    };
    arguments.extend((0..5).map(|i| bound(call.address.checked_add(8 * i).unwrap())));
    arguments.extend(call.words.iter().copied().map(bound));
    arguments.extend((0..6).map(|_| refl(c("Bool"), c("Bool.true"))));
    let instance = scope
        .close(&bytes.lam(Expr::apps(proof, arguments)))
        .unwrap();
    trust_ir::proof::encode_clean_expr_dag_v2(&instance).unwrap()
}

fn reject_caller(
    checker: &TranslationRechecker<CallerWriter>,
    label: &str,
    module: &Module,
    proof: &[u8],
) {
    let error = checker.recheck_dag_v2(&(), module, proof).expect_err(label);
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
            serde_json::to_vec_pretty(
                &serde_json::json!({"label":label,"stage":error.stage(),"reason":error.reason()}),
            )
            .unwrap(),
        )
        .unwrap();
        std::fs::write(directory.join(format!("{label}.rejected-dag")), proof).unwrap();
    }
}
