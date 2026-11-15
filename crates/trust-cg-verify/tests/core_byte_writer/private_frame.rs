// Copyright 2026 Andrew Yates | Apache-2.0

//! Compose the captured execution with a fresh private sixteen-byte read.
//! Freshness is an actual allocation-history premise, including retired rows.
//! This supplies no native address representation, stack ownership or ABI proof.

use super::*;

fn option_nat() -> Expr {
    app("IROption", [c("Nat")])
}
fn read(bytes: Expr, base: Expr) -> Expr {
    app("ir_byte_read_word_v1", [bytes, nat(16), base])
}
fn final_bytes(config: Expr) -> Expr {
    app(
        "ir_byte_mem_bytes_v1",
        [app(
            "ir_byte_world_memory_v1",
            [c("Nat"), app("ir_byte_final_world_v1", [c("Nat"), config])],
        )],
    )
}
fn trans(ty: Expr, left: Expr, middle: Expr, right: Expr, a: Expr, b: Expr) -> Expr {
    Expr::apps(
        Expr::const_(
            Name::from_string("Eq.trans"),
            vec![Level::succ(Level::zero())],
        ),
        [ty, left, middle, right, a, b],
    )
}

struct Frame {
    base: ScopedLocal,
    fresh: ScopedLocal,
    offset: ScopedLocal,
    inside: ScopedLocal,
}
impl Frame {
    fn new(scope: &mut LocalScope, caller: &Caller) -> Self {
        let base = scope.try_local(c("Nat")).unwrap();
        let fresh = scope
            .try_local(eq(
                c("Nat"),
                app(
                    "ir_byte_overlap_count_v1",
                    [caller.rows.clone(), base.term().clone(), nat(16)],
                ),
                nat(0),
            ))
            .unwrap();
        let offset = scope.try_local(c("Nat")).unwrap();
        let inside = scope
            .try_local(app("Nat.lt", [offset.term().clone(), nat(16)]))
            .unwrap();
        Self {
            base,
            fresh,
            offset,
            inside,
        }
    }
    fn address(&self) -> Expr {
        app(
            "Nat.add",
            [self.base.term().clone(), self.offset.term().clone()],
        )
    }
    fn point_claim(&self, caller: &Caller, model: &MachineModel) -> Expr {
        let executed = model.run(&NatTerm::literal(51), caller.initial(model));
        self.offset.pi(self.inside.pi(eq(
            option_nat(),
            Expr::app(final_bytes(executed), self.address()),
            Expr::app(caller.bytes.clone(), self.address()),
        )))
    }
    fn claim(&self, caller: &Caller, model: &MachineModel, wrong_read: bool) -> Expr {
        let executed = model.run(&NatTerm::literal(51), caller.initial(model));
        app(
            "And",
            [
                eq(model.config_type(), executed.clone(), caller.terminal()),
                app(
                    "And",
                    [
                        eq(
                            option_nat(),
                            read(final_bytes(executed), self.base.term().clone()),
                            read(
                                caller.bytes.clone(),
                                if wrong_read {
                                    app("Nat.add", [self.base.term().clone(), nat(8)])
                                } else {
                                    self.base.term().clone()
                                },
                            ),
                        ),
                        self.point_claim(caller, model),
                    ],
                ),
            ],
        )
    }
    fn close(&self, body: Expr, proof: bool) -> Expr {
        if proof {
            self.base.lam(self.fresh.lam(body))
        } else {
            self.base.pi(self.fresh.pi(body))
        }
    }
}

struct FrameWriter;
impl SourceTranslationModel for FrameWriter {
    type Source = bool;
    fn build_environment() -> Result<Environment, String> {
        WriterModel::build_environment()
    }
    fn reconstruct(wrong_read: &bool, target: &Module) -> Result<Expr, String> {
        // Reconstruct the actual captured execution, not a store-trace premise.
        let _ = CallerWriter::reconstruct(&(), target)?;
        let reflected =
            reflect_core_module_v1(target, &[(FuncId::new(0), 4096)]).map_err(|e| e.to_string())?;
        let model = MachineModel::new(c("Nat"), &reflected, providers());
        let mut scope = LocalScope::new();
        let caller = Caller::new(&mut scope);
        let frame = Frame::new(&mut scope, &caller);
        scope
            .close(&caller.close(
                frame.close(frame.claim(&caller, &model, *wrong_read), false),
                false,
            ))
            .map_err(|e| e.to_string())
    }
}

#[derive(Clone, Copy)]
enum Fault {
    None,
    Freshness,
    Access,
    PointBound,
}

fn point_proof(
    caller: &Caller,
    frame: &Frame,
    model: &MachineModel,
    execution: Expr,
    fault: Fault,
) -> Expr {
    let address = frame.address();
    let at = |bytes| Expr::app(bytes, address.clone());
    let original = at(caller.bytes.clone());
    let mut bytes = caller.bytes.clone();
    let mut preserved = refl(option_nat(), original.clone());
    for i in 0..5 {
        let written = app(
            "ir_byte_write_word_v1",
            [
                bytes.clone(),
                caller.address(i),
                nat(8),
                caller.words[i].clone(),
            ],
        );
        let apart = app(
            "ir_byte_fresh_range_disjoint_v1",
            [
                caller.rows.clone(),
                frame.base.term().clone(),
                nat(16),
                nat(0),
                caller.address(i),
                nat(8),
                nat(8),
                app("Nat.zero_lt_succ", [nat(15)]),
                frame.fresh.term().clone(),
                caller.accesses[i].term().clone(),
            ],
        );
        let outside = app(
            "ir_byte_disjoint_range_point_v1",
            [
                frame.base.term().clone(),
                nat(16),
                caller.address(i),
                nat(8),
                frame.offset.term().clone(),
                apart,
                if matches!(fault, Fault::PointBound) {
                    app("Nat.zero_lt_succ", [nat(15)])
                } else {
                    frame.inside.term().clone()
                },
            ],
        );
        let step = app(
            "ir_byte_write_outside_v1",
            [
                bytes.clone(),
                caller.address(i),
                nat(8),
                caller.words[i].clone(),
                address.clone(),
                outside,
            ],
        );
        preserved = trans(
            option_nat(),
            at(written.clone()),
            at(bytes),
            original.clone(),
            step,
            preserved,
        );
        bytes = written;
    }
    let executed = model.run(&NatTerm::literal(51), caller.initial(model));
    let terminal = caller.terminal();
    let projected = app(
        "ir_eq_cong",
        [
            model.config_type(),
            option_nat(),
            Expr::lam(
                BinderInfo::Default,
                model.config_type(),
                at(final_bytes(Expr::bvar(0))),
            ),
            executed.clone(),
            terminal.clone(),
            execution,
        ],
    );
    frame.offset.lam(frame.inside.lam(trans(
        option_nat(),
        at(final_bytes(executed)),
        at(final_bytes(terminal)),
        original,
        projected,
        preserved,
    )))
}

fn assemble(module: &Module, writer: &Expr, fault: Fault) -> Vec<u8> {
    let reflected = reflect_core_module_v1(module, &[(FuncId::new(0), 4096)]).unwrap();
    let model = MachineModel::new(c("Nat"), &reflected, providers());
    let mut scope = LocalScope::new();
    let caller = Caller::new(&mut scope);
    let frame = Frame::new(&mut scope, &caller);
    let executed = model.run(&NatTerm::literal(51), caller.initial(&model));
    let terminal = caller.terminal();
    let actual_execution = Expr::apps(
        writer.clone(),
        caller.binders.iter().map(|v| v.term().clone()),
    );
    let execution_local = scope
        .try_local(eq(model.config_type(), executed.clone(), terminal.clone()))
        .unwrap();
    let execution = execution_local.term().clone();
    let projected = app(
        "ir_eq_cong",
        [
            model.config_type(),
            option_nat(),
            Expr::lam(
                BinderInfo::Default,
                model.config_type(),
                read(final_bytes(Expr::bvar(0)), frame.base.term().clone()),
            ),
            executed.clone(),
            terminal.clone(),
            execution.clone(),
        ],
    );
    let original_read = read(caller.bytes.clone(), frame.base.term().clone());
    let mut bytes = caller.bytes.clone();
    let mut unchanged = refl(option_nat(), original_read.clone());
    for i in 0..5 {
        let written = app(
            "ir_byte_write_word_v1",
            [
                bytes.clone(),
                caller.address(i),
                nat(8),
                caller.words[i].clone(),
            ],
        );
        let step = app(
            "ir_byte_fresh_range_read_preserved_v1",
            [
                bytes.clone(),
                caller.rows.clone(),
                frame.base.term().clone(),
                nat(16),
                nat(0), // This law's row-owner parameter supplies no ownership.
                caller.address(i),
                nat(8),
                nat(8),
                caller.words[i].clone(),
                app("Nat.zero_lt_succ", [nat(15)]),
                if matches!(fault, Fault::Freshness) {
                    refl(c("Nat"), nat(0))
                } else {
                    frame.fresh.term().clone()
                },
                caller.accesses[if matches!(fault, Fault::Access) && i == 0 {
                    1
                } else {
                    i
                }]
                .term()
                .clone(),
            ],
        );
        unchanged = trans(
            option_nat(),
            read(written.clone(), frame.base.term().clone()),
            read(bytes, frame.base.term().clone()),
            original_read.clone(),
            step,
            unchanged,
        );
        bytes = written;
    }
    let observation = trans(
        option_nat(),
        read(final_bytes(executed), frame.base.term().clone()),
        read(final_bytes(terminal), frame.base.term().clone()),
        original_read,
        projected,
        unchanged,
    );
    let claim = frame.claim(&caller, &model, false);
    let parts = claim.get_app_args();
    let observations = parts[1].get_app_args();
    let observations = app(
        "And.intro",
        [
            observations[0].clone(),
            observations[1].clone(),
            observation,
            point_proof(&caller, &frame, &model, execution.clone(), fault),
        ],
    );
    let proof = app(
        "And.intro",
        [parts[0].clone(), parts[1].clone(), execution, observations],
    );
    let term = scope
        .close(&caller.close(
            frame.close(execution_local.let_(actual_execution, proof), true),
            true,
        ))
        .unwrap();
    trust_ir::proof::encode_clean_expr_dag_v2(&term).unwrap()
}

struct FrameInstance;
impl SourceTranslationModel for FrameInstance {
    type Source = (WriterCall, u64);
    fn build_environment() -> Result<Environment, String> {
        WriterModel::build_environment()
    }
    fn reconstruct((call, base): &Self::Source, module: &Module) -> Result<Expr, String> {
        let _ = WriterModel::reconstruct(call, module)?;
        let reflected =
            reflect_core_module_v1(module, &[(FuncId::new(0), 4096)]).map_err(|e| e.to_string())?;
        let model = MachineModel::new(c("Nat"), &reflected, providers());
        let mut scope = LocalScope::new();
        let bytes = scope.try_local(bytes_type()).unwrap();
        let offset = scope.try_local(c("Nat")).unwrap();
        let inside = scope
            .try_local(app("Nat.lt", [offset.term().clone(), nat(16)]))
            .unwrap();
        let address = app("Nat.add", [nat(*base), offset.term().clone()]);
        let mut args = vec![ptr(nat(call.address))];
        args.extend(call.words.iter().copied().map(nat).map(scalar));
        let initial = app(
            "ir_byte_init_v1",
            [
                c("Nat"),
                model.context().clone(),
                nat(0),
                list("IRScalar", &args),
                memory(call, bytes.term().clone()),
                nat(call.host),
            ],
        );
        let executed = model.run(&NatTerm::literal(51), initial);
        let claim = app(
            "And",
            [
                eq(
                    model.config_type(),
                    executed.clone(),
                    expected(call, bytes.term().clone(), Corruption::None),
                ),
                app(
                    "And",
                    [
                        eq(
                            option_nat(),
                            read(final_bytes(executed.clone()), nat(*base)),
                            read(bytes.term().clone(), nat(*base)),
                        ),
                        offset.pi(inside.pi(eq(
                            option_nat(),
                            Expr::app(final_bytes(executed), address.clone()),
                            Expr::app(bytes.term().clone(), address),
                        ))),
                    ],
                ),
            ],
        );
        scope.close(&bytes.pi(claim)).map_err(|e| e.to_string())
    }
}

fn instantiate_frame(proof: &[u8], call: &WriterCall, base: u64) -> Vec<u8> {
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
    let bound = |word| {
        app(
            "Nat.le_add_right",
            [app("Nat.succ", [nat(word)]), nat(u64::MAX - word)],
        )
    };
    arguments.extend((0..5).map(|i| bound(call.address.checked_add(8 * i).unwrap())));
    arguments.extend(call.words.iter().copied().map(bound));
    arguments.extend((0..6).map(|_| refl(c("Bool"), c("Bool.true"))));
    arguments.extend([nat(base), refl(c("Nat"), nat(0))]);
    // Specialize the untrusted candidate before replay. Every remaining proof
    // argument and the independent concrete conclusion still pass the kernel;
    // this normalization itself grants no authority or cached acceptance.
    let mut proof = proof;
    for argument in arguments {
        let clean_kernel::expr::ExprKind::Lam(_, _, body) = proof.kind() else {
            panic!("universal frame proof telescope");
        };
        proof = body.instantiate(&argument);
    }
    let term = scope.close(&bytes.lam(proof)).unwrap();
    trust_ir::proof::encode_clean_expr_dag_v2(&term).unwrap()
}
fn reject<M: SourceTranslationModel>(
    checker: &TranslationRechecker<M>,
    label: &str,
    source: &M::Source,
    module: &Module,
    proof: &[u8],
) {
    let error = checker
        .recheck_dag_v2(source, module, proof)
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
            serde_json::to_vec_pretty(
                &serde_json::json!({"label":label,"stage":error.stage(),"reason":error.reason()}),
            )
            .unwrap(),
        )
        .unwrap();
        std::fs::write(directory.join(format!("{label}.rejected-dag")), proof).unwrap();
    }
}

#[test]
fn writer_preserves_fresh_private_frame() {
    let module = module();
    let writer =
        trust_ir::proof::decode_clean_expr_dag_v2(&assemble_caller(&module, CallerFault::None))
            .unwrap();
    let proof = assemble(&module, &writer, Fault::None);
    let checker = TranslationRechecker::<FrameWriter>::new(Default::default()).unwrap();
    let checked = checker.recheck_dag_v2(&false, &module, &proof).unwrap();
    export(
        "caller-private-frame",
        checked.proof_term(),
        serde_json::json!({
            "proof_bytes":proof.len(),"instructions":51,
            "quantified":"all caller-world inputs and arbitrary private frame base",
            "premises":"actual caller entry, ranges and five access guards; zero allocation-history overlap with the sixteen-byte frame",
            "claim":"complete original terminal world, unchanged sixteen-byte read and pointwise preservation of every private-frame byte in the actual executed result",
            "native_authority":false
        }),
    );
    let instances = TranslationRechecker::<FrameInstance>::new(Default::default()).unwrap();
    for base in [32, 128] {
        let call = invocation();
        let instance = instantiate_frame(&proof, &call, base);
        let source = (call, base);
        let checked = instances
            .recheck_dag_v2(&source, &module, &instance)
            .unwrap();
        export(
            &format!("caller-private-frame-{base}"),
            checked.proof_term(),
            serde_json::json!({
                "proof_bytes":instance.len(), "frame_base":base,
                "caller_address":80,"instantiated_universal_proof":true,"all_initial_bytes":true,
                "native_authority":false
            }),
        );
    }
    for (label, base) in [("frame-live-overlap", 80), ("frame-retired-overlap", 16)] {
        let call = invocation();
        let instance = instantiate_frame(&proof, &call, base);
        reject(&instances, label, &(call, base), &module, &instance);
    }
    reject(&checker, "frame-wrong-read", &true, &module, &proof);
    for (label, fault) in [
        ("frame-missing-freshness", Fault::Freshness),
        ("frame-wrong-access", Fault::Access),
        ("frame-wrong-point-bound", Fault::PointBound),
    ] {
        reject(
            &checker,
            label,
            &false,
            &module,
            &assemble(&module, &writer, fault),
        );
    }
    let mut changed = module.clone();
    if let Inst::Store { value, .. } = &mut changed.functions[0].blocks[0].body[49].inst {
        *value = ValueId::new(2);
    } else {
        panic!("captured final store");
    }
    reject(&checker, "frame-changed-store", &false, &changed, &proof);
}
