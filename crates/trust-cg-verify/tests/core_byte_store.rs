// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! Candidates are untrusted. Every positive and semantic negative goes through
//! the public CG consumer with the real, immutable Clean ByteV1 vocabulary.

use clean_kernel::{BinderInfo, Expr, Level, Name};
use clean_verify::eval_ir::{EvalIrVocabulary, shared_specification_with_stack};
use std::sync::OnceLock;
use trust_cg_verify::core_byte_store::{ByteAllocation, ByteStoreInvocation, ByteStoreRechecker};
use trust_ir::{BlockId, Endianness, StructPassingPolicy, TargetInfo};
use trust_ir::{FuncId, Inst, Module, Ty};
use trust_ir_build::{
    ModuleBuilder,
    core_execution::{
        Assembler, ByteStoreEight, ByteStoreEightPremises, Catalog, Coordinate, EntryTarget,
        Limits, MemoryPremises, PendingEquality, PendingProof,
    },
    scoped_local::LocalScope,
};
use trust_ir_build::{
    core_execution::{MachineModel, NatTerm},
    core_reflection::reflect_core_module_v1,
};

fn c(name: &str) -> Expr {
    Expr::const_str(name)
}
fn app(name: &str, args: impl IntoIterator<Item = Expr>) -> Expr {
    Expr::apps(c(name), args)
}
fn nat(value: u64) -> Expr {
    Expr::nat_lit(value)
}
fn list(ty: &str, values: &[Expr]) -> Expr {
    values
        .iter()
        .rev()
        .fold(app("IRList.nil", [c(ty)]), |tail, value| {
            app("IRList.cons", [c(ty), value.clone(), tail])
        })
}
fn byte_map_type() -> Expr {
    Expr::pi(BinderInfo::Default, c("Nat"), app("IROption", [c("Nat")]))
}
fn providers() -> Expr {
    // Total failing provider. The admitted module has no imports or calls.
    let body = app(
        "IRByteImportResultV1.mk",
        [
            c("Nat"),
            app("IROutcome.stuck", [c("IRFault.no_func")]),
            Expr::bvar(1),
            Expr::bvar(0),
        ],
    );
    [
        c("Nat"),
        app("IRList", [c("IRScalar")]),
        c("IRByteMemoryV1"),
        c("Nat"),
    ]
    .into_iter()
    .rev()
    .fold(body, |body, ty| Expr::lam(BinderInfo::Default, ty, body))
}

// Test-only, untrusted term assembly. The public checker separately rebuilds
// the claim from the original module and invocation.
trait InvocationTerms {
    fn rows(&self) -> Expr;
    fn memory(&self, bytes: Expr) -> Expr;
    fn arguments(&self) -> Expr;
    fn initial(&self, model: &MachineModel, bytes: Expr) -> Expr;
    fn terminal(&self, bytes: Expr) -> Expr;
}
impl InvocationTerms for ByteStoreInvocation {
    fn rows(&self) -> Expr {
        list(
            "IRByteAllocationV1",
            &self
                .allocations
                .iter()
                .map(|row| {
                    app(
                        "IRByteAllocationV1.mk",
                        [
                            nat(row.base),
                            nat(row.size),
                            nat(u64::from(row.owner)),
                            c(if row.live { "Bool.true" } else { "Bool.false" }),
                        ],
                    )
                })
                .collect::<Vec<_>>(),
        )
    }
    fn memory(&self, bytes: Expr) -> Expr {
        app(
            "IRByteMemoryV1.mk",
            [self.rows(), bytes, nat(self.allocation_cursor)],
        )
    }
    fn arguments(&self) -> Expr {
        list(
            "IRScalar",
            &[
                app("IRScalar.ptr_", [nat(self.address)]),
                app("IRScalar.int_", [nat(self.word)]),
            ],
        )
    }
    fn initial(&self, model: &MachineModel, bytes: Expr) -> Expr {
        app(
            "ir_byte_init_v1",
            [
                c("Nat"),
                model.context().clone(),
                nat(u64::from(self.function.index())),
                self.arguments(),
                self.memory(bytes),
                nat(self.host_state),
            ],
        )
    }
    fn terminal(&self, bytes: Expr) -> Expr {
        // Independent specification, not an assembler endpoint. ByteV1 chooses
        // a fresh activation above ALL owners, including retired rows, then
        // advances its counter. The admitted body allocates no activation data.
        let historical_max = self
            .allocations
            .iter()
            .map(|row| row.owner)
            .max()
            .unwrap_or(0);
        let memory = self.memory(app(
            "ir_byte_write_word_v1",
            [bytes, nat(self.address), nat(8), nat(self.word)],
        ));
        let world = app(
            "IRByteWorldV1.mk",
            [
                c("Nat"),
                memory,
                nat(self.host_state),
                list("Nat", &[]),
                nat(u64::from(historical_max) + 2),
            ],
        );
        app(
            "IRByteConfigV1.halted",
            [
                c("Nat"),
                app("IROutcome.ret", [list("IRScalar", &[])]),
                world,
            ],
        )
    }
}

fn checker() -> &'static ByteStoreRechecker {
    static CHECKER: OnceLock<ByteStoreRechecker> = OnceLock::new();
    CHECKER.get_or_init(|| ByteStoreRechecker::new().unwrap())
}
fn limits() -> Limits {
    Limits {
        max_operations: 10_000,
        max_locals: 1_000,
        max_list_items: 1_000,
        max_lookup_candidates: 32,
        lookup_heartbeats: 5_000_000,
        lookup_cache_entries: 100_000,
    }
}
fn target(align: u64) -> (Module, BlockId) {
    let mut builder = ModuleBuilder::new_with_target_info(
        "caller_store",
        TargetInfo {
            triple: "aarch64-unknown-linux-gnu".into(),
            pointer_size: 8,
            endianness: Endianness::Little,
            abi: Some("aapcs64".into()),
            struct_passing: StructPassingPolicy::NativeC,
        },
    );
    let sig = builder.add_func_type(vec![Ty::Ptr, Ty::I64], vec![]);
    let fid = builder.declare_function("store_word", sig);
    let mut function = builder.define_function(fid).unwrap();
    let block = function.create_block();
    let pointer = function.add_block_param(block, Ty::Ptr);
    let word = function.add_block_param(block, Ty::I64);
    function.switch_to_block(block);
    function.store_aligned(Ty::I64, pointer, word, align);
    function.ret(vec![]);
    function.build();
    (
        builder.build().expect("ModuleBuilder::build: test fixture"),
        block,
    )
}
fn invocation(module: &Module) -> ByteStoreInvocation {
    ByteStoreInvocation {
        function: module.functions[0].id,
        address: 80,
        word: 0xfedc_ba98_7654_3210,
        allocations: vec![
            ByteAllocation {
                base: 16,
                size: 16,
                owner: 0,
                live: true,
            },
            ByteAllocation {
                base: 80,
                size: 16,
                owner: 0,
                live: true,
            },
            ByteAllocation {
                base: 128,
                size: 8,
                owner: 7,
                live: false,
            },
        ],
        // Deliberately below existing ranges; it cannot establish freshness.
        allocation_cursor: 1,
        host_state: 37,
    }
}
fn conversion(ty: Expr, left: Expr, right: Expr) -> PendingEquality {
    let proof = Expr::apps(
        Expr::const_(
            Name::from_string("Eq.refl"),
            vec![Level::succ(Level::zero())],
        ),
        [ty.clone(), right.clone()],
    );
    PendingEquality::candidate(ty, left, right, proof)
}
fn truth(left: Expr) -> PendingEquality {
    conversion(c("Bool"), left, c("Bool.true"))
}
fn some(ty: &str, value: Expr) -> Expr {
    app("IROption.some", [c(ty), value])
}

#[derive(Clone, Copy, Default)]
enum Corruption {
    #[default]
    None,
    FalseStoredWord,
    WrongReturnPc,
    EraseMemoryWrite,
    ChangeUnwrittenBytes,
    ChangeCursor,
    ChangeHost,
    DropRetiredHistory,
    ReuseOwnerCounter,
}

fn candidate(
    source: &ByteStoreInvocation,
    module: &Module,
    block: BlockId,
    corruption: Corruption,
) -> Vec<u8> {
    let reflected = reflect_core_module_v1(module, &[(source.function, 4096)]).unwrap();
    let model = MachineModel::new(c("Nat"), &reflected, providers());
    let mut catalog = Catalog::new(
        shared_specification_with_stack(EvalIrVocabulary::ByteV1)
            .unwrap()
            .env(),
        &reflected,
        limits(),
    )
    .unwrap();
    let entry = catalog.entry(source.function).unwrap();
    let store = catalog
        .fetch(Coordinate {
            function: source.function,
            block,
            instruction: 0,
        })
        .unwrap();
    let returning = catalog
        .fetch(Coordinate {
            function: source.function,
            block,
            instruction: if matches!(corruption, Corruption::WrongReturnPc) {
                0
            } else {
                1
            },
        })
        .unwrap();
    let mut scope = LocalScope::new();
    let bytes = scope.try_local(byte_map_type()).unwrap();
    let mut assembler = Assembler::new(&mut scope, limits()).unwrap();
    let memory = source.memory(bytes.term().clone());
    let initialized = entry
        .initialize(
            &mut assembler,
            &model,
            source.arguments(),
            memory.clone(),
            nat(source.host_state),
            truth(EntryTarget::memory_admission(memory)),
            truth(entry.admission(&model, source.arguments()).unwrap()),
        )
        .unwrap();

    let word = nat(if matches!(corruption, Corruption::FalseStoredWord) {
        source.word.wrapping_add(1)
    } else {
        source.word
    });
    let literal = if matches!(corruption, Corruption::FalseStoredWord) {
        source.word.wrapping_add(1)
    } else {
        source.word
    };
    let ty = app("IRTy.int_", [nat(64)]);
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
    let codec = assembler
        .byte_i64_codec(
            model.context().clone(),
            word.clone(),
            conversion(
                app("IROption", [c("IRByteLayoutV1")]),
                app("ir_byte_layout_v1", [model.context().clone(), ty]),
                some("IRByteLayoutV1", layout),
            ),
            PendingProof::candidate(
                app("Nat.lt", [word.clone(), c("ir_byte_limit_v1")]),
                app(
                    "Nat.le_add_right",
                    [app("Nat.succ", [word]), nat(u64::MAX - literal)],
                ),
            ),
        )
        .unwrap();
    let Inst::Store { ptr, align, .. } = &module.functions[0].blocks[0].body[0].inst else {
        unreachable!()
    };
    let pointer = app(
        "ir_getd",
        [initialized.current().machine(), nat(u64::from(ptr.index()))],
    );
    let memory = app(
        "ir_byte_world_memory_v1",
        [c("Nat"), initialized.current().world.clone()],
    );
    let align = nat(align.unwrap_or(0));
    let stored = assembler
        .byte_store_eight(
            &codec,
            ByteStoreEight {
                pointer: pointer.clone(),
                address: nat(source.address),
                requested_align: align.clone(),
                memory: memory.clone(),
            },
            ByteStoreEightPremises {
                pointer: conversion(
                    app("IROption", [c("Nat")]),
                    app("ir_byte_pointer_address_v1", [pointer]),
                    some("Nat", nat(source.address)),
                ),
                accessible: truth(app(
                    "ir_byte_accessible_v1",
                    [
                        app("ir_byte_mem_allocs_v1", [memory]),
                        nat(source.address),
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
    let checks = store
        .memory_checks(&model, initialized.current(), &stored.result)
        .unwrap();
    let bridge = assembler
        .conversion(
            c("IRByteMemoryResultV1"),
            checks.evaluation,
            stored.evaluated.left().clone(),
        )
        .unwrap();
    let evaluated = assembler.compose(bridge, stored.evaluated).unwrap();
    let transferred = store
        .memory_value(
            &mut assembler,
            &model,
            initialized.current(),
            stored.result,
            MemoryPremises {
                evaluated,
                allocations: stored.allocations,
                result: truth(checks.result),
                before: initialized.valid().clone(),
            },
        )
        .unwrap();

    // Corrupt complete terminal endpoints, while retaining the honest public
    // invocation. A value-only projection would miss these frame violations.
    let mut endpoint_source = source.clone();
    match corruption {
        Corruption::ChangeCursor => endpoint_source.allocation_cursor += 1,
        Corruption::ChangeHost => endpoint_source.host_state += 1,
        Corruption::DropRetiredHistory => {
            endpoint_source.allocations.pop();
        }
        Corruption::ReuseOwnerCounter => (),
        _ => (),
    }
    let terminal_bytes = if matches!(corruption, Corruption::ChangeUnwrittenBytes) {
        Expr::lam(BinderInfo::Default, c("Nat"), some("Nat", nat(0)))
    } else {
        bytes.term().clone()
    };
    let mut terminal = if matches!(corruption, Corruption::EraseMemoryWrite) {
        app(
            "IRByteConfigV1.halted",
            [
                c("Nat"),
                app("IROutcome.ret", [list("IRScalar", &[])]),
                app(
                    "IRByteWorldV1.mk",
                    [
                        c("Nat"),
                        source.memory(bytes.term().clone()),
                        nat(source.host_state),
                        list("Nat", &[]),
                        nat(9),
                    ],
                ),
            ],
        )
    } else {
        endpoint_source.terminal(terminal_bytes)
    };
    if matches!(
        corruption,
        Corruption::ReuseOwnerCounter | Corruption::DropRetiredHistory
    ) {
        let mut fields: Vec<Expr> = terminal
            .get_app_args()
            .iter()
            .map(|x| (*x).clone())
            .collect();
        let mut world: Vec<Expr> = fields[2]
            .get_app_args()
            .iter()
            .map(|x| (*x).clone())
            .collect();
        // Isolate counter corruption from allocation-history corruption.
        world[4] = nat(if matches!(corruption, Corruption::ReuseOwnerCounter) {
            1
        } else {
            9
        });
        fields[2] = app("IRByteWorldV1.mk", world);
        terminal = app("IRByteConfigV1.halted", fields);
    }
    let dispatched = returning
        .step(
            &mut assembler,
            &model,
            transferred.current(),
            transferred.valid().clone(),
        )
        .unwrap();
    let reduction = assembler
        .conversion(model.config_type(), dispatched.right().clone(), terminal)
        .unwrap();
    let returned = assembler.compose(dispatched, reduction).unwrap();
    let returned = assembler
        .one_step(&model, transferred.current().running(&model), returned)
        .unwrap();
    let run = assembler
        .concatenate(transferred.run().clone(), returned)
        .unwrap();
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
                &NatTerm::literal(2),
                source.initial(&model, bytes.term().clone()),
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
    let complete = assembler.compose(before, mapped).unwrap();
    let complete = assembler.compose(complete, after).unwrap();
    let complete = assembler.compose(complete, run.equality().clone()).unwrap();
    let term = scope.close(&bytes.lam(complete.term().clone())).unwrap();
    assert!(!term.has_fvar_quick());
    trust_ir::proof::encode_clean_expr_dag_v2(&term).unwrap()
}

fn reject(source: &ByteStoreInvocation, module: &Module, proof: &[u8], stage: &str) {
    let error = checker().recheck(source, module, proof).unwrap_err();
    assert_eq!(error.stage(), stage, "{error}");
    for resource in [
        "heartbeat",
        "budget",
        "timeout",
        "fuel exhausted",
        "recursion limit",
    ] {
        assert!(
            !error.reason().to_ascii_lowercase().contains(resource),
            "{error}"
        );
    }
}

#[test]
fn core_byte_store_replays_all_initial_bytes_and_canonical_word_boundaries() {
    let (module, block) = target(8);
    let mut source = invocation(&module);
    for word in [0, 1, 1_u64 << 63, u64::MAX, source.word] {
        source.word = word;
        for address in [80, 88] {
            source.address = address;
            let proof = candidate(&source, &module, block, Corruption::None);
            let checked = checker().recheck(&source, &module, &proof).unwrap();
            assert!(std::ptr::eq(checked.module(), &module));
            assert_eq!(checked.invocation(), &source);
            assert_eq!(checked.proof_bytes(), proof);
            if let Some(directory) = std::env::var_os("TCG_CORE_BYTE_REPLAY_EXPORT") {
                let stem = format!("store-{address}-{word:016x}");
                std::fs::write(
                    std::path::Path::new(&directory).join(format!("{stem}.dag")),
                    &proof,
                )
                .unwrap();
                std::fs::write(
                    std::path::Path::new(&directory).join(format!("{stem}.json")),
                    serde_json::to_vec_pretty(&serde_json::json!({"address":address,"word":word,
                        "proof_bytes":proof.len()}))
                    .unwrap(),
                )
                .unwrap();
            }
        }
    }
}

#[test]
fn core_byte_store_rejects_forged_fetched_execution_and_complete_terminal_world() {
    let (module, block) = target(8);
    let source = invocation(&module);
    for corruption in [
        Corruption::FalseStoredWord,
        Corruption::WrongReturnPc,
        Corruption::EraseMemoryWrite,
        Corruption::ChangeUnwrittenBytes,
        Corruption::ChangeCursor,
        Corruption::ChangeHost,
        Corruption::DropRetiredHistory,
        Corruption::ReuseOwnerCounter,
    ] {
        let proof = candidate(&source, &module, block, corruption);
        reject(&source, &module, &proof, "kernel audit");
    }
}

#[test]
fn core_byte_store_rejects_false_caller_memory_admission_and_access() {
    let (module, block) = target(8);
    for kind in 0..7 {
        let mut source = invocation(&module);
        match kind {
            0 => source.allocations[1].live = false,
            1 => source.allocations[1].size = 7,
            2 => source.allocations.push(source.allocations[1].clone()),
            3 => source.allocations[1].owner = 2,
            4 => source.address = 81,
            5 => source.address = 96,
            6 => source.address = 0,
            _ => unreachable!(),
        }
        let proof = candidate(&source, &module, block, Corruption::None);
        reject(&source, &module, &proof, "kernel audit");
    }
}

#[test]
fn core_byte_store_retained_proof_binds_inputs_and_decodes_exactly() {
    let (module, block) = target(8);
    let source = invocation(&module);
    let proof = candidate(&source, &module, block, Corruption::None);
    checker().recheck(&source, &module, &proof).unwrap();
    for kind in 0..6 {
        let mut changed = source.clone();
        match kind {
            0 => changed.word ^= 1,
            1 => changed.address += 8,
            2 => changed.allocation_cursor += 1,
            3 => changed.host_state += 1,
            4 => changed.allocations[2].owner += 1,
            5 => changed.allocations[0].size += 8,
            _ => unreachable!(),
        }
        reject(&changed, &module, &proof, "kernel audit");
    }
    let (changed, _) = target(32);
    reject(&source, &changed, &proof, "kernel audit");
    let mut trailing = proof.clone();
    trailing.push(0);
    reject(&source, &module, &trailing, "decode");
    reject(&source, &module, &proof[..proof.len() - 1], "decode");
    reject(&source, &module, &[], "decode");
}

#[test]
fn core_byte_store_replays_last_addressable_byte_and_rejects_wrapping_allocations() {
    let (module, block) = target(8);
    let mut source = invocation(&module);
    source.address = u64::MAX - 7;
    source.allocations[1].base = source.address;
    source.allocations[1].size = 8;
    let proof = candidate(&source, &module, block, Corruption::None);
    checker().recheck(&source, &module, &proof).unwrap();
    source.allocations[1].size = 9;
    let proof = candidate(&source, &module, block, Corruption::None);
    reject(&source, &module, &proof, "kernel audit");
}

#[test]
fn core_byte_store_refuses_unsupported_original_modules_and_unbounded_rows() {
    let (module, block) = target(8);
    let source = invocation(&module);
    let proof = candidate(&source, &module, block, Corruption::None);
    for kind in 0..6 {
        let mut changed = module.clone();
        match kind {
            0 => {
                changed.functions[0].blocks[0].body.pop();
            }
            1 => {
                changed.functions.push(changed.functions[0].clone());
            }
            2 => {
                if let Inst::Store { volatile, .. } =
                    &mut changed.functions[0].blocks[0].body[0].inst
                {
                    *volatile = true;
                }
            }
            3 => {
                changed.functions[0].blocks[0].body[0].inst = Inst::Copy {
                    ty: Ty::I64,
                    operand: changed.functions[0].blocks[0].params[1].0,
                }
            }
            4 => changed.functions[0].id = FuncId::new(100),
            5 => changed.func_types[0].params[0] = Ty::RefMut(Box::new(Ty::I64)),
            _ => unreachable!(),
        }
        reject(&source, &changed, &proof, "reconstruct");
    }
    let mut changed = source.clone();
    changed
        .allocations
        .resize(65, changed.allocations[0].clone());
    reject(&changed, &module, &proof, "reconstruct");
}
