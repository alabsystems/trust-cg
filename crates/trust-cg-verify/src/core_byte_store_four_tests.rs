// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! The existing public consumer replays a pending four-byte proof against the
//! SAME original module and caller invocation. No native/publication authority,
//! alternate evaluator, flattened source body or per-proof vocabulary is used.

use super::*;
use std::sync::OnceLock;
use trust_ir::{BlockId, Endianness, StructPassingPolicy, TargetInfo};
use trust_ir_build::{
    ModuleBuilder,
    core_execution::{
        Assembler, ByteStoreFour, ByteStoreFourPremises, Catalog, Coordinate, EntryTarget, Limits,
        MemoryPremises, PendingEquality, PendingProof,
    },
    scoped_local::LocalScope,
};

fn checker() -> &'static ByteStoreRechecker {
    static CHECKER: OnceLock<ByteStoreRechecker> = OnceLock::new();
    CHECKER.get_or_init(|| ByteStoreRechecker::new().unwrap())
}

fn limits() -> Limits {
    // The existing CG caller-store producer's limits, not certificate settings.
    Limits {
        max_operations: 10_000,
        max_locals: 1_000,
        max_list_items: 1_000,
        max_lookup_candidates: 32,
        lookup_heartbeats: 5_000_000,
        lookup_cache_entries: 100_000,
    }
}

fn target(ty: Ty, align: u64) -> (Module, BlockId) {
    let mut builder = ModuleBuilder::new_with_target_info(
        "caller_store_four",
        TargetInfo {
            triple: "aarch64-apple-darwin".into(),
            pointer_size: 8,
            endianness: Endianness::Little,
            abi: Some("aapcs64".into()),
            struct_passing: StructPassingPolicy::NativeC,
        },
    );
    let signature = builder.add_func_type(vec![Ty::Ptr, ty.clone()], vec![]);
    let function = builder.declare_function("store_integer", signature);
    let mut body = builder.define_function(function).unwrap();
    let block = body.create_block();
    let pointer = body.add_block_param(block, Ty::Ptr);
    let value = body.add_block_param(block, ty.clone());
    body.switch_to_block(block);
    body.store_aligned(ty, pointer, value, align);
    body.ret(vec![]);
    body.build();
    let module = builder.build().expect("ModuleBuilder::build: test fixture");
    assert!(trust_ir_build::validate_module(&module).is_empty());
    (module, block)
}

fn invocation(module: &Module) -> ByteStoreInvocation {
    ByteStoreInvocation {
        function: module.functions[0].id,
        address: 80,
        word: 0x0102_0304,
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
        // Storage rights come from checked admission/access, not this cursor.
        allocation_cursor: 1,
        host_state: 37,
    }
}

fn option(ty: &str) -> Expr {
    app("IROption", [c(ty)])
}

fn some(ty: &str, value: Expr) -> Expr {
    app("IROption.some", [c(ty), value])
}

fn conversion(ty: Expr, left: Expr, right: Expr) -> PendingEquality {
    let term = Expr::apps(
        Expr::const_(
            Name::from_string("Eq.refl"),
            vec![Level::succ(Level::zero())],
        ),
        [ty.clone(), right.clone()],
    );
    PendingEquality::candidate(ty, left, right, term)
}

fn truth(left: Expr) -> PendingEquality {
    conversion(c("Bool"), left, c("Bool.true"))
}

#[derive(Clone, Copy, Default)]
enum Corruption {
    #[default]
    None,
    StoredWord,
    OverwideWrite,
    UnwrittenBytes,
    Cursor,
    Host,
    RetiredHistory,
    OwnerCounter,
}

fn expected_terminal(source: &ByteStoreInvocation, bytes: Expr, corruption: Corruption) -> Expr {
    // Independent complete-world endpoint. Initial bytes stay universally
    // bound, so a spurious eight-byte write is not hidden by zero-filled memory.
    let historical_owner = source
        .allocations
        .iter()
        .map(|row| u64::from(row.owner))
        .max()
        .unwrap_or(0);
    let next = if matches!(corruption, Corruption::OwnerCounter) {
        1
    } else {
        historical_owner + 2
    };
    let mut rows = source.allocations.clone();
    if matches!(corruption, Corruption::RetiredHistory) {
        rows.pop();
    }
    let rows = list(
        "IRByteAllocationV1",
        &rows
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
    );
    let bytes = if matches!(corruption, Corruption::UnwrittenBytes) {
        Expr::lam(BinderInfo::Default, c("Nat"), some("Nat", nat(0)))
    } else {
        bytes
    };
    let width = if matches!(corruption, Corruption::OverwideWrite) {
        8
    } else {
        4
    };
    let memory = app(
        "IRByteMemoryV1.mk",
        [
            rows,
            app(
                "ir_byte_write_word_v1",
                [bytes, nat(source.address), nat(width), nat(source.word)],
            ),
            nat(source.allocation_cursor + u64::from(matches!(corruption, Corruption::Cursor))),
        ],
    );
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
                    nat(source.host_state + u64::from(matches!(corruption, Corruption::Host))),
                    list("Nat", &[]),
                    nat(next),
                ],
            ),
        ],
    )
}

fn candidate(
    source: &ByteStoreInvocation,
    module: &Module,
    block: BlockId,
    corruption: Corruption,
) -> Vec<u8> {
    // The producer consumes the original validated module and actual fetched
    // fields; no replacement function or source metadata skeleton is formed.
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
    let store_site = catalog
        .fetch(Coordinate {
            function: source.function,
            block,
            instruction: 0,
        })
        .unwrap();
    let return_site = catalog
        .fetch(Coordinate {
            function: source.function,
            block,
            instruction: 1,
        })
        .unwrap();
    let Inst::Store { ty, ptr, align, .. } = &module.functions[0].blocks[0].body[0].inst else {
        panic!("original store")
    };
    let ty = match ty {
        Ty::I32 => app("IRTy.int_", [nat(32)]),
        Ty::U32 => app("IRTy.uint_", [nat(32)]),
        _ => panic!("four-byte producer requires actual I32/U32"),
    };
    let mut scope = LocalScope::new();
    let bytes = scope.try_local(byte_map_type()).unwrap();
    let mut assembler = Assembler::new(&mut scope, limits()).unwrap();
    let incoming = source.memory(bytes.term().clone());
    let initialized = entry
        .initialize(
            &mut assembler,
            &model,
            source.arguments(),
            incoming.clone(),
            nat(source.host_state),
            truth(EntryTarget::memory_admission(incoming)),
            truth(entry.admission(&model, source.arguments()).unwrap()),
        )
        .unwrap();
    let literal = source.word + u64::from(matches!(corruption, Corruption::StoredWord));
    assert!(literal <= u64::from(u32::MAX));
    let word = nat(literal);
    let layout = app(
        "IRByteLayoutV1.mk",
        [
            ty.clone(),
            nat(4),
            nat(4),
            list("IRTy", &[]),
            list("Nat", &[]),
        ],
    );
    let codec = assembler
        .byte_integer32_codec(
            model.context().clone(),
            ty.clone(),
            word.clone(),
            conversion(
                option("IRByteLayoutV1"),
                app("ir_byte_layout_v1", [model.context().clone(), ty]),
                some("IRByteLayoutV1", layout),
            ),
            PendingProof::candidate(
                app("Nat.lt", [word.clone(), app("ir_nat_pow2", [nat(32)])]),
                app(
                    "Nat.le_add_right",
                    [app("Nat.succ", [word]), nat(u64::from(u32::MAX) - literal)],
                ),
            ),
        )
        .unwrap();
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
        .byte_store_four(
            &codec,
            ByteStoreFour {
                pointer: pointer.clone(),
                address: nat(source.address),
                requested_align: align.clone(),
                memory: memory.clone(),
            },
            ByteStoreFourPremises {
                pointer: conversion(
                    option("Nat"),
                    app("ir_byte_pointer_address_v1", [pointer]),
                    some("Nat", nat(source.address)),
                ),
                accessible: truth(app(
                    "ir_byte_accessible_v1",
                    [
                        app("ir_byte_mem_allocs_v1", [memory]),
                        nat(source.address),
                        nat(4),
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
    let checks = store_site
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
    let transferred = store_site
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
    let dispatched = return_site
        .step(
            &mut assembler,
            &model,
            transferred.current(),
            transferred.valid().clone(),
        )
        .unwrap();
    let reduction = assembler
        .conversion(
            model.config_type(),
            dispatched.right().clone(),
            expected_terminal(source, bytes.term().clone(), corruption),
        )
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
    drop(assembler);
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
fn ordinary_four_byte_consumer_replays_original_modules_and_canonical_words() {
    for ty in [Ty::I32, Ty::U32] {
        let (module, block) = target(ty, 4);
        let mut source = invocation(&module);
        for word in [0, 1, 0x0102_0304, 0x8000_0000, u64::from(u32::MAX)] {
            source.word = word;
            for address in [80, 84] {
                source.address = address;
                let proof = candidate(&source, &module, block, Corruption::None);
                let checked = checker().recheck(&source, &module, &proof).unwrap();
                assert!(std::ptr::eq(checked.module(), &module));
                assert!(std::ptr::eq(checked.invocation(), &source));
                assert!(std::ptr::eq(checked.proof_bytes().as_ptr(), proof.as_ptr()));
                assert_eq!(checked.proof_bytes(), proof);
                assert_eq!(module.functions[0].blocks[0].body.len(), 2);
            }
        }
        source.address = u64::MAX - 3;
        source.allocations[1].base = source.address;
        source.allocations[1].size = 4;
        let proof = candidate(&source, &module, block, Corruption::None);
        checker().recheck(&source, &module, &proof).unwrap();
        source.allocations[1].size = 5;
        let proof = candidate(&source, &module, block, Corruption::None);
        reject(&source, &module, &proof, "kernel audit");
    }
}

#[test]
fn ordinary_four_byte_consumer_rejects_wrong_whole_memory_and_caller_state() {
    for ty in [Ty::I32, Ty::U32] {
        let (module, block) = target(ty, 4);
        let source = invocation(&module);
        for corruption in [
            Corruption::StoredWord,
            Corruption::OverwideWrite,
            Corruption::UnwrittenBytes,
            Corruption::Cursor,
            Corruption::Host,
            Corruption::RetiredHistory,
            Corruption::OwnerCounter,
        ] {
            let proof = candidate(&source, &module, block, corruption);
            reject(&source, &module, &proof, "kernel audit");
        }
        let proof = candidate(&source, &module, block, Corruption::None);
        checker().recheck(&source, &module, &proof).unwrap();
        for mutation in 0..6 {
            let mut changed = source.clone();
            match mutation {
                0 => changed.word ^= 1,
                1 => changed.address += 4,
                2 => changed.allocation_cursor += 1,
                3 => changed.host_state += 1,
                4 => changed.allocations[2].owner += 1,
                5 => changed.allocations[0].size += 4,
                _ => unreachable!(),
            }
            reject(&changed, &module, &proof, "kernel audit");
        }
        for mutation in 0..7 {
            let mut changed = source.clone();
            match mutation {
                0 => changed.allocations[1].live = false,
                1 => changed.allocations[1].size = 3,
                2 => changed.allocations.push(changed.allocations[1].clone()),
                3 => changed.allocations[1].owner = 2,
                4 => changed.address = 81,
                5 => changed.address = 96,
                6 => changed.address = 0,
                _ => unreachable!(),
            }
            let proof = candidate(&changed, &module, block, Corruption::None);
            reject(&changed, &module, &proof, "kernel audit");
        }
    }
}

#[test]
fn ordinary_four_byte_consumer_binds_source_signature_operands_and_width() {
    let (module, block) = target(Ty::U32, 4);
    let source = invocation(&module);
    let proof = candidate(&source, &module, block, Corruption::None);
    checker().recheck(&source, &module, &proof).unwrap();
    for mutation in 0..7 {
        let mut changed = module.clone();
        match mutation {
            0 => changed.func_types[0].params[1] = Ty::I32,
            1 => {
                if let Inst::Store { ty, .. } = &mut changed.functions[0].blocks[0].body[0].inst {
                    *ty = Ty::I32;
                }
            }
            2 => changed.func_types[0].params[0] = Ty::RefMut(Box::new(Ty::U32)),
            3 => {
                if let Inst::Store { volatile, .. } =
                    &mut changed.functions[0].blocks[0].body[0].inst
                {
                    *volatile = true;
                }
            }
            4 => {
                if let Inst::Store { ptr, .. } = &mut changed.functions[0].blocks[0].body[0].inst {
                    *ptr = trust_ir::ValueId::new(999);
                }
            }
            5 => {
                changed.functions[0].blocks[0].body.pop().unwrap();
            }
            6 => changed.functions[0].id = FuncId::new(100),
            _ => unreachable!(),
        }
        reject(&source, &changed, &proof, "reconstruct");
    }
    let (overwide_module, _) = target(Ty::I64, 8);
    reject(&source, &overwide_module, &proof, "kernel audit");
    let (overaligned_module, _) = target(Ty::U32, 32);
    reject(&source, &overaligned_module, &proof, "kernel audit");
    let mut out_of_range = source.clone();
    out_of_range.word = 1_u64 << 32;
    reject(&out_of_range, &module, &proof, "reconstruct");
    out_of_range.word = u64::MAX;
    reject(&out_of_range, &module, &proof, "reconstruct");
}

#[test]
fn ordinary_four_byte_consumer_refuses_unknown_declarations_and_malformed_dag() {
    let (module, block) = target(Ty::I32, 4);
    let source = invocation(&module);
    let proof = candidate(&source, &module, block, Corruption::None);
    checker().recheck(&source, &module, &proof).unwrap();
    let unknown =
        trust_ir::proof::encode_clean_expr_dag_v2(&c("not_a_byte_store_proof_declaration"))
            .unwrap();
    reject(&source, &module, &unknown, "kernel audit");
    let mut trailing = proof.clone();
    trailing.push(0);
    reject(&source, &module, &trailing, "decode");
    reject(&source, &module, &proof[..proof.len() - 1], "decode");
    reject(&source, &module, &[], "decode");
    let mut too_many = source.clone();
    too_many
        .allocations
        .resize(65, too_many.allocations[0].clone());
    reject(&too_many, &module, &proof, "reconstruct");
    let mut big_endian = module.clone();
    big_endian.target_info.as_mut().unwrap().endianness = Endianness::Big;
    reject(&source, &big_endian, &proof, "reconstruct");
}
