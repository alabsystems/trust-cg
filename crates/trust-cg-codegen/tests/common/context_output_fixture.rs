// Copyright 2026 Andrew Yates | Apache-2.0
//! Shared independently authored closed source DATA for the native consumer.
//! Reuses the IR canary's exact canonical ByteV1 program, never its target
//! denotation or a second compiler. The production certificate factory remains
//! the original shared source-family owner.
use super::cg;
#[path = "context_output_contract_fixture.rs"]
mod contract;
pub(crate) use contract::plan;
use trust_ir::proof::{IslandEnvironment, encode_island_declarations_v1};
use trust_ir::{CallingConv, Module, Ty};
use trust_ir_build::ModuleBuilder;
use trust_ir_build::clean_kernel::{BinderInfo, Expr, Level, Name, env::Declaration};
fn c(n: &str) -> Expr {
    Expr::const_str(n)
}
fn a(n: &str, xs: impl IntoIterator<Item = Expr>) -> Expr {
    Expr::apps(c(n), xs)
}
fn lam(t: Expr, b: Expr) -> Expr {
    Expr::lam(BinderInfo::Default, t, b)
}
fn word(lane: u64, mutation: Mutation) -> Expr {
    if matches!(mutation, Mutation::MixedTypes) && lane == 0 {
        c("IRTy.ptr_")
    } else {
        a(
            if matches!(mutation, Mutation::MixedTypes) && lane == 2 {
                "IRTy.int_"
            } else {
                "IRTy.uint_"
            },
            [Expr::nat_lit(64)],
        )
    }
}
fn domains() -> [Expr; 4] {
    [
        c("IRByteContextV1"),
        c("IRByteMemoryV1"),
        c("Nat"),
        c("Nat"),
    ]
}
fn effect_type() -> Expr {
    domains()
        .into_iter()
        .rev()
        .fold(c("IRByteMemoryResultV1"), |b, t| {
            Expr::pi(BinderInfo::Default, t, b)
        })
}

// A source program written without reading a Module or target denotation:
// read each of five context words, then store that word to its output lane.
// Faults stop immediately and retain the actual fault memory, including earlier
// completed writes. The source returns unit, never a fabricated scalar status.
#[derive(Clone, Copy)]
enum Mutation {
    None,
    MixedTypes,
    DeadInboundsGep,
    ReadNext,
    OmitLastStore,
    EraseFault,
}
fn source(mutation: Mutation) -> IslandEnvironment {
    fn bind(op: Expr, good: Expr, mutation: Mutation) -> Expr {
        let failure = if matches!(mutation, Mutation::EraseFault) {
            a(
                "IRByteMemoryResultV1.value",
                [c("IRScalar.unit_"), Expr::bvar(0)],
            )
        } else {
            a("IRByteMemoryResultV1.fault", [Expr::bvar(1), Expr::bvar(0)])
        };
        Expr::apps(
            Expr::const_(
                Name::from_string("IRByteMemoryResultV1.rec"),
                vec![Level::succ(Level::zero())],
            ),
            [
                lam(c("IRByteMemoryResultV1"), c("IRByteMemoryResultV1")),
                lam(c("IRScalar"), lam(c("IRByteMemoryV1"), good)),
                lam(c("IROutcome"), lam(c("IRByteMemoryV1"), failure)),
                op,
            ],
        )
    }
    fn gep(ctx: Expr, mem: Expr, ptr: Expr, offset: u64) -> Expr {
        a(
            "ir_byte_gep_typed_v1",
            [
                ctx,
                a("IRTy.int_", [Expr::nat_lit(8)]),
                ptr,
                a(
                    "ir_byte_gep_typed_index_v1",
                    [
                        a("IRTy.int_", [Expr::nat_lit(64)]),
                        a("IRScalar.int_", [Expr::nat_lit(offset)]),
                    ],
                ),
                c("Bool.false"),
                mem,
            ],
        )
    }
    fn lane(n: u64, ctx: Expr, mem: Expr, input: Expr, output: Expr, mutation: Mutation) -> Expr {
        if n == 5 {
            if matches!(mutation, Mutation::DeadInboundsGep) {
                let operation = a(
                    "ir_byte_gep_typed_v1",
                    [
                        ctx,
                        a("IRTy.int_", [Expr::nat_lit(8)]),
                        input,
                        a(
                            "ir_byte_gep_typed_index_v1",
                            [
                                a("IRTy.int_", [Expr::nat_lit(64)]),
                                a("IRScalar.int_", [Expr::nat_lit(64)]),
                            ],
                        ),
                        c("Bool.true"),
                        mem,
                    ],
                );
                return bind(
                    operation,
                    a(
                        "IRByteMemoryResultV1.value",
                        [c("IRScalar.unit_"), Expr::bvar(0)],
                    ),
                    mutation,
                );
            }
            return a("IRByteMemoryResultV1.value", [c("IRScalar.unit_"), mem]);
        }
        fn read_store(
            n: u64,
            ctx: Expr,
            mem: Expr,
            original: [Expr; 2],
            addresses: [Expr; 2],
            mutation: Mutation,
        ) -> Expr {
            let [input, output] = addresses;
            let load = a(
                "ir_byte_load_v1",
                [
                    ctx.clone(),
                    word(n, mutation),
                    input,
                    Expr::nat_lit(8),
                    c("Bool.false"),
                    mem,
                ],
            );
            let after_load = if n == 4 && matches!(mutation, Mutation::OmitLastStore) {
                lane(
                    n + 1,
                    ctx.lift(2),
                    Expr::bvar(0),
                    c("IRScalar.nullptr_"),
                    output.lift(2),
                    mutation,
                )
            } else {
                let store = a(
                    "ir_byte_store_v1",
                    [
                        ctx.lift(2),
                        word(n, mutation),
                        output.lift(2),
                        Expr::bvar(1),
                        Expr::nat_lit(8),
                        c("Bool.false"),
                        Expr::bvar(0),
                    ],
                );
                bind(
                    store,
                    lane(
                        n + 1,
                        ctx.lift(4),
                        Expr::bvar(0),
                        original[0].lift(4),
                        original[1].lift(4),
                        mutation,
                    ),
                    mutation,
                )
            };
            bind(load, after_load, mutation)
        }
        // Reconstruct original parameter references by their lexical depth.
        // Every prior lane adds four successful binders (eight for n>0).
        if n == 0 && !matches!(mutation, Mutation::ReadNext) {
            read_store(
                n,
                ctx,
                mem,
                [input.clone(), output.clone()],
                [input, output],
                mutation,
            )
        } else {
            let delta = if n == 0 { 8 } else { n * 8 };
            let input_gep = gep(ctx.clone(), mem.clone(), input.clone(), delta);
            let output_gep = gep(ctx.lift(2), Expr::bvar(0), output.lift(2), n * 8);
            // After two GEP results, restore the original context/output
            // addresses for the recursive next lane through explicit arguments.
            let loaded = read_store(
                n,
                ctx.lift(4),
                Expr::bvar(0),
                [input.lift(4), output.lift(4)],
                [Expr::bvar(3), Expr::bvar(1)],
                mutation,
            );
            bind(input_gep, bind(output_gep, loaded, mutation), mutation)
        }
    }
    let body = lane(
        0,
        Expr::bvar(3),
        Expr::bvar(2),
        a("IRScalar.ptr_", [Expr::bvar(1)]),
        a("IRScalar.ptr_", [Expr::bvar(0)]),
        mutation,
    );
    let value = domains().into_iter().rev().fold(body, |b, t| lam(t, b));
    IslandEnvironment::new(
        encode_island_declarations_v1(&[Declaration::Definition {
            name: Name::from_string("Source.copyFive"),
            level_params: vec![],
            type_: effect_type(),
            value,
            is_reducible: true,
        }])
        .unwrap(),
    )
}

fn module() -> Module {
    module_typed(false, false)
}
fn module_typed(mixed: bool, dead_gep: bool) -> Module {
    let mut m = ModuleBuilder::new_with_target_info(
        "closed_context_output",
        cg::CoreHostJitTarget::detect()
            .unwrap()
            .trust_ir_target_info()
            .clone(),
    );
    let signature = m.add_func_type(vec![Ty::Ptr, Ty::Ptr], vec![]);
    let mut f = m.function("copy_five", signature);
    f.set_calling_conv(CallingConv::C);
    let block = f.create_block();
    let input = f.add_block_param(block, Ty::Ptr);
    let output = f.add_block_param(block, Ty::Ptr);
    f.switch_to_block(block);
    for n in 0..5 {
        let (ip, op) = if n == 0 {
            (input, output)
        } else {
            (
                f.gep_byte_offset(input, n * 8),
                f.gep_byte_offset(output, n * 8),
            )
        };
        let ty = if mixed && n == 0 {
            Ty::Ptr
        } else if mixed && n == 2 {
            Ty::I64
        } else {
            Ty::U64
        };
        let value = f.load_aligned(ty.clone(), ip, 8);
        f.store_aligned(ty, op, value, 8);
    }
    if dead_gep {
        let index = f.iconst(Ty::I64, 64);
        f.gep_inbounds(Ty::I8, input, vec![index]);
    }
    f.ret(vec![]);
    f.build();
    m.build().unwrap()
}
pub(crate) fn certified(mixed: bool, dead: bool) -> Module {
    assert!(!(mixed && dead));
    let module = module_typed(mixed, dead);
    let mutation = if mixed {
        Mutation::MixedTypes
    } else if dead {
        Mutation::DeadInboundsGep
    } else {
        Mutation::None
    };
    contract::certify(module, &source(mutation), "Source.copyFive")
        .expect("genuine independently authored full effect")
}
pub(crate) fn source_mutations_refuse() {
    let module = module();
    for mutation in [
        Mutation::ReadNext,
        Mutation::OmitLastStore,
        Mutation::EraseFault,
    ] {
        let error = contract::certify(module.clone(), &source(mutation), "Source.copyFive")
            .err()
            .expect("changed independent source must refuse");
        assert!(error.contains("TypeMismatch"), "actual refusal: {error}");
    }
}
pub(crate) fn manifest(
    module: &Module,
    generation: cg::compile_service::CompileGeneration,
) -> cg::jit_contract::ArtifactManifestV1 {
    contract::manifest(module, "source:Source.copyFive", generation)
}
