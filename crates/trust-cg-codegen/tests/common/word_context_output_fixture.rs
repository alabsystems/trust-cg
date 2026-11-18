// Copyright 2026 Andrew Yates | Apache-2.0
//! Independent one-word source DATA and ordinary typed Core, without a target
//! denotation, second compiler or assumed source/native correspondence.
use super::cg;
#[path = "context_output_contract_fixture.rs"]
mod contract;
pub(crate) use contract::plan;
use trust_ir::proof::{IslandEnvironment, encode_island_declarations_v1};
use trust_ir::{CallingConv, Module, Ty};
use trust_ir_build::ModuleBuilder;
use trust_ir_build::clean_kernel::{BinderInfo, Expr, Level, Name, env::Declaration};

fn c(name: &str) -> Expr {
    Expr::const_str(name)
}
fn a(name: &str, terms: impl IntoIterator<Item = Expr>) -> Expr {
    Expr::apps(c(name), terms)
}
fn lam(ty: Expr, body: Expr) -> Expr {
    Expr::lam(BinderInfo::Default, ty, body)
}
fn word() -> Expr {
    a("IRTy.uint_", [Expr::nat_lit(64)])
}
fn returned() -> Expr {
    a(
        "IRByteMemoryResultV1.value",
        [c("IRScalar.unit_"), Expr::bvar(0)],
    )
}
fn bind(operation: Expr, success: Expr) -> Expr {
    Expr::apps(
        Expr::const_(
            Name::from_string("IRByteMemoryResultV1.rec"),
            vec![Level::succ(Level::zero())],
        ),
        [
            lam(c("IRByteMemoryResultV1"), c("IRByteMemoryResultV1")),
            lam(c("IRScalar"), lam(c("IRByteMemoryV1"), success)),
            lam(
                c("IROutcome"),
                lam(
                    c("IRByteMemoryV1"),
                    a("IRByteMemoryResultV1.fault", [Expr::bvar(1), Expr::bvar(0)]),
                ),
            ),
            operation,
        ],
    )
}
fn source(literal: Option<u64>) -> IslandEnvironment {
    let body = if let Some(value) = literal {
        bind(
            a(
                "ir_byte_store_v1",
                [
                    Expr::bvar(3),
                    word(),
                    a("IRScalar.ptr_", [Expr::bvar(0)]),
                    a("IRScalar.int_", [Expr::nat_lit(value)]),
                    Expr::nat_lit(8),
                    c("Bool.false"),
                    Expr::bvar(2),
                ],
            ),
            returned(),
        )
    } else {
        let store = bind(
            a(
                "ir_byte_store_v1",
                [
                    Expr::bvar(5),
                    word(),
                    a("IRScalar.ptr_", [Expr::bvar(2)]),
                    Expr::bvar(1),
                    Expr::nat_lit(8),
                    c("Bool.false"),
                    Expr::bvar(0),
                ],
            ),
            returned(),
        );
        bind(
            a(
                "ir_byte_load_v1",
                [
                    Expr::bvar(3),
                    word(),
                    a("IRScalar.ptr_", [Expr::bvar(1)]),
                    Expr::nat_lit(8),
                    c("Bool.false"),
                    Expr::bvar(2),
                ],
            ),
            store,
        )
    };
    let domains = [
        c("IRByteContextV1"),
        c("IRByteMemoryV1"),
        c("Nat"),
        c("Nat"),
    ];
    let ty = domains
        .iter()
        .rev()
        .fold(c("IRByteMemoryResultV1"), |body, ty| {
            Expr::pi(BinderInfo::Default, ty.clone(), body)
        });
    let value = domains
        .into_iter()
        .rev()
        .fold(body, |body, ty| lam(ty, body));
    IslandEnvironment::new(
        encode_island_declarations_v1(&[Declaration::Definition {
            name: Name::from_string("Source.wordEffect"),
            level_params: vec![],
            type_: ty,
            value,
            is_reducible: true,
        }])
        .unwrap(),
    )
}
fn core(literal: Option<u64>) -> Module {
    let mut module = ModuleBuilder::new_with_target_info(
        "non_tla_word_effect",
        cg::CoreHostJitTarget::detect()
            .unwrap()
            .trust_ir_target_info()
            .clone(),
    );
    let signature = module.add_func_type(vec![Ty::Ptr, Ty::Ptr], vec![]);
    let mut function = module.function("word_effect", signature);
    function.set_calling_conv(CallingConv::C);
    let block = function.create_block();
    let context = function.add_block_param(block, Ty::Ptr);
    let output = function.add_block_param(block, Ty::Ptr);
    function.switch_to_block(block);
    let value = match literal {
        Some(value) => function.iconst(Ty::U64, i128::from(value)),
        None => function.load_aligned(Ty::U64, context, 8),
    };
    function.store_aligned(Ty::U64, output, value, 8);
    function.ret(vec![]);
    function.build();
    module.build().unwrap()
}
pub(crate) fn certified(literal: Option<u64>) -> Module {
    let started = std::time::Instant::now();
    let module = contract::certify(core(literal), &source(literal), "Source.wordEffect")
        .expect("real kernel replay of independent one-word source");
    println!(
        "WORD_SOURCE_KERNEL_CERTIFICATION_SECONDS={:.9}",
        started.elapsed().as_secs_f64()
    );
    module
}
pub(crate) fn false_source_refuses() {
    let error =
        contract::certify(core(Some(42)), &source(Some(43)), "Source.wordEffect").unwrap_err();
    assert!(
        error.contains("TypeMismatch"),
        "actual independent false source refusal: {error}"
    );
}
pub(crate) fn manifest(module: &Module) -> cg::jit_contract::ArtifactManifestV1 {
    contract::manifest(
        module,
        "source:Source.wordEffect",
        cg::compile_service::CompileGeneration::new(1),
    )
}
