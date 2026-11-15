// Copyright 2026 Andrew Yates | Apache-2.0
//! Independently replayed SOURCE/Core input for ordinary licensed lowering.
//! Serialized producer DATA is untrusted until each real consumer succeeds.
//! No native invocation, physical access, frame or machine proof is claimed.
use super::*;
use trust_ir_build::clean_kernel::{BinderInfo, Expr, Name};
use trust_ir_build::core_execution::{Catalog, Limits};
use trust_ir_build::source_readonly_calls::{
    check_readonly_source_family, reflect_readonly_source_core_module_v1,
};
fn constant(name: &str) -> Expr {
    Expr::const_(Name::from_string(name), vec![])
}
fn nat(n: u64) -> Expr {
    Expr::nat_lit(n)
}
fn app(name: &str, args: impl IntoIterator<Item = Expr>) -> Expr {
    Expr::apps(constant(name), args)
}
fn list(ty: &str, values: &[Expr]) -> Expr {
    values
        .iter()
        .rev()
        .fold(app("IRList.nil", [constant(ty)]), |tail, head| {
            app("IRList.cons", [constant(ty), head.clone(), tail])
        })
}
fn memory() -> Expr {
    let mut mem = app(
        "IRByteMemoryV1.mk",
        [
            list(
                "IRByteAllocationV1",
                &[app(
                    "IRByteAllocationV1.mk",
                    [nat(80), nat(24), nat(0), constant("Bool.true")],
                )],
            ),
            Expr::lam(
                BinderInfo::Default,
                constant("Nat"),
                app("IROption.none", [constant("Nat")]),
            ),
            nat(104),
        ],
    );
    for (index, word) in [42, 43, 44].into_iter().enumerate() {
        mem = app(
            "IRByteMemoryV1.mk",
            [
                app("ir_byte_mem_allocs_v1", [mem.clone()]),
                app(
                    "ir_byte_write_word_v1",
                    [
                        app("ir_byte_mem_bytes_v1", [mem.clone()]),
                        nat(80 + 8 * index as u64),
                        nat(8),
                        nat(word),
                    ],
                ),
                app("ir_byte_mem_next_v1", [mem]),
            ],
        );
    }
    mem
}
fn providers() -> Expr {
    Expr::lam(
        BinderInfo::Default,
        constant("Nat"),
        Expr::lam(
            BinderInfo::Default,
            app("IRList", [constant("IRScalar")]),
            Expr::lam(
                BinderInfo::Default,
                constant("IRByteMemoryV1"),
                Expr::lam(
                    BinderInfo::Default,
                    constant("Nat"),
                    app(
                        "IRByteImportResultV1.mk",
                        [
                            constant("Nat"),
                            app("IROutcome.stuck", [constant("IRFault.no_func")]),
                            Expr::bvar(1),
                            Expr::bvar(0),
                        ],
                    ),
                ),
            ),
        ),
    )
}
fn original() -> trust_ir::Module {
    trust_ir::binary::deserialize_module(include_bytes!(
        "../tests/fixtures/licensed_readonly_entry/original-module.bin"
    ))
    .unwrap()
}
#[test]
fn licensed_readonly_original_source_core_owner_reaches_ordinary_lowering_queries() {
    let module = original();
    let report = trust_ir_build::validate_module_with_config(
        &module,
        &trust_ir_build::ValidationConfig::pinned()
            .with_bound_certificates(true)
            .with_source_bound_certificates(true)
            .with_gate_evidence(true),
    );
    assert!(report.is_ok(), "{:?}", report.errors());
    let family = check_readonly_source_family(&report).unwrap();
    let reflected = reflect_readonly_source_core_module_v1(
        &family,
        &[
            (trust_ir::FuncId::new(0), 4096),
            (trust_ir::FuncId::new(1), 8192),
        ],
    )
    .unwrap();
    let specification = clean_verify::eval_ir::shared_specification_with_stack(
        clean_verify::eval_ir::EvalIrVocabulary::ByteV1,
    )
    .unwrap();
    let mut catalog = Catalog::new(
        specification.env(),
        &reflected,
        Limits {
            max_operations: 100_000,
            max_locals: 10_000,
            max_list_items: 1_000,
            max_lookup_candidates: 1_000,
            lookup_heartbeats: 2_000_000,
            lookup_cache_entries: 100_000,
        },
    )
    .unwrap();
    let selected = catalog
        .readonly_eight_forward_call(trust_ir::FuncId::new(1), trust_ir::FuncId::new(0))
        .unwrap();
    let core = selected
        .check_entry_proof(
            constant("Nat"),
            providers(),
            memory(),
            nat(37),
            88,
            43,
            include_bytes!("../tests/fixtures/licensed_readonly_entry/entry.proof.dag-v2"),
        )
        .unwrap();
    let entry = core
        .check_source_family(
            &family,
            include_bytes!("../tests/fixtures/licensed_readonly_entry/effect.proof.dag-v2"),
        )
        .unwrap();
    let (lowered, _validation) =
        trust_cg_lower::translate_module_strict_for_arch_with_tls_and_validation_with_license(
            &module,
            trust_cg_lower::GuardCarrierArch::AArch64,
            trust_cg_lower::TlsDialect::MachOTlv,
            &trust_cg_lower::CodegenLicensePolicy::default(),
        )
        .unwrap();
    let leaf = &lowered[0].0;
    assert!(
        bind_read_only_source(&module, 0, leaf).is_err(),
        "diagnostic metadata refusal must stay closed"
    );
    let queries = bind_licensed_read_only_source(&entry, leaf).unwrap();
    assert!(std::ptr::eq(queries.core_entry(), &entry));
    assert!(std::ptr::eq(queries.queries().module(), &module));
    assert_eq!(queries.queries().read_requirements().len(), 1);
    assert_eq!(queries.queries().load_obligations().len(), 1);
    let mut wrong = leaf.clone();
    wrong.name.push_str("_foreign");
    assert!(bind_licensed_read_only_source(&entry, &wrong).is_err());
    let mut wrong = leaf.clone();
    wrong.signature.returns[0] = trust_cg_lower::Type::I32;
    assert!(bind_licensed_read_only_source(&entry, &wrong).is_err());
    let caller = &lowered[1].0;
    assert!(bind_licensed_read_only_source(&entry, caller).is_err());
}
