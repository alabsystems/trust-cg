// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0
//! Real adapter regression inputs; these tests grant no ABI proof credit.

#[path = "common/native_scalar_c_abi.rs"]
mod fixtures;

use trust_cg_lower::{
    CodegenLicensePolicy, GuardCarrierArch, NativeAbiContext, ObjectAccessModel,
    ObjectSymbolPolicy, TlsDialect, UnlicensedBodyPolicy,
};
use trust_ir::signature_abi::{AbiExtension, AbiPassMode};
use trust_ir::{Inst, Module, Ty};

fn license() -> CodegenLicensePolicy {
    CodegenLicensePolicy::default().with_unlicensed(UnlicensedBodyPolicy::Permit)
}

fn lower(
    module: &Module,
    triple: &str,
) -> Result<Vec<(trust_cg_lower::Function, trust_cg_lower::ProofContext)>, String> {
    let (arch, native) = if triple.starts_with("aarch64-") {
        (
            GuardCarrierArch::AArch64,
            NativeAbiContext::aarch64(triple.into()).unwrap(),
        )
    } else {
        (
            GuardCarrierArch::X86_64,
            NativeAbiContext::x86_system_v(triple.into()).unwrap(),
        )
    };
    let access = ObjectAccessModel::from(if triple.contains("-apple-") {
        TlsDialect::MachOTlv
    } else {
        TlsDialect::ElfLocalExec
    });
    let admitted =
        trust_cg_lower::admit_module(module, &license(), &[]).map_err(|e| e.to_string())?;
    trust_cg_lower::translate_admitted_module_for_native_scalar_c_abi(
        &admitted,
        arch,
        access,
        ObjectSymbolPolicy::default(),
        &native,
    )
    .map(|result| result.0)
    .map_err(|e| e.to_string())
}

const TRIPLES: [&str; 4] = [
    "aarch64-apple-darwin",
    "aarch64-unknown-linux-gnu",
    "x86_64-apple-darwin",
    "x86_64-unknown-linux-gnu",
];

#[test]
fn native_context_consumes_fixed_and_variadic_prototypes_without_erasing_them() {
    for triple in TRIPLES {
        for variadic in [false, true] {
            let fixed = if variadic {
                vec![Ty::I32]
            } else {
                vec![Ty::I8, Ty::U16, Ty::Ptr, Ty::F64]
            };
            let actual = if variadic {
                vec![Ty::I32, Ty::I64, Ty::F64, Ty::Ptr]
            } else {
                fixed.clone()
            };
            let module = fixtures::fixture(triple, fixed, actual, Some(Ty::I8), variadic);
            let before = module.clone();
            let lir = lower(&module, triple).unwrap_or_else(|e| panic!("{triple}: {e}"));
            assert_eq!(module, before);
            let calls = lir[0]
                .0
                .blocks
                .values()
                .flat_map(|block| &block.instructions)
                .filter(|inst| {
                    matches!(
                        inst.opcode,
                        trust_cg_lower::instructions::Opcode::Call { .. }
                            | trust_cg_lower::instructions::Opcode::CallVariadic { .. }
                    )
                })
                .count();
            assert_eq!(calls, 1);
        }
    }
}

#[test]
fn extensions_modes_target_owner_and_unwind_mutants_are_refused() {
    let triple = "aarch64-apple-darwin";
    let base = fixtures::fixture(triple, vec![Ty::I8], vec![Ty::I8], Some(Ty::I8), false);
    for mutant in 0..9 {
        let mut module = base.clone();
        let abi = module.func_types[0].abi.as_mut().unwrap();
        match mutant {
            0 => {
                if let AbiPassMode::Direct(scalar) = &mut abi.arguments[0].mode {
                    scalar.attributes.extension = AbiExtension::Zero;
                }
            }
            1 => abi.arguments[0].mode = AbiPassMode::Ignore,
            2 => abi.fixed_count = 0,
            3 => abi.can_unwind = true,
            4 => abi.source_abi = "RustCall".into(),
            5 => abi.arguments[0].bindings[0].carrier_bytes = 2,
            6 => {
                if let AbiPassMode::Direct(scalar) = &mut abi.result.mode {
                    scalar.attributes.extension = AbiExtension::None;
                }
            }
            7 => {
                if let AbiPassMode::Direct(scalar) = &mut abi.arguments[0].mode {
                    scalar.attributes.in_reg = true;
                }
            }
            8 => abi.target.abi = "unmodeled-abi".into(),
            _ => unreachable!(),
        }
        assert!(lower(&module, triple).is_err(), "mutant {mutant}");
    }
    assert!(lower(&base, "aarch64-unknown-linux-gnu").is_err());
    assert!(lower(&base, "x86_64-unknown-linux-gnu").is_err());
}

#[test]
fn anonymous_arguments_require_promotions_and_supported_scalar_types() {
    for ty in [Ty::I8, Ty::U16, Ty::F32, Ty::I128] {
        let module = fixtures::fixture(
            "aarch64-apple-darwin",
            vec![Ty::I32],
            vec![Ty::I32, ty],
            None,
            true,
        );
        assert!(lower(&module, "aarch64-apple-darwin").is_err());
    }
}

#[test]
fn contextless_template_inline_and_indirect_paths_keep_their_floor() {
    let triple = "aarch64-apple-darwin";
    let mut module = fixtures::fixture(triple, vec![Ty::I64], vec![Ty::I64], Some(Ty::I64), false);
    assert!(trust_cg_lower::reject_unconsumed_v41_target_neutral_surface(&module).is_err());
    assert!(
        trust_cg_lower::translate_function_with_license(&module.functions[1], &module, &license())
            .is_err()
    );
    assert!(
        trust_cg_lower::translate_body_template(
            &module,
            &module.functions[1],
            GuardCarrierArch::AArch64,
            ObjectAccessModel::default(),
            &license()
        )
        .is_err()
    );
    let callee = module.functions[0].id;
    let args = module.functions[1].blocks[0]
        .params
        .iter()
        .map(|(v, _)| *v)
        .collect();
    module.functions[1].blocks[0].body[0].inst = Inst::CallCannotUnwind { callee, args };
    assert!(lower(&module, triple).is_err());
    assert!(NativeAbiContext::x86_system_v("x86_64-pc-windows-msvc".into()).is_err());
}

#[test]
fn interned_prototype_can_belong_to_multiple_foreign_symbols() {
    let triple = "aarch64-apple-darwin";
    let mut module = fixtures::fixture(triple, vec![Ty::I64], vec![Ty::I64], Some(Ty::I64), false);
    let mut another = module.functions[0].clone();
    another.id = trust_ir::FuncId::new(2);
    another.name = "another_foreign_scalar".into();
    module.functions.push(another);
    lower(&module, triple).unwrap();
}

#[test]
fn recorded_callee_cannot_escape_through_closure_or_function_values() {
    let triple = "aarch64-apple-darwin";
    let base = fixtures::fixture(triple, vec![Ty::I64], vec![Ty::I64], Some(Ty::I64), false);
    for mutant in 0..5 {
        let mut module = base.clone();
        let closure = module
            .add_closure_type(trust_ir::ty::ClosureTy {
                func: module.functions[1].ty,
                captures: vec![],
            })
            .unwrap();
        let foreign_id = module.functions[0].id;
        let foreign_name = module.functions[0].name.clone();
        match mutant {
            0 => module.closure_types[closure.as_usize()].func = module.functions[0].ty,
            1..=3 => {
                let value = match mutant {
                    1 => trust_ir::Constant::FnDef(foreign_id),
                    2 => trust_ir::Constant::SymbolAddr {
                        symbol: foreign_name,
                        addend: 0,
                    },
                    _ => trust_ir::Constant::Closure {
                        func: foreign_id,
                        captures: vec![],
                    },
                };
                module.functions[1].blocks[0].body.insert(
                    0,
                    trust_ir::InstrNode::new(Inst::Const {
                        ty: if mutant == 3 {
                            Ty::Closure(closure)
                        } else {
                            Ty::Ptr
                        },
                        value,
                    })
                    .with_result(trust_ir::ValueId::new(10)),
                );
            }
            4 => module.functions[1].blocks[0].body.insert(
                0,
                trust_ir::InstrNode::new(Inst::MakeClosure {
                    ty: closure,
                    func: foreign_id,
                    captures: vec![],
                })
                .with_result(trust_ir::ValueId::new(10)),
            ),
            _ => unreachable!(),
        }
        assert!(lower(&module, triple).is_err(), "escape mutant {mutant}");
    }
}

#[test]
fn rustc_llvm_apple_aliases_do_not_select_another_native_abi() {
    for (source, compiler) in [
        ("arm64-apple-macosx11.0.0", "aarch64-apple-darwin"),
        ("x86_64-apple-macosx10.15.0", "x86_64-apple-darwin"),
    ] {
        let module = fixtures::fixture(source, vec![Ty::I64], vec![Ty::I64], Some(Ty::I64), false);
        lower(&module, compiler).unwrap();
    }
    for source in [
        "arm64e-apple-macosx11.0.0",
        "aarch64-apple-ios",
        "aarch64-unknown-linux-musl",
    ] {
        let module = fixtures::fixture(source, vec![Ty::I64], vec![Ty::I64], Some(Ty::I64), false);
        assert!(lower(&module, "aarch64-apple-darwin").is_err());
    }
}
