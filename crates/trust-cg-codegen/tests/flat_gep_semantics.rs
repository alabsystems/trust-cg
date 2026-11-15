//! Compare native GEP results with closed-form whole-pointee address arithmetic.
//! The pinned TrustIR interpreter also checks every supported byte layout before
//! lowering. Records and closures explicitly retain its missing-layout boundary.
//! No dereference or host-memory model is involved: addresses are integers
//! converted to dangling pointers, advanced, and converted back to integers.
#![cfg(all(
    any(target_arch = "aarch64", target_arch = "x86_64"),
    any(target_os = "linux", target_os = "macos")
))]

use std::collections::HashMap;
use trust_cg_codegen::{
    CodegenLicensePolicy, Compiler, CompilerConfig, CoreHostJitTarget, Target,
    UnlicensedBodyPolicy, pipeline::OptLevel,
};
use trust_ir::interpret::{InterpretOptions, InterpretValue, Interpreter};
use trust_ir::{
    CastOp, ClosureTy, EnumDef, EnumId, EnumLayoutDescriptor, EnumTagEncoding, EnumTagRepr,
    EnumVariant, FieldDef, FuncId, Module, RecordDef, RecordId, StructDef, StructId, StructRepr,
    Ty,
};
use trust_ir_build::ModuleBuilder;

fn field(name: &str, ty: Ty, offset: Option<u64>) -> FieldDef {
    FieldDef {
        name: name.into(),
        ty,
        offset,
    }
}

fn pointee(mb: &mut ModuleBuilder, shape: &str) -> (Ty, u64) {
    match shape {
        "scalar" => (Ty::U32, 4),
        "tuple" => (Ty::Tuple(vec![Ty::U8, Ty::U64]), 16),
        "array" => {
            let element = mb.add_type(Ty::U64);
            let row = mb.add_type(Ty::Array(element, 4));
            (Ty::Array(row, 2), 64)
        }
        "record" => {
            let id = mb.add_record(RecordDef {
                id: RecordId::new(0),
                name: shape.into(),
                fields: vec![field("a", Ty::U8, None), field("b", Ty::U64, None)],
            });
            (Ty::Record(id), 16)
        }
        "closure" => {
            let func = mb.add_func_type(vec![], vec![]);
            let id = mb.add_closure_type(ClosureTy {
                func,
                captures: vec![Ty::U8, Ty::U64],
            });
            (Ty::Closure(id), 16)
        }
        "enum" | "niche" => {
            let mut def = EnumDef::new(
                EnumId::new(0),
                shape,
                vec![
                    EnumVariant {
                        name: "None".into(),
                        fields: vec![],
                        field_names: vec![],
                    },
                    EnumVariant {
                        name: "Some".into(),
                        fields: vec![Ty::Ptr],
                        field_names: vec![],
                    },
                ],
            );
            let size = if shape == "niche" {
                def.layout = Some(EnumLayoutDescriptor {
                    encoding: EnumTagEncoding::Niche {
                        untagged_variant: 1,
                        niche_variants_start: 0,
                        niche_variants_end: 0,
                        niche_start: 0,
                        niche_offset: 0,
                        niche_ty: EnumTagRepr::U64,
                    },
                    size: 8,
                    align: 8,
                    variant_field_offsets: vec![vec![], vec![0]],
                });
                8
            } else {
                16
            };
            (Ty::Enum(mb.add_enum(def)), size)
        }
        "struct" | "packed" | "declared" => {
            let (repr, fields, size, align, stride) = match shape {
                "packed" => (
                    StructRepr::Packed(1),
                    vec![field("a", Ty::U8, Some(0)), field("b", Ty::U64, Some(1))],
                    Some(9),
                    Some(1),
                    9,
                ),
                "declared" => (
                    StructRepr::Rust,
                    vec![field("a", Ty::U64, Some(8)), field("b", Ty::U64, Some(0))],
                    Some(16),
                    Some(8),
                    16,
                ),
                _ => (
                    StructRepr::C,
                    vec![field("a", Ty::U8, Some(0)), field("b", Ty::U64, Some(8))],
                    Some(16),
                    Some(8),
                    16,
                ),
            };
            let id = mb.add_struct(StructDef {
                id: StructId::new(0),
                name: shape.into(),
                origin: None,
                fields,
                size,
                align,
                repr,
            });
            (Ty::Struct(id), stride)
        }
        _ => panic!("unknown shape {shape}"),
    }
}

fn module(shape: &str, count: usize, index_ty: Ty, constant_second: bool) -> (Module, u64) {
    let mut mb = ModuleBuilder::new(format!("flat_gep_{shape}"));
    let (pointee, stride) = pointee(&mut mb, shape);
    let signature = mb.add_func_type(vec![Ty::U64; 3], vec![Ty::U64]);
    let mut fb = mb.function("address", signature);
    let entry = fb.create_block();
    let args: Vec<_> = (0..3).map(|_| fb.add_block_param(entry, Ty::U64)).collect();
    fb.switch_to_block(entry);
    let address = fb.iconst(Ty::U64, 4096);
    let base = fb.cast(CastOp::IntToPtr, Ty::U64, Ty::Ptr, address);
    let mut indices: Vec<_> = args
        .into_iter()
        .take(count)
        .map(|value| {
            if index_ty == Ty::U64 {
                value
            } else {
                let op = if index_ty == Ty::I64 {
                    CastOp::Bitcast
                } else {
                    CastOp::Trunc
                };
                fb.cast(op, Ty::U64, index_ty.clone(), value)
            }
        })
        .collect();
    if constant_second {
        indices[1] = fb.iconst(index_ty, 1);
    }
    let result = fb.gep(pointee, base, indices);
    let result = fb.cast(CastOp::PtrToInt, Ty::Ptr, Ty::U64, result);
    fb.ret(vec![result]);
    fb.build();
    let module = mb.build().expect("ModuleBuilder::build: test fixture");
    assert_eq!(trust_ir_build::validate_module(&module), [], "{shape}");
    (module, stride)
}

fn interpreted(module: &Module, row: [u64; 3]) -> Result<u64, String> {
    let result = Interpreter::with_module(module)
        .with_options(InterpretOptions {
            fuel: 100,
            max_call_depth: 2,
            panic_strategy: trust_ir::interpret::PanicStrategy::Abort,
        })
        .execute_func(
            FuncId::new(0),
            row.into_iter()
                .map(|value| InterpretValue::int(Ty::U64, i128::from(value)).unwrap()),
        )
        .map_err(|error| error.to_string())?;
    assert_eq!(result.host_calls, 0);
    assert_eq!(result.returns.len(), 1);
    Ok(u64::try_from(result.returns[0].as_int().unwrap().as_unsigned()).unwrap())
}

fn check(shape: &str, count: usize, index_ty: Ty, rows: &[[u64; 3]]) {
    check_with_constant_second(shape, count, index_ty, rows, false);
}

fn check_with_constant_second(
    shape: &str,
    count: usize,
    index_ty: Ty,
    rows: &[[u64; 3]],
    constant_second: bool,
) {
    let (module, stride) = module(shape, count, index_ty, constant_second);
    // Establish the address independently before attempting compilation. The
    // reference interpreter has no byte layout for records or closures; assert
    // that precise boundary instead of treating its error as an execution oracle.
    let reference_supported = !matches!(shape, "record" | "closure");
    let expected: Vec<_> = rows
        .iter()
        .map(|&row| {
            let mut indices = row[..count].to_vec();
            if constant_second {
                indices[1] = 1;
            }
            let expected = 4096 + indices.iter().sum::<u64>() * stride;
            if reference_supported {
                assert_eq!(
                    interpreted(&module, row).expect("defined TrustIR execution"),
                    expected
                );
            } else {
                let error = interpreted(&module, row).unwrap_err();
                assert_eq!(
                    error,
                    format!("type_error at bb0: {shape}.0 has no byte layout")
                );
            }
            expected
        })
        .collect();
    if reference_supported {
        eprintln!(
            "FLAT_GEP_REFERENCE shape={shape} indices={count} cases={}",
            rows.len()
        );
    } else {
        eprintln!(
            "FLAT_GEP_LAYOUT_BOUNDARY shape={shape} indices={count} cases={}",
            rows.len()
        );
    }
    let host = CoreHostJitTarget::detect().expect("supported native test host");
    for opt in [OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::O3] {
        let mut config = CompilerConfig::jit_fast(Target::host());
        config.opt_level = opt;
        let compiler = Compiler::new_for_target_spec(config, host.target_spec())
            .with_codegen_license(
                CodegenLicensePolicy::default().with_unlicensed(UnlicensedBodyPolicy::Permit),
            );
        let result = compiler
            .compile_module_to_jit(&module, &HashMap::new())
            .unwrap_or_else(|error| panic!("{shape}, {count} indices, {opt:?}: {error}"));
        // SAFETY: the validated function has exactly this scalar signature.
        // It performs no dereference; its executable buffer outlives the call.
        let function = unsafe {
            result
                .buffer
                .get_fn_bound::<extern "C" fn(u64, u64, u64) -> u64>("address")
        }
        .expect("address");
        for (&row, expected) in rows.iter().zip(&expected) {
            assert_eq!(
                function.as_ref()(row[0], row[1], row[2]),
                *expected,
                "{shape}, {count} indices, {opt:?}, {row:?}"
            );
        }
    }
    eprintln!(
        "FLAT_GEP_NATIVE shape={shape} indices={count} calls={}",
        rows.len() * 4
    );
}

const ROWS: &[[u64; 3]] = &[[0, 0, 0], [0, 1, 0], [1, 0, 0], [1, 2, 3], [9, 7, 5]];

#[test]
fn scalar_indices_match_reference() {
    for count in [2, 3] {
        check("scalar", count, Ty::U64, ROWS);
    }
}

#[test]
fn tuple_indices_match_reference() {
    for count in [2, 3] {
        check("tuple", count, Ty::U64, ROWS);
    }
}

#[test]
fn struct_indices_match_reference() {
    for count in [2, 3] {
        check("struct", count, Ty::U64, ROWS);
    }
}

#[test]
fn record_indices_match_layout_arithmetic() {
    for count in [2, 3] {
        check("record", count, Ty::U64, ROWS);
    }
}

#[test]
fn nested_array_indices_match_reference() {
    for count in [2, 3] {
        check("array", count, Ty::U64, ROWS);
    }
}

#[test]
fn packed_indices_match_reference() {
    for count in [2, 3] {
        check("packed", count, Ty::U64, ROWS);
    }
}

#[test]
fn declared_indices_match_reference() {
    for count in [2, 3] {
        check("declared", count, Ty::U64, ROWS);
    }
}

#[test]
fn closure_indices_match_layout_arithmetic() {
    for count in [2, 3] {
        check("closure", count, Ty::U64, ROWS);
    }
}

#[test]
fn direct_enum_indices_match_reference() {
    for count in [2, 3] {
        check("enum", count, Ty::U64, ROWS);
    }
}

#[test]
fn niche_enum_indices_match_reference() {
    for count in [2, 3] {
        check("niche", count, Ty::U64, ROWS);
    }
}

#[test]
fn empty_and_single_index_controls_match_reference() {
    for count in [0, 1] {
        check("scalar", count, Ty::U64, ROWS);
    }
}

#[test]
fn narrow_indices_keep_signedness_and_width() {
    for ty in [Ty::U8, Ty::U16, Ty::U32] {
        check("packed", 3, ty, &[[0, 128, 255], [255, 1, 128]]);
    }
    for ty in [Ty::I8, Ty::I16, Ty::I32, Ty::I64] {
        check("packed", 3, ty, &[[0, 1, 127], [127, 3, 2]]);
    }
}

#[test]
fn negative_index_is_outside_the_reference_defined_domain() {
    let (module, _) = module("scalar", 2, Ty::I8, false);
    assert!(
        interpreted(&module, [0, 255, 0])
            .unwrap_err()
            .contains("negative index")
    );
    // Do not compare native execution of source-level UB with a numeric answer.
}

/// The old native lowering accepted a literal second index and returned the
/// selected field's address, so these cases detect a wrong result rather
/// than only the refusal of dynamic indices.
#[test]
fn constant_second_index_matches_whole_object_stride() {
    for shape in ["struct", "record", "packed", "declared"] {
        check_with_constant_second(shape, 2, Ty::U64, &[[0, 1, 0], [3, 1, 0]], true);
    }
}
