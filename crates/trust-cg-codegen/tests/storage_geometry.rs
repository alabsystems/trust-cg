//! Native address-only Storage geometry; never an initialized Storage value.
#![cfg(all(
    any(target_arch = "aarch64", target_arch = "x86_64"),
    any(target_os = "linux", target_os = "macos")
))]
use std::collections::HashMap;
use trust_cg_codegen::{
    CodegenLicensePolicy, Compiler, CompilerConfig, CoreHostJitTarget, Target,
    UnlicensedBodyPolicy, pipeline::OptLevel,
};
use trust_ir::{
    BinOp, CastOp, FieldDef, Module, StorageLayout, StructDef, StructId, StructRepr, Ty,
};
use trust_ir_build::ModuleBuilder;

fn storage() -> Ty {
    Ty::Storage(StorageLayout::new(80, 8))
}
fn module(parent: bool, multi: bool) -> Module {
    let mut mb = ModuleBuilder::new("address_only_storage");
    let pointee = if parent {
        Ty::Struct(mb.add_struct(StructDef {
            id: StructId::new(0),
            name: "Parent".into(),
            origin: None,
            fields: vec![
                FieldDef {
                    name: "head".into(),
                    ty: Ty::U64,
                    offset: Some(0),
                },
                FieldDef {
                    name: "backing".into(),
                    ty: storage(),
                    offset: Some(8),
                },
                FieldDef {
                    name: "tail".into(),
                    ty: Ty::U64,
                    offset: Some(88),
                },
            ],
            size: Some(96),
            align: Some(8),
            repr: StructRepr::Rust,
        }))
    } else {
        storage()
    };
    let element = mb.add_type(pointee.clone());
    let sig = mb.add_func_type(vec![], vec![Ty::U64]);
    let mut fb = mb.function("address_only", sig);
    let block = fb.create_block();
    fb.switch_to_block(block);
    let base = fb.alloca(Ty::Array(element, 3));
    let one = fb.iconst(Ty::U64, 1);
    let indices = if multi { vec![one, one] } else { vec![one] };
    let address = fb.gep(pointee, base, indices);
    let address = if parent {
        fb.gep_byte_offset(address, 88)
    } else {
        address
    };
    let value = fb.iconst(Ty::U64, 7);
    fb.store(Ty::U64, address, value);
    let loaded = fb.load(Ty::U64, address);
    let start = fb.cast(CastOp::PtrToInt, Ty::Ptr, Ty::U64, base);
    let end = fb.cast(CastOp::PtrToInt, Ty::Ptr, Ty::U64, address);
    let offset = fb.binop(BinOp::Sub, Ty::U64, end, start);
    let result = fb.binop(BinOp::Add, Ty::U64, loaded, offset);
    fb.ret(vec![result]);
    fb.build();
    mb.build().expect("valid address-only source")
}
fn compiler(opt: OptLevel) -> Compiler {
    let host = CoreHostJitTarget::detect().expect("supported native host");
    let mut config = CompilerConfig::jit_fast(Target::host());
    config.opt_level = opt;
    Compiler::new_for_target_spec(config, host.target_spec()).with_codegen_license(
        CodegenLicensePolicy::default().with_unlicensed(UnlicensedBodyPolicy::Permit),
    )
}
#[test]
fn storage_and_parent_allocation_stride_execute_without_by_value_carriers() {
    for parent in [false, true] {
        for multi in [false, true] {
            for counted in [false, true] {
                let mut module = module(parent, multi);
                if counted {
                    let trust_ir::Inst::Alloca {
                        ty: Ty::Array(element, 3),
                        ..
                    } = &module.functions[0].blocks[0].body[0].inst
                    else {
                        panic!("exact source allocation");
                    };
                    let pointee = module.types[element.as_usize()].clone();
                    let count = trust_ir::ValueId::new(100);
                    let body = &mut module.functions[0].blocks[0].body;
                    body[0].inst = trust_ir::Inst::Alloca {
                        ty: pointee,
                        count: Some(count),
                        align: None,
                    };
                    body.insert(
                        0,
                        trust_ir::InstrNode::new(trust_ir::Inst::Const {
                            ty: Ty::U64,
                            value: trust_ir::Constant::Int(3),
                        })
                        .with_result(count),
                    );
                }
                assert!(trust_ir_build::validate_module(&module).is_empty());
                for opt in [OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::O3] {
                    let result = compiler(opt)
                        .compile_module_to_jit(&module, &HashMap::new())
                        .expect("geometry only native compilation");
                    // SAFETY: the actual source has no arguments and exactly U64
                    // result. Its scalar access stays within its own three-element
                    // allocation, either Array(T,3) or Alloca(T,count=3).
                    let callable = unsafe {
                        result
                            .buffer
                            .get_fn_bound::<extern "C" fn() -> u64>("address_only")
                    }
                    .expect("native callable");
                    let stride = if parent { 96 } else { 80 };
                    let steps = if multi { 2 } else { 1 };
                    let expected = 7 + stride * steps + if parent { 88 } else { 0 };
                    assert_eq!(
                        callable.as_ref()(),
                        expected,
                        "parent={parent} multi={multi} counted={counted} opt={opt:?}"
                    );
                }
            }
        }
    }
    // Zero size does not erase the declared alignment or create a value.
    let mut mb = ModuleBuilder::new("aligned_empty_storage");
    let sig = mb.add_func_type(vec![], vec![Ty::U64]);
    let mut fb = mb.function("alignment", sig);
    let block = fb.create_block();
    fb.switch_to_block(block);
    let address = fb.alloca(Ty::Storage(StorageLayout::new(0, 32)));
    let word = fb.cast(CastOp::PtrToInt, Ty::Ptr, Ty::U64, address);
    let mask = fb.iconst(Ty::U64, 31);
    let remainder = fb.binop(BinOp::And, Ty::U64, word, mask);
    fb.ret(vec![remainder]);
    fb.build();
    let module = mb.build().unwrap();
    for opt in [OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::O3] {
        let result = compiler(opt)
            .compile_module_to_jit(&module, &HashMap::new())
            .unwrap();
        // SAFETY: the source has this exact scalar signature; no memory access.
        let callable = unsafe {
            result
                .buffer
                .get_fn_bound::<extern "C" fn() -> u64>("alignment")
        }
        .unwrap();
        assert_eq!(
            callable.as_ref()(),
            0,
            "zero-sized Storage alignment {opt:?}"
        );
    }
}
#[test]
fn storage_parent_by_value_and_overlapping_geometry_refuse_before_execution() {
    let mut by_value = module(true, false);
    let mut unused = by_value.func_types[0].clone();
    unused.params = vec![Ty::Struct(StructId::new(0))];
    by_value.func_types.push(unused);
    let error = compiler(OptLevel::O0)
        .compile_module_to_jit(&by_value, &HashMap::new())
        .expect_err("unused ABI still refuses")
        .to_string();
    assert!(error.to_lowercase().contains("storage"), "{error}");
    let mut overlap = module(true, false);
    overlap.structs[0].fields[2].offset = Some(80);
    let error = compiler(OptLevel::O0)
        .compile_module_to_jit(&overlap, &HashMap::new())
        .expect_err("overlap must refuse")
        .to_string();
    assert!(
        error.to_lowercase().contains("geometry") || error.to_lowercase().contains("layout"),
        "{error}"
    );
}

#[test]
fn storage_geometry_keeps_static_frame_limit_and_refuses_unqualified_address_operands() {
    for layout in [
        StorageLayout::new(1 << 21, 8),
        StorageLayout::new(0, 1 << 21),
    ] {
        let mut module = module(false, false);
        module.types[0] = Ty::Storage(layout);
        let error = compiler(OptLevel::O0)
            .compile_module_to_jit(&module, &HashMap::new())
            .expect_err("oversized storage frame must refuse before execution")
            .to_string();
        assert!(
            error.contains("Alloca") && error.contains("static limit"),
            "{error}"
        );
    }
    for ty in [Ty::F64, Ty::U64] {
        let mut module = module(false, false);
        let count = trust_ir::ValueId::new(99);
        module.func_types[0].params = vec![ty.clone()];
        let block = &mut module.functions[0].blocks[0];
        block.params.push((count, ty));
        let trust_ir::Inst::Alloca { count: actual, .. } = &mut block.body[0].inst else {
            panic!("actual alloca");
        };
        *actual = Some(count);
        let error = compiler(OptLevel::O0)
            .compile_module_to_jit(&module, &HashMap::new())
            .expect_err("unqualified storage count must refuse")
            .to_string();
        assert!(error.contains("Storage allocation count"), "{error}");
    }
    let mut wide_index = module(false, false);
    let index = trust_ir::ValueId::new(101);
    let body = &mut wide_index.functions[0].blocks[0].body;
    for node in body.iter_mut() {
        if let trust_ir::Inst::GEP {
            pointee_ty: Ty::Storage(_),
            indices,
            ..
        } = &mut node.inst
        {
            *indices = vec![index];
        }
    }
    body.insert(
        0,
        trust_ir::InstrNode::new(trust_ir::Inst::Const {
            ty: Ty::U128,
            value: trust_ir::Constant::Int(1),
        })
        .with_result(index),
    );
    let error = compiler(OptLevel::O0)
        .compile_module_to_jit(&wide_index, &HashMap::new())
        .expect_err("wide Storage GEP index must refuse")
        .to_string();
    assert!(error.contains("Storage GEP index"), "{error}");
}

#[test]
fn storage_free_reference_and_native_consumer_preserves_scalar_results() {
    use trust_ir::interpret::{InterpretValue, Interpreter};

    let mut mb = ModuleBuilder::new("storage_free_consumer");
    let sig = mb.add_func_type(vec![], vec![Ty::U64]);
    let mut fb = mb.function("scalar_entry", sig);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    let answer = fb.uconst(Ty::U64, 42);
    fb.ret(vec![answer]);
    fb.build();
    let mut ty = Ty::U64;
    for _ in 0..32 {
        let id = mb.add_type(ty);
        ty = Ty::Array(id, 1);
        mb.add_func_type(vec![Ty::PtrConst(Box::new(ty.clone()))], vec![]);
    }
    let module = mb.build().expect("finite storage-free module");
    assert!(trust_ir_build::validate_module(&module).is_empty());
    let layouts = module.layout_table();
    let mut violations = vec![];
    module.visit_storage_violations(&layouts, |v| violations.push(v));
    assert!(violations.is_empty());
    assert_eq!(layouts.stats().reach_steps, 0);
    let interpreter = Interpreter::with_module(&module);
    let expected = InterpretValue::int(Ty::U64, 42).unwrap();
    for opt in [OptLevel::O0, OptLevel::O2] {
        let result = compiler(opt)
            .compile_module_to_jit(&module, &HashMap::new())
            .expect("ordinary native scalar consumer");
        // SAFETY: the validated source has exactly this no-argument U64 signature.
        let callable = unsafe {
            result
                .buffer
                .get_fn_bound::<extern "C" fn() -> u64>("scalar_entry")
        }
        .expect("native scalar callable");
        for _ in 0..8 {
            let outcome = interpreter
                .execute_func(module.functions[0].id, [])
                .unwrap();
            assert_eq!(outcome.returns, vec![expected.clone()]);
            assert_eq!(callable.as_ref()(), 42, "{opt:?}");
        }
    }
}
