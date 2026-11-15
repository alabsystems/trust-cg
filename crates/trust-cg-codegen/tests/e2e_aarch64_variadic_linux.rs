// Copyright 2026 Andrew Yates | Apache-2.0
//! Native Linux AAPCS64 oracle: independently compiled C va_arg consumers read
//! calls emitted by TrustCG, with exact Linux targets and all optimization levels.
//! The producer performs C default promotions explicitly; this is execution
//! evidence, not proof-emission authority.

#![cfg(all(target_arch = "aarch64", target_os = "linux"))]

#[path = "common/fresh_dir.rs"]
mod fresh_dir;

use std::{fs, process::Command};
use trust_cg_codegen::{Compiler, CompilerConfig, pipeline::OptLevel, target::TargetSpec};
use trust_ir::{
    Block, BlockId, CastOp, Endianness, FieldDef, FuncId, FuncTy, Function, Inst, InstrNode,
    Linkage, Module, StructDef, StructId, StructPassingPolicy, StructRepr, TargetInfo, Ty, ValueId,
};

fn c_type(ty: &Ty) -> &'static str {
    match ty {
        Ty::I8 => "int8_t",
        Ty::U8 => "uint8_t",
        Ty::I16 => "int16_t",
        Ty::U16 => "uint16_t",
        Ty::I32 => "int32_t",
        Ty::U32 => "uint32_t",
        Ty::I64 => "int64_t",
        Ty::U64 => "uint64_t",
        Ty::I128 => "__int128",
        Ty::F32 => "float",
        Ty::F64 => "double",
        Ty::Struct(id) => match id.index() {
            0 => "Pair",
            1 => "Big",
            2 => "Hfa",
            _ => panic!("{ty:?}"),
        },
        _ => panic!("{ty:?}"),
    }
}

fn literal(ty: &Ty, index: usize) -> String {
    let n = index as u64 + 3;
    match ty {
        Ty::U64 => format!("UINT64_C(0xfedcba9876543200) + {n}"),
        Ty::I128 => format!("((__int128){n} << 83) - {}", 17 * n),
        Ty::F32 | Ty::F64 => format!("{}.25", 3 * n),
        Ty::Struct(id) => match id.index() {
            0 => format!("(Pair){{{n}, {}}}", 7 * n),
            1 => format!("(Big){{{n}, {}, {}}}", 7 * n, 19 * n),
            2 => format!("(Hfa){{{n}.25, {}.5, {}.75}}", 7 * n, 19 * n),
            _ => panic!("{ty:?}"),
        },
        Ty::U8 => format!("(uint8_t){}", 200 + n),
        Ty::U16 => format!("(uint16_t){}", 50000 + n),
        _ => format!("({})-{}", c_type(ty), 7 * n),
    }
}

fn digest(ty: &Ty, name: &str) -> String {
    match ty {
        Ty::F32 | Ty::F64 => format!("double_bits((double){name})"),
        Ty::I128 => format!("((uint64_t){name} ^ (uint64_t)(((__uint128_t){name}) >> 64))"),
        Ty::Struct(id) => match id.index() {
            0 => format!("({name}.a * UINT64_C(17) ^ {name}.b)"),
            1 => format!("({name}.a * UINT64_C(17) ^ {name}.b * UINT64_C(71) ^ {name}.c)"),
            2 => format!(
                "(double_bits({name}.a) * UINT64_C(17) ^ double_bits({name}.b) * UINT64_C(71) ^ double_bits({name}.c))"
            ),
            _ => panic!("{ty:?}"),
        },
        _ => format!("(uint64_t){name}"),
    }
}

fn promoted(ty: &Ty) -> Option<(Ty, CastOp)> {
    match ty {
        Ty::I8 | Ty::I16 => Some((Ty::I32, CastOp::SExt)),
        Ty::U8 | Ty::U16 => Some((Ty::I32, CastOp::ZExt)),
        Ty::F32 => Some((Ty::F64, CastOp::FPExt)),
        _ => None,
    }
}

fn add_case(
    module: &mut Module,
    c: &mut String,
    checks: &mut String,
    params: Vec<Ty>,
    fixed: usize,
    reverse: bool,
) {
    assert!(fixed > 0 && fixed <= params.len());
    let ordinal = module.functions.len() / 2;
    let callee_name = format!("oracle_{ordinal}");
    let wrapper_name = format!("native_{ordinal}");
    let mut order: Vec<_> = (0..params.len()).collect();
    if reverse {
        order[fixed..].reverse();
    }
    let call_types: Vec<_> = order
        .iter()
        .enumerate()
        .map(|(position, &index)| {
            if position < fixed {
                params[index].clone()
            } else {
                promoted(&params[index]).map_or_else(|| params[index].clone(), |(ty, _)| ty)
            }
        })
        .collect();
    let callee_type = module
        .add_func_type(FuncTy {
            params: call_types[..fixed].to_vec(),
            returns: vec![Ty::U64],
            abi: None,
            is_vararg: true,
        })
        .expect("Module::add_func_type: test fixture");
    let callee = FuncId::new(module.functions.len() as u32);
    let mut external = Function::new(callee, &callee_name, callee_type, BlockId::new(0));
    external.linkage = Linkage::External;
    external.blocks.clear();
    module
        .try_add_function(external)
        .expect("Module::try_add_function: test fixture");
    let wrapper_type = module
        .add_func_type(FuncTy {
            params: params.clone(),
            returns: vec![Ty::U64],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut wrapper = Function::new(
        FuncId::new(module.functions.len() as u32),
        &wrapper_name,
        wrapper_type,
        BlockId::new(0),
    );
    let mut body = Vec::new();
    let mut next = params.len() as u32;
    let args = order
        .iter()
        .enumerate()
        .map(|(position, &index)| {
            let input = ValueId::new(index as u32);
            if position >= fixed
                && let Some((dst_ty, op)) = promoted(&params[index])
            {
                let result = ValueId::new(next);
                next += 1;
                body.push(
                    InstrNode::new(Inst::Cast {
                        op,
                        src_ty: params[index].clone(),
                        dst_ty,
                        operand: input,
                    })
                    .with_result(result),
                );
                result
            } else {
                input
            }
        })
        .collect();
    let result = ValueId::new(next);
    body.push(InstrNode::new(Inst::Call { callee, args }).with_result(result));
    body.push(InstrNode::new(Inst::Return {
        values: vec![result],
    }));
    wrapper.blocks = vec![Block {
        id: BlockId::new(0),
        params: params
            .iter()
            .cloned()
            .enumerate()
            .map(|(index, ty)| (ValueId::new(index as u32), ty))
            .collect(),
        body,
    }];
    module
        .try_add_function(wrapper)
        .expect("Module::try_add_function: test fixture");

    // This C compiler independently determines the actual variadic ABI. The
    // expected result is a native call with the same logical argument sequence;
    // neither expected register placement nor values come from TrustCG output.
    let named = call_types[..fixed]
        .iter()
        .enumerate()
        .map(|(index, ty)| format!("{} a{index}", c_type(ty)))
        .collect::<Vec<_>>()
        .join(", ");
    c.push_str(&format!("__attribute__((noinline)) uint64_t {callee_name}({named}, ...) {{\nva_list ap; va_start(ap, a{});\nuint64_t result = 0;\n", fixed - 1));
    for (index, ty) in call_types.iter().enumerate() {
        if index >= fixed {
            c.push_str(&format!(
                "{} a{index} = va_arg(ap, {});\n",
                c_type(ty),
                c_type(ty)
            ));
        }
        c.push_str(&format!(
            "result = result * UINT64_C(257) ^ {};\n",
            digest(ty, &format!("a{index}"))
        ));
    }
    c.push_str("va_end(ap); return result;\n}\n");
    c.push_str(&format!(
        "extern uint64_t {wrapper_name}({});\n",
        params.iter().map(c_type).collect::<Vec<_>>().join(", ")
    ));
    let values: Vec<_> = params
        .iter()
        .enumerate()
        .map(|(index, ty)| literal(ty, index))
        .collect();
    checks.push_str(&format!("{{ uint64_t actual = {wrapper_name}({}); uint64_t expected = {callee_name}({}); if(actual != expected) {{ printf(\"case {ordinal}: expected=%llu actual=%llu\\n\", (unsigned long long)expected, (unsigned long long)actual); return {}; }} }}\n",
        values.join(", "), order.iter().map(|&index| values[index].clone()).collect::<Vec<_>>().join(", "), ordinal + 1));
}

fn corpus() -> (Module, String) {
    let mut module = Module::new("linux_variadic_abi");
    module.target_info = Some(TargetInfo {
        triple: "aarch64-unknown-linux-gnu".into(),
        pointer_size: 8,
        endianness: Endianness::Little,
        abi: Some("aapcs64".into()),
        struct_passing: StructPassingPolicy::NativeC,
    });
    for (index, (name, fields)) in [
        ("Pair", vec![Ty::U64; 2]),
        ("Big", vec![Ty::U64; 3]),
        ("Hfa", vec![Ty::F64; 3]),
    ]
    .into_iter()
    .enumerate()
    {
        module.structs.push(StructDef {
            origin: None,
            id: StructId::new(index as u32),
            name: name.into(),
            size: Some(fields.len() as u64 * 8),
            align: Some(8),
            repr: StructRepr::C,
            fields: fields
                .into_iter()
                .enumerate()
                .map(|(field, ty)| FieldDef {
                    name: format!("field{field}"),
                    ty,
                    offset: Some(field as u64 * 8),
                })
                .collect(),
        });
    }
    let mut c = String::from(
        "#include <stdint.h>\n#include <stdio.h>\n#include <stdarg.h>\n#include <string.h>\ntypedef struct { uint64_t a,b; } Pair;\ntypedef struct { uint64_t a,b,c; } Big;\ntypedef struct { double a,b,c; } Hfa;\nstatic uint64_t double_bits(double x) { uint64_t b; memcpy(&b,&x,8); return b; }\n",
    );
    let mut checks = String::new();
    for count in [1, 2, 7, 8, 9, 12] {
        add_case(
            &mut module,
            &mut c,
            &mut checks,
            vec![Ty::I64; count],
            1,
            true,
        );
        let mut types = vec![Ty::I64];
        types.extend(vec![Ty::F64; count]);
        add_case(&mut module, &mut c, &mut checks, types, 1, true);
    }
    for fixed in [1, 5, 17] {
        let types = (0..20)
            .map(|index| if index % 2 == 0 { Ty::I64 } else { Ty::F64 })
            .collect();
        add_case(&mut module, &mut c, &mut checks, types, fixed, true);
    }
    let mut narrow_fixed = vec![Ty::I64; 8];
    narrow_fixed.extend([Ty::I8, Ty::I16, Ty::F32, Ty::F64, Ty::I64, Ty::F64]);
    add_case(&mut module, &mut c, &mut checks, narrow_fixed, 12, false);
    add_case(
        &mut module,
        &mut c,
        &mut checks,
        vec![Ty::I64, Ty::I8, Ty::U8, Ty::I16, Ty::U16, Ty::F32],
        1,
        true,
    );
    for prefix in [1, 7, 8, 9] {
        let mut types = vec![Ty::I64; prefix];
        types.extend([Ty::I128, Ty::U64]);
        add_case(&mut module, &mut c, &mut checks, types, 1, false);
    }
    for aggregate in 0..3 {
        for prefix in [1, 7, 8, 9] {
            let mut types = vec![Ty::I64; prefix];
            types.extend([Ty::Struct(StructId::new(aggregate)), Ty::U64]);
            add_case(&mut module, &mut c, &mut checks, types, 1, false);
        }
    }
    for count in [5, 6, 7, 8] {
        let mut types = vec![Ty::I64];
        types.extend(vec![Ty::F64; count]);
        types.extend([Ty::Struct(StructId::new(2)), Ty::F64]);
        add_case(&mut module, &mut c, &mut checks, types, 1, false);
    }
    c.push_str(&format!("int main(void) {{\n{checks}puts(\"Linux variadic ABI corpus matched native C\"); return 0; }}\n"));
    (module, c)
}

#[test]
fn linux_variadic_calls_match_native_c_o0_through_o3() {
    let (module, driver) = corpus();
    let dir = fresh_dir::create("trust_cg_linux_varargs_");
    let c_path = dir.join("driver.c");
    fs::write(&c_path, driver).unwrap();
    for level in [OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::O3] {
        let target = TargetSpec::parse("aarch64-unknown-linux-gnu").unwrap();
        let compiler = Compiler::new_for_target_spec(
            CompilerConfig {
                opt_level: level,
                ..CompilerConfig::default()
            },
            target,
        )
        .with_codegen_license(permit_unlicensed());
        let result = compiler
            .compile(&module)
            .unwrap_or_else(|error| panic!("{level:?}: {error:?}; retained {}", dir.display()));
        assert_eq!(&result.object_code[..4], b"\x7fELF");
        let object = dir.join(format!("{level:?}.o"));
        let binary = dir.join(format!("{level:?}"));
        fs::write(&object, result.object_code).unwrap();
        let link = Command::new("cc")
            .args(["-O2", "-fno-inline"])
            .arg(&c_path)
            .arg(&object)
            .arg("-o")
            .arg(&binary)
            .output()
            .expect("native C compiler is required");
        assert!(
            link.status.success(),
            "{level:?} link: {} (retained {})",
            String::from_utf8_lossy(&link.stderr),
            dir.display()
        );
        let run = Command::new(&binary).output().unwrap();
        assert!(
            run.status.success(),
            "{level:?} execution: status={} stdout={} stderr={} (retained {})",
            run.status,
            String::from_utf8_lossy(&run.stdout),
            String::from_utf8_lossy(&run.stderr),
            dir.display()
        );
    }
    fs::remove_dir_all(dir).unwrap();
}

/// This file's fixtures are hand-built and carry no codegen license
/// (`body_gate: None`), which trust-cg REFUSES by default (roadmap WS7.5,
/// decision gate DG-73). Its compiles state `Permit` explicitly, so none of
/// them passes because it was silently refused.
fn permit_unlicensed() -> trust_cg_lower::CodegenLicensePolicy {
    trust_cg_lower::CodegenLicensePolicy::default()
        .with_unlicensed(trust_cg_lower::UnlicensedBodyPolicy::Permit)
}
