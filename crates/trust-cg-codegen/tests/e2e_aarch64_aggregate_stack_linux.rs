// Copyright 2026 Andrew Yates | Apache-2.0
//! Pinned native two-direction oracle for naturally sixteen-aligned aggregates
//! crossing the AAPCS64 register/stack boundary. Native C calls TrustCG callees;
//! separate TrustCG callers call native C, so matching mistakes cannot cancel.
//! Default compiler verification policy is unchanged. This is execution evidence.

#![cfg(all(target_arch = "aarch64", target_os = "linux"))]

#[path = "common/fresh_dir.rs"]
mod fresh_dir;

use std::{fs, process::Command};
use trust_cg_codegen::{Compiler, CompilerConfig, pipeline::OptLevel, target::TargetSpec};
use trust_ir::{
    BinOp, Block, BlockId, CastOp, Constant, Endianness, FieldDef, FuncId, FuncTy, Function, Inst,
    InstrNode, Linkage, Module, StructDef, StructId, StructPassingPolicy, StructRepr, TargetInfo,
    Ty, ValueId,
};

fn c_type(ty: &Ty) -> &'static str {
    match ty {
        Ty::U64 => "uint64_t",
        Ty::Struct(id) if id.index() == 0 => "Wide",
        Ty::Struct(_) => "Large",
        _ => panic!("unexpected parameter {ty:?}"),
    }
}

fn function(module: &mut Module, name: &str, params: Vec<Ty>, body: Vec<InstrNode>) {
    let ty = module
        .add_func_type(FuncTy {
            params: params.clone(),
            returns: vec![Ty::I128],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut f = Function::new(
        FuncId::new(module.functions.len() as u32),
        name,
        ty,
        BlockId::new(0),
    );
    f.blocks = vec![Block {
        id: BlockId::new(0),
        params: params
            .into_iter()
            .enumerate()
            .map(|(i, ty)| (ValueId::new(i as u32), ty))
            .collect(),
        body,
    }];
    module
        .try_add_function(f)
        .expect("Module::try_add_function: test fixture");
}

fn corpus() -> (Module, String) {
    let mut module = Module::new("linux_aggregate_stack_abi");
    module.target_info = Some(TargetInfo {
        triple: "aarch64-unknown-linux-gnu".into(),
        pointer_size: 8,
        endianness: Endianness::Little,
        abi: Some("aapcs64".into()),
        struct_passing: StructPassingPolicy::NativeC,
    });
    for (id, name, fields, size) in [
        (0, "Wide", vec![Ty::I128], 16),
        (1, "Large", vec![Ty::I128, Ty::U64], 32),
    ] {
        module.structs.push(StructDef {
            origin: None,
            id: StructId::new(id),
            name: name.into(),
            size: Some(size),
            align: Some(16),
            repr: StructRepr::C,
            fields: fields
                .into_iter()
                .enumerate()
                .map(|(i, ty)| FieldDef {
                    name: format!("field{i}"),
                    ty,
                    offset: Some(i as u64 * 16),
                })
                .collect(),
        });
    }
    let mut c = String::from(
        "#include <stdint.h>\n#include <stdio.h>\n#include <stdarg.h>\n\
         typedef struct { __int128 value; } Wide;\n\
         typedef struct { __int128 value; uint64_t extra; } Large;\n\
         _Static_assert(sizeof(Wide)==16 && _Alignof(Wide)==16, \"Wide ABI\");\n\
         _Static_assert(sizeof(Large)==32 && _Alignof(Large)==16, \"Large ABI\");\n\
         static int check(const char *name, __int128 actual, __int128 expected) {\n\
           if(actual == expected) return 0;\n\
           printf(\"%s: expected=%llx:%llx actual=%llx:%llx\\n\", name,\n\
             (unsigned long long)((__uint128_t)expected>>64), (unsigned long long)expected,\n\
             (unsigned long long)((__uint128_t)actual>>64), (unsigned long long)actual);\n\
           return 1;\n}\n",
    );
    let mut checks = String::new();
    // Odd/even GPR starts, pair exhaustion, and NSAA residues zero/eight.
    for kind in 0..2 {
        for prefix in [0, 1, 6, 7, 8, 9, 10, 11, 12] {
            let tag = format!("{kind}_{prefix}");
            let aggregate = Ty::Struct(StructId::new(kind));
            let mut params = vec![Ty::U64; prefix];
            params.extend([aggregate.clone(), Ty::U64]);
            let declaration = params
                .iter()
                .enumerate()
                .map(|(i, ty)| format!("{} a{i}", c_type(ty)))
                .collect::<Vec<_>>()
                .join(", ");
            let payload =
                "((__int128)UINT64_C(0x123456789abcdef) << 64) + UINT64_C(0x3579246813579246)";
            let value = if kind == 0 {
                format!("(Wide){{{payload}}}")
            } else {
                format!("(Large){{{payload}, UINT64_C(0x31415926)}}")
            };
            let mut values = (0..prefix)
                .map(|i| format!("UINT64_C({})", 100 + i))
                .collect::<Vec<_>>();
            values.extend([value.clone(), "UINT64_C(0x27182818)".into()]);
            let all_values = values.join(", ");
            let mut expression = format!("(__uint128_t)a{prefix}.value");
            if kind == 1 {
                expression.push_str(&format!(" + a{prefix}.extra"));
            }
            for i in (0..prefix).chain(std::iter::once(prefix + 1)) {
                expression.push_str(&format!(" + a{i}"));
            }
            // TrustCG callee consumes the aggregate and every surrounding scalar.
            // `ExtractField` declares the RESULT (field) type, which trust-ir's
            // validator checks; since WS7.3 every ingestion entry refuses the
            // historical aggregate-type spelling (`BinOpTypeMismatch` at the
            // first `add` of the extracted value).
            let mut body = vec![
                InstrNode::new(Inst::ExtractField {
                    ty: Ty::I128,
                    aggregate: ValueId::new(prefix as u32),
                    field: 0,
                })
                .with_result(ValueId::new(100)),
            ];
            let mut acc = ValueId::new(100);
            let mut next = 101;
            let mut scalars: Vec<_> = (0..prefix)
                .chain(std::iter::once(prefix + 1))
                .map(|i| ValueId::new(i as u32))
                .collect();
            if kind == 1 {
                body.push(
                    InstrNode::new(Inst::ExtractField {
                        ty: Ty::U64,
                        aggregate: ValueId::new(prefix as u32),
                        field: 1,
                    })
                    .with_result(ValueId::new(next)),
                );
                scalars.push(ValueId::new(next));
                next += 1;
            }
            for scalar in scalars {
                body.push(
                    InstrNode::new(Inst::Cast {
                        op: CastOp::ZExt,
                        src_ty: Ty::U64,
                        dst_ty: Ty::I128,
                        operand: scalar,
                    })
                    .with_result(ValueId::new(next)),
                );
                body.push(
                    InstrNode::new(Inst::BinOp {
                        op: BinOp::Add,
                        ty: Ty::I128,
                        lhs: acc,
                        rhs: ValueId::new(next),
                    })
                    .with_result(ValueId::new(next + 1)),
                );
                acc = ValueId::new(next + 1);
                next += 2;
            }
            body.push(InstrNode::new(Inst::Return { values: vec![acc] }));
            function(&mut module, &format!("consume_{tag}"), params.clone(), body);
            c.push_str(&format!("extern __int128 consume_{tag}({declaration});\n"));
            // Each native helper independently lowers either a named call, or
            // va_arg reads with one/nine/etc. named arguments. Caller inputs
            // arrive in registers: the outgoing stack path is tested in isolation.
            let fixed_counts = if prefix > 1 {
                vec![params.len(), 1, prefix]
            } else {
                vec![params.len(), 1]
            };
            for fixed in fixed_counts {
                let suffix = format!("{tag}_{fixed}");
                let variadic = fixed < params.len();
                let signature = params[..fixed]
                    .iter()
                    .enumerate()
                    .map(|(i, ty)| format!("{} a{i}", c_type(ty)))
                    .collect::<Vec<_>>()
                    .join(", ");
                c.push_str(&format!(
                    "__attribute__((noinline)) __int128 oracle_{suffix}({signature}{}) {{\n",
                    if variadic { ", ..." } else { "" }
                ));
                if variadic {
                    c.push_str(&format!("va_list ap; va_start(ap, a{});\n", fixed - 1));
                    for (i, ty) in params.iter().enumerate().skip(fixed) {
                        c.push_str(&format!(
                            "{} a{i} = va_arg(ap, {});\n",
                            c_type(ty),
                            c_type(ty)
                        ));
                    }
                    c.push_str("va_end(ap);\n");
                }
                c.push_str(&format!("return (__int128)({expression});\n}}\n"));
                let oracle_ty = module
                    .add_func_type(FuncTy {
                        params: params[..fixed].to_vec(),
                        returns: vec![Ty::I128],
                        abi: None,
                        is_vararg: variadic,
                    })
                    .expect("Module::add_func_type: test fixture");
                let oracle = FuncId::new(module.functions.len() as u32);
                let mut external = Function::new(
                    oracle,
                    format!("oracle_{suffix}"),
                    oracle_ty,
                    BlockId::new(0),
                );
                external.linkage = Linkage::External;
                external.blocks.clear();
                module
                    .try_add_function(external)
                    .expect("Module::try_add_function: test fixture");
                let mut body = Vec::new();
                let mut args = Vec::new();
                for i in 0..prefix {
                    let value = ValueId::new(10 + i as u32);
                    body.push(
                        InstrNode::new(Inst::Const {
                            ty: Ty::U64,
                            value: Constant::Int(100 + i as i128),
                        })
                        .with_result(value),
                    );
                    args.push(value);
                }
                args.extend([ValueId::new(0), ValueId::new(1)]);
                body.push(
                    InstrNode::new(Inst::Call {
                        callee: oracle,
                        args,
                    })
                    .with_result(ValueId::new(100)),
                );
                body.push(InstrNode::new(Inst::Return {
                    values: vec![ValueId::new(100)],
                }));
                function(
                    &mut module,
                    &format!("send_{suffix}"),
                    vec![aggregate.clone(), Ty::U64],
                    body,
                );
                c.push_str(&format!(
                    "extern __int128 send_{suffix}({}, uint64_t);\n",
                    c_type(&aggregate)
                ));
                checks.push_str(&format!("failures += check(\"send_{suffix}\", send_{suffix}({value}, UINT64_C(0x27182818)), oracle_{suffix}({all_values}));\n"));
                if !variadic {
                    checks.push_str(&format!("failures += check(\"consume_{tag}\", consume_{tag}({all_values}), oracle_{suffix}({all_values}));\n"));
                }
            }
        }
    }
    c.push_str(&format!(
        "int main(void) {{ int failures = 0;\n{checks}return failures != 0;\n}}\n"
    ));
    (module, c)
}

#[test]
fn linux_aggregate_stack_alignment_matches_native_c_both_directions_o0_through_o3() {
    let (module, driver) = corpus();
    let dir = fresh_dir::create("trust_cg_linux_aggregate_stack_");
    let c_path = dir.join("driver.c");
    fs::write(&c_path, driver).unwrap();
    for level in [OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::O3] {
        let compiler = Compiler::new_for_target_spec(
            CompilerConfig {
                opt_level: level,
                ..CompilerConfig::default()
            },
            TargetSpec::parse("aarch64-unknown-linux-gnu").unwrap(),
        )
        .with_codegen_license(permit_unlicensed());
        let output = compiler
            .compile(&module)
            .unwrap_or_else(|error| panic!("{level:?}: {error:?}; retained {}", dir.display()));
        assert_eq!(&output.object_code[..4], b"\x7fELF");
        let object = dir.join(format!("{level:?}.o"));
        let binary = dir.join(format!("{level:?}"));
        fs::write(&object, output.object_code).unwrap();
        let link = Command::new("cc")
            .args(["-O2", "-fno-inline"])
            .arg(&c_path)
            .arg(&object)
            .arg("-o")
            .arg(&binary)
            .output()
            .expect("native C compiler required");
        assert!(
            link.status.success(),
            "{level:?} link: {}; retained {}",
            String::from_utf8_lossy(&link.stderr),
            dir.display()
        );
        let run = Command::new(binary).output().unwrap();
        assert!(
            run.status.success(),
            "{level:?}: status={} stdout={} stderr={}; retained {}",
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
