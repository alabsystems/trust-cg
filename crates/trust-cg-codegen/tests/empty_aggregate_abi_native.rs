// Copyright 2026 Andrew Yates | Apache-2.0
//! Ordinary C <-> CG empty-aggregate arguments, including register overflow.
//! Native execution evidence only; hand-authored IR carries no source licence.
#![cfg(all(
    target_arch = "aarch64",
    any(target_os = "macos", all(target_os = "linux", target_env = "gnu"))
))]

#[path = "common/fresh_dir.rs"]
mod fresh_dir;
#[path = "common/native_host.rs"]
mod native_host;
#[path = "common/rosetta.rs"]
mod process;

use std::{fs, process::Command};
use trust_cg_codegen::{Compiler, CompilerConfig, pipeline::OptLevel, target::TargetSpec};
use trust_ir::{
    BinOp, Block, BlockId, CallingConv, Constant, FuncId, FuncTy, Function, Inst, InstrNode,
    Linkage, Module, StructDef, StructId, StructRepr, Ty, ValueId,
};

fn aggregate_parameters(empty: &Ty) -> Vec<Ty> {
    let mut parameters = Vec::new();
    for _ in 0..9 {
        parameters.extend([empty.clone(), Ty::U64]);
    }
    parameters.push(empty.clone());
    parameters
}

fn fixture() -> Module {
    let mut module = Module::new("empty_aggregate_abi");
    module.target_info = Some(native_host::target_info());
    module.structs.push(StructDef {
        id: StructId::new(0),
        name: "Empty".into(),
        fields: vec![],
        size: Some(0),
        align: Some(1),
        repr: StructRepr::C,
        origin: None,
    });
    let empty = Ty::Struct(StructId::new(0));
    let parameters = aggregate_parameters(&empty);
    let aggregate_signature = module
        .add_func_type(FuncTy {
            params: parameters.clone(),
            returns: vec![Ty::U64],
            is_vararg: false,
            abi: None,
        })
        .unwrap();
    let mut take = Function::new(
        FuncId::new(0),
        "cg_take",
        aggregate_signature,
        BlockId::new(0),
    );
    take.calling_conv = CallingConv::C;
    let mut body = vec![];
    let mut next = parameters.len() as u32;
    let mut sum = None;
    for scalar in 0..9 {
        let constant = ValueId::new(next);
        next += 1;
        body.push(
            InstrNode::new(Inst::Const {
                ty: Ty::U64,
                value: Constant::Int(scalar + 1),
            })
            .with_result(constant),
        );
        let term = ValueId::new(next);
        next += 1;
        body.push(
            InstrNode::new(Inst::BinOp {
                op: BinOp::Mul,
                ty: Ty::U64,
                lhs: ValueId::new(scalar as u32 * 2 + 1),
                rhs: constant,
            })
            .with_result(term),
        );
        sum = Some(match sum {
            None => term,
            Some(previous) => {
                let added = ValueId::new(next);
                next += 1;
                body.push(
                    InstrNode::new(Inst::BinOp {
                        op: BinOp::Add,
                        ty: Ty::U64,
                        lhs: previous,
                        rhs: term,
                    })
                    .with_result(added),
                );
                added
            }
        });
    }
    body.push(InstrNode::new(Inst::Return {
        values: vec![sum.unwrap()],
    }));
    take.blocks = vec![Block {
        id: BlockId::new(0),
        params: parameters
            .into_iter()
            .enumerate()
            .map(|(i, t)| (ValueId::new(i as u32), t))
            .collect(),
        body,
    }];
    module.try_add_function(take).unwrap();
    let mut oracle = Function::new(
        FuncId::new(1),
        "oracle",
        aggregate_signature,
        BlockId::new(0),
    );
    oracle.calling_conv = CallingConv::C;
    oracle.linkage = Linkage::External;
    module.try_add_function(oracle).unwrap();
    let caller_signature = module
        .add_func_type(FuncTy {
            params: vec![Ty::U64; 9],
            returns: vec![Ty::U64],
            is_vararg: false,
            abi: None,
        })
        .unwrap();
    let mut pass = Function::new(FuncId::new(2), "cg_pass", caller_signature, BlockId::new(0));
    pass.calling_conv = CallingConv::C;
    let environment = ValueId::new(9);
    let mut arguments = vec![];
    for scalar in 0..9 {
        arguments.extend([environment, ValueId::new(scalar)]);
    }
    arguments.push(environment);
    pass.blocks = vec![Block {
        id: BlockId::new(0),
        params: (0..9).map(|i| (ValueId::new(i), Ty::U64)).collect(),
        body: vec![
            InstrNode::new(Inst::MakeAggregate {
                ty: empty,
                variant: None,
                fields: vec![],
            })
            .with_result(environment),
            InstrNode::new(Inst::Call {
                callee: FuncId::new(1),
                args: arguments,
            })
            .with_result(ValueId::new(10)),
            InstrNode::new(Inst::Return {
                values: vec![ValueId::new(10)],
            }),
        ],
    }];
    module.try_add_function(pass).unwrap();
    module
}

const DRIVER: &str = r#"
#include <stdint.h>
typedef struct {} E;
#define PARAMETERS E z0,uint64_t a0,E z1,uint64_t a1,E z2,uint64_t a2,E z3,uint64_t a3,E z4,uint64_t a4,E z5,uint64_t a5,E z6,uint64_t a6,E z7,uint64_t a7,E z8,uint64_t a8,E z9
#define ARGUMENTS (E){},a[0],(E){},a[1],(E){},a[2],(E){},a[3],(E){},a[4],(E){},a[5],(E){},a[6],(E){},a[7],(E){},a[8],(E){}
uint64_t oracle(PARAMETERS) {
    (void)z0;(void)z1;(void)z2;(void)z3;(void)z4;(void)z5;(void)z6;(void)z7;(void)z8;(void)z9;
    return a0+2*a1+3*a2+4*a3+5*a4+6*a5+7*a6+8*a7+9*a8;
}
extern uint64_t cg_take(PARAMETERS);
extern uint64_t cg_pass(uint64_t,uint64_t,uint64_t,uint64_t,uint64_t,uint64_t,uint64_t,uint64_t,uint64_t);
int main(int argc,char **argv) {
    (void)argv;
    const uint64_t seeds[]={0,1,7,255,UINT64_C(0x8000000000000000),UINT64_MAX};
    for(unsigned k=0;k<sizeof(seeds)/sizeof(seeds[0]);++k) {
        uint64_t a[9],expected=0;
        for(unsigned i=0;i<9;++i) { a[i]=seeds[k]^((i+1)*UINT64_C(0x0101010101010101)); expected+=(i+1)*a[i]; }
        if(argc>1)expected^=1;
        if(cg_take(ARGUMENTS)!=expected)return 97;
        if(cg_pass(a[0],a[1],a[2],a[3],a[4],a[5],a[6],a[7],a[8])!=expected)return 98;
    }
    return 0;
}
"#;

#[test]
fn empty_aggregate_arguments_cross_the_real_c_boundary_in_both_directions() {
    let module = fixture();
    let errors = trust_ir_build::validate_module(&module);
    assert!(errors.is_empty(), "{errors:?}");
    let directory = fresh_dir::create("trust-cg-empty-argument-");
    let driver = directory.join("driver.c");
    fs::write(&driver, DRIVER).unwrap();
    for level in [OptLevel::O0, OptLevel::O2] {
        let object = Compiler::new_for_target_spec(
            CompilerConfig {
                opt_level: level,
                ..Default::default()
            },
            TargetSpec::parse(native_host::TRIPLE).unwrap(),
        )
        .with_codegen_license(
            trust_cg_lower::CodegenLicensePolicy::default()
                .with_unlicensed(trust_cg_lower::UnlicensedBodyPolicy::Permit),
        )
        .compile(&module)
        .unwrap_or_else(|e| panic!("{level:?}: {e:?}"))
        .object_code;
        let object_path = directory.join(format!("{level:?}.o"));
        let binary = directory.join(format!("{level:?}.exe"));
        fs::write(&object_path, object).unwrap();
        let linked = Command::new(native_host::C_COMPILER)
            .args(["-std=gnu11", "-O2", "-Wall", "-Wextra", "-Werror"])
            .arg(&driver)
            .arg(&object_path)
            .arg("-o")
            .arg(&binary)
            .output()
            .unwrap();
        assert!(
            linked.status.success(),
            "{level:?}: {}",
            String::from_utf8_lossy(&linked.stderr)
        );
        for (poison, expected) in [(false, 0), (true, 97)] {
            let mut command = Command::new(&binary);
            if poison {
                command.arg("--poison");
            }
            let result =
                process::command_output_with_timeout(&mut command, process::codegen_run_timeout())
                    .unwrap();
            assert!(!result.timed_out, "{level:?}: native oracle timed out");
            assert_eq!(
                result.output.status.code(),
                Some(expected),
                "{level:?}: {}",
                String::from_utf8_lossy(&result.output.stderr)
            );
        }
    }
}
