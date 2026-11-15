// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0
//! Source integer comparisons used only by a branch must keep every predicate
//! and the conditional memory effect, including noncanonical narrow high bits.
#![cfg(all(
    target_arch = "aarch64",
    any(target_os = "macos", all(target_os = "linux", target_env = "gnu"))
))]

#[path = "common/native_host.rs"]
mod native_host;
#[path = "common/rosetta.rs"]
mod process;

#[path = "common/fresh_dir.rs"]
mod fresh_dir;

use std::{fs, process::Command};
use trust_cg_codegen::{
    Compiler, CompilerConfig,
    pipeline::{OptLevel, Pipeline, PipelineConfig},
    target::TargetSpec,
};
use trust_cg_ir::AArch64Opcode;
use trust_ir::{
    Block, BlockId, CastOp, Constant, FuncId, FuncTy, Function, ICmpOp, Inst, InstrNode, Linkage,
    Module, Ty, ValueId,
};

const PREDICATES: [(ICmpOp, &str, &str, bool); 10] = [
    (ICmpOp::Eq, "eq", "==", false),
    (ICmpOp::Ne, "ne", "!=", false),
    (ICmpOp::Slt, "slt", "<", true),
    (ICmpOp::Sle, "sle", "<=", true),
    (ICmpOp::Sgt, "sgt", ">", true),
    (ICmpOp::Sge, "sge", ">=", true),
    (ICmpOp::Ult, "ult", "<", false),
    (ICmpOp::Ule, "ule", "<=", false),
    (ICmpOp::Ugt, "ugt", ">", false),
    (ICmpOp::Uge, "uge", ">=", false),
];
const VALUES: &[u64] = &[
    0,
    1,
    2,
    7,
    8,
    127,
    128,
    255,
    256,
    4095,
    4096,
    32767,
    32768,
    65535,
    65536,
    0x7fff_ffff,
    0x8000_0000,
    0xffff_ffff,
    0x1_0000_0000,
    0x7fff_ffff_ffff_ffff,
    0x8000_0000_0000_0000,
    u64::MAX - 1,
    u64::MAX,
];

fn fixture() -> (Module, String) {
    let mut module = Module::new("direct_compare_branches");
    module.target_info = Some(native_host::target_info());
    let signature = module
        .add_func_type(FuncTy {
            params: vec![Ty::U64, Ty::U64, Ty::Ptr],
            returns: vec![],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut driver = String::from("#include <stdint.h>\n#include <stddef.h>\n#include <stdio.h>\n");
    let mut rows = vec![];
    for (width, ty) in [(8, Ty::U8), (16, Ty::U16), (32, Ty::U32), (64, Ty::U64)] {
        for (op, label, operator, signed) in PREDICATES {
            let name = format!("branch_{width}_{label}");
            let mut function = Function::new(
                FuncId::new(module.functions.len() as u32),
                &name,
                signature,
                BlockId::new(0),
            );
            function.linkage = Linkage::External;
            let v = ValueId::new;
            let mut entry = Block::new(BlockId::new(0));
            entry.params = vec![(v(0), Ty::U64), (v(1), Ty::U64), (v(2), Ty::Ptr)];
            let (lhs, rhs) = if width < 64 {
                for (source, result) in [(0, 3), (1, 4)] {
                    entry.body.push(
                        InstrNode::new(Inst::Cast {
                            op: CastOp::Trunc,
                            src_ty: Ty::U64,
                            dst_ty: ty.clone(),
                            operand: v(source),
                        })
                        .with_result(v(result)),
                    );
                }
                (v(3), v(4))
            } else {
                (v(0), v(1))
            };
            entry.body.push(
                InstrNode::new(Inst::ICmp {
                    op,
                    ty: ty.clone(),
                    lhs,
                    rhs,
                })
                .with_result(v(5)),
            );
            entry.body.push(InstrNode::new(Inst::CondBr {
                cond: v(5),
                then_target: BlockId::new(1),
                then_args: vec![],
                else_target: BlockId::new(2),
                else_args: vec![],
            }));
            let mut yes = Block::new(BlockId::new(1));
            yes.body = vec![
                InstrNode::new(Inst::Const {
                    ty: Ty::U64,
                    value: Constant::Int(0xfedcba9876543210),
                })
                .with_result(v(6)),
                InstrNode::new(Inst::Store {
                    ty: Ty::U64,
                    ptr: v(2),
                    value: v(6),
                    volatile: false,
                    align: Some(8),
                }),
                InstrNode::new(Inst::Return { values: vec![] }),
            ];
            let mut no = Block::new(BlockId::new(2));
            no.body
                .push(InstrNode::new(Inst::Return { values: vec![] }));
            function.blocks = vec![entry, yes, no];
            module
                .try_add_function(function)
                .expect("Module::try_add_function: test fixture");
            let c_type = format!("{}int{width}_t", if signed { "" } else { "u" });
            driver.push_str(&format!("extern void {name}(uint64_t,uint64_t,uint64_t*);\nstatic int expect_{name}(uint64_t a,uint64_t b) {{ return ({c_type})a {operator} ({c_type})b; }}\n"));
            rows.push(format!("{{\"{name}\",{name},expect_{name}}}"));
        }
    }
    driver.push_str("struct Case { const char *name; void (*run)(uint64_t,uint64_t,uint64_t*); int (*expected)(uint64_t,uint64_t); };\nstatic const struct Case cases[]={");
    driver.push_str(&rows.join(","));
    driver.push_str("};\nstatic const uint64_t values[]={");
    driver.push_str(
        &VALUES
            .iter()
            .map(|value| format!("UINT64_C(0x{value:016x})"))
            .collect::<Vec<_>>()
            .join(","),
    );
    driver.push_str("};\n");
    driver.push_str(r#"
static int check(const struct Case *c,uint64_t a,uint64_t b) {
    uint64_t arena[3]={UINT64_C(0x1111222233334444),UINT64_C(0x5555666677778888),UINT64_C(0x9999aaaabbbbcccc)};
    c->run(a,b,&arena[1]);
    uint64_t expected=c->expected(a,b)?UINT64_C(0xfedcba9876543210):UINT64_C(0x5555666677778888);
    if(arena[0]!=UINT64_C(0x1111222233334444)||arena[1]!=expected||arena[2]!=UINT64_C(0x9999aaaabbbbcccc)) {
        fprintf(stderr,"%s a=%llx b=%llx got=%llx expected=%llx\n",c->name,(unsigned long long)a,(unsigned long long)b,(unsigned long long)arena[1],(unsigned long long)expected);return 1;
    }
    return 0;
}
int main(void) {
    unsigned long calls=0; uint64_t seed=UINT64_C(0x123456789abcdef);
    for(size_t c=0;c<sizeof(cases)/sizeof(cases[0]);c++) {
        for(size_t a=0;a<sizeof(values)/sizeof(values[0]);a++)for(size_t b=0;b<sizeof(values)/sizeof(values[0]);b++) {
            if(check(&cases[c],values[a],values[b]))return 1;
            calls++;
        }
        for(unsigned sample=0;sample<257;sample++) {
            seed^=seed<<13;seed^=seed>>7;seed^=seed<<17;uint64_t a=seed;
            seed^=seed<<13;seed^=seed>>7;seed^=seed<<17;
            if(check(&cases[c],a,seed))return 1;
            calls++;
        }
    }
    printf("DIRECT_BRANCH_NATIVE calls=%lu\n",calls);return 0;
}
"#);
    (module, driver)
}

#[test]
fn integer_branch_predicates_and_conditional_stores_match_native_c_at_all_levels() {
    let (module, driver) = fixture();
    let errors = trust_ir_build::validate_module(&module);
    assert!(errors.is_empty(), "{errors:?}");
    let directory = fresh_dir::create("trust-cg-direct-branches-");
    let source = directory.join("driver.c");
    fs::write(&source, driver).unwrap();
    fs::write(
        directory.join("source.trust-ir.json"),
        serde_json::to_vec_pretty(&module).unwrap(),
    )
    .unwrap();
    let mut total_calls = 0;
    for level in [OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::O3] {
        let pipeline = Pipeline::new(PipelineConfig {
            opt_level: level,
            verify: false,
            ..PipelineConfig::for_target(native_host::TRIPLE)
        });
        for function in &module.functions {
            let (lir, _) = trust_cg_lower::translate_function_with_license(
                function,
                &module,
                &permit_unlicensed(),
            )
            .unwrap();
            let machine = pipeline.prepare_function(&lir).unwrap();
            assert!(
                !machine
                    .insts
                    .iter()
                    .any(|inst| inst.opcode == AArch64Opcode::CSet),
                "{} {level:?}",
                function.name
            );
        }
        let output = Compiler::new_for_target_spec(
            CompilerConfig {
                opt_level: level,
                ..Default::default()
            },
            TargetSpec::parse(native_host::TRIPLE).unwrap(),
        )
        .with_codegen_license(permit_unlicensed())
        .compile(&module)
        .unwrap();
        let object = directory.join(format!("branches-{level:?}.o"));
        fs::write(&object, &output.object_code).unwrap();
        native_host::assert_native_object(&output.object_code);
        let binary = directory.join(format!("driver-{level:?}"));
        let linked = process::command_output_with_timeout(
            Command::new(native_host::C_COMPILER)
                .args(["-std=c11", "-O2", "-Wall", "-Wextra", "-Werror"])
                .arg(&source)
                .arg(&object)
                .args(native_host::link_hardening_args())
                .arg("-o")
                .arg(&binary),
            process::codegen_link_timeout(),
        )
        .unwrap();
        fs::write(
            directory.join(format!("link-{level:?}.log")),
            &linked.output.stderr,
        )
        .unwrap();
        assert!(
            !linked.timed_out && linked.output.status.success(),
            "{}",
            String::from_utf8_lossy(&linked.output.stderr)
        );
        let run =
            process::run_executable_with_timeout(&binary, process::codegen_run_timeout()).unwrap();
        fs::write(
            directory.join(format!("run-{level:?}.log")),
            &run.output.stdout,
        )
        .unwrap();
        assert!(
            !run.timed_out && run.output.status.success(),
            "{level:?} files={} {}",
            directory.display(),
            String::from_utf8_lossy(&run.output.stderr)
        );
        let expected = (VALUES.len() * VALUES.len() + 257) * module.functions.len();
        assert_eq!(
            String::from_utf8(run.output.stdout).unwrap(),
            format!("DIRECT_BRANCH_NATIVE calls={expected}\n")
        );
        total_calls += expected;
    }
    println!("DIRECT_BRANCH_NATIVE_ARTIFACTS={}", directory.display());
    println!("DIRECT_BRANCH_NATIVE_CALLS={total_calls}");
}

/// This file's fixtures are hand-built and carry no codegen license
/// (`body_gate: None`), which trust-cg REFUSES by default (roadmap WS7.5,
/// decision gate DG-73). Its compiles state `Permit` explicitly, so none of
/// them passes because it was silently refused.
fn permit_unlicensed() -> trust_cg_lower::CodegenLicensePolicy {
    trust_cg_lower::CodegenLicensePolicy::default()
        .with_unlicensed(trust_cg_lower::UnlicensedBodyPolicy::Permit)
}
