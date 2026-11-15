// Copyright 2026 Andrew Yates | Apache-2.0
//! Native independent C/CG argument and return boundaries for 1-4 naturally
//! aligned V64/V128 members. Pointer-based public wrappers isolate each ABI
//! direction; scalar-aggregate controls pin StackAddr type preservation too.
//! Every member is selected in every argument/call-result direction; aggregate
//! returns compare all bytes. Weighted incoming/outgoing FP sentinels exercise
//! the live prefix and following scalar across FPR exhaustion and stack spill.
//! Default compilation policy is unchanged. This is execution evidence only.

#![cfg(all(target_arch = "aarch64", any(target_os = "linux", target_os = "macos")))]

#[path = "common/rosetta.rs"]
mod process;

#[path = "common/native_host.rs"]
mod native_host;

#[path = "common/fresh_dir.rs"]
mod fresh_dir;

#[path = "common/field_typed.rs"]
mod field_typed;

use std::{fs, process::Command};
use trust_cg_codegen::{Compiler, CompilerConfig, pipeline::OptLevel, target::TargetSpec};
use trust_ir::{
    BinOp, Block, BlockId, Constant, Endianness, FieldDef, FuncId, FuncTy, Function, Inst,
    InstrNode, Linkage, Module, StructDef, StructId, StructPassingPolicy, StructRepr, TargetInfo,
    Ty, ValueId,
};

fn function(
    module: &mut Module,
    name: &str,
    params: Vec<Ty>,
    result: Option<Ty>,
    body: Vec<InstrNode>,
) -> FuncId {
    let ty = module
        .add_func_type(FuncTy {
            params: params.clone(),
            returns: result.into_iter().collect(),
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let id = FuncId::new(module.functions.len() as u32);
    let mut function = Function::new(id, name, ty, BlockId::new(0));
    if body.is_empty() {
        function.linkage = Linkage::External;
    } else {
        function.blocks = vec![Block {
            id: BlockId::new(0),
            params: params
                .into_iter()
                .enumerate()
                .map(|(i, t)| (ValueId::new(i as u32), t))
                .collect(),
            body,
        }];
    }
    module
        .try_add_function(function)
        .expect("Module::try_add_function: test fixture");
    id
}

fn corpus(
    bytes: u64,
    count: u32,
    scalar: bool,
    fp_prefix: usize,
    selected: u32,
) -> (Module, String) {
    let mut module = Module::new("linux_native_hva_probe");
    module.target_info = Some(TargetInfo {
        triple: "aarch64-unknown-linux-gnu".into(),
        pointer_size: 8,
        endianness: Endianness::Little,
        abi: Some("aapcs64".into()),
        struct_passing: StructPassingPolicy::NativeC,
    });
    let vector = if scalar {
        Ty::I64
    } else {
        Ty::Vector(Box::new(Ty::I64), (bytes / 8) as u32)
    };
    let aggregate = Ty::Struct(StructId::new(0));
    module.structs.push(StructDef {
        origin: None,
        id: StructId::new(0),
        name: "HVA".into(),
        size: Some(bytes * u64::from(count)),
        align: Some(bytes),
        repr: StructRepr::C,
        fields: (0..count)
            .map(|i| FieldDef {
                name: format!("f{i}"),
                ty: vector.clone(),
                offset: Some(u64::from(i) * bytes),
            })
            .collect(),
    });
    let ret = |value| {
        InstrNode::new(Inst::Return {
            values: vec![ValueId::new(value)],
        })
    };
    let load = || {
        InstrNode::new(Inst::Load {
            ty: aggregate.clone(),
            ptr: ValueId::new(0),
            volatile: false,
            align: Some(bytes),
        })
        .with_result(ValueId::new(1))
    };
    let extract = |arg| {
        InstrNode::new(Inst::ExtractField {
            ty: aggregate.clone(),
            aggregate: ValueId::new(arg),
            field: selected,
        })
        .with_result(ValueId::new(100))
    };
    let store = |out| {
        InstrNode::new(Inst::Store {
            ty: vector.clone(),
            value: ValueId::new(100),
            ptr: ValueId::new(out),
            volatile: false,
            align: Some(bytes),
        })
    };
    let void_ret = || InstrNode::new(Inst::Return { values: vec![] });
    let mut consume_params = vec![Ty::F64; fp_prefix];
    consume_params.extend([aggregate.clone(), Ty::F64, Ty::Ptr, Ty::Ptr]);
    let mut consume_body = vec![extract(fp_prefix as u32), store(fp_prefix as u32 + 2)];
    let mut sum = ValueId::new(fp_prefix as u32 + 1);
    for index in 0..fp_prefix {
        let weight = ValueId::new(400 + index as u32 * 3);
        let product = ValueId::new(401 + index as u32 * 3);
        let next = ValueId::new(402 + index as u32 * 3);
        consume_body.push(
            InstrNode::new(Inst::Const {
                ty: Ty::F64,
                value: Constant::Float((index + 1) as f64),
            })
            .with_result(weight),
        );
        consume_body.push(
            InstrNode::new(Inst::BinOp {
                op: BinOp::FMul,
                ty: Ty::F64,
                lhs: ValueId::new(index as u32),
                rhs: weight,
            })
            .with_result(product),
        );
        consume_body.push(
            InstrNode::new(Inst::BinOp {
                op: BinOp::FAdd,
                ty: Ty::F64,
                lhs: sum,
                rhs: product,
            })
            .with_result(next),
        );
        sum = next;
    }
    consume_body.push(InstrNode::new(Inst::Store {
        ty: Ty::F64,
        value: sum,
        ptr: ValueId::new(fp_prefix as u32 + 3),
        volatile: false,
        align: Some(8),
    }));
    consume_body.push(void_ret());
    function(
        &mut module,
        "cg_consume",
        consume_params.clone(),
        None,
        consume_body,
    );
    let c_consume = function(&mut module, "c_consume", consume_params, None, vec![]);
    let send_load = InstrNode::new(Inst::Load {
        ty: aggregate.clone(),
        ptr: ValueId::new(0),
        volatile: false,
        align: Some(bytes),
    })
    .with_result(ValueId::new(3));
    let mut send_body = vec![send_load];
    let mut send_args = Vec::new();
    for index in 0..fp_prefix {
        let id = ValueId::new(200 + index as u32);
        send_body.push(
            InstrNode::new(Inst::Const {
                ty: Ty::F64,
                value: Constant::Float(index as f64 + 10.25),
            })
            .with_result(id),
        );
        send_args.push(id);
    }
    send_body.push(
        InstrNode::new(Inst::Const {
            ty: Ty::F64,
            value: Constant::Float(77.5),
        })
        .with_result(ValueId::new(300)),
    );
    send_args.extend([
        ValueId::new(3),
        ValueId::new(300),
        ValueId::new(1),
        ValueId::new(2),
    ]);
    send_body.push(InstrNode::new(Inst::Call {
        callee: c_consume,
        args: send_args,
    }));
    send_body.push(void_ret());
    function(
        &mut module,
        "cg_send",
        vec![Ty::Ptr, Ty::Ptr, Ty::Ptr],
        None,
        send_body,
    );
    function(
        &mut module,
        "cg_make",
        vec![Ty::Ptr],
        Some(aggregate.clone()),
        vec![load(), ret(1)],
    );
    let c_make = function(
        &mut module,
        "c_make",
        vec![Ty::Ptr],
        Some(aggregate.clone()),
        vec![],
    );
    function(
        &mut module,
        "cg_receive",
        vec![Ty::Ptr, Ty::Ptr],
        None,
        vec![
            InstrNode::new(Inst::Call {
                callee: c_make,
                args: vec![ValueId::new(0)],
            })
            .with_result(ValueId::new(3)),
            extract(3),
            store(1),
            void_ret(),
        ],
    );
    // Direct short-vector return canary: preserving the aggregate member type
    // must also preserve V64 itself through the MachIR signature/RET guard.
    function(
        &mut module,
        "cg_vector",
        vec![vector.clone()],
        Some(vector.clone()),
        vec![ret(0)],
    );
    let c_vector = function(
        &mut module,
        "c_vector",
        vec![vector.clone()],
        Some(vector.clone()),
        vec![],
    );
    function(
        &mut module,
        "cg_vector_send",
        vec![Ty::Ptr],
        Some(vector.clone()),
        vec![
            InstrNode::new(Inst::Load {
                ty: vector.clone(),
                ptr: ValueId::new(0),
                volatile: false,
                align: Some(bytes),
            })
            .with_result(ValueId::new(1)),
            InstrNode::new(Inst::Call {
                callee: c_vector,
                args: vec![ValueId::new(1)],
            })
            .with_result(ValueId::new(2)),
            ret(2),
        ],
    );
    let fields = (0..count)
        .map(|i| format!("V f{i};"))
        .collect::<Vec<_>>()
        .join(" ");
    let offsets = (0..count)
        .map(|i| {
            format!(
                "_Static_assert(offsetof(HVA,f{i})=={},\"offset{i}\");",
                u64::from(i) * bytes
            )
        })
        .collect::<Vec<_>>()
        .join("\n");
    let fills = (0..count)
        .map(|i| {
            (0..bytes / 8)
                .map(|j| {
                    format!(
                        "a.f{i}{}=INT64_C({});",
                        if scalar {
                            String::new()
                        } else {
                            format!("[{j}]")
                        },
                        0x123456789a000000u64 + u64::from(i) * 257 + j
                    )
                })
                .collect::<Vec<_>>()
                .join("\n")
        })
        .collect::<Vec<_>>()
        .join("\n");
    let attribute = if scalar {
        String::new()
    } else {
        format!("__attribute__((vector_size({bytes})))")
    };
    let fp_decls = (0..fp_prefix)
        .map(|i| format!("double p{i}, "))
        .collect::<String>();
    let fp_values = (0..fp_prefix)
        .map(|i| format!("{}.25, ", i + 10))
        .collect::<String>();
    let fp_checks = (0..fp_prefix)
        .map(|i| format!("p{i} != {}.25 || ", i + 10))
        .collect::<String>();
    let fp_sum = (0..fp_prefix)
        .map(|i| format!(" + p{i} * {}.0", i + 1))
        .collect::<String>();
    let expected_sum = 77.5
        + (0..fp_prefix)
            .map(|i| (i as f64 + 10.25) * (i + 1) as f64)
            .sum::<f64>();
    let c = format!(
        r#"#include <stdint.h>
#include <stdio.h>
#include <stddef.h>
#include <string.h>
#include <stdlib.h>
typedef int64_t V {attribute};
typedef struct {{ {fields} }} HVA;
_Static_assert(sizeof(V)=={bytes} && _Alignof(V)=={bytes}, "vector layout");
_Static_assert(sizeof(HVA)=={size} && _Alignof(HVA)=={bytes}, "HVA layout");
{offsets}
__attribute__((noinline)) void c_consume({fp_decls}HVA a, double tail, V *out, double *fp_out) {{ *out=a.f{last}; *fp_out=tail{fp_sum}; if({fp_checks}tail != 77.5) *out=(V){{0}}; }}
__attribute__((noinline)) HVA c_make(const HVA *p) {{ return *p; }}
__attribute__((noinline)) V c_vector(V value) {{ return value; }}
extern void cg_consume({fp_decls}HVA, double, V *, double *);
extern void cg_send(const HVA *, V *, double *);
extern HVA cg_make(const HVA *);
extern void cg_receive(const HVA *, V *);
extern V cg_vector(V);
extern V cg_vector_send(const V *);
static void dump(const void *p, size_t n) {{ const unsigned char *b=p; for(size_t i=0;i<n;i++) printf("%02x",b[i]); }}
int main(int argc, char **argv) {{
  HVA a; {fills}
  int mode=argc>1?atoi(argv[1]):0;
  V actual={{0}}, expected=a.f{last};
  double fp_actual=0;
  if(mode==0) cg_consume({fp_values}a,77.5,&actual,&fp_actual);
  else if(mode==1) cg_send(&a,&actual,&fp_actual);
  else if(mode==2) {{ HVA whole=cg_make(&a); int bad=memcmp(&whole,&a,sizeof(a))!=0; printf("return expected=");dump(&a,sizeof(a));printf(" actual=");dump(&whole,sizeof(whole));printf("\n");return bad; }}
  else if(mode==3) cg_receive(&a,&actual);
  else if(mode==5) actual=cg_vector(expected);
  else if(mode==6) actual=cg_vector_send(&expected);
  else {{ c_consume({fp_values}c_make(&a),77.5,&actual,&fp_actual); }}
  int bad=memcmp(&actual,&expected,sizeof(V))!=0 || ((mode==0 || mode==1 || mode==4) && fp_actual != {expected_sum});
  printf("mode=%d expected=",mode);dump(&expected,sizeof(V));printf(" actual=");dump(&actual,sizeof(V));printf(" fp=%a expected_fp=%a\n",fp_actual,(double){expected_sum});
  return bad;
}}
"#,
        size = bytes * u64::from(count),
        last = selected
    );
    (module, c)
}

#[test]
fn native_hva_and_loaded_aggregate_boundaries_o0_through_o3() {
    let root = fresh_dir::create("trust_cg_hva_");
    let mut failures = Vec::new();
    let mut executed = 0;
    for scalar in [false, true] {
        for bytes in [8, 16] {
            if scalar && bytes != 8 {
                continue;
            }
            for count in 1..=4 {
                for fp_prefix in [0, 7, 8, 9] {
                    if scalar && fp_prefix != 0 {
                        continue;
                    }
                    for selected in 0..count {
                        let (mut module, c) = corpus(bytes, count, scalar, fp_prefix, selected);
                        // Execute the host's own object and ABI lowering.
                        module.target_info = Some(native_host::target_info());
                        let prefix = format!(
                            "{}_v{}_n{count}_fp{fp_prefix}_member{selected}",
                            if scalar { "scalar_control" } else { "hva" },
                            bytes * 8
                        );
                        let cpath = root.join(format!("{prefix}.c"));
                        fs::write(&cpath, c).unwrap();
                        fs::write(
                            root.join(format!("{prefix}.ir-debug")),
                            format!("{module:#?}"),
                        )
                        .unwrap();
                        for opt in [OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::O3] {
                            let stem = format!("{prefix}_{opt:?}");
                            let compiler = Compiler::new_for_target_spec(
                                CompilerConfig {
                                    opt_level: opt,
                                    ..Default::default()
                                },
                                TargetSpec::parse(native_host::TRIPLE).unwrap(),
                            )
                            .with_codegen_license(permit_unlicensed());
                            let output = match compiler.compile(&field_typed::normalized(&module)) {
                                Ok(output) => output,
                                Err(error) => {
                                    failures.push(format!("REFUSED {stem}: {error:?}"));
                                    continue;
                                }
                            };
                            native_host::assert_native_object(&output.object_code);
                            let object = root.join(format!("{stem}.o"));
                            fs::write(&object, output.object_code).unwrap();
                            let binary = root.join(&stem);
                            let linked = Command::new("cc")
                                .args(["-O2", "-fno-inline"])
                                .arg(&cpath)
                                .arg(&object)
                                .arg("-o")
                                .arg(&binary)
                                .output()
                                .expect("native C compiler required");
                            if !linked.status.success() {
                                failures.push(format!(
                                    "LINK_FAIL {stem}: {}",
                                    String::from_utf8_lossy(&linked.stderr)
                                ));
                                continue;
                            }
                            let modes: &[u8] = if fp_prefix == 0 && count == 1 && !scalar {
                                &[0, 1, 2, 3, 4, 5, 6]
                            } else if fp_prefix == 0 {
                                &[0, 1, 2, 3, 4]
                            } else {
                                &[0, 1, 4]
                            };
                            for mode in modes {
                                let run = process::command_output_with_timeout(
                                    Command::new(&binary).arg(mode.to_string()),
                                    process::exec_timeout(std::time::Duration::from_secs(5)),
                                )
                                .unwrap();
                                executed += 1;
                                if run.timed_out || !run.output.status.success() {
                                    failures.push(format!(
                                        "{stem} mode={mode} status={} timed_out={} stdout={} stderr={}",
                                        run.output.status,
                                        run.timed_out,
                                        String::from_utf8_lossy(&run.output.stdout).trim(),
                                        String::from_utf8_lossy(&run.output.stderr).trim()
                                    ));
                                }
                            }
                        }
                    }
                }
            }
        }
    }
    assert!(
        failures.is_empty(),
        "{}; retained {}",
        failures.join("\n"),
        root.display()
    );
    println!(
        "validated {executed} native C/CG boundary executions ({})",
        native_host::HOST
    );
    fs::remove_dir_all(root).unwrap();
}

#[test]
fn darwin_hva_and_short_vector_shapes_still_emit_with_exact_target() {
    for bytes in [8, 16] {
        for count in 1..=4 {
            for fp_prefix in [0, 7, 9] {
                let (mut module, _) = corpus(bytes, count, false, fp_prefix, count - 1);
                let info = module.target_info.as_mut().unwrap();
                info.triple = "aarch64-apple-darwin".into();
                info.abi = None;
                for opt in [OptLevel::O0, OptLevel::O2] {
                    let output = Compiler::new_for_target_spec(
                        CompilerConfig {
                            opt_level: opt,
                            ..Default::default()
                        },
                        TargetSpec::parse("aarch64-apple-darwin").unwrap(),
                    )
                    .with_codegen_license(permit_unlicensed())
                    .compile(&field_typed::normalized(&module))
                    .unwrap_or_else(|error| {
                        panic!(
                            "Darwin V{}x{count} prefix={fp_prefix} {opt:?}: {error:?}",
                            bytes * 8
                        )
                    });
                    assert_eq!(
                        &output.object_code[..4],
                        &[0xcf, 0xfa, 0xed, 0xfe],
                        "must emit a real Mach-O object"
                    );
                }
            }
        }
    }
}

/// This file's fixtures are hand-built and carry no codegen license
/// (`body_gate: None`), which trust-cg REFUSES by default (roadmap WS7.5,
/// decision gate DG-73). Its compiles state `Permit` explicitly, so none of
/// them passes because it was silently refused.
fn permit_unlicensed() -> trust_cg_lower::CodegenLicensePolicy {
    trust_cg_lower::CodegenLicensePolicy::default()
        .with_unlicensed(trust_cg_lower::UnlicensedBodyPolicy::Permit)
}
