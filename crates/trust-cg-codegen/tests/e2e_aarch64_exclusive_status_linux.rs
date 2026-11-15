// Copyright 2026 Andrew Yates | Apache-2.0
//! STLXR's W-status operand is an output, including when it spills.
//!
//! This uses the public prebuilt-MachIR pipeline, not frontend non-LSE atomic
//! admission. `verify: true` retains the existing diagnostic policy (uncovered
//! instructions are tolerated); the separate inventory control requires these
//! exclusive instructions to remain ineligible for proof-required promotion.
//! CLREX forces failure: every native call must return 1 without changing memory.
//! This is not retry-loop, success-path, ordering, or linearizability evidence.

#![cfg(feature = "verify")]

#[path = "common/fresh_dir.rs"]
mod fresh_dir;

use trust_cg_ir::{
    AArch64Opcode as O, MachFunction, MachInst, MachOperand as A, Signature, Type,
    regs::{RegClass, VReg, W0, W1, W2, X0, X1, X2, X3},
};

fn append(function: &mut MachFunction, opcode: O, operands: Vec<A>) {
    let id = function.push_inst(MachInst::new(opcode, operands));
    function.append_inst(function.entry, id);
}

// Only called under the native-host cfg below; dead on any other host, and
// the workspace denies warnings.
#[allow(dead_code)]
fn pressure_function(width: u32, initialized: bool, pressure: usize) -> MachFunction {
    let mut function = MachFunction::new(
        format!("cg_status_{width}_{}_p{pressure}", u8::from(initialized)),
        Signature::new(vec![Type::I64; 4], vec![Type::I32]),
    );
    let status = VReg::new(function.alloc_vreg(), RegClass::Gpr32);
    if initialized {
        append(
            &mut function,
            O::VolatileLdrRI,
            vec![A::VReg(status), A::PReg(X2), A::Imm(0)],
        );
    }
    let mut values = Vec::new();
    for index in 0..pressure {
        let value = VReg::new(function.alloc_vreg(), RegClass::Gpr64);
        append(
            &mut function,
            O::VolatileLdrRI,
            vec![A::VReg(value), A::PReg(X2), A::Imm(8 + 8 * index as i64)],
        );
        values.push(value);
    }
    append(
        &mut function,
        O::Stlxr,
        vec![
            A::VReg(status),
            A::PReg(if width == 32 { W1 } else { X1 }),
            A::PReg(X0),
        ],
    );
    for (index, value) in values.into_iter().enumerate() {
        append(
            &mut function,
            O::VolatileStrRI,
            vec![A::VReg(value), A::PReg(X3), A::Imm(8 * index as i64)],
        );
    }
    append(&mut function, O::Copy, vec![A::PReg(W0), A::VReg(status)]);
    let ret = function.push_inst(MachInst::new(O::Ret, vec![]).with_implicit_uses(&[W0]));
    function.append_inst(function.entry, ret);
    function
}

#[test]
#[cfg(feature = "verify")]
fn exclusive_status_operand_repair_does_not_authorize_proof_promotion() {
    std::thread::Builder::new()
        .stack_size(16 * 1024 * 1024)
        .spawn(|| {
            for opcode in [O::Ldaxr, O::Stlxr] {
                let mut function = MachFunction::new(
                    format!("unproven_{opcode:?}"),
                    Signature::new(vec![Type::I64, Type::I64], vec![]),
                );
                let operands = if opcode == O::Ldaxr {
                    vec![A::PReg(W2), A::PReg(X0)]
                } else {
                    vec![A::PReg(W2), A::PReg(X1), A::PReg(X0)]
                };
                append(&mut function, opcode, operands);
                append(&mut function, O::Ret, vec![]);
                let report = trust_cg_verify::verify_function(&function);
                let inventory = report.emitted_opcode_inventory();
                assert!(!inventory.is_promotable(), "{opcode:?}: {inventory:?}");
                assert!(
                    inventory.uncovered_non_pseudo_opcodes().iter().any(
                        |row| row.opcode == trust_cg_verify::InstructionOpcode::AArch64(opcode)
                    ),
                    "the exclusive opcode itself must block: {inventory:?}"
                );
                assert!(!report.all_genuinely_verified());
            }
        })
        .unwrap()
        .join()
        .unwrap();
}

#[cfg(all(
    target_arch = "aarch64",
    any(target_os = "macos", all(target_os = "linux", target_env = "gnu")),
    feature = "verify"
))]
#[path = "common/rosetta.rs"]
mod process;

#[cfg(all(
    target_arch = "aarch64",
    any(target_os = "macos", all(target_os = "linux", target_env = "gnu")),
    feature = "verify"
))]
#[path = "common/native_host.rs"]
mod native_host;

#[cfg(all(
    target_arch = "aarch64",
    any(target_os = "macos", all(target_os = "linux", target_env = "gnu")),
    feature = "verify"
))]
mod native {
    use super::*;
    use std::{fmt::Write, fs, process::Command};
    use trust_cg_codegen::pipeline::{OptLevel, Pipeline, PipelineConfig};

    fn status_is_spilled_and_reloaded(function: &MachFunction) -> bool {
        let instructions: Vec<_> = function
            .block_order
            .iter()
            .flat_map(|id| function.block(*id).insts.iter())
            .map(|id| function.inst(*id))
            .collect();
        let exclusive: Vec<_> = instructions
            .iter()
            .enumerate()
            .filter(|(_, inst)| inst.opcode == O::Stlxr)
            .collect();
        assert_eq!(exclusive.len(), 1, "native case must execute one STLXR");
        let (index, instruction) = exclusive[0];
        let Some(store) = instructions.get(index + 1) else {
            return false;
        };
        // Inspect the actual final, frame-lowered stream, not pressure alone.
        // The status W-register must be written to a stack spill location and
        // later reloaded from that same location before returning its value.
        if store.opcode != O::StrRI
            || store.operands.len() != 2
            || !matches!(store.operands[1], A::MemOp { base, .. } if base == trust_cg_ir::regs::FP || base == trust_cg_ir::regs::SP)
            || store.operands[0] != instruction.operands[0]
        {
            return false;
        }
        instructions[index + 2..].iter().any(|load| {
            load.opcode == O::LdrRI
                && load.operands.len() == 2
                && load.operands[1..] == store.operands[1..]
        })
    }

    const ASSEMBLY: &str = r#"
.text
.p2align 2
.global invoke_clear
.type invoke_clear,%function
invoke_clear:
    mov x9,x0
    mov x0,x1
    mov x1,x2
    mov x2,x3
    mov x3,x4
    clrex
    br x9
.size invoke_clear,.-invoke_clear
.global asm_status32
.type asm_status32,%function
asm_status32:
    stlxr w2,w1,[x0]
    mov w0,w2
    ret
.size asm_status32,.-asm_status32
.global asm_status64
.type asm_status64,%function
asm_status64:
    stlxr w2,x1,[x0]
    mov w0,w2
    ret
.size asm_status64,.-asm_status64
.section .note.GNU-stack,"",@progbits
"#;

    fn driver(functions: &[MachFunction]) -> String {
        let mut c = String::from(
            r#"
#include <stdint.h>
#include <stdio.h>
typedef uint32_t (*function_t)(uint64_t*,uint64_t,const uint64_t*,uint64_t*);
extern uint32_t invoke_clear(function_t,uint64_t*,uint64_t,const uint64_t*,uint64_t*);
extern uint32_t asm_status32(uint64_t*,uint64_t,const uint64_t*,uint64_t*);
extern uint32_t asm_status64(uint64_t*,uint64_t,const uint64_t*,uint64_t*);
static unsigned checks, failures, calls, controls;
static void check(uint64_t got,uint64_t expected) {
  checks++; if(got!=expected) { if(failures<8) fprintf(stderr,"check %u: got %llx expected %llx\n",checks,(unsigned long long)got,(unsigned long long)expected); failures++; }
}
static void one(function_t function,unsigned width,unsigned pressure) {
  const uint64_t guard=0xa5a5a5a5a5a5a5a5ULL;
  for(unsigned pattern=0;pattern<4;pattern++) {
    uint64_t input[33],output[34],memory[3],oracle[3];
    input[0]=(uint64_t[]){0x5a,0,0xffffffff,0x80000000}[pattern];
    for(unsigned i=1;i<33;i++) input[i]=(0xdeadbeef76543210ULL^(0x9e3779b97f4a7c15ULL*i))+(pattern*0x100000001ULL);
    for(unsigned i=0;i<34;i++) output[i]=guard;
    for(unsigned i=0;i<3;i++) memory[i]=oracle[i]=guard^(0x123456789abcdefULL*(i+pattern+1));
    uint64_t desired=0xfedcba9876543210ULL^pattern;
    uint32_t expected=invoke_clear(width==32?asm_status32:asm_status64,&oracle[1],desired,input,output+1);
    controls++;check(expected,1);
    uint32_t actual=invoke_clear(function,&memory[1],desired,input,output+1);
    calls++;check(actual,1);
    for(unsigned i=0;i<3;i++) {check(oracle[i],guard^(0x123456789abcdefULL*(i+pattern+1)));check(memory[i],oracle[i]);}
    for(unsigned i=0;i<34;i++) check(output[i],i>=1&&i<=pressure?input[i]:guard);
  }
}
"#,
        );
        for function in functions {
            writeln!(
                c,
                "extern uint32_t {}(uint64_t*,uint64_t,const uint64_t*,uint64_t*);",
                function.name
            )
            .unwrap();
        }
        c.push_str("int main(void) {\n");
        for function in functions {
            let width = if function.name.contains("_32_") {
                32
            } else {
                64
            };
            let pressure = if function.name.ends_with("_p32") {
                32
            } else {
                0
            };
            writeln!(c, "one({}, {width}, {pressure});", function.name).unwrap();
        }
        c.push_str(r#"
 if(calls!=32||controls!=32||checks!=1344||failures) {fprintf(stderr,"calls=%u controls=%u checks=%u failures=%u\n",calls,controls,checks,failures);return 1;}
 puts("PASS 32 CG calls, 32 assembly controls, 1344 value/guard checks");return 0;
}
"#);
        c
    }

    #[test]
    fn stlxr_failure_status_survives_pressure_all_optimization_levels() {
        for opt in [OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::O3] {
            let directory = fresh_dir::create("trust-cg-exclusive-status-");
            let mut functions = Vec::new();
            for width in [32, 64] {
                for initialized in [false, true] {
                    for pressure in [0, 32] {
                        functions.push(pressure_function(width, initialized, pressure));
                    }
                }
            }
            assert_eq!(functions.len(), 8);
            fs::write(directory.join("driver.c"), driver(&functions)).unwrap();
            fs::write(directory.join("control.S"), native_host::assembly(ASSEMBLY)).unwrap();
            let pipeline = Pipeline::new(PipelineConfig {
                opt_level: opt,
                target_triple: native_host::TRIPLE.into(),
                verify: true,
                ..Default::default()
            });
            let mut objects = Vec::new();
            let mut status_spill_cases = 0;
            for mut function in functions {
                fs::write(
                    directory.join(format!("{}.input", function.name)),
                    format!("{function:#?}"),
                )
                .unwrap();
                let bytes = pipeline
                    .compile_ir_function(&mut function)
                    .unwrap_or_else(|error| panic!("{opt:?} files={directory:?}: {error:?}"));
                native_host::assert_native_object(&bytes);
                fs::write(
                    directory.join(format!("{}.final", function.name)),
                    format!("{function:#?}"),
                )
                .unwrap();
                status_spill_cases += usize::from(status_is_spilled_and_reloaded(&function));
                let object = directory.join(format!("{}.o", function.name));
                fs::write(&object, bytes).unwrap();
                objects.push(object);
            }
            assert!(
                status_spill_cases > 0,
                "{opt:?} files={directory:?}: no actual status spill/reload was exercised"
            );
            let binary = directory.join("run");
            let link = process::command_output_with_timeout(
                Command::new("cc")
                    .arg(format!("-{opt:?}"))
                    .arg("-fno-inline")
                    .args(native_host::link_hardening_args())
                    .arg(directory.join("driver.c"))
                    .arg(directory.join("control.S"))
                    .args(&objects)
                    .arg("-o")
                    .arg(&binary),
                process::codegen_link_timeout(),
            )
            .unwrap();
            assert!(
                !link.timed_out && link.output.status.success(),
                "{opt:?} files={directory:?}: {}",
                String::from_utf8_lossy(&link.output.stderr)
            );
            let run = process::run_executable_with_timeout(&binary, process::codegen_run_timeout())
                .unwrap();
            assert!(
                !run.timed_out && run.output.status.success(),
                "{opt:?} files={directory:?}: {} {}",
                String::from_utf8_lossy(&run.output.stdout),
                String::from_utf8_lossy(&run.output.stderr)
            );
            assert_eq!(
                String::from_utf8_lossy(&run.output.stdout).trim(),
                "PASS 32 CG calls, 32 assembly controls, 1344 value/guard checks",
                "{opt:?} files={directory:?}: incomplete native execution"
            );
            eprintln!(
                "{opt:?}: {}; {status_spill_cases} actual status spill/reload cases",
                String::from_utf8_lossy(&run.output.stdout).trim(),
            );
            fs::remove_dir_all(directory).unwrap();
        }
    }
}
