// Copyright 2026 Andrew Yates | Apache-2.0
//! AAPCS64 Bool ingress: only the least-significant byte is an argument/result.
//! Table 3 maps Bool to an unsigned byte (valid values 0/1); Stage C leaves
//! unused register bits unspecified. See the Arm ABI, not a compiler extension:
//! https://github.com/ARM-software/abi-aa/blob/main/aapcs64/aapcs64.rst
//! These independent selector/refutation and native C/assembly checks are
//! regression evidence, not formal proof or proof-required JIT qualification.

use trust_cg_ir::{AArch64Opcode, regs::PReg};
use trust_cg_lower::{
    abi::{AArch64AbiVariant, gpr},
    function::Signature,
    instructions::{Block as LBlock, Value},
    isel::{ISelInst, ISelOperand, InstructionSelector},
    types::Type,
};

fn formal_capture_is_byte_normalized(inst: &ISelInst, source: PReg) -> bool {
    inst.opcode == AArch64Opcode::Uxtb
        && matches!(inst.operands.as_slice(), [ISelOperand::VReg(_), ISelOperand::PReg(reg)] if *reg == source)
}

#[test]
fn bool_abi_selector_ingress_and_livein_refutation_gate() {
    // Every register position, stack overflow, both ABI variants, later FP
    // formals, and a live incoming hidden-result pointer. Expected registers
    // come from the ABI specification, not the production classifier.
    for variant in [AArch64AbiVariant::Aapcs64, AArch64AbiVariant::Darwin] {
        for bool_position in 0..12 {
            for sret in [false, true] {
                let mut params = vec![Type::I64; 12];
                params[bool_position] = Type::B1;
                params.push(Type::F64);
                let signature = Signature {
                    params,
                    returns: if sret {
                        vec![Type::Struct(vec![Type::I64; 3])]
                    } else {
                        vec![]
                    },
                };
                let mut selector =
                    InstructionSelector::new("bool_formal".into(), signature.clone());
                selector.set_abi_variant(variant);
                selector
                    .lower_formal_arguments(&signature, LBlock(0))
                    .unwrap();
                let selected = selector.finalize();
                let instructions = &selected.blocks[&LBlock(0)].insts;
                if bool_position < 8 {
                    let source = PReg::new(gpr::X0.encoding() + bool_position as u16);
                    let capture = instructions
                        .iter()
                        .find(|inst| formal_capture_is_byte_normalized(inst, source))
                        .unwrap_or_else(|| {
                            panic!("unnormalized Bool argument {bool_position}: {instructions:?}")
                        });
                    for later in bool_position + 1..8 {
                        assert!(
                            capture
                                .implicit_uses
                                .contains(&PReg::new(gpr::X0.encoding() + later as u16))
                        );
                    }
                    assert!(capture.implicit_uses.contains(&gpr::D0));
                    let mut old_bug = capture.clone();
                    old_bug.opcode = AArch64Opcode::Copy;
                    assert!(!formal_capture_is_byte_normalized(&old_bug, source));
                    let mut wrong_width = capture.clone();
                    wrong_width.opcode = AArch64Opcode::Uxth;
                    assert!(!formal_capture_is_byte_normalized(&wrong_width, source));
                } else {
                    assert_eq!(
                        instructions
                            .iter()
                            .filter(|inst| inst.opcode == AArch64Opcode::LdrbRI)
                            .count(),
                        1
                    );
                }
            }
        }
    }
}

#[test]
fn bool_call_results_capture_every_register_before_normalization() {
    // CG's explicit multi-result convention, not a standard C aggregate return:
    // Bool before and after I64/I128 lanes, plus an independent FP bank.
    // Capture order matters: normalization must not reuse an uncaptured lane.
    for indirect in [false, true] {
        let signature = Signature {
            params: vec![],
            returns: vec![],
        };
        let mut selector = InstructionSelector::new("bool_results".into(), signature);
        selector.set_abi_variant(AArch64AbiVariant::Aapcs64);
        selector.define_block_params(&[(Value(0), Type::I64)]);
        let types = [Type::B1, Type::I64, Type::I128, Type::B1, Type::F64];
        let results: Vec<_> = (1..=5).map(Value).collect();
        if indirect {
            selector
                .select_call_indirect(&Value(0), &[], &results, &types, LBlock(0))
                .unwrap();
        } else {
            selector
                .select_call("external", &[], &results, &types, LBlock(0))
                .unwrap();
        }
        let (selected, values) = selector.finalize_with_value_map();
        let instructions = &selected.blocks[&LBlock(0)].insts;
        let first_normalize = instructions
            .iter()
            .position(|inst| inst.opcode == AArch64Opcode::Uxtb)
            .expect("Bool call results must be normalized");
        let captures: Vec<_> = instructions
            .iter()
            .enumerate()
            .filter_map(|(i, inst)| match (inst.opcode, inst.operands.as_slice()) {
                (AArch64Opcode::Copy, [ISelOperand::VReg(dst), ISelOperand::PReg(source)]) => {
                    Some((i, *dst, *source))
                }
                _ => None,
            })
            .collect();
        assert_eq!(captures.len(), 6);
        assert!(captures.iter().all(|(i, _, _)| *i < first_normalize));
        assert_eq!(
            captures
                .iter()
                .map(|(_, _, source)| *source)
                .collect::<Vec<_>>(),
            vec![gpr::X0, gpr::X1, gpr::X2, gpr::X3, gpr::X4, gpr::D0]
        );
        for (value, capture_index) in [(Value(1), 0), (Value(4), 4)] {
            let raw = captures[capture_index].1;
            let canonical = &values[&value];
            assert_ne!(*canonical, ISelOperand::VReg(raw));
            assert!(
                instructions[first_normalize..]
                    .iter()
                    .any(|inst| inst.opcode == AArch64Opcode::Uxtb
                        && inst.operands == vec![canonical.clone(), ISelOperand::VReg(raw)])
            );
        }
    }
}

#[cfg(all(target_arch = "aarch64", target_os = "linux", target_env = "gnu"))]
#[path = "common/rosetta.rs"]
mod process;

#[path = "common/fresh_dir.rs"]
mod fresh_dir;

#[cfg(all(target_arch = "aarch64", target_os = "linux", target_env = "gnu"))]
mod native {
    use super::process;
    use std::{fmt::Write, fs, process::Command};
    use trust_cg_codegen::{Compiler, CompilerConfig, pipeline::OptLevel, target::TargetSpec};
    use trust_ir::{
        BinOp, CallingConv, CastOp, Endianness, ICmpOp, Module, StructPassingPolicy, TargetInfo, Ty,
    };
    use trust_ir_build::{ModuleBuilder, validate_module};

    fn corpus() -> Module {
        let mut m = ModuleBuilder::new_with_target_info(
            "linux_bool_abi",
            TargetInfo {
                triple: "aarch64-unknown-linux-gnu".into(),
                pointer_size: 8,
                endianness: Endianness::Little,
                abi: Some("aapcs64".into()),
                struct_passing: StructPassingPolicy::NativeC,
            },
        );
        let bool_sig = m.add_func_type(vec![Ty::U64], vec![Ty::Bool]);
        let dirty = m.declare_function("dirty_bool_return", bool_sig);
        for mode in 0..10 {
            let params = if mode < 4 {
                vec![Ty::Bool, Ty::Bool]
            } else if mode < 7 {
                vec![Ty::U64]
            } else {
                vec![Ty::Ptr, Ty::U64]
            };
            let sig = m.add_func_type(
                params.clone(),
                vec![if mode == 0 { Ty::Bool } else { Ty::U64 }],
            );
            let mut f = m.function(format!("cg_mode{mode}"), sig);
            let entry = f.create_block();
            let args: Vec<_> = params
                .into_iter()
                .map(|ty| f.add_block_param(entry, ty))
                .collect();
            f.switch_to_block(entry);
            let value = if mode < 4 {
                args[0]
            } else if mode < 7 {
                f.call(dirty, vec![args[0]])
            } else {
                f.call_indirect_cc(args[0], bool_sig, vec![args[1]], CallingConv::C)
            };
            let operation = if mode < 4 { mode } else { 1 + (mode - 4) % 3 };
            match operation {
                0 => f.ret(vec![value]),
                1 => {
                    let result = f.cast(CastOp::ZExt, Ty::Bool, Ty::U64, value);
                    f.ret(vec![result]);
                }
                2 => {
                    let rhs = if mode == 2 {
                        args[1]
                    } else {
                        f.bool_const(true)
                    };
                    let result = f.icmp(ICmpOp::Eq, Ty::Bool, value, rhs);
                    let result = f.cast(CastOp::ZExt, Ty::Bool, Ty::U64, result);
                    f.ret(vec![result]);
                }
                _ => {
                    let yes = f.create_block();
                    let no = f.create_block();
                    f.condbr(value, yes, vec![], no, vec![]);
                    for (block, number) in [(yes, 17), (no, 29)] {
                        f.switch_to_block(block);
                        let result = f.iconst(Ty::U64, number);
                        f.ret(vec![result]);
                    }
                }
            }
            f.build();
        }
        // A Bool at every GPR/stack position, surrounded by full-width integer
        // canaries. Weighted sums make permutations and overwritten suffix
        // live-ins observable; stack Bool padding is intentionally poisoned.
        for position in 0..12 {
            let mut params = vec![Ty::U64; 12];
            params[position] = Ty::Bool;
            let sig = m.add_func_type(params.clone(), vec![Ty::U64]);
            let mut f = m.function(format!("cg_pressure{position}"), sig);
            let entry = f.create_block();
            let args: Vec<_> = params
                .into_iter()
                .map(|ty| f.add_block_param(entry, ty))
                .collect();
            f.switch_to_block(entry);
            let mut sum = f.iconst(Ty::U64, 0);
            for (i, value) in args.into_iter().enumerate() {
                let value = if i == position {
                    f.cast(CastOp::ZExt, Ty::Bool, Ty::U64, value)
                } else {
                    value
                };
                let weight = f.iconst(Ty::U64, i as i128 + 1);
                let term = f.binop(BinOp::Mul, Ty::U64, value, weight);
                sum = f.binop(BinOp::Add, Ty::U64, sum, term);
            }
            f.ret(vec![sum]);
            f.build();
        }
        // Explicit CG multi-result ABI, implemented independently in assembly.
        // Only the ordinary C wrapper crosses a C-language function boundary.
        let returns = vec![Ty::Bool, Ty::U64, Ty::U128, Ty::Bool, Ty::F64];
        let multi_sig = m.add_func_type(vec![Ty::U64], returns.clone());
        let multi = m.declare_function("dirty_multi_return", multi_sig);
        for indirect in [false, true] {
            let sig = m.add_func_type(vec![Ty::Ptr, Ty::Ptr, Ty::U64, Ty::Ptr], vec![]);
            let mut f = m.function(
                if indirect {
                    "cg_multi_indirect"
                } else {
                    "cg_multi_direct"
                },
                sig,
            );
            let entry = f.create_block();
            let out = f.add_block_param(entry, Ty::Ptr);
            let live = f.add_block_param(entry, Ty::Ptr);
            let raw = f.add_block_param(entry, Ty::U64);
            let callee = f.add_block_param(entry, Ty::Ptr);
            f.switch_to_block(entry);
            let preserved: Vec<_> = (0..20)
                .map(|lane| {
                    let pointer = f.gep_byte_offset(live, lane * 8);
                    f.load_volatile(Ty::U64, pointer)
                })
                .collect();
            let result = if indirect {
                f.call_indirect_results_cc::<5>(callee, multi_sig, vec![raw], CallingConv::Fast)
            } else {
                f.call_results::<5>(multi, vec![raw])
            };
            let mut offset = 0;
            for (value, ty) in result.into_iter().zip(returns.clone()) {
                let (value, ty) = if ty == Ty::Bool {
                    (f.cast(CastOp::ZExt, Ty::Bool, Ty::U64, value), Ty::U64)
                } else {
                    (value, ty)
                };
                let pointer = f.gep_byte_offset(out, offset);
                offset += if ty == Ty::U128 { 16 } else { 8 };
                // U128 is ordinary memory here, not one volatile event: its
                // two-word store is the admitted, intended representation.
                f.store(ty, pointer, value);
            }
            for value in preserved {
                let pointer = f.gep_byte_offset(out, offset);
                offset += 8;
                f.store_volatile(Ty::U64, pointer, value);
            }
            f.ret(vec![]);
            f.build();
        }
        let mut module = m.build().expect("ModuleBuilder::build: test fixture");
        module
            .functions
            .iter_mut()
            .find(|f| f.id == multi)
            .unwrap()
            .calling_conv = CallingConv::Fast;
        assert_eq!(validate_module(&module), []);
        module
    }

    const ASSEMBLY: &str = r#"
.text
.global raw_call_many
.type raw_call_many,%function
raw_call_many:
 sub sp,sp,#48
 stp x29,x30,[sp,#32]
 mov x29,sp
 mov x16,x0
 mov x9,x1
 ldp x10,x11,[x9,#64]
 stp x10,x11,[sp]
 ldp x10,x11,[x9,#80]
 stp x10,x11,[sp,#16]
 ldp x0,x1,[x9]
 ldp x2,x3,[x9,#16]
 ldp x4,x5,[x9,#32]
 ldp x6,x7,[x9,#48]
 blr x16
 ldp x29,x30,[sp,#32]
 add sp,sp,#48
 ret
.size raw_call_many,.-raw_call_many
.global dirty_bool_return
.type dirty_bool_return,%function
dirty_bool_return:
 ret
.size dirty_bool_return,.-dirty_bool_return
.global dirty_multi_return
.type dirty_multi_return,%function
dirty_multi_return:
 mov x1,#0x2345
 mov x2,#0x3456
 mov x3,#0x4567
 eor x4,x0,#1
 fmov d0,#1.0
 ret
.size dirty_multi_return,.-dirty_multi_return
.section .note.GNU-stack,"",%progbits
"#;

    fn driver() -> String {
        let mut c = String::from(
            r#"
#include <stdint.h>
#include <stdbool.h>
#include <stdio.h>
#include <string.h>
_Static_assert(sizeof(bool)==1,"AAPCS64 Bool unsigned byte");
extern uint64_t raw_call_many(void*,const uint64_t*);
extern bool dirty_bool_return(uint64_t);
extern void dirty_multi_return(void);
__attribute__((noinline)) bool c_mode0(bool a,bool b){(void)b;return a;}
__attribute__((noinline)) uint64_t c_mode1(bool a,bool b){(void)b;return a;}
__attribute__((noinline)) uint64_t c_mode2(bool a,bool b){return a==b;}
__attribute__((noinline)) uint64_t c_mode3(bool a,bool b){(void)b;return a?17:29;}
__attribute__((noinline)) uint64_t c_mode4(uint64_t a){return dirty_bool_return(a);}
__attribute__((noinline)) uint64_t c_mode5(uint64_t a){return dirty_bool_return(a)==true;}
__attribute__((noinline)) uint64_t c_mode6(uint64_t a){return dirty_bool_return(a)?17:29;}
__attribute__((noinline)) uint64_t c_mode7(bool(*f)(uint64_t),uint64_t a){return f(a);}
__attribute__((noinline)) uint64_t c_mode8(bool(*f)(uint64_t),uint64_t a){return f(a)==true;}
__attribute__((noinline)) uint64_t c_mode9(bool(*f)(uint64_t),uint64_t a){return f(a)?17:29;}
extern bool cg_mode0(bool,bool);
extern uint64_t cg_mode1(bool,bool),cg_mode2(bool,bool),cg_mode3(bool,bool);
extern uint64_t cg_mode4(uint64_t),cg_mode5(uint64_t),cg_mode6(uint64_t);
extern uint64_t cg_mode7(bool(*)(uint64_t),uint64_t),cg_mode8(bool(*)(uint64_t),uint64_t),cg_mode9(bool(*)(uint64_t),uint64_t);
extern void cg_multi_direct(uint64_t*,const uint64_t*,uint64_t,void*);
extern void cg_multi_indirect(uint64_t*,const uint64_t*,uint64_t,void*);
static unsigned checks;
static int check(uint64_t actual,uint64_t expected,const char*name,unsigned test){
 if(actual!=expected){printf("FAIL %s case=%u actual=%016lx expected=%016lx\n",name,test,actual,expected);return 1;}
 checks++;return 0;
}
"#,
        );
        for position in 0..12 {
            let params = (0..12)
                .map(|i| format!("{} a{i}", if i == position { "bool" } else { "uint64_t" }))
                .collect::<Vec<_>>()
                .join(",");
            let sum = (0..12)
                .map(|i| format!("(uint64_t)a{i}*{}", i + 1))
                .collect::<Vec<_>>()
                .join("+");
            writeln!(c,"extern uint64_t cg_pressure{position}({params});\n__attribute__((noinline)) uint64_t c_pressure{position}({params}){{return {sum};}}").unwrap();
        }
        c.push_str("int main(void){\nvoid* cg_modes[]={");
        c.push_str(
            &(0..10)
                .map(|i| format!("cg_mode{i}"))
                .collect::<Vec<_>>()
                .join(","),
        );
        c.push_str("};void* c_modes[]={");
        c.push_str(
            &(0..10)
                .map(|i| format!("c_mode{i}"))
                .collect::<Vec<_>>()
                .join(","),
        );
        c.push_str("};void* cg_pressure[]={");
        c.push_str(
            &(0..12)
                .map(|i| format!("cg_pressure{i}"))
                .collect::<Vec<_>>()
                .join(","),
        );
        c.push_str("};void* c_pressure[]={");
        c.push_str(
            &(0..12)
                .map(|i| format!("c_pressure{i}"))
                .collect::<Vec<_>>()
                .join(","),
        );
        c.push_str(r#"};
 const uint64_t uppers[]={0,0x100,0xffffff00,UINT64_C(0xdeadbeef00000000)};
 for(unsigned mode=0;mode<10;mode++)for(unsigned ua=0;ua<4;ua++)for(unsigned ub=0;ub<4;ub++)for(unsigned a=0;a<2;a++)for(unsigned b=0;b<2;b++){
  uint64_t args[12]={uppers[ua]|a,uppers[ub]|b};
  if(mode>=7){args[0]=(uintptr_t)dirty_bool_return;args[1]=uppers[ua]|a;}
  unsigned operation=mode<4?mode:1+(mode-4)%3;
  uint64_t expected=operation<2?a:operation==2?(mode==2?a==b:a):a?17:29;
  uint64_t native=raw_call_many(c_modes[mode],args),actual=raw_call_many(cg_modes[mode],args);
  if(mode==0){native&=255;actual&=255;} /* Unused result bits are not compared. */
  if(check(native,expected,"C control",mode)||check(actual,expected,"CG Bool boundary",mode))return 1;
 }
 for(unsigned position=0;position<12;position++)for(unsigned upper=0;upper<4;upper++)for(unsigned b=0;b<2;b++){
  uint64_t args[12],expected=0;
  for(unsigned i=0;i<12;i++){args[i]=UINT64_C(0xabcdef0123456789)+i*UINT64_C(0x11111222);expected+=(i==position?b:args[i])*(i+1);}
  args[position]=uppers[upper]|b;
  if(check(raw_call_many(c_pressure[position],args),expected,"C pressure",position)||check(raw_call_many(cg_pressure[position],args),expected,"CG pressure",position))return 2;
 }
 void(*multi[])(uint64_t*,const uint64_t*,uint64_t,void*)={cg_multi_direct,cg_multi_indirect};
 for(unsigned indirect=0;indirect<2;indirect++)for(unsigned upper=0;upper<4;upper++)for(unsigned b=0;b<2;b++){
  uint64_t live[20],out[28],expected[28]={b,0x2345,0x3456,0x4567,b^1,UINT64_C(0x3ff0000000000000)};
  for(unsigned i=0;i<20;i++){live[i]=UINT64_C(0x8abc0123456789ef)+i*UINT64_C(0x100000001);expected[6+i]=live[i];}
  for(unsigned i=0;i<28;i++)out[i]=UINT64_C(0x3c3c3c3c3c3c3c3c);
  expected[26]=expected[27]=UINT64_C(0x3c3c3c3c3c3c3c3c);
  multi[indirect](out,live,uppers[upper]|b,dirty_multi_return);
  for(unsigned i=0;i<28;i++)if(check(out[i],expected[i],"CG multi-result/live lane",i))return 3;
 }
 printf("PASS %u value checks (C controls and CG results; multi-result lanes counted separately)\n",checks);
 return 0;
}
"#);
        c
    }

    #[test]
    fn native_dirty_bool_arguments_results_and_pressure_o0_through_o3() {
        let module = corpus();
        for opt in [OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::O3] {
            let dir = crate::fresh_dir::create("trust-cg-bool-abi-");
            fs::write(dir.join("input.ir-debug"), format!("{module:#?}")).unwrap();
            let output = Compiler::new_for_target_spec(
                CompilerConfig {
                    opt_level: opt,
                    ..Default::default()
                },
                TargetSpec::parse("aarch64-unknown-linux-gnu").unwrap(),
            )
            .with_codegen_license(super::permit_unlicensed())
            .compile(&module)
            .unwrap();
            assert_eq!(&output.object_code[..4], b"\x7fELF");
            fs::write(dir.join("module.o"), output.object_code).unwrap();
            fs::write(dir.join("driver.c"), driver()).unwrap();
            fs::write(dir.join("caller.S"), ASSEMBLY).unwrap();
            let binary = dir.join("driver");
            let link = process::command_output_with_timeout(
                Command::new("cc")
                    .arg(format!("-{opt:?}"))
                    .arg("-fno-inline")
                    .arg(dir.join("driver.c"))
                    .arg(dir.join("caller.S"))
                    .arg(dir.join("module.o"))
                    .arg("-o")
                    .arg(&binary),
                process::codegen_link_timeout(),
            )
            .unwrap();
            assert!(
                !link.timed_out && link.output.status.success(),
                "{opt:?} files={dir:?}: {}",
                String::from_utf8_lossy(&link.output.stderr)
            );
            let run = process::run_executable_with_timeout(&binary, process::codegen_run_timeout())
                .unwrap();
            assert!(
                !run.timed_out && run.output.status.success(),
                "{opt:?} files={dir:?}: {} {}",
                String::from_utf8_lossy(&run.output.stdout),
                String::from_utf8_lossy(&run.output.stderr)
            );
            assert_eq!(
                String::from_utf8_lossy(&run.output.stdout).trim(),
                "PASS 1920 value checks (C controls and CG results; multi-result lanes counted separately)",
                "{opt:?} files={dir:?}: incomplete native execution"
            );
            eprintln!(
                "{opt:?}: {}",
                String::from_utf8_lossy(&run.output.stdout).trim()
            );
            fs::remove_dir_all(&dir).unwrap();
        }
    }
}

/// This file's fixtures are hand-built and carry no codegen license
/// (`body_gate: None`), which trust-cg REFUSES by default (roadmap WS7.5,
/// decision gate DG-73). Its compiles state `Permit` explicitly, so none of
/// them passes because it was silently refused.
// Its callers are target-gated tests; on a host where none of them compiles
// the helper is unused.
#[allow(dead_code)]
fn permit_unlicensed() -> trust_cg_lower::CodegenLicensePolicy {
    trust_cg_lower::CodegenLicensePolicy::default()
        .with_unlicensed(trust_cg_lower::UnlicensedBodyPolicy::Permit)
}
