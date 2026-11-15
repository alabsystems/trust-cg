// Copyright 2026 Andrew Yates | Apache-2.0
//! DarwinPCS twin of the native half of `e2e_aarch64_bool_abi_linux.rs`:
//! `bool` and narrow-integer arguments and results across the C boundary,
//! natively on `aarch64-apple-darwin` at O0-O3 against Apple clang.
//!
//! Apple arm64 departs from AAPCS64 here. `bool` is still one byte (0 or 1),
//! but the CALLER sign- or zero-extends every argument narrower than 32 bits
//! to 32 bits, and the CALLEE extends a narrow result to 32 bits, so only bits
//! 32-63 of such a register are unspecified; on the stack a narrow argument
//! occupies its natural size at its natural alignment. The raw callers and
//! probes below are hand-written Apple assembly, so neither the value placement
//! nor the dirt comes from either compiler:
//!
//! * clang-compiled controls and TrustCG functions receive `bool` arguments
//!   whose bits 32-63 are dirty (the only dirt DarwinPCS permits), at every
//!   register and stack position, with the padding after a lone stack `bool`
//!   poisoned, and several `bool`/narrow arguments packed into one stack word;
//! * TrustCG results (`bool` and every narrow integer) are captured in full
//!   from X0 and must be extended to 32 bits, and clang calls that rely on
//!   the extension must see the value;
//! * TrustCG callers pass `bool` and narrow integers produced by truncation
//!   from dirty 64-bit values to a probe that records X0-X7 and the stack:
//!   each register must hold the value extended to 32 bits and each stack
//!   argument its value at its packed offset (`Trunc` already zero-extends,
//!   so of the caller-side extensions only sign extension of a negative
//!   `i8`/`i16` is observable here);
//! * the explicit TrustCG multi-result convention (not a C boundary) keeps the
//!   Linux suite's dirty-lane Bool normalization and live-value preservation.
//!
//! Execution evidence on this host, not a proof.

#![cfg(all(target_arch = "aarch64", target_os = "macos"))]

#[path = "common/darwin_c_boundary.rs"]
mod boundary;

use boundary::{fresh_dir, process};
use std::{fmt::Write, fs, process::Command};
use trust_ir::{BinOp, CallingConv, CastOp, ICmpOp, Module, Ty};
use trust_ir_build::{ModuleBuilder, validate_module};

/// Narrow integers the probes and result checks cover, with their C types.
const NARROW: [(Ty, &str); 6] = [
    (Ty::I8, "int8_t"),
    (Ty::U8, "uint8_t"),
    (Ty::I16, "int16_t"),
    (Ty::U16, "uint16_t"),
    (Ty::I32, "int32_t"),
    (Ty::U32, "uint32_t"),
];

/// Parameters of the stack-packing functions: X0-X7 hold `u64`, then
/// `bool, bool, u8, bool` pack into bytes 0-3, `u64` is at 8, `bool` at 16 and
/// `i16` at 18.
fn packed_params() -> Vec<Ty> {
    let mut params = vec![Ty::U64; 8];
    params.extend([
        Ty::Bool,
        Ty::Bool,
        Ty::U8,
        Ty::Bool,
        Ty::U64,
        Ty::Bool,
        Ty::I16,
    ]);
    params
}

/// Twelve `bool` then eight narrow integers for the CG-caller probes: eight
/// `bool` in W0-W7, four packed at `[sp]..[sp, #3]`; the narrow probe takes
/// `i8, u8, i16, u16, i32, u32, i8, u8` in W0-W7 and the same six types again
/// on the stack at offsets 0, 1, 2, 4, 8 and 12.
fn narrow_probe_params() -> Vec<Ty> {
    let mut params: Vec<Ty> = NARROW.iter().map(|(ty, _)| ty.clone()).collect();
    params.extend([Ty::I8, Ty::U8]);
    params.extend(NARROW.iter().map(|(ty, _)| ty.clone()));
    params
}

fn weighted_sum(
    f: &mut trust_ir_build::FunctionBuilder<'_>,
    args: &[(trust_ir::ValueId, Ty)],
) -> trust_ir::ValueId {
    let mut sum = f.iconst(Ty::U64, 0);
    for (i, (value, ty)) in args.iter().enumerate() {
        let widened = match ty {
            Ty::U64 => *value,
            Ty::Bool | Ty::U8 | Ty::U16 | Ty::U32 => {
                f.cast(CastOp::ZExt, ty.clone(), Ty::U64, *value)
            }
            _ => {
                let wide = f.cast(CastOp::SExt, ty.clone(), Ty::I64, *value);
                f.cast(CastOp::Bitcast, Ty::I64, Ty::U64, wide)
            }
        };
        let weight = f.iconst(Ty::U64, i as i128 + 1);
        let term = f.binop(BinOp::Mul, Ty::U64, widened, weight);
        sum = f.binop(BinOp::Add, Ty::U64, sum, term);
    }
    sum
}

fn corpus() -> Module {
    let mut m = ModuleBuilder::new_with_target_info("darwin_bool_abi", boundary::target_info());
    let bool_sig = m.add_func_type(vec![Ty::U64], vec![Ty::Bool]);
    let dirty = m.declare_function("dirty_bool_return", bool_sig);
    // Modes 0-9: the Linux suite's Bool arguments/results, direct and
    // indirect Bool-returning callees.
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
    // A Bool at every GPR/stack position among full-width canaries.
    for position in 0..12 {
        let mut params = vec![Ty::U64; 12];
        params[position] = Ty::Bool;
        let sig = m.add_func_type(params.clone(), vec![Ty::U64]);
        let mut f = m.function(format!("cg_pressure{position}"), sig);
        let entry = f.create_block();
        let args: Vec<_> = params
            .iter()
            .map(|ty| (f.add_block_param(entry, ty.clone()), ty.clone()))
            .collect();
        f.switch_to_block(entry);
        let sum = weighted_sum(&mut f, &args);
        f.ret(vec![sum]);
        f.build();
    }
    // Several narrow stack arguments packed into one word.
    {
        let params = packed_params();
        let sig = m.add_func_type(params.clone(), vec![Ty::U64]);
        let mut f = m.function("cg_packed", sig);
        let entry = f.create_block();
        let args: Vec<_> = params
            .iter()
            .map(|ty| (f.add_block_param(entry, ty.clone()), ty.clone()))
            .collect();
        f.switch_to_block(entry);
        let sum = weighted_sum(&mut f, &args);
        f.ret(vec![sum]);
        f.build();
    }
    // Narrow results produced by truncation (dirty upper bits before the
    // callee's extension).
    for (ty, _) in NARROW.iter().chain(&[(Ty::Bool, "bool")]) {
        let sig = m.add_func_type(vec![Ty::U64], vec![ty.clone()]);
        let mut f = m.function(format!("cg_ret_{}", c_name(ty)), sig);
        let entry = f.create_block();
        let x = f.add_block_param(entry, Ty::U64);
        f.switch_to_block(entry);
        let narrow = f.cast(CastOp::Trunc, Ty::U64, ty.clone(), x);
        f.ret(vec![narrow]);
        f.build();
    }
    // CG callers passing truncated Bool/narrow values to the recording probe
    // and to a clang control with the same signature.
    let bool_probe_params = vec![Ty::Bool; 12];
    let narrow_params = narrow_probe_params();
    for (name, params) in [("bools", bool_probe_params), ("narrow", narrow_params)] {
        let probe_sig = m.add_func_type(params.clone(), vec![]);
        let probe = m.declare_function(format!("probe_{name}"), probe_sig);
        let control_sig = m.add_func_type(params.clone(), vec![Ty::U64]);
        let control = m.declare_function(format!("c_sum_{name}"), control_sig);
        // cg_send_<name>(bits, dirt): argument i is Trunc((bits >> 3i) ^ dirt)
        // for narrow integers and Trunc((bits >> i) ^ dirt) for Bool. The
        // 64-bit carriers are dirty, but `Trunc` leaves each value
        // zero-extended, so only a negative signed value needs (and so
        // observes) the caller's extension to 32 bits; the driver computes
        // every expected value from the same formula.
        let sig = m.add_func_type(vec![Ty::U64, Ty::U64], vec![Ty::U64]);
        let mut f = m.function(format!("cg_send_{name}"), sig);
        let entry = f.create_block();
        let bits = f.add_block_param(entry, Ty::U64);
        let dirt = f.add_block_param(entry, Ty::U64);
        f.switch_to_block(entry);
        let mut values = Vec::new();
        for (i, ty) in params.iter().enumerate() {
            let shift = f.iconst(Ty::U64, if *ty == Ty::Bool { i } else { 3 * i } as i128);
            let shifted = f.binop(BinOp::LShr, Ty::U64, bits, shift);
            let carrier = f.binop(BinOp::Xor, Ty::U64, shifted, dirt);
            values.push(f.cast(CastOp::Trunc, Ty::U64, ty.clone(), carrier));
        }
        f.call_void(probe, values.clone());
        let result = f.call(control, values);
        f.ret(vec![result]);
        f.build();
    }
    // The explicit CG multi-result ABI (Fast calling convention), implemented
    // independently in assembly.
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

fn c_name(ty: &Ty) -> &'static str {
    match ty {
        Ty::Bool => "bool",
        Ty::I8 => "i8",
        Ty::U8 => "u8",
        Ty::I16 => "i16",
        Ty::U16 => "u16",
        Ty::I32 => "i32",
        Ty::U32 => "u32",
        other => panic!("no C name for {other:?}"),
    }
}

/// Apple arm64 assembly: a raw caller with an explicit register and stack
/// image, the dirty Bool callees, and the recording probes.
const ASSEMBLY: &str = r#"
.text
; uint64_t raw_call(void *fn, const uint64_t regs[8], const uint8_t stack[64])
; Returns X0 of the callee in full.
.globl _raw_call
.p2align 2
_raw_call:
 sub sp, sp, #80
 stp x29, x30, [sp, #64]
 add x29, sp, #64
 mov x16, x0
 mov x9, x1
 ldp x10, x11, [x2]
 stp x10, x11, [sp]
 ldp x10, x11, [x2, #16]
 stp x10, x11, [sp, #16]
 ldp x10, x11, [x2, #32]
 stp x10, x11, [sp, #32]
 ldp x10, x11, [x2, #48]
 stp x10, x11, [sp, #48]
 ldp x0, x1, [x9]
 ldp x2, x3, [x9, #16]
 ldp x4, x5, [x9, #32]
 ldp x6, x7, [x9, #48]
 blr x16
 ldp x29, x30, [sp, #64]
 add sp, sp, #80
 ret
; bool dirty_bool_return(uint64_t): returns its argument unchanged. The
; driver passes only DarwinPCS-legal results: 0/1 in W0, bits 32-63 dirty.
.globl _dirty_bool_return
.p2align 2
_dirty_bool_return:
 ret
; The CG multi-result convention: Bool lanes with dirty upper bits.
.globl _dirty_multi_return
.p2align 2
_dirty_multi_return:
 mov x1, #0x2345
 mov x2, #0x3456
 mov x3, #0x4567
 eor x4, x0, #1
 fmov d0, #1.0
 ret
; Record X0-X7 and the first 16 incoming stack bytes into probe_record[10].
.globl _probe_bools
.globl _probe_narrow
.p2align 2
_probe_bools:
_probe_narrow:
 adrp x9, _probe_record@PAGE
 add x9, x9, _probe_record@PAGEOFF
 stp x0, x1, [x9]
 stp x2, x3, [x9, #16]
 stp x4, x5, [x9, #32]
 stp x6, x7, [x9, #48]
 ldp x10, x11, [sp]
 stp x10, x11, [x9, #64]
 ret
"#;

fn driver() -> String {
    let mut c = String::from(
        r#"
#include <stdint.h>
#include <stdbool.h>
#include <stdio.h>
#include <string.h>
_Static_assert(sizeof(bool)==1, "DarwinPCS bool is one byte");
extern uint64_t raw_call(void *, const uint64_t *, const uint8_t *);
extern bool dirty_bool_return(uint64_t);
uint64_t probe_record[10];
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
extern uint64_t cg_packed(uint64_t,uint64_t,uint64_t,uint64_t,uint64_t,uint64_t,uint64_t,uint64_t,bool,bool,uint8_t,bool,uint64_t,bool,int16_t);
__attribute__((noinline)) uint64_t c_packed(uint64_t a0,uint64_t a1,uint64_t a2,uint64_t a3,uint64_t a4,uint64_t a5,uint64_t a6,uint64_t a7,bool b8,bool b9,uint8_t u10,bool b11,uint64_t a12,bool b13,int16_t s14){
 return a0*1+a1*2+a2*3+a3*4+a4*5+a5*6+a6*7+a7*8+(uint64_t)b8*9+(uint64_t)b9*10+(uint64_t)u10*11+(uint64_t)b11*12+a12*13+(uint64_t)b13*14+(uint64_t)(int64_t)s14*15;
}
extern void cg_multi_direct(uint64_t*,const uint64_t*,uint64_t,void*);
extern void cg_multi_indirect(uint64_t*,const uint64_t*,uint64_t,void*);
extern void dirty_multi_return(void);
extern uint64_t cg_send_bools(uint64_t,uint64_t), cg_send_narrow(uint64_t,uint64_t);
static unsigned checks;
static int check(uint64_t actual,uint64_t expected,const char*name,unsigned test){
 if(actual!=expected){printf("FAIL %s case=%u actual=%016llx expected=%016llx\n",name,test,(unsigned long long)actual,(unsigned long long)expected);return 1;}
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
        writeln!(c, "extern uint64_t cg_pressure{position}({params});\n__attribute__((noinline)) uint64_t c_pressure{position}({params}){{return {sum};}}").unwrap();
    }
    for (ty, c_type) in NARROW.iter().chain(&[(Ty::Bool, "bool")]) {
        writeln!(c, "extern {c_type} cg_ret_{}(uint64_t);", c_name(ty)).unwrap();
    }
    // The clang controls of the CG-caller probes.
    let bool_params = (0..12)
        .map(|i| format!("bool a{i}"))
        .collect::<Vec<_>>()
        .join(",");
    let bool_sum = (0..12)
        .map(|i| format!("(uint64_t)a{i}*{}", i + 1))
        .collect::<Vec<_>>()
        .join("+");
    writeln!(
        c,
        "__attribute__((noinline)) uint64_t c_sum_bools({bool_params}){{return {bool_sum};}}"
    )
    .unwrap();
    let narrow_types: Vec<&str> = NARROW
        .iter()
        .map(|(_, c)| *c)
        .chain(["int8_t", "uint8_t"])
        .chain(NARROW.iter().map(|(_, c)| *c))
        .collect();
    let narrow_params = narrow_types
        .iter()
        .enumerate()
        .map(|(i, t)| format!("{t} a{i}"))
        .collect::<Vec<_>>()
        .join(",");
    let narrow_sum = narrow_types
        .iter()
        .enumerate()
        .map(|(i, t)| {
            if t.starts_with('u') {
                format!("(uint64_t)a{i}*{}", i + 1)
            } else {
                format!("(uint64_t)(int64_t)a{i}*{}", i + 1)
            }
        })
        .collect::<Vec<_>>()
        .join("+");
    writeln!(
        c,
        "__attribute__((noinline)) uint64_t c_sum_narrow({narrow_params}){{return {narrow_sum};}}"
    )
    .unwrap();
    c.push_str("static const char *narrow_types[] = {");
    for t in &narrow_types {
        write!(c, "\"{t}\",").unwrap();
    }
    c.push_str("};\n");
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
 /* DarwinPCS permits dirt only in bits 32-63 of a narrow register argument
    or result: the low 32 bits of a bool are exactly 0 or 1. */
 const uint64_t uppers[]={0,UINT64_C(0x100000000),UINT64_C(0xffffffff00000000),UINT64_C(0xdeadbeef00000000)};
 uint8_t stack[64];
 for(unsigned mode=0;mode<10;mode++)for(unsigned ua=0;ua<4;ua++)for(unsigned ub=0;ub<4;ub++)for(unsigned a=0;a<2;a++)for(unsigned b=0;b<2;b++){
  uint64_t regs[8]={uppers[ua]|a,uppers[ub]|b,0x11,0x22,0x33,0x44,0x55,0x66};
  memset(stack,0xa5,sizeof stack);
  if(mode>=7){regs[0]=(uintptr_t)dirty_bool_return;regs[1]=uppers[ua]|a;}
  unsigned operation=mode<4?mode:1+(mode-4)%3;
  uint64_t expected=operation<2?a:operation==2?(mode==2?a==b:a):a?17:29;
  uint64_t native=raw_call(c_modes[mode],regs,stack),actual=raw_call(cg_modes[mode],regs,stack);
  /* A bool result is extended to 32 bits by the callee: bits 32-63 alone are unspecified. */
  if(mode==0){native&=0xffffffffu;actual&=0xffffffffu;}
  if(check(native,expected,"C control",mode)||check(actual,expected,"CG Bool boundary",mode))return 1;
 }
 for(unsigned position=0;position<12;position++)for(unsigned upper=0;upper<4;upper++)for(unsigned b=0;b<2;b++){
  uint64_t regs[8],expected=0,value[12];
  for(unsigned i=0;i<12;i++){value[i]=UINT64_C(0xabcdef0123456789)+i*UINT64_C(0x11111222);if(i==position)value[i]=b;expected+=value[i]*(i+1);}
  memset(stack,0xa5,sizeof stack);
  for(unsigned i=0;i<8;i++)regs[i]=i==position?(uppers[upper]|b):value[i];
  /* Stack words: a lone bool takes byte 0 of its 8-aligned word; its padding stays poisoned. */
  for(unsigned i=8;i<12;i++){if(i==position)stack[8*(i-8)]=(uint8_t)b;else memcpy(stack+8*(i-8),&value[i],8);}
  if(check(raw_call(c_pressure[position],regs,stack),expected,"C pressure",position)||check(raw_call(cg_pressure[position],regs,stack),expected,"CG pressure",position))return 2;
 }
 for(unsigned pattern=0;pattern<64;pattern++){
  /* bool,bool,u8,bool at bytes 0-3, u64 at 8, bool at 16, i16 at 18 (natural-size packing). */
  uint64_t regs[8],expected=0;
  for(unsigned i=0;i<8;i++){regs[i]=UINT64_C(0x0102030405060708)*(i+3)+pattern;expected+=regs[i]*(i+1);}
  bool b8=pattern&1,b9=(pattern>>1)&1,b11=(pattern>>2)&1,b13=(pattern>>3)&1;
  uint8_t u10=(uint8_t)(0x80|pattern*5);int16_t s14=(int16_t)(-1000-(int)pattern*37);uint64_t a12=UINT64_C(0xfedcba9876543210)^pattern;
  memset(stack,0xa5,sizeof stack);
  stack[0]=b8;stack[1]=b9;stack[2]=u10;stack[3]=b11;memcpy(stack+8,&a12,8);stack[16]=b13;memcpy(stack+18,&s14,2);
  expected+=(uint64_t)b8*9+(uint64_t)b9*10+(uint64_t)u10*11+(uint64_t)b11*12+a12*13+(uint64_t)b13*14+(uint64_t)(int64_t)s14*15;
  if(check(raw_call(c_packed,regs,stack),expected,"C packed stack",pattern)||check(raw_call(cg_packed,regs,stack),expected,"CG packed stack",pattern))return 3;
  if(check(cg_packed(regs[0],regs[1],regs[2],regs[3],regs[4],regs[5],regs[6],regs[7],b8,b9,u10,b11,a12,b13,s14),expected,"C->CG packed call",pattern))return 3;
 }
 /* TrustCG narrow results: extended to 32 bits by the callee. */
 const uint64_t inputs[]={0,1,2,0x7f,0x80,0xff,0x100,0x7fff,0x8000,0xffff,UINT64_C(0x80000000),UINT64_C(0xdeadbeef8badf00d),UINT64_C(0x12345678fffffffe),UINT64_C(0xffffffffffffffff)};
 for(unsigned i=0;i<sizeof inputs/sizeof*inputs;i++){
  uint64_t x=inputs[i],regs[8]={x,0,0,0,0,0,0,0};
  memset(stack,0xa5,sizeof stack);
  struct { void *fn; uint32_t want; const char *name; } rows[]={
   {cg_ret_i8,(uint32_t)(int32_t)(int8_t)x,"i8 result"},{cg_ret_u8,(uint32_t)(uint8_t)x,"u8 result"},
   {cg_ret_i16,(uint32_t)(int32_t)(int16_t)x,"i16 result"},{cg_ret_u16,(uint32_t)(uint16_t)x,"u16 result"},
   {cg_ret_i32,(uint32_t)x,"i32 result"},{cg_ret_u32,(uint32_t)x,"u32 result"},
   {cg_ret_bool,(uint32_t)(x&1),"bool result"}};
  for(unsigned r=0;r<sizeof rows/sizeof*rows;r++)
   if(check((uint32_t)raw_call(rows[r].fn,regs,stack),rows[r].want,rows[r].name,i))return 4;
  /* clang callers relying on the extension. */
  if(check((uint64_t)(int64_t)cg_ret_i8(x),(uint64_t)(int64_t)(int8_t)x,"i8 result in C",i)
   ||check((uint64_t)cg_ret_u8(x),(uint64_t)(uint8_t)x,"u8 result in C",i)
   ||check((uint64_t)(int64_t)cg_ret_i16(x),(uint64_t)(int64_t)(int16_t)x,"i16 result in C",i)
   ||check((uint64_t)cg_ret_u16(x),(uint64_t)(uint16_t)x,"u16 result in C",i)
   ||check((uint64_t)cg_ret_bool(x),x&1,"bool result in C",i))return 4;
 }
 /* TrustCG callers: register images extended to 32 bits, stack values packed. */
 const uint64_t dirts[]={0,UINT64_C(0xa5a5a5a5a5a5a5a4),UINT64_C(0xfffffffffffffffe),UINT64_C(0x5a5a5a5a00000000)};
 for(unsigned d=0;d<4;d++)for(unsigned pattern=0;pattern<16;pattern++){
  uint64_t bits=UINT64_C(0x9e3779b97f4a7c15)*(pattern+1);
  uint64_t dirt=dirts[d];
  memset(probe_record,0,sizeof probe_record);
  uint64_t sum=cg_send_bools(bits,dirt),expected=0;
  const uint8_t *stack_bytes=(const uint8_t*)&probe_record[8];
  for(unsigned i=0;i<12;i++){
   uint64_t v=((bits>>i)^dirt)&1;expected+=v*(i+1);
   if(i<8){if(check(probe_record[i]&0xffffffffu,v,"CG bool argument register (W extended)",i))return 5;}
   else if(check(stack_bytes[i-8],v,"CG bool stack byte",i))return 5;
  }
  if(check(sum,expected,"CG bools -> C control",pattern))return 5;
  memset(probe_record,0,sizeof probe_record);
  sum=cg_send_narrow(bits,dirt);expected=0;
  static const unsigned offsets[]={0,1,2,4,8,12};
  for(unsigned i=0;i<14;i++){
   uint64_t carrier=(bits>>(3*i))^dirt; const char *t=narrow_types[i];
   uint32_t want32; int64_t value;
   if(!strcmp(t,"int8_t")){value=(int8_t)carrier;want32=(uint32_t)(int32_t)(int8_t)carrier;}
   else if(!strcmp(t,"uint8_t")){value=(uint8_t)carrier;want32=(uint8_t)carrier;}
   else if(!strcmp(t,"int16_t")){value=(int16_t)carrier;want32=(uint32_t)(int32_t)(int16_t)carrier;}
   else if(!strcmp(t,"uint16_t")){value=(uint16_t)carrier;want32=(uint16_t)carrier;}
   else if(!strcmp(t,"int32_t")){value=(int32_t)carrier;want32=(uint32_t)carrier;}
   else {value=(uint32_t)carrier;want32=(uint32_t)carrier;}
   expected+=(uint64_t)value*(i+1);
   if(i<8){if(check(probe_record[i]&0xffffffffu,want32,"CG narrow argument register (W extended)",i))return 6;}
   else {
    unsigned k=i-8,size=k<2?1:k<4?2:4; uint32_t got=0; memcpy(&got,stack_bytes+offsets[k],size);
    uint32_t want=size==1?(uint8_t)want32:size==2?(uint16_t)want32:want32;
    if(check(got,want,"CG narrow stack value (natural size and offset)",i))return 6;
   }
  }
  if(check(sum,expected,"CG narrow -> C control",pattern))return 6;
 }
 void(*multi[])(uint64_t*,const uint64_t*,uint64_t,void*)={cg_multi_direct,cg_multi_indirect};
 for(unsigned indirect=0;indirect<2;indirect++)for(unsigned upper=0;upper<4;upper++)for(unsigned b=0;b<2;b++){
  uint64_t live[20],out[28],expected[28]={b,0x2345,0x3456,0x4567,b^1,UINT64_C(0x3ff0000000000000)};
  for(unsigned i=0;i<20;i++){live[i]=UINT64_C(0x8abc0123456789ef)+i*UINT64_C(0x100000001);expected[6+i]=live[i];}
  for(unsigned i=0;i<28;i++)out[i]=UINT64_C(0x3c3c3c3c3c3c3c3c);
  expected[26]=expected[27]=UINT64_C(0x3c3c3c3c3c3c3c3c);
  multi[indirect](out,live,uppers[upper]|b,dirty_multi_return);
  for(unsigned i=0;i<28;i++)if(check(out[i],expected[i],"CG multi-result/live lane",i))return 7;
 }
 printf("PASS %u value checks\n",checks);
 return 0;
}
"#);
    c
}

/// Every check the driver makes; the run must report exactly this many.
const EXPECTED_CHECKS: usize = 10 * 4 * 4 * 2 * 2 * 2 // modes: C control + CG
    + 12 * 4 * 2 * 2 // pressure: C + CG
    + 64 * 3 // packed stack: raw C, raw CG, C->CG call
    + 14 * (7 + 5) // narrow results: raw + clang callers
    + 4 * 16 * (12 + 1 + 14 + 1) // CG callers: probe lanes + control sums
    + 2 * 4 * 2 * 28; // multi-result lanes

#[test]
fn native_darwin_bool_and_narrow_boundaries_o0_through_o3() {
    let module = corpus();
    let dir = fresh_dir::create("trust-cg-darwin-bool-abi-");
    fs::write(dir.join("input.ir-debug"), format!("{module:#?}")).unwrap();
    fs::write(dir.join("driver.c"), driver()).unwrap();
    fs::write(dir.join("support.s"), ASSEMBLY).unwrap();
    let mut executed = 0;
    for level in boundary::LEVELS {
        let object = boundary::compile(&module, level)
            .unwrap_or_else(|error| panic!("{level:?}: {error}; retained {}", dir.display()));
        let object_path = dir.join(format!("{level:?}.o"));
        fs::write(&object_path, object).unwrap();
        let binary = dir.join(format!("{level:?}"));
        let link = process::command_output_with_timeout(
            Command::new("cc")
                .args(["-O2", "-fno-inline"])
                .arg(dir.join("driver.c"))
                .arg(dir.join("support.s"))
                .arg(&object_path)
                .arg("-o")
                .arg(&binary),
            process::codegen_link_timeout(),
        )
        .unwrap();
        assert!(
            !link.timed_out && link.output.status.success(),
            "{level:?} link: {}; retained {}",
            String::from_utf8_lossy(&link.output.stderr),
            dir.display()
        );
        let run =
            process::run_executable_with_timeout(&binary, process::codegen_run_timeout()).unwrap();
        let stdout = String::from_utf8_lossy(&run.output.stdout);
        assert!(
            !run.timed_out && run.output.status.success(),
            "{level:?}: status={} {stdout} {}; retained {}",
            run.output.status,
            String::from_utf8_lossy(&run.output.stderr),
            dir.display()
        );
        assert_eq!(
            stdout.trim(),
            format!("PASS {EXPECTED_CHECKS} value checks"),
            "{level:?}: incomplete native execution; retained {}",
            dir.display()
        );
        executed += EXPECTED_CHECKS;
    }
    fs::remove_dir_all(&dir).unwrap();
    println!("PASS {executed} DarwinPCS Bool/narrow boundary checks at O0-O3");
}
