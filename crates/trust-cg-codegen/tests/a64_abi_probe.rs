// a64_abi_probe.rs — AAPCS64 by-value struct / float ABI conformance ORACLE.
//
// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0
//
// # What this is
//
// The on-host analog of the clang C-ABI oracle that caught four x86 SysV
// aggregate-ABI bugs. This developer box is Intel, so native AArch64 EXECUTION
// is hardware-blocked, but the emitted machine code is just bytes: the
// `a64_interp` module DECODES and INTERPRETS it. This oracle compiles small
// callees that take a by-value struct / float argument (or return one), then —
// crucially — sets up the argument registers/stack INDEPENDENTLY per the AAPCS64
// SPEC (not by copying the bridge's own classification), runs the bridge-emitted
// callee, and checks it reads the AAPCS64-correct register.
//
// So a bridge that reads a Homogeneous Floating-point Aggregate (HFA) from
// x-registers instead of v-registers (the AArch64 twin of the x86 "SSE class in
// a GPR" bug), or that classifies a mixed {int,float} struct like SysV (float in
// a v-reg) rather than like AAPCS64 (whole struct in x-registers), is CAUGHT
// on-host and fails this test.
//
// # AAPCS64 rules exercised (Procedure Call Standard for the Arm 64-bit
//   Architecture, "Parameter passing", §6.8; Apple arm64 ABI):
//
//   * HFA (1-4 members, ALL the same FP type): each member in a consecutive
//     v-register of the member's class — S0.. for f32, D0.. for f64. NOT x-regs.
//   * A composite that is NOT an HFA and is <= 16 bytes: passed in consecutive
//     x-registers (NGRN), 8 bytes each — INCLUDING any float members. This is
//     the key divergence from x86 SysV, where a trailing f64 eightbyte would go
//     in an SSE register.
//   * A composite > 16 bytes: passed INDIRECTLY — the caller places it in memory
//     and passes a pointer in the next x-register.
//   * Once the 8 FP arg registers (v0-v7) are used, further FP args go on the
//     stack (at [caller_sp + offset]).
//   * A returned aggregate > 16 bytes uses the indirect result (sret) convention:
//     the caller passes a result buffer pointer in x8 and the callee stores the
//     result there.
//   * A zero-sized member (e.g. an empty inner aggregate) is transparent to HFA
//     classification and to layout.
//
// Every register the interpreter cannot model fails CLOSED (decode-or-reject),
// so this oracle can never give a false PASS by ignoring the instruction under
// test.

#![allow(clippy::all)]
mod common;
use common::a64_interp::{A64Interp, MachoText, extract_text, symbol_addrs, text_branch_relocs};
use trust_cg_codegen::compiler::{Compiler, CompilerConfig};
use trust_cg_codegen::pipeline::OptLevel;
use trust_cg_codegen::target::{Target, TargetSpec};
use trust_ir::{
    BinOp, Block as B, BlockId, CallingConv, CastOp, FieldDef, FuncId, FuncTy, FuncTyId,
    Function as F, Inst, InstrNode, Linkage, Module as M, StructDef, StructId, Ty, ValueId,
};

// --------------------------------------------------------------------------
// trust-ir module construction helpers
// --------------------------------------------------------------------------

fn node(inst: Inst, results: Vec<u32>) -> InstrNode {
    InstrNode {
        inst,
        results: results.into_iter().map(ValueId::new).collect(),
        proofs: vec![],
        span: None,
        proof_context: None,
        scope: None,
    }
}

fn struct_def(id: u32, name: &str, fields: &[Ty]) -> StructDef {
    StructDef {
        id: StructId::new(id),
        name: name.to_string(),
        fields: fields
            .iter()
            .enumerate()
            .map(|(i, ty)| FieldDef {
                name: format!("f{i}"),
                ty: ty.clone(),
                offset: None,
            })
            .collect(),
        size: None,
        align: None,
        repr: Default::default(),
    }
}

/// A minimal SSA function builder that hands out fresh value ids and records
/// InstrNodes.
struct Fb {
    nodes: Vec<InstrNode>,
    next: u32,
}
impl Fb {
    /// `first_free` is the first value id not already claimed by block params.
    fn new(first_free: u32) -> Self {
        Fb {
            nodes: vec![],
            next: first_free,
        }
    }
    fn emit1(&mut self, inst: Inst) -> ValueId {
        let id = self.next;
        self.next += 1;
        self.nodes.push(node(inst, vec![id]));
        ValueId::new(id)
    }
    fn emit0(&mut self, inst: Inst) {
        self.nodes.push(node(inst, vec![]));
    }
    /// Extract float field `field` (type `fty`) of aggregate `agg` (type
    /// `agg_ty`) and cast it to an i64 (truncating toward zero).
    fn float_field_as_i64(&mut self, agg_ty: &Ty, agg: ValueId, field: u32, fty: Ty) -> ValueId {
        let f = self.emit1(Inst::ExtractField {
            ty: agg_ty.clone(),
            aggregate: agg,
            field,
        });
        self.emit1(Inst::Cast {
            op: CastOp::FPToSI,
            src_ty: fty,
            dst_ty: Ty::I64,
            operand: f,
        })
    }
    /// Extract i64 field `field` of aggregate `agg`.
    fn int_field(&mut self, agg_ty: &Ty, agg: ValueId, field: u32) -> ValueId {
        self.emit1(Inst::ExtractField {
            ty: agg_ty.clone(),
            aggregate: agg,
            field,
        })
    }
    fn add(&mut self, a: ValueId, b: ValueId) -> ValueId {
        self.emit1(Inst::BinOp {
            op: BinOp::Add,
            ty: Ty::I64,
            lhs: a,
            rhs: b,
        })
    }
    fn ret(&mut self, v: ValueId) {
        self.emit0(Inst::Return { values: vec![v] });
    }
}

/// Assemble a module with a single function.
fn module(
    name: &str,
    structs: Vec<StructDef>,
    fty: FuncTy,
    fn_name: &str,
    params: Vec<(ValueId, Ty)>,
    body: Vec<InstrNode>,
) -> M {
    let mut m = M {
        name: name.into(),
        functions: vec![],
        structs,
        records: vec![],
        closure_types: vec![],
        globals: vec![],
        func_types: vec![fty],
        types: vec![],
        proof_obligations: vec![],
        proof_certificates: vec![],
        enums: vec![],
        target_info: None,
        files: vec![],
        obligation_diagnostics: vec![],
        spec_modules: vec![],
        universes: vec![],
        predicates: vec![],
    };
    m.functions.push(F {
        attrs: Default::default(),
        id: FuncId::new(0),
        name: fn_name.into(),
        ty: FuncTyId::new(0),
        entry: BlockId::new(0),
        blocks: vec![B {
            id: BlockId::new(0),
            params,
            body,
        }],
        proofs: vec![],
        calling_conv: CallingConv::default(),
        linkage: Linkage::default(),
        summary: None,
        producer: None,
        value_names: None,
        scopes: None,
        source_provenance: None,
    });
    m
}

fn compile(m: &M, opt: OptLevel) -> Vec<u8> {
    // Explicit Darwin spec: the interp harness parses Mach-O (`extract_text`
    // asserts MH_MAGIC_64), and the default target spec is host-OS-aware —
    // on a Linux host it would emit ELF. Cross-emission only, never linked or
    // executed natively; same pattern as e2e_x86_64_dispatcher's
    // compile_aarch64_darwin_module.
    let c = Compiler::new_for_target_spec(
        CompilerConfig {
            opt_level: opt,
            target: Target::Aarch64,
            ..CompilerConfig::default()
        },
        TargetSpec::parse("aarch64-apple-darwin").expect("parse aarch64-apple-darwin target spec"),
    );
    c.compile(m).expect("aarch64 compile").object_code
}

/// Build an interpreter over the compiled object's `__text` and return it plus
/// the entry offset of `sym`.
fn interp_for<'a>(obj: &'a [u8], sym: &str) -> (A64Interp, usize) {
    let text: MachoText = extract_text(obj);
    let addrs = symbol_addrs(obj);
    let entry = (*addrs.get(sym).unwrap_or_else(|| {
        panic!(
            "symbol {sym} not found; have {:?}",
            addrs.keys().collect::<Vec<_>>()
        )
    }) - text.addr) as usize;
    let it = A64Interp::new(text.bytes).with_branch_relocs(text_branch_relocs(obj));
    (it, entry)
}

const DATA_BASE: u64 = 0x0004_0000; // 256 KiB: above any tiny __text, below the 1 MiB stack top.
const DST_BASE: u64 = 0x0005_0000;
const STACK_TOP: u64 = 0x0010_0000; // must match a64_interp::STACK_TOP.
const POISON: u64 = 0xDEAD_BEEF_DEAD_BEEF;

fn write_i64(it: &mut A64Interp, addr: u64, val: u64) {
    for k in 0..8u64 {
        it.mem.insert(addr + k, (val >> (8 * k)) as u8);
    }
}
fn read_i64(it: &A64Interp, addr: u64) -> u64 {
    let mut v = 0u64;
    for k in 0..8u64 {
        v |= (*it.mem.get(&(addr + k)).unwrap_or(&0) as u64) << (8 * k);
    }
    v
}
fn write_f64(it: &mut A64Interp, addr: u64, val: f64) {
    write_i64(it, addr, val.to_bits());
}
/// Poison x0..x7 with a distinctive non-argument value: if a v-register argument
/// is (wrongly) read from a GPR, the result is garbage, not the expected value.
fn poison_gprs(it: &mut A64Interp) {
    for i in 0..8 {
        it.set_x(i, POISON ^ i as u64);
    }
}
/// Poison d0..d7: if a GPR argument is (wrongly) read from a v-register, garbage.
fn poison_fp(it: &mut A64Interp) {
    for i in 0..8 {
        it.set_d_bits(i, POISON ^ (0xF00 | i as u64));
    }
}

// --------------------------------------------------------------------------
// HFA argument shapes: members in consecutive v-registers of the member class.
// --------------------------------------------------------------------------

/// `fn callee(s: {f32, f32}) -> i64 { (s.0 as i64) + (s.1 as i64) }`
#[test]
fn hfa_f32x2_in_s0_s1() {
    let agg = Ty::Struct(StructId::new(0));
    let mut fb = Fb::new(1);
    let a = fb.float_field_as_i64(&agg, ValueId::new(0), 0, Ty::F32);
    let b = fb.float_field_as_i64(&agg, ValueId::new(0), 1, Ty::F32);
    let s = fb.add(a, b);
    fb.ret(s);
    let m = module(
        "hfa2",
        vec![struct_def(0, "Hfa2", &[Ty::F32, Ty::F32])],
        FuncTy {
            params: vec![agg.clone()],
            returns: vec![Ty::I64],
            is_vararg: false,
        },
        "_callee",
        vec![(ValueId::new(0), agg)],
        fb.nodes,
    );
    for opt in [OptLevel::O0, OptLevel::O2] {
        let obj = compile(&m, opt);
        let (mut it, entry) = interp_for(&obj, "__callee");
        poison_gprs(&mut it); // HFA must NOT be read from x-regs.
        it.set_s(0, 3.0);
        it.set_s(1, 5.0);
        let x0 = it.run(entry).unwrap_or_else(|e| panic!("{opt:?}: {e:?}"));
        assert_eq!(x0, 8, "{opt:?}: HFA {{f32,f32}} must come from S0/S1");
    }
}

/// `fn callee(s: {f64, f64}) -> i64` — members in D0, D1.
#[test]
fn hfa_f64x2_in_d0_d1() {
    let agg = Ty::Struct(StructId::new(0));
    let mut fb = Fb::new(1);
    let a = fb.float_field_as_i64(&agg, ValueId::new(0), 0, Ty::F64);
    let b = fb.float_field_as_i64(&agg, ValueId::new(0), 1, Ty::F64);
    let s = fb.add(a, b);
    fb.ret(s);
    let m = module(
        "hfa2d",
        vec![struct_def(0, "Hfa2d", &[Ty::F64, Ty::F64])],
        FuncTy {
            params: vec![agg.clone()],
            returns: vec![Ty::I64],
            is_vararg: false,
        },
        "_callee",
        vec![(ValueId::new(0), agg)],
        fb.nodes,
    );
    for opt in [OptLevel::O0, OptLevel::O2] {
        let obj = compile(&m, opt);
        let (mut it, entry) = interp_for(&obj, "__callee");
        poison_gprs(&mut it);
        it.set_d(0, 100.0);
        it.set_d(1, 23.0);
        let x0 = it.run(entry).unwrap_or_else(|e| panic!("{opt:?}: {e:?}"));
        assert_eq!(x0, 123, "{opt:?}: HFA {{f64,f64}} must come from D0/D1");
    }
}

/// `fn callee(s: {f32, f32, f32, f32}) -> i64` — members in S0..S3 (4 = max HFA).
#[test]
fn hfa_f32x4_in_s0_s3() {
    let agg = Ty::Struct(StructId::new(0));
    let mut fb = Fb::new(1);
    let mut acc = fb.float_field_as_i64(&agg, ValueId::new(0), 0, Ty::F32);
    for field in 1..4 {
        let f = fb.float_field_as_i64(&agg, ValueId::new(0), field, Ty::F32);
        acc = fb.add(acc, f);
    }
    fb.ret(acc);
    let m = module(
        "hfa4",
        vec![struct_def(0, "Hfa4", &[Ty::F32, Ty::F32, Ty::F32, Ty::F32])],
        FuncTy {
            params: vec![agg.clone()],
            returns: vec![Ty::I64],
            is_vararg: false,
        },
        "_callee",
        vec![(ValueId::new(0), agg)],
        fb.nodes,
    );
    for opt in [OptLevel::O0, OptLevel::O2] {
        let obj = compile(&m, opt);
        let (mut it, entry) = interp_for(&obj, "__callee");
        poison_gprs(&mut it);
        it.set_s(0, 1.0);
        it.set_s(1, 2.0);
        it.set_s(2, 3.0);
        it.set_s(3, 4.0);
        let x0 = it.run(entry).unwrap_or_else(|e| panic!("{opt:?}: {e:?}"));
        assert_eq!(x0, 10, "{opt:?}: HFA {{f32;4}} must come from S0..S3");
    }
}

/// `fn callee(s: {f64, f64, f64}) -> i64` — members in D0..D2.
#[test]
fn hfa_f64x3_in_d0_d2() {
    let agg = Ty::Struct(StructId::new(0));
    let mut fb = Fb::new(1);
    let mut acc = fb.float_field_as_i64(&agg, ValueId::new(0), 0, Ty::F64);
    for field in 1..3 {
        let f = fb.float_field_as_i64(&agg, ValueId::new(0), field, Ty::F64);
        acc = fb.add(acc, f);
    }
    fb.ret(acc);
    let m = module(
        "hfa3d",
        vec![struct_def(0, "Hfa3d", &[Ty::F64, Ty::F64, Ty::F64])],
        FuncTy {
            params: vec![agg.clone()],
            returns: vec![Ty::I64],
            is_vararg: false,
        },
        "_callee",
        vec![(ValueId::new(0), agg)],
        fb.nodes,
    );
    for opt in [OptLevel::O0, OptLevel::O2] {
        let obj = compile(&m, opt);
        let (mut it, entry) = interp_for(&obj, "__callee");
        poison_gprs(&mut it);
        it.set_d(0, 10.0);
        it.set_d(1, 20.0);
        it.set_d(2, 30.0);
        let x0 = it.run(entry).unwrap_or_else(|e| panic!("{opt:?}: {e:?}"));
        assert_eq!(x0, 60, "{opt:?}: HFA {{f64;3}} must come from D0..D2");
    }
}

// --------------------------------------------------------------------------
// Mixed (non-HFA) small composites: whole struct in x-registers, 8 bytes each,
// INCLUDING float members. The AAPCS64-vs-SysV divergence.
// --------------------------------------------------------------------------

/// `fn callee(s: {i64, f64}) -> i64 { s.0 + (s.1 as i64) }`
/// AAPCS64: i64 in x0, the f64 in x1 (NOT a v-register).
#[test]
fn mixed_i64_f64_in_x0_x1() {
    let agg = Ty::Struct(StructId::new(0));
    let mut fb = Fb::new(1);
    let a = fb.int_field(&agg, ValueId::new(0), 0);
    let b = fb.float_field_as_i64(&agg, ValueId::new(0), 1, Ty::F64);
    let s = fb.add(a, b);
    fb.ret(s);
    let m = module(
        "mix_if",
        vec![struct_def(0, "MixIF", &[Ty::I64, Ty::F64])],
        FuncTy {
            params: vec![agg.clone()],
            returns: vec![Ty::I64],
            is_vararg: false,
        },
        "_callee",
        vec![(ValueId::new(0), agg)],
        fb.nodes,
    );
    for opt in [OptLevel::O0, OptLevel::O2] {
        let obj = compile(&m, opt);
        let (mut it, entry) = interp_for(&obj, "__callee");
        poison_fp(&mut it); // the f64 field must come from x1, NOT d0.
        it.set_x(0, 1000);
        it.set_x(1, 7.0f64.to_bits());
        let x0 = it.run(entry).unwrap_or_else(|e| panic!("{opt:?}: {e:?}"));
        assert_eq!(
            x0, 1007,
            "{opt:?}: mixed {{i64,f64}} f64 must come from x1 (AAPCS64, not SysV)"
        );
    }
}

/// `fn callee(s: {f64, i64}) -> i64` — f64 in x0, i64 in x1.
#[test]
fn mixed_f64_i64_in_x0_x1() {
    let agg = Ty::Struct(StructId::new(0));
    let mut fb = Fb::new(1);
    let a = fb.float_field_as_i64(&agg, ValueId::new(0), 0, Ty::F64);
    let b = fb.int_field(&agg, ValueId::new(0), 1);
    let s = fb.add(a, b);
    fb.ret(s);
    let m = module(
        "mix_fi",
        vec![struct_def(0, "MixFI", &[Ty::F64, Ty::I64])],
        FuncTy {
            params: vec![agg.clone()],
            returns: vec![Ty::I64],
            is_vararg: false,
        },
        "_callee",
        vec![(ValueId::new(0), agg)],
        fb.nodes,
    );
    for opt in [OptLevel::O0, OptLevel::O2] {
        let obj = compile(&m, opt);
        let (mut it, entry) = interp_for(&obj, "__callee");
        poison_fp(&mut it); // the f64 field must come from x0, NOT d0.
        it.set_x(0, 9.0f64.to_bits());
        it.set_x(1, 500);
        let x0 = it.run(entry).unwrap_or_else(|e| panic!("{opt:?}: {e:?}"));
        assert_eq!(x0, 509, "{opt:?}: mixed {{f64,i64}} f64 must come from x0");
    }
}

/// `fn callee(s: {i64, i64}) -> i64` — small all-int struct in x0, x1.
#[test]
fn small_i64x2_in_x0_x1() {
    let agg = Ty::Struct(StructId::new(0));
    let mut fb = Fb::new(1);
    let a = fb.int_field(&agg, ValueId::new(0), 0);
    let b = fb.int_field(&agg, ValueId::new(0), 1);
    let s = fb.add(a, b);
    fb.ret(s);
    let m = module(
        "si2",
        vec![struct_def(0, "Si2", &[Ty::I64, Ty::I64])],
        FuncTy {
            params: vec![agg.clone()],
            returns: vec![Ty::I64],
            is_vararg: false,
        },
        "_callee",
        vec![(ValueId::new(0), agg)],
        fb.nodes,
    );
    for opt in [OptLevel::O0, OptLevel::O2] {
        let obj = compile(&m, opt);
        let (mut it, entry) = interp_for(&obj, "__callee");
        poison_fp(&mut it);
        it.set_x(0, 40);
        it.set_x(1, 2);
        let x0 = it.run(entry).unwrap_or_else(|e| panic!("{opt:?}: {e:?}"));
        assert_eq!(x0, 42, "{opt:?}: small {{i64,i64}} in x0,x1");
    }
}

// --------------------------------------------------------------------------
// Large composite (> 16 bytes) argument: indirect via a pointer in x0.
// --------------------------------------------------------------------------

/// `fn callee(s: {i64, i64, i64}) -> i64 { s.0 + s.1 + s.2 }` — 24 bytes, indirect.
#[test]
fn large_i64x3_indirect_ptr_in_x0() {
    let agg = Ty::Struct(StructId::new(0));
    let mut fb = Fb::new(1);
    let mut acc = fb.int_field(&agg, ValueId::new(0), 0);
    for field in 1..3 {
        let f = fb.int_field(&agg, ValueId::new(0), field);
        acc = fb.add(acc, f);
    }
    fb.ret(acc);
    let m = module(
        "big3",
        vec![struct_def(0, "Big3", &[Ty::I64, Ty::I64, Ty::I64])],
        FuncTy {
            params: vec![agg.clone()],
            returns: vec![Ty::I64],
            is_vararg: false,
        },
        "_callee",
        vec![(ValueId::new(0), agg)],
        fb.nodes,
    );
    for opt in [OptLevel::O0, OptLevel::O2] {
        let obj = compile(&m, opt);
        let (mut it, entry) = interp_for(&obj, "__callee");
        poison_fp(&mut it);
        // AAPCS64: the caller places the aggregate in memory and passes a pointer.
        write_i64(&mut it, DATA_BASE, 7);
        write_i64(&mut it, DATA_BASE + 8, 8);
        write_i64(&mut it, DATA_BASE + 16, 9);
        it.set_x(0, DATA_BASE);
        let x0 = it.run(entry).unwrap_or_else(|e| panic!("{opt:?}: {e:?}"));
        assert_eq!(
            x0, 24,
            "{opt:?}: >16B struct passed indirect via pointer in x0"
        );
    }
}

// --------------------------------------------------------------------------
// FP argument-register exhaustion: the 9th f64 spills to the stack.
// --------------------------------------------------------------------------

/// `fn callee(a0..a8: f64) -> i64 { (a0 + .. + a8) as i64 }` — 9 f64 params:
/// a0..a7 in D0..D7, a8 on the stack at [caller_sp + 0].
#[test]
fn fp_arg_exhaustion_ninth_on_stack() {
    let params: Vec<(ValueId, Ty)> = (0..9).map(|i| (ValueId::new(i), Ty::F64)).collect();
    let mut fb = Fb::new(9);
    // cast each param to i64, then sum.
    let mut casts = Vec::new();
    for i in 0..9u32 {
        casts.push(fb.emit1(Inst::Cast {
            op: CastOp::FPToSI,
            src_ty: Ty::F64,
            dst_ty: Ty::I64,
            operand: ValueId::new(i),
        }));
    }
    let mut acc = casts[0];
    for c in &casts[1..] {
        acc = fb.add(acc, *c);
    }
    fb.ret(acc);
    let m = module(
        "fpx9",
        vec![],
        FuncTy {
            params: vec![Ty::F64; 9],
            returns: vec![Ty::I64],
            is_vararg: false,
        },
        "_callee",
        params,
        fb.nodes,
    );
    for opt in [OptLevel::O0, OptLevel::O2] {
        let obj = compile(&m, opt);
        let (mut it, entry) = interp_for(&obj, "__callee");
        for i in 0..8 {
            it.set_d(i, (i + 1) as f64); // 1..8 in D0..D7
        }
        // 9th f64 (value 9.0) on the incoming stack at [caller_sp + 0] == STACK_TOP.
        write_f64(&mut it, STACK_TOP, 9.0);
        let x0 = it.run(entry).unwrap_or_else(|e| panic!("{opt:?}: {e:?}"));
        assert_eq!(
            x0, 45,
            "{opt:?}: 9th f64 must be read from the stack (D0-D7 exhausted)"
        );
    }
}

// --------------------------------------------------------------------------
// Indirect result (sret): a returned aggregate > 16 bytes goes to [x8].
// --------------------------------------------------------------------------

/// `fn callee(s: {i64, i64, i64}) -> {i64, i64, i64} { s }` — the 24-byte struct
/// comes in indirect (pointer in x0) and is returned via the sret pointer in x8.
#[test]
fn sret_large_struct_via_x8() {
    let agg = Ty::Struct(StructId::new(0));
    let body = vec![node(
        Inst::Return {
            values: vec![ValueId::new(0)],
        },
        vec![],
    )];
    let m = module(
        "sret3",
        vec![struct_def(0, "Sret3", &[Ty::I64, Ty::I64, Ty::I64])],
        FuncTy {
            params: vec![agg.clone()],
            returns: vec![agg.clone()],
            is_vararg: false,
        },
        "_callee",
        vec![(ValueId::new(0), agg)],
        body,
    );
    for opt in [OptLevel::O0, OptLevel::O2] {
        let obj = compile(&m, opt);
        let (mut it, entry) = interp_for(&obj, "__callee");
        poison_fp(&mut it);
        write_i64(&mut it, DATA_BASE, 11);
        write_i64(&mut it, DATA_BASE + 8, 22);
        write_i64(&mut it, DATA_BASE + 16, 33);
        it.set_x(0, DATA_BASE); // incoming struct pointer (indirect arg)
        it.set_x(8, DST_BASE); // sret result buffer pointer
        let _ = it.run(entry).unwrap_or_else(|e| panic!("{opt:?}: {e:?}"));
        assert_eq!(read_i64(&it, DST_BASE), 11, "{opt:?}: sret[0] via x8");
        assert_eq!(read_i64(&it, DST_BASE + 8), 22, "{opt:?}: sret[1] via x8");
        assert_eq!(read_i64(&it, DST_BASE + 16), 33, "{opt:?}: sret[2] via x8");
    }
}

// --------------------------------------------------------------------------
// Zero-sized member transparency: an empty inner aggregate does not disturb HFA
// classification. `{f32, {}, f32}` is still an HFA {f32;2} in S0, S1.
// --------------------------------------------------------------------------

/// `fn callee(s: {f32, {}, f32}) -> i64 { (s.0 as i64) + (s.2 as i64) }`.
#[test]
fn hfa_with_zst_member_still_in_s0_s1() {
    let agg = Ty::Struct(StructId::new(0));
    let mut fb = Fb::new(1);
    let a = fb.float_field_as_i64(&agg, ValueId::new(0), 0, Ty::F32);
    // field 1 is the empty inner struct (ZST); the second float is field 2.
    let b = fb.float_field_as_i64(&agg, ValueId::new(0), 2, Ty::F32);
    let s = fb.add(a, b);
    fb.ret(s);
    let m = module(
        "hfazst",
        vec![
            struct_def(1, "Empty", &[]),
            struct_def(
                0,
                "HfaZst",
                &[Ty::F32, Ty::Struct(StructId::new(1)), Ty::F32],
            ),
        ],
        FuncTy {
            params: vec![agg.clone()],
            returns: vec![Ty::I64],
            is_vararg: false,
        },
        "_callee",
        vec![(ValueId::new(0), agg)],
        fb.nodes,
    );
    for opt in [OptLevel::O0, OptLevel::O2] {
        let obj = compile(&m, opt);
        let (mut it, entry) = interp_for(&obj, "__callee");
        poison_gprs(&mut it);
        it.set_s(0, 2.0);
        it.set_s(1, 5.0);
        let x0 = it.run(entry).unwrap_or_else(|e| panic!("{opt:?}: {e:?}"));
        assert_eq!(
            x0, 7,
            "{opt:?}: HFA with a ZST member still comes from S0/S1"
        );
    }
}
