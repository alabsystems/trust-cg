// Copyright 2026 Andrew Yates | Apache-2.0
//! Shared TrustIR corpus and C driver for the AArch64 hidden-result (`sret`)
//! native controls (`e2e_aarch64_sret.rs` on Darwin,
//! `e2e_aarch64_sret_linux.rs` on Linux); ledger L01-P5.
//!
//! A C function returning a 40-byte non-homogeneous struct receives the
//! result address in X8 (AAPCS64 §6.9 indirect result location register),
//! outside the X0-X7 argument bank, so its ordinary arguments are numbered as
//! if the hidden pointer did not exist. TrustIR states that convention in two
//! shapes and both must produce byte-identical machine conventions:
//!
//! * structural: `returns: [Struct(Big)]`, which the target ABI classifies
//!   indirect. The FUNCTION TYPE itself carries the identity, so a pointer that
//!   flows dynamically (a C function pointer passed as a parameter) can be
//!   called through it;
//! * pre-lowered: `params: [Ptr sret, ...], returns: []`, the frontend-lowered
//!   form carried by `ParamAttrs::sret` on the DECLARATION. The pinned trust-ir
//!   has no attribute slot on a `FuncTy` and none on a `CallIndirect`, so the
//!   adapter establishes an indirect call's identity only through trust-ir's
//!   own typed provenance (`Const FnDef` reached through `Copy` /
//!   `ReifyFnPointer`) to such a declaration, and refuses an edge that
//!   disagrees with it.
//!
//! Every callee takes nine integer, nine floating-point and two narrow
//! arguments, so one integer, one double and both narrow arguments are passed
//! on the stack, and the CG callee calls a C helper while every argument is
//! still live, so the hidden pointer and the arguments must survive X8 and the
//! caller-saved bank being clobbered. The narrow stack arguments are where the
//! two conventions the corpus is compiled for differ: DarwinPCS packs them at
//! 4-byte offsets, base AAPCS64 (Arm IHI 0055 §6.8.2 stage C rule C.16 in the
//! current Arm numbering: an argument smaller than 8 bytes has its size set to
//! 8 bytes) gives each an 8-byte slot; the corpus states only the TrustIR
//! types and each host test links against its own C compiler, so the
//! placement rule is exercised by execution on both hosts. The driver's
//! success lines name the oracle through the `ORACLE` macro (`clang` unless
//! the including test defines it).
//!
//! Execution evidence, not proof of the hidden-result convention.
#![allow(dead_code)]

use trust_ir::{
    BinOp, Block, BlockId, CallingConv, CastOp, Constant, Endianness, FieldDef, FuncId, FuncTy,
    FuncTyId, Function, Inst, InstrNode, Linkage, Module, ParamAttrs, StructDef, StructId,
    StructPassingPolicy, StructRepr, TargetInfo, Ty, ValueId,
};

pub const INTS: usize = 9;
pub const FLOATS: usize = 9;
pub const NARROWS: usize = 2;
pub const ARGS: usize = INTS + FLOATS + NARROWS;

/// Functions [`build_callee_module`] defines, in definition order, and the
/// C helper it imports.
pub const CALLEE_SYMBOLS: &[&str] = &["cg_sret_attr", "cg_sret_struct"];
pub const CALLEE_IMPORTS: &[&str] = &["mix64"];

/// Functions [`build_caller_module`] defines, in definition order, and the C
/// callees it imports.
pub const CALLER_SYMBOLS: &[&str] = &[
    "cg_call_attr_fp",
    "cg_call_struct_fp",
    "cg_call_attr_va",
    "cg_call_struct_va",
];
pub const CALLER_IMPORTS: &[&str] = &["c_big_attr", "c_big_va_attr", "c_big_va_struct"];

/// The caller whose `CallIndirect` resolves, through `Const FnDef`, to the
/// pre-lowered declaration [`STATIC_PROVENANCE_CALLEE`]: it must stay an
/// indirect call (`BLR` with the buffer in X8), never a devirtualized `BL`.
pub const STATIC_PROVENANCE_CALLER: &str = "cg_call_attr_fp";
pub const STATIC_PROVENANCE_CALLEE: &str = "c_big_attr";

pub fn new_module(triple: &str, name: &str) -> Module {
    let mut module = Module::new(name);
    module.target_info = Some(TargetInfo {
        triple: triple.into(),
        pointer_size: 8,
        endianness: Endianness::Little,
        abi: Some("aapcs64".into()),
        struct_passing: StructPassingPolicy::NativeC,
    });
    module
}

/// `struct Big { int64_t i; double d; int64_t j; double e; int32_t m0; int32_t m1; }`:
/// 40 bytes, 8-aligned, not a homogeneous aggregate, so the result is indirect.
pub fn define_big(module: &mut Module) -> Ty {
    let id = StructId::new(module.structs.len() as u32);
    let fields = [
        ("i", Ty::I64, 0),
        ("d", Ty::F64, 8),
        ("j", Ty::I64, 16),
        ("e", Ty::F64, 24),
        ("m0", Ty::I32, 32),
        ("m1", Ty::I32, 36),
    ];
    module.structs.push(StructDef {
        origin: None,
        id,
        name: "Big".into(),
        size: Some(40),
        align: Some(8),
        repr: StructRepr::C,
        fields: fields
            .iter()
            .map(|(name, ty, offset)| FieldDef {
                name: (*name).into(),
                ty: ty.clone(),
                offset: Some(*offset),
            })
            .collect(),
    });
    Ty::Struct(id)
}

/// The ordinary argument list every callee takes: nine `int64_t`, nine
/// `double`, two `int32_t`.
pub fn ordinary_params() -> Vec<Ty> {
    let mut params = vec![Ty::I64; INTS];
    params.extend(vec![Ty::F64; FLOATS]);
    params.extend(vec![Ty::I32; NARROWS]);
    params
}

pub fn add_sig(
    module: &mut Module,
    params: Vec<Ty>,
    returns: Vec<Ty>,
    is_vararg: bool,
) -> FuncTyId {
    module
        .add_func_type(FuncTy {
            params,
            returns,
            abi: None,
            is_vararg,
        })
        .expect("Module::add_func_type: test fixture")
}

/// Declare an external C function; `sret` marks parameter 0 as the hidden
/// return buffer (the pre-lowered shape).
pub fn declare(module: &mut Module, name: &str, sig: FuncTyId, sret: bool) -> FuncId {
    let id = FuncId::new(module.functions.len() as u32);
    let mut function = Function::new(id, name, sig, BlockId::new(0));
    function.linkage = Linkage::External;
    function.blocks = Vec::new();
    if sret {
        let arity = module.func_types[sig.index() as usize].params.len();
        function.attrs.params = vec![ParamAttrs::default(); arity];
        function.attrs.params[0].sret = true;
    }
    module
        .try_add_function(function)
        .expect("Module::try_add_function: test fixture");
    id
}

/// SSA body builder with a fresh-value counter.
pub struct Body {
    pub body: Vec<InstrNode>,
    pub next: u32,
}

impl Body {
    pub fn new(first_free: u32) -> Self {
        Self {
            body: Vec::new(),
            next: first_free,
        }
    }

    pub fn fresh(&mut self) -> ValueId {
        let value = ValueId::new(self.next);
        self.next += 1;
        value
    }

    pub fn emit(&mut self, inst: Inst) -> ValueId {
        let result = self.fresh();
        self.body.push(InstrNode::new(inst).with_result(result));
        result
    }

    pub fn emit_void(&mut self, inst: Inst) {
        self.body.push(InstrNode::new(inst));
    }

    pub fn binop(&mut self, op: BinOp, ty: Ty, lhs: ValueId, rhs: ValueId) -> ValueId {
        self.emit(Inst::BinOp { op, ty, lhs, rhs })
    }

    pub fn cast(&mut self, op: CastOp, src_ty: Ty, dst_ty: Ty, operand: ValueId) -> ValueId {
        self.emit(Inst::Cast {
            op,
            src_ty,
            dst_ty,
            operand,
        })
    }

    /// Compute the `Big` value every oracle expects from the argument values
    /// `args` (`[a0..a8, d0..d8, n0, n1]`), calling `mix64` FIRST so that every
    /// argument, and the caller's hidden pointer, stays live across a call
    /// that clobbers X8 and the whole caller-saved bank.
    pub fn big_value(&mut self, big: &Ty, mix64: FuncId, args: &[ValueId]) -> ValueId {
        assert_eq!(args.len(), ARGS);
        let a = &args[..INTS];
        let d = &args[INTS..INTS + FLOATS];
        let n = &args[INTS + FLOATS..];
        let mixed = self.emit(Inst::Call {
            callee: mix64,
            args: vec![a[1], a[7]],
        });
        // i = a0 + a2 + a4 + a6 + a8 (left-associated, like the C oracle).
        let mut i = a[0];
        for k in [2, 4, 6, 8] {
            i = self.binop(BinOp::Add, Ty::I64, i, a[k]);
        }
        let mut dsum = d[0];
        for k in [2, 4, 6, 8] {
            dsum = self.binop(BinOp::FAdd, Ty::F64, dsum, d[k]);
        }
        let j = self.binop(BinOp::Add, Ty::I64, mixed, a[3]);
        let j = self.binop(BinOp::Add, Ty::I64, j, a[5]);
        let mut e = d[1];
        for k in [3, 5, 7] {
            e = self.binop(BinOp::FAdd, Ty::F64, e, d[k]);
        }
        let m0 = self.binop(BinOp::Add, Ty::I32, n[0], n[1]);
        let m1 = self.binop(BinOp::Sub, Ty::I32, n[1], n[0]);
        self.big_from_lanes(big, [i, dsum, j, e, m0, m1])
    }

    /// Assemble a `Big` from its six lane values: an all-constant seed, then
    /// one InsertField per lane (the adapter refuses `Inst::Undef` for
    /// aggregates rather than invent a value).
    pub fn big_from_lanes(&mut self, big: &Ty, lanes: [ValueId; 6]) -> ValueId {
        let mut value = self.emit(Inst::Const {
            ty: big.clone(),
            value: Constant::Aggregate(vec![
                Constant::Int(0),
                Constant::Float(0.0),
                Constant::Int(0),
                Constant::Float(0.0),
                Constant::Int(0),
                Constant::Int(0),
            ]),
        });
        for (field, lane) in lanes.into_iter().enumerate() {
            value = self.emit(Inst::InsertField {
                ty: big.clone(),
                aggregate: value,
                field: field as u32,
                value: lane,
            });
        }
        value
    }

    pub fn store_big(&mut self, big: &Ty, ptr: ValueId, value: ValueId) {
        self.emit_void(Inst::Store {
            ty: big.clone(),
            ptr,
            value,
            volatile: false,
            align: Some(8),
        });
    }
}

pub fn define(
    module: &mut Module,
    name: &str,
    sig: FuncTyId,
    params: Vec<(ValueId, Ty)>,
    body: Body,
) {
    let id = FuncId::new(module.functions.len() as u32);
    let mut function = Function::new(id, name, sig, BlockId::new(0));
    function.blocks = vec![Block {
        id: BlockId::new(0),
        params,
        body: body.body,
    }];
    module
        .try_add_function(function)
        .expect("Module::try_add_function: test fixture");
}

/// [`define`] for the pre-lowered shape: parameter 0 is the hidden return
/// buffer (`ParamAttrs::sret`) of a definition with an empty return list.
pub fn define_sret(
    module: &mut Module,
    name: &str,
    sig: FuncTyId,
    params: Vec<(ValueId, Ty)>,
    body: Body,
) {
    let id = FuncId::new(module.functions.len() as u32);
    let mut function = Function::new(id, name, sig, BlockId::new(0));
    function.attrs.params = vec![ParamAttrs::default(); params.len()];
    function.attrs.params[0].sret = true;
    function.blocks = vec![Block {
        id: BlockId::new(0),
        params,
        body: body.body,
    }];
    module
        .try_add_function(function)
        .expect("Module::try_add_function: test fixture");
}

pub fn params_from(tys: &[Ty]) -> Vec<(ValueId, Ty)> {
    tys.iter()
        .enumerate()
        .map(|(index, ty)| (ValueId::new(index as u32), ty.clone()))
        .collect()
}

pub fn values(range: std::ops::Range<u32>) -> Vec<ValueId> {
    range.map(ValueId::new).collect()
}

pub fn declare_mix64(module: &mut Module) -> FuncId {
    let sig = add_sig(module, vec![Ty::I64, Ty::I64], vec![Ty::I64], false);
    declare(module, "mix64", sig, false)
}

/// CG callees for a C caller: `cg_sret_attr` (pre-lowered shape) and
/// `cg_sret_struct` (structural shape). C declares both as
/// `struct Big f(9 x int64_t, 9 x double, 2 x int32_t)`.
pub fn build_callee_module(triple: &str) -> Module {
    let mut module = new_module(triple, "sret_callees");
    let big = define_big(&mut module);
    let mix64 = declare_mix64(&mut module);

    let mut attr_params = vec![Ty::Ptr];
    attr_params.extend(ordinary_params());
    let attr_sig = add_sig(&mut module, attr_params.clone(), vec![], false);
    let mut body = Body::new(attr_params.len() as u32);
    let value = body.big_value(&big, mix64, &values(1..1 + ARGS as u32));
    body.store_big(&big, ValueId::new(0), value);
    body.emit_void(Inst::Return { values: vec![] });
    define_sret(
        &mut module,
        "cg_sret_attr",
        attr_sig,
        params_from(&attr_params),
        body,
    );

    let struct_params = ordinary_params();
    let struct_sig = add_sig(&mut module, struct_params.clone(), vec![big.clone()], false);
    let mut body = Body::new(struct_params.len() as u32);
    let value = body.big_value(&big, mix64, &values(0..ARGS as u32));
    body.emit_void(Inst::Return {
        values: vec![value],
    });
    define(
        &mut module,
        "cg_sret_struct",
        struct_sig,
        params_from(&struct_params),
        body,
    );
    module
}

/// CG callers of C callees, each writing the C result into `out`:
///
/// * `cg_call_attr_fp(out, args...)`: `CallIndirect` through a `Const FnDef`
///   of the pre-lowered declaration `c_big_attr` (a `BLR` whose X8 is `out`);
/// * `cg_call_struct_fp(fp, out, args...)`: `CallIndirect` through the pointer
///   C passed, typed structurally (`returns: [Big]`);
/// * `cg_call_attr_va(out, args...)`: direct variadic call to the pre-lowered
///   declaration `c_big_va_attr(sret, int n, ...)`;
/// * `cg_call_struct_va(out, args...)`: direct variadic call to the structural
///   declaration `struct Big c_big_va_struct(int n, ...)`.
pub fn build_caller_module(triple: &str) -> Module {
    let mut module = new_module(triple, "sret_callers");
    let big = define_big(&mut module);

    let mut attr_params = vec![Ty::Ptr];
    attr_params.extend(ordinary_params());
    let attr_sig = add_sig(&mut module, attr_params.clone(), vec![], false);
    let c_big_attr = declare(&mut module, STATIC_PROVENANCE_CALLEE, attr_sig, true);
    let struct_sig = add_sig(&mut module, ordinary_params(), vec![big.clone()], false);
    let va_attr_sig = add_sig(&mut module, vec![Ty::Ptr, Ty::I32], vec![], true);
    let c_big_va_attr = declare(&mut module, "c_big_va_attr", va_attr_sig, true);
    let va_struct_sig = add_sig(&mut module, vec![Ty::I32], vec![big.clone()], true);
    let c_big_va_struct = declare(&mut module, "c_big_va_struct", va_struct_sig, false);

    // cg_call_attr_fp(out, args...)
    let mut body = Body::new(attr_params.len() as u32);
    let fp = body.emit(Inst::Const {
        ty: Ty::Func(attr_sig),
        value: Constant::FnDef(c_big_attr),
    });
    let mut args = vec![ValueId::new(0)];
    args.extend(values(1..1 + ARGS as u32));
    body.emit_void(Inst::CallIndirect {
        callee: fp,
        sig: attr_sig,
        args,
        calling_conv: CallingConv::C,
    });
    body.emit_void(Inst::Return { values: vec![] });
    define(
        &mut module,
        STATIC_PROVENANCE_CALLER,
        attr_sig,
        params_from(&attr_params),
        body,
    );

    // cg_call_struct_fp(fp, out, args...)
    let mut fp_params = vec![Ty::Ptr, Ty::Ptr];
    fp_params.extend(ordinary_params());
    let fp_sig = add_sig(&mut module, fp_params.clone(), vec![], false);
    let mut body = Body::new(fp_params.len() as u32);
    let result = body.emit(Inst::CallIndirect {
        callee: ValueId::new(0),
        sig: struct_sig,
        args: values(2..2 + ARGS as u32),
        calling_conv: CallingConv::C,
    });
    body.store_big(&big, ValueId::new(1), result);
    body.emit_void(Inst::Return { values: vec![] });
    define(
        &mut module,
        "cg_call_struct_fp",
        fp_sig,
        params_from(&fp_params),
        body,
    );

    // cg_call_attr_va(out, args...)
    let mut body = Body::new(attr_params.len() as u32);
    let count = body.emit(Inst::Const {
        ty: Ty::I32,
        value: Constant::Int(ARGS as i128),
    });
    let mut args = vec![ValueId::new(0), count];
    args.extend(values(1..1 + ARGS as u32));
    body.emit_void(Inst::Call {
        callee: c_big_va_attr,
        args,
    });
    body.emit_void(Inst::Return { values: vec![] });
    define(
        &mut module,
        "cg_call_attr_va",
        attr_sig,
        params_from(&attr_params),
        body,
    );

    // cg_call_struct_va(out, args...)
    let mut body = Body::new(attr_params.len() as u32);
    let count = body.emit(Inst::Const {
        ty: Ty::I32,
        value: Constant::Int(ARGS as i128),
    });
    let mut args = vec![count];
    args.extend(values(1..1 + ARGS as u32));
    let result = body.emit(Inst::Call {
        callee: c_big_va_struct,
        args,
    });
    body.store_big(&big, ValueId::new(0), result);
    body.emit_void(Inst::Return { values: vec![] });
    define(
        &mut module,
        "cg_call_struct_va",
        attr_sig,
        params_from(&attr_params),
        body,
    );
    module
}

/// A module whose only function calls `callee` (declared with `attrs`) with
/// `call_sig` through a `ReifyFnPointer`-cast pointer.
pub fn indirect_edge_module(
    triple: &str,
    declared: (Vec<Ty>, Vec<Ty>, bool),
    attrs: impl FnOnce(&mut Vec<ParamAttrs>),
    edge: (Vec<Ty>, Vec<Ty>, bool),
    results: usize,
) -> Module {
    let mut module = new_module(triple, "sret_edge");
    let declared_returns = declared.1.clone();
    let declared_sig = add_sig(&mut module, declared.0.clone(), declared.1, declared.2);
    let callee = declare(&mut module, "callee", declared_sig, false);
    let mut params = vec![ParamAttrs::default(); declared.0.len()];
    attrs(&mut params);
    module.functions[callee.index() as usize].attrs.params = params;
    // An edge that states the declaration's exact signature names the
    // declaration's signature id: trust-ir compares signature ids nominally
    // (`CallEdgeSignatureMismatch` between two equal copies), and every
    // ingestion entry refuses what the validator refuses (WS7.3).
    let edge_sig = if (&edge.0, &edge.1, edge.2) == (&declared.0, &declared_returns, declared.2) {
        declared_sig
    } else {
        add_sig(&mut module, edge.0.clone(), edge.1, edge.2)
    };
    let caller_sig = add_sig(&mut module, edge.0.clone(), vec![], false);
    let mut body = Body::new(edge.0.len() as u32);
    let fp = body.emit(Inst::Const {
        ty: Ty::Func(declared_sig),
        value: Constant::FnDef(callee),
    });
    let raw = body.emit(Inst::Cast {
        op: CastOp::ReifyFnPointer,
        src_ty: Ty::Func(declared_sig),
        dst_ty: Ty::Ptr,
        operand: fp,
    });
    let mut node = InstrNode::new(Inst::CallIndirect {
        callee: raw,
        sig: edge_sig,
        args: values(0..edge.0.len() as u32),
        calling_conv: CallingConv::C,
    });
    for _ in 0..results {
        let result = body.fresh();
        node = node.with_result(result);
    }
    body.body.push(node);
    body.emit_void(Inst::Return { values: vec![] });
    define(
        &mut module,
        "caller",
        caller_sig,
        params_from(&edge.0),
        body,
    );
    module
}

/// The three declaration shapes the selector cannot place, each refused by
/// name: a hidden parameter at index 1 (`[TCG-SRET-ABI]`, "only a leading
/// hidden return-buffer parameter is supported"), a hidden parameter beside a
/// return value (`[TCG-SRET-ABI]`, "requires an empty return list") and a
/// variadic DEFINITION with a hidden buffer (`[TCG-VARIADIC-DEFINITION]`: no
/// `va_start` lowering exists, so the definition, not the convention, is what
/// is refused).
pub fn sret_at_index_1_module(triple: &str) -> Module {
    let mut module = new_module(triple, "sret_index_1");
    let _ = define_big(&mut module);
    let _ = declare_mix64(&mut module);
    let sig = add_sig(&mut module, vec![Ty::I64, Ty::Ptr], vec![], false);
    let callee = declare(&mut module, "late_sret", sig, false);
    module.functions[callee.index() as usize].attrs.params = vec![ParamAttrs::default(); 2];
    module.functions[callee.index() as usize].attrs.params[1].sret = true;
    let mut body = Body::new(2);
    body.emit_void(Inst::Call {
        callee,
        args: vec![ValueId::new(0), ValueId::new(1)],
    });
    body.emit_void(Inst::Return { values: vec![] });
    define(
        &mut module,
        "caller",
        sig,
        params_from(&[Ty::I64, Ty::Ptr]),
        body,
    );
    module
}

pub fn sret_with_return_module(triple: &str) -> Module {
    let mut module = new_module(triple, "sret_with_return");
    let sig = add_sig(&mut module, vec![Ty::Ptr], vec![Ty::I64], false);
    let callee = declare(&mut module, "sret_and_value", sig, true);
    let caller_sig = add_sig(&mut module, vec![Ty::Ptr], vec![], false);
    let mut body = Body::new(1);
    let _ = body.emit(Inst::Call {
        callee,
        args: vec![ValueId::new(0)],
    });
    body.emit_void(Inst::Return { values: vec![] });
    define(
        &mut module,
        "caller",
        caller_sig,
        params_from(&[Ty::Ptr]),
        body,
    );
    module
}

pub fn sret_variadic_definition_module(triple: &str) -> Module {
    let mut module = new_module(triple, "sret_variadic_definition");
    let big = define_big(&mut module);
    let mix64 = declare_mix64(&mut module);
    let mut params = vec![Ty::Ptr];
    params.extend(ordinary_params());
    let sig = add_sig(&mut module, params.clone(), vec![], true);
    let mut body = Body::new(params.len() as u32);
    let value = body.big_value(&big, mix64, &values(1..1 + ARGS as u32));
    body.store_big(&big, ValueId::new(0), value);
    body.emit_void(Inst::Return { values: vec![] });
    define_sret(&mut module, "cg_va_sret", sig, params_from(&params), body);
    module
}

/// C oracle shared by every driver. `ORACLE` names the C compiler in the
/// success lines; a host test defines it on the compiler command line.
pub const ORACLE_PRELUDE: &str = r#"
#include <stdarg.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>

#ifndef ORACLE
#define ORACLE "clang"
#endif

struct Big { int64_t i; double d; int64_t j; double e; int32_t m0; int32_t m1; };

int64_t mix64(int64_t x, int64_t y) { return x * 31 + y; }

#define ORDINARY_PARAMS \
    int64_t a0, int64_t a1, int64_t a2, int64_t a3, int64_t a4, int64_t a5, int64_t a6, \
    int64_t a7, int64_t a8, double d0, double d1, double d2, double d3, double d4, \
    double d5, double d6, double d7, double d8, int32_t n0, int32_t n1
#define ORDINARY_ARGS a0, a1, a2, a3, a4, a5, a6, a7, a8, d0, d1, d2, d3, d4, d5, d6, d7, d8, n0, n1

static struct Big expected(ORDINARY_PARAMS) {
    struct Big r;
    r.i = a0 + a2 + a4 + a6 + a8;
    r.d = d0 + d2 + d4 + d6 + d8;
    r.j = mix64(a1, a7) + a3 + a5;
    r.e = d1 + d3 + d5 + d7;
    r.m0 = n0 + n1;
    r.m1 = n1 - n0;
    return r;
}

static const int64_t A[9] = {
    0x0101010101010101LL, 0x0202020202020202LL, 0x0303030303030303LL,
    0x0404040404040404LL, 0x0505050505050505LL, 0x0606060606060606LL,
    0x0707070707070707LL, 0x0808080808080808LL, -0x0909090909090909LL,
};
static const double D[9] = { 1.75, -2.5, 3.25, -4.125, 5.5, -6.0625, 7.875, -8.375, 9.1875 };
static const int32_t N0 = 0x12345678, N1 = -0x0f0f0f10;

#define SPREAD A[0], A[1], A[2], A[3], A[4], A[5], A[6], A[7], A[8], \
    D[0], D[1], D[2], D[3], D[4], D[5], D[6], D[7], D[8], N0, N1

static int same_as(const char *what, const struct Big *got, struct Big want) {
    if (memcmp(got, &want, sizeof want) == 0) return 1;
    printf("%s: got {%lld %a %lld %a %d %d} want {%lld %a %lld %a %d %d}\n", what,
           (long long)got->i, got->d, (long long)got->j, got->e, got->m0, got->m1,
           (long long)want.i, want.d, (long long)want.j, want.e, want.m0, want.m1);
    return 0;
}

static int same(const char *what, const struct Big *got) {
    return same_as(what, got, expected(SPREAD));
}
"#;

/// Exact success line of [`CALLEE_DRIVER`] for the oracle name `oracle`.
pub fn callee_pass_line(oracle: &str) -> String {
    format!("C caller -> CG sret callees agree with {oracle}")
}

/// Exact success line of [`CALLER_DRIVER`] for the oracle name `oracle`.
pub fn caller_pass_line(oracle: &str) -> String {
    format!("CG caller -> C sret callees agree with {oracle}")
}

pub const CALLEE_DRIVER: &str = r#"
typedef struct Big (*big_fn)(ORDINARY_PARAMS);
extern struct Big cg_sret_attr(ORDINARY_PARAMS);
extern struct Big cg_sret_struct(ORDINARY_PARAMS);

int main(void) {
    big_fn volatile fns[2] = { cg_sret_attr, cg_sret_struct };
    const char *names[2] = { "C caller -> cg_sret_attr", "C caller -> cg_sret_struct" };
    for (int k = 0; k < 2; k++) {
        struct Big got;
        memset(&got, 0x5a, sizeof got);
        got = fns[k](SPREAD);
        if (!same(names[k], &got)) return k + 1;
    }
    printf("C caller -> CG sret callees agree with " ORACLE "\n");
    return 0;
}
"#;

pub const CALLER_DRIVER: &str = r#"
struct Big c_big_attr(ORDINARY_PARAMS) { return expected(ORDINARY_ARGS); }
struct Big c_big_dyn(ORDINARY_PARAMS) { return expected(ORDINARY_ARGS); }

static struct Big from_va(int n, va_list ap) {
    int64_t a[9]; double d[9]; int32_t nn[2];
    if (n != 20) { struct Big bad; memset(&bad, 0xee, sizeof bad); return bad; }
    for (int k = 0; k < 9; k++) a[k] = va_arg(ap, int64_t);
    for (int k = 0; k < 9; k++) d[k] = va_arg(ap, double);
    for (int k = 0; k < 2; k++) nn[k] = va_arg(ap, int32_t);
    return expected(a[0], a[1], a[2], a[3], a[4], a[5], a[6], a[7], a[8],
                    d[0], d[1], d[2], d[3], d[4], d[5], d[6], d[7], d[8], nn[0], nn[1]);
}
struct Big c_big_va_attr(int n, ...) {
    va_list ap; va_start(ap, n);
    struct Big r = from_va(n, ap);
    va_end(ap);
    return r;
}
struct Big c_big_va_struct(int n, ...) {
    va_list ap; va_start(ap, n);
    struct Big r = from_va(n, ap);
    va_end(ap);
    return r;
}

typedef struct Big (*big_fn)(ORDINARY_PARAMS);
extern void cg_call_attr_fp(struct Big *out, ORDINARY_PARAMS);
extern void cg_call_struct_fp(big_fn fp, struct Big *out, ORDINARY_PARAMS);
extern void cg_call_attr_va(struct Big *out, ORDINARY_PARAMS);
extern void cg_call_struct_va(struct Big *out, ORDINARY_PARAMS);

int main(void) {
    struct Big got;
    memset(&got, 0x5a, sizeof got);
    cg_call_attr_fp(&got, SPREAD);
    if (!same("CG caller -> c_big_attr through a static function pointer", &got)) return 1;
    memset(&got, 0x5a, sizeof got);
    big_fn volatile dyn = c_big_dyn;
    cg_call_struct_fp(dyn, &got, SPREAD);
    if (!same("CG caller -> c_big_dyn through a C function pointer", &got)) return 2;
    memset(&got, 0x5a, sizeof got);
    cg_call_attr_va(&got, SPREAD);
    if (!same("CG caller -> variadic c_big_va_attr", &got)) return 3;
    memset(&got, 0x5a, sizeof got);
    cg_call_struct_va(&got, SPREAD);
    if (!same("CG caller -> variadic c_big_va_struct", &got)) return 4;
    printf("CG caller -> C sret callees agree with " ORACLE "\n");
    return 0;
}
"#;
