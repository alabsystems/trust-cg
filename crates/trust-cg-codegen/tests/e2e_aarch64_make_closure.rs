// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Runtime capture values and producer-observed closure layouts. These are
//! native/interpreter/C comparisons, not a machine-code proof claim.

#![cfg(all(target_arch = "aarch64", target_os = "macos"))]

#[path = "common/construct_sweep.rs"]
mod fixture;
use fixture::native;

use fixture::{Body, define, sweep_module};
use sha2::{Digest, Sha256};
use trust_cg_codegen::pipeline::OptLevel;
use trust_ir::interpret::{InterpretValue, Interpreter};
use trust_ir::{BinOp, CallingConv, ClosureLayoutDescriptor, ClosureTy, Inst, Module, Ty, ValueId};

fn constant(body: &mut Body, value: i128) -> ValueId {
    body.emit(Inst::Const {
        ty: Ty::U64,
        value: trust_ir::Constant::Int(value),
    })
}

fn add(body: &mut Body, a: ValueId, b: ValueId) -> ValueId {
    body.emit(Inst::BinOp {
        op: BinOp::Add,
        ty: Ty::U64,
        lhs: a,
        rhs: b,
    })
}

fn module() -> Module {
    let mut module = sweep_module("runtime_closure_captures");
    let apparent = module
        .add_func_type(trust_ir::FuncTy {
            params: vec![Ty::U64],
            returns: vec![Ty::U64],
            abi: None,
            is_vararg: false,
        })
        .unwrap();
    let closure = trust_ir::ClosureTyId::new(0);
    module.closure_types.push(ClosureTy {
        func: apparent,
        captures: vec![Ty::Ptr, Ty::U8, Ty::U64],
    });
    // Same total size/alignment as the native carrier, but a different field
    // order. A declaration-order write would corrupt both tag and pointer.
    module.closure_layouts.push(ClosureLayoutDescriptor {
        origin: None,
        closure,
        size: 24,
        align: 8,
        capture_offsets: vec![8, 0, 16],
    });
    let mut body = Body::new();
    let cell = body.param(Ty::Ptr);
    let tag = body.param(Ty::U8);
    let delta = body.param(Ty::U64);
    let step = body.param(Ty::U64);
    let old = body.emit(Inst::Load {
        ty: Ty::U64,
        ptr: cell,
        volatile: false,
        align: None,
    });
    let tag = body.emit(Inst::Cast {
        op: trust_ir::CastOp::ZExt,
        src_ty: Ty::U8,
        dst_ty: Ty::U64,
        operand: tag,
    });
    let n = add(&mut body, old, delta);
    let n = add(&mut body, n, step);
    let n = add(&mut body, n, tag);
    body.effect(Inst::Store {
        ty: Ty::U64,
        ptr: cell,
        value: n,
        volatile: false,
        align: None,
    });
    body.effect(Inst::Return { values: vec![n] });
    let target = define(
        &mut module,
        "captured_bump",
        vec![Ty::Ptr, Ty::U8, Ty::U64, Ty::U64],
        vec![Ty::U64],
        body,
    );
    module.functions[target.as_usize()].linkage = trust_ir::Linkage::Internal;

    let mut body = Body::new();
    let initial = body.param(Ty::U64);
    let tag = body.param(Ty::U8);
    let delta = body.param(Ty::U64);
    let step = body.param(Ty::U64);
    let cell = body.emit(Inst::Alloca {
        ty: Ty::U64,
        count: None,
        align: None,
    });
    body.effect(Inst::Store {
        ty: Ty::U64,
        ptr: cell,
        value: initial,
        volatile: false,
        align: None,
    });
    let env = body.emit(Inst::MakeClosure {
        ty: closure,
        func: target,
        captures: vec![cell, tag, delta],
    });
    let copied = body.emit(Inst::Copy {
        ty: Ty::Closure(closure),
        operand: env,
    });
    let one = constant(&mut body, 1);
    let changed_delta = add(&mut body, delta, one);
    let updated = body.emit(Inst::InsertField {
        ty: Ty::Closure(closure),
        aggregate: copied,
        field: 2,
        value: changed_delta,
    });
    let first = body.emit(Inst::CallIndirect {
        callee: env,
        sig: apparent,
        args: vec![step],
        calling_conv: CallingConv::C,
    });
    let second = body.emit(Inst::CallIndirect {
        callee: updated,
        sig: apparent,
        args: vec![step],
        calling_conv: CallingConv::C,
    });
    let thousand = constant(&mut body, 1000);
    let first = body.emit(Inst::BinOp {
        op: BinOp::Mul,
        ty: Ty::U64,
        lhs: first,
        rhs: thousand,
    });
    let result = add(&mut body, first, second);
    body.effect(Inst::Return {
        values: vec![result],
    });
    define(
        &mut module,
        "runtime_closure",
        vec![Ty::U64, Ty::U8, Ty::U64, Ty::U64],
        vec![Ty::U64],
        body,
    );

    let mut body = Body::new();
    let out = body.param(Ty::Ptr);
    let cell = body.param(Ty::Ptr);
    let tag = body.param(Ty::U8);
    let delta = body.param(Ty::U64);
    let env = body.emit(Inst::MakeClosure {
        ty: closure,
        func: target,
        captures: vec![cell, tag, delta],
    });
    body.effect(Inst::Store {
        ty: Ty::Closure(closure),
        ptr: out,
        value: env,
        volatile: false,
        align: None,
    });
    body.effect(Inst::Return { values: vec![] });
    define(
        &mut module,
        "dump_closure",
        vec![Ty::Ptr, Ty::Ptr, Ty::U8, Ty::U64],
        vec![],
        body,
    );
    module
}

fn interpret(module: &Module, args: [u64; 4]) -> u64 {
    let values: Vec<InterpretValue> = [Ty::U64, Ty::U8, Ty::U64, Ty::U64]
        .into_iter()
        .zip(args)
        .map(|(ty, value)| InterpretValue::int(ty, i128::from(value)).unwrap())
        .collect();
    let result = Interpreter::with_module(module)
        .execute_function(module.function_by_name("runtime_closure").unwrap(), values)
        .unwrap();
    result.returns[0].as_int().unwrap().as_unsigned() as u64
}

#[test]
fn runtime_captures_execute_with_pointer_identity_and_value_semantics() {
    let module = module();
    let cases = [[0, 7, 3, 5], [41, 255, 17, 8], [200, 0, 0, 1]];
    for args in cases {
        let first = args.iter().sum::<u64>();
        let second = first + args[1] + args[2] + 1 + args[3];
        assert_eq!(interpret(&module, args), first * 1000 + second);
    }
    let driver = r#"
#include <stdint.h>
#include <string.h>
extern uint64_t runtime_closure(uint64_t, uint8_t, uint64_t, uint64_t);
extern void dump_closure(void *, uint64_t *, uint8_t, uint64_t);
int main(void) {
    const uint64_t cases[][4] = {{0,7,3,5},{41,255,17,8},{200,0,0,1}};
    for (unsigned i=0;i<3;i++) {
        const uint64_t *a=cases[i];
        uint64_t first=a[0]+a[1]+a[2]+a[3];
        uint64_t second=first+a[1]+a[2]+1+a[3];
        if (runtime_closure(a[0],a[1],a[2],a[3]) != first*1000+second) return 1;
    }
    _Alignas(8) unsigned char bytes[24];
    uint64_t cell=55, delta=0x1122334455667788ULL, saved_delta;
    uint64_t *saved_ptr;
    memset(bytes,0,sizeof bytes);
    dump_closure(bytes,&cell,203,delta);
    memcpy(&saved_ptr,bytes+8,sizeof saved_ptr);
    memcpy(&saved_delta,bytes+16,sizeof saved_delta);
    if (bytes[0]!=203 || saved_ptr!=&cell || saved_delta!=delta) return 2;
    return 0;
}
"#;
    let mut executions = 0;
    for opt in [OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::O3] {
        let object = native::compile(&module, opt);
        record_native_execution(&format!("runtime_closure_{opt:?}"), &object, driver);
        executions += 1;
    }
    assert_eq!(executions, 4);
}

/// A runtime condition selects the environment, not the code pointer. Both
/// arms retain their pointer/tag/wide captures and producer-observed offsets.
#[test]
fn same_code_selected_closures_execute_both_runtime_environments() {
    let mut module = module();
    let target = module.function_by_name("captured_bump").unwrap().id;
    let apparent = module.closure_types[0].func;
    let closure = trust_ir::ClosureTyId::new(0);
    let mut body = Body::new();
    let choose = body.param(Ty::U64);
    let left = body.param(Ty::U64);
    let right = body.param(Ty::U64);
    let zero = constant(&mut body, 0);
    let cond = body.emit(Inst::ICmp {
        op: trust_ir::ICmpOp::Ne,
        ty: Ty::U64,
        lhs: choose,
        rhs: zero,
    });
    let left_cell = body.emit(Inst::Alloca {
        ty: Ty::U64,
        count: None,
        align: None,
    });
    let right_cell = body.emit(Inst::Alloca {
        ty: Ty::U64,
        count: None,
        align: None,
    });
    let ten = constant(&mut body, 10);
    let twenty = constant(&mut body, 20);
    for (ptr, value) in [(left_cell, ten), (right_cell, twenty)] {
        body.effect(Inst::Store {
            ty: Ty::U64,
            ptr,
            value,
            volatile: false,
            align: None,
        });
    }
    let left_tag = body.emit(Inst::Const {
        ty: Ty::U8,
        value: trust_ir::Constant::Int(3),
    });
    let right_tag = body.emit(Inst::Const {
        ty: Ty::U8,
        value: trust_ir::Constant::Int(7),
    });
    let left = body.emit(Inst::MakeClosure {
        ty: closure,
        func: target,
        captures: vec![left_cell, left_tag, left],
    });
    let right = body.emit(Inst::MakeClosure {
        ty: closure,
        func: target,
        captures: vec![right_cell, right_tag, right],
    });
    let selected = body.emit(Inst::Select {
        ty: Ty::Closure(closure),
        cond,
        then_val: left,
        else_val: right,
    });
    let copied = body.emit(Inst::Copy {
        ty: Ty::Closure(closure),
        operand: selected,
    });
    let result = body.emit(Inst::CallIndirect {
        callee: copied,
        sig: apparent,
        args: vec![zero],
        calling_conv: CallingConv::C,
    });
    // Observe both destinations as well as the result: the unselected cell
    // must remain untouched, and every selected capture must come from one env.
    let after_left = body.emit(Inst::Load {
        ty: Ty::U64,
        ptr: left_cell,
        volatile: false,
        align: None,
    });
    let after_right = body.emit(Inst::Load {
        ty: Ty::U64,
        ptr: right_cell,
        volatile: false,
        align: None,
    });
    let hundred = constant(&mut body, 100);
    let ten_thousand = constant(&mut body, 10000);
    let result = body.emit(Inst::BinOp {
        op: BinOp::Mul,
        ty: Ty::U64,
        lhs: result,
        rhs: ten_thousand,
    });
    let after_left = body.emit(Inst::BinOp {
        op: BinOp::Mul,
        ty: Ty::U64,
        lhs: after_left,
        rhs: hundred,
    });
    let result = add(&mut body, result, after_left);
    let result = add(&mut body, result, after_right);
    body.effect(Inst::Return {
        values: vec![result],
    });
    define(
        &mut module,
        "selected_closure",
        vec![Ty::U64; 3],
        vec![Ty::U64],
        body,
    );
    let cases = [[0u64, 13, 41], [1, 13, 41], [2, 1000, 3], [0, 1000, 3]];
    for [choose, left, right] in cases {
        let (value, after_left, after_right) = if choose != 0 {
            (left + 13, left + 13, 20)
        } else {
            (right + 27, 10, right + 27)
        };
        let expected = value * 10000 + after_left * 100 + after_right;
        let args: Vec<InterpretValue> = [choose, left, right]
            .into_iter()
            .map(|value| InterpretValue::int(Ty::U64, i128::from(value)).unwrap())
            .collect();
        let result = Interpreter::with_module(&module)
            .execute_function(module.function_by_name("selected_closure").unwrap(), args)
            .unwrap();
        assert_eq!(
            result.returns[0].as_int().unwrap().as_unsigned(),
            u128::from(expected)
        );
    }
    let driver = r#"
#include <stdint.h>
extern uint64_t selected_closure(uint64_t, uint64_t, uint64_t);
int main(void) {
    const uint64_t cases[][3] = {{0,13,41},{1,13,41},{2,1000,3},{0,1000,3}};
    for (unsigned i=0;i<4;i++) {
        const uint64_t *a=cases[i];
        uint64_t value=a[0] ? a[1]+13 : a[2]+27;
        uint64_t after_left=a[0] ? value : 10;
        uint64_t after_right=a[0] ? 20 : value;
        if (selected_closure(a[0],a[1],a[2]) != value*10000+after_left*100+after_right) return 1;
    }
    return 0;
}
"#;
    for opt in [OptLevel::O0, OptLevel::O2] {
        let object = native::compile(&module, opt);
        record_native_execution(&format!("selected_closure_{opt:?}"), &object, driver);
    }
}

/// A runtime condition selects the environment, not the code pointer. Both
/// arms retain their pointer/tag/wide captures and producer-observed offsets.
#[test]
fn same_code_block_parameters_execute_both_runtime_environments() {
    let mut module = module();
    let target = module.function_by_name("captured_bump").unwrap().id;
    let apparent = module.closure_types[0].func;
    let closure = trust_ir::ClosureTyId::new(0);
    let mut body = Body::new();
    let choose = body.param(Ty::U64);
    let left = body.param(Ty::U64);
    let right = body.param(Ty::U64);
    let zero = constant(&mut body, 0);
    let cond = body.emit(Inst::ICmp {
        op: trust_ir::ICmpOp::Ne,
        ty: Ty::U64,
        lhs: choose,
        rhs: zero,
    });
    let left_cell = body.emit(Inst::Alloca {
        ty: Ty::U64,
        count: None,
        align: None,
    });
    let right_cell = body.emit(Inst::Alloca {
        ty: Ty::U64,
        count: None,
        align: None,
    });
    let ten = constant(&mut body, 10);
    let twenty = constant(&mut body, 20);
    for (ptr, value) in [(left_cell, ten), (right_cell, twenty)] {
        body.effect(Inst::Store {
            ty: Ty::U64,
            ptr,
            value,
            volatile: false,
            align: None,
        });
    }
    let left_tag = body.emit(Inst::Const {
        ty: Ty::U8,
        value: trust_ir::Constant::Int(3),
    });
    let right_tag = body.emit(Inst::Const {
        ty: Ty::U8,
        value: trust_ir::Constant::Int(7),
    });
    let left = body.emit(Inst::MakeClosure {
        ty: closure,
        func: target,
        captures: vec![left_cell, left_tag, left],
    });
    let right = body.emit(Inst::MakeClosure {
        ty: closure,
        func: target,
        captures: vec![right_cell, right_tag, right],
    });
    let (left_block, left_params) = body.block(&[Ty::Closure(closure)]);
    let (right_block, right_params) = body.block(&[Ty::Closure(closure)]);
    let (merge, merge_params) = body.block(&[Ty::Closure(closure)]);
    let (forward, forward_params) = body.block(&[Ty::Closure(closure)]);
    body.effect(Inst::CondBr {
        cond,
        then_target: left_block,
        then_args: vec![left],
        else_target: right_block,
        else_args: vec![right],
    });
    for (block, param) in [(left_block, left_params[0]), (right_block, right_params[0])] {
        body.switch_to(block);
        body.effect(Inst::Br {
            target: merge,
            args: vec![param],
        });
    }
    body.switch_to(merge);
    body.effect(Inst::Br {
        target: forward,
        args: vec![merge_params[0]],
    });
    body.switch_to(forward);
    let selected = forward_params[0];
    let copied = body.emit(Inst::Copy {
        ty: Ty::Closure(closure),
        operand: selected,
    });
    let result = body.emit(Inst::CallIndirect {
        callee: copied,
        sig: apparent,
        args: vec![zero],
        calling_conv: CallingConv::C,
    });
    // Observe both destinations as well as the result: the unselected cell
    // must remain untouched, and every selected capture must come from one env.
    let after_left = body.emit(Inst::Load {
        ty: Ty::U64,
        ptr: left_cell,
        volatile: false,
        align: None,
    });
    let after_right = body.emit(Inst::Load {
        ty: Ty::U64,
        ptr: right_cell,
        volatile: false,
        align: None,
    });
    let hundred = constant(&mut body, 100);
    let ten_thousand = constant(&mut body, 10000);
    let result = body.emit(Inst::BinOp {
        op: BinOp::Mul,
        ty: Ty::U64,
        lhs: result,
        rhs: ten_thousand,
    });
    let after_left = body.emit(Inst::BinOp {
        op: BinOp::Mul,
        ty: Ty::U64,
        lhs: after_left,
        rhs: hundred,
    });
    let result = add(&mut body, result, after_left);
    let result = add(&mut body, result, after_right);
    body.effect(Inst::Return {
        values: vec![result],
    });
    define(
        &mut module,
        "merged_closure",
        vec![Ty::U64; 3],
        vec![Ty::U64],
        body,
    );
    let cases = [[0u64, 13, 41], [1, 13, 41], [2, 1000, 3], [0, 1000, 3]];
    for [choose, left, right] in cases {
        let (value, after_left, after_right) = if choose != 0 {
            (left + 13, left + 13, 20)
        } else {
            (right + 27, 10, right + 27)
        };
        let expected = value * 10000 + after_left * 100 + after_right;
        let args: Vec<InterpretValue> = [choose, left, right]
            .into_iter()
            .map(|value| InterpretValue::int(Ty::U64, i128::from(value)).unwrap())
            .collect();
        let result = Interpreter::with_module(&module)
            .execute_function(module.function_by_name("merged_closure").unwrap(), args)
            .unwrap();
        assert_eq!(
            result.returns[0].as_int().unwrap().as_unsigned(),
            u128::from(expected)
        );
    }
    let driver = r#"
#include <stdint.h>
extern uint64_t merged_closure(uint64_t, uint64_t, uint64_t);
int main(void) {
    const uint64_t cases[][3] = {{0,13,41},{1,13,41},{2,1000,3},{0,1000,3}};
    for (unsigned i=0;i<4;i++) {
        const uint64_t *a=cases[i];
        uint64_t value=a[0] ? a[1]+13 : a[2]+27;
        uint64_t after_left=a[0] ? value : 10;
        uint64_t after_right=a[0] ? 20 : value;
        if (merged_closure(a[0],a[1],a[2]) != value*10000+after_left*100+after_right) return 1;
    }
    return 0;
}
"#;
    eprintln!(
        "BLOCK_CLOSURE_DRIVER_SHA256={:x}",
        Sha256::digest(driver.as_bytes())
    );
    let census = trust_cg_lower::module_local_function_identity_census(&module);
    eprintln!("BLOCK_CLOSURE_CENSUS {census:?}");
    assert_eq!(census.direct_edges, 3);
    assert_eq!(census.materialized_identities, 0);
    for opt in [OptLevel::O0, OptLevel::O2] {
        let object = native::compile(&module, opt);
        let tag = format!("merged_closure_{opt:?}");
        if let Some(directory) = std::env::var_os("CLOSURE_BLOCK_RETAIN_DIR") {
            let directory = std::path::PathBuf::from(directory);
            std::fs::create_dir_all(&directory).unwrap();
            std::fs::write(directory.join(format!("{tag}.o")), &object).unwrap();
            std::fs::write(directory.join(format!("{tag}.c")), driver).unwrap();
        }
        record_native_execution(&tag, &object, driver);
    }
}

fn constant_layout_module() -> Module {
    let mut module = sweep_module("constant_closure_observed_offsets");
    let apparent = module
        .add_func_type(trust_ir::FuncTy {
            params: vec![],
            returns: vec![Ty::U64],
            abi: None,
            is_vararg: false,
        })
        .unwrap();
    let closure = trust_ir::ClosureTyId::new(0);
    module.closure_types.push(ClosureTy {
        func: apparent,
        captures: vec![Ty::U8, Ty::U64],
    });
    module.closure_layouts.push(ClosureLayoutDescriptor {
        origin: None,
        closure,
        size: 16,
        align: 8,
        capture_offsets: vec![8, 0],
    });
    let mut body = Body::new();
    let _tag = body.param(Ty::U8);
    let wide = body.param(Ty::U64);
    body.effect(Inst::Return { values: vec![wide] });
    let target = define(
        &mut module,
        "constant_target",
        vec![Ty::U8, Ty::U64],
        vec![Ty::U64],
        body,
    );
    let literal = trust_ir::Constant::Closure {
        func: target,
        captures: vec![
            trust_ir::Constant::Int(171),
            trust_ir::Constant::Int(0x1122334455667788),
        ],
    };
    let mut body = Body::new();
    let env = body.emit(Inst::Const {
        ty: Ty::Closure(closure),
        value: literal.clone(),
    });
    let tag = body.emit(Inst::ExtractField {
        ty: Ty::U8,
        aggregate: env,
        field: 0,
    });
    let wide = body.emit(Inst::ExtractField {
        ty: Ty::U64,
        aggregate: env,
        field: 1,
    });
    let tag = body.emit(Inst::Cast {
        op: trust_ir::CastOp::ZExt,
        src_ty: Ty::U8,
        dst_ty: Ty::U64,
        operand: tag,
    });
    let result = add(&mut body, wide, tag);
    body.effect(Inst::Return {
        values: vec![result],
    });
    define(&mut module, "constant_fields", vec![], vec![Ty::U64], body);
    let mut body = Body::new();
    let out = body.param(Ty::Ptr);
    let env = body.emit(Inst::Const {
        ty: Ty::Closure(closure),
        value: literal,
    });
    body.effect(Inst::Store {
        ty: Ty::Closure(closure),
        ptr: out,
        value: env,
        volatile: false,
        align: None,
    });
    body.effect(Inst::Return { values: vec![] });
    define(&mut module, "constant_bytes", vec![Ty::Ptr], vec![], body);
    module
}

#[test]
fn declared_constant_closure_offsets_execute_natively_and_match_c_bytes() {
    let module = constant_layout_module();
    let outcome = Interpreter::with_module(&module)
        .execute_function(module.function_by_name("constant_fields").unwrap(), vec![])
        .unwrap();
    assert_eq!(
        outcome.returns[0].as_int().unwrap().as_unsigned(),
        0x1122334455667788 + 171
    );
    let driver = r#"
#include <stdint.h>
#include <string.h>
extern uint64_t constant_fields(void);
extern void constant_bytes(void *);
int main(void) {
    const uint64_t wide=0x1122334455667788ULL;
    _Alignas(8) unsigned char bytes[16];
    uint64_t saved;
    memset(bytes,0,sizeof bytes);
    constant_bytes(bytes);
    memcpy(&saved,bytes,sizeof saved);
    if (saved!=wide || bytes[8]!=171) return 1;
    if (constant_fields()!=wide+171) return 2;
    return 0;
}
"#;
    for opt in [OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::O3] {
        let object = native::compile(&module, opt);
        record_native_execution(&format!("constant_closure_layout_{opt:?}"), &object, driver);
    }
}

fn record_native_execution(tag: &str, object: &[u8], driver: &str) {
    // Keep each target's scratch lifetime bounded by the control. The native
    // gate independently rejects temporary leftovers after a target exits.
    let evidence_guard = tempfile::Builder::new()
        .prefix(&format!("cg-closure-evidence-{tag}-"))
        .tempdir()
        .unwrap();
    let evidence = evidence_guard.path();
    std::fs::write(evidence.join("module.o"), object).unwrap();
    std::fs::write(evidence.join("driver.c"), driver).unwrap();
    assert_eq!(native::link_run(tag, object, driver), Some(0));
    eprintln!(
        "NATIVE_EXECUTION tag={tag} exit=0 object_sha256={:x} driver_sha256={:x} evidence={}",
        Sha256::digest(object),
        Sha256::digest(driver.as_bytes()),
        evidence.display(),
    );
}

fn stored_module() -> Module {
    let mut module = module();
    let closure = trust_ir::ClosureTyId::new(0);
    let apparent = module.closure_types[0].func;
    let target = module.function_by_name("captured_bump").unwrap().id;
    let mut body = Body::new();
    let initial = body.param(Ty::U64);
    let tag = body.param(Ty::U8);
    let delta = body.param(Ty::U64);
    let step = body.param(Ty::U64);
    let cell = body.emit(Inst::Alloca {
        ty: Ty::U64,
        count: None,
        align: None,
    });
    body.effect(Inst::Store {
        ty: Ty::U64,
        ptr: cell,
        value: initial,
        volatile: false,
        align: None,
    });
    let env = body.emit(Inst::MakeClosure {
        ty: closure,
        func: target,
        captures: vec![cell, tag, delta],
    });
    let slot = body.emit(Inst::Alloca {
        ty: Ty::Closure(closure),
        count: None,
        align: None,
    });
    body.effect(Inst::Store {
        ty: Ty::Closure(closure),
        ptr: slot,
        value: env,
        volatile: false,
        align: None,
    });
    let one = constant(&mut body, 1);
    let changed = add(&mut body, initial, one);
    body.effect(Inst::Store {
        ty: Ty::U64,
        ptr: cell,
        value: changed,
        volatile: false,
        align: None,
    });
    let loaded = body.emit(Inst::Load {
        ty: Ty::Closure(closure),
        ptr: slot,
        volatile: false,
        align: None,
    });
    let result = body.emit(Inst::CallIndirect {
        callee: loaded,
        sig: apparent,
        args: vec![step],
        calling_conv: CallingConv::C,
    });
    let observed = body.emit(Inst::Load {
        ty: Ty::U64,
        ptr: cell,
        volatile: false,
        align: None,
    });
    let thousand = constant(&mut body, 1000);
    let result = body.emit(Inst::BinOp {
        op: BinOp::Mul,
        ty: Ty::U64,
        lhs: result,
        rhs: thousand,
    });
    let result = add(&mut body, result, observed);
    body.effect(Inst::Return {
        values: vec![result],
    });
    define(
        &mut module,
        "stored_runtime_closure",
        vec![Ty::U64, Ty::U8, Ty::U64, Ty::U64],
        vec![Ty::U64],
        body,
    );
    module
}

#[test]
fn stored_closure_load_calls_the_bound_target_and_observes_original_pointer_effects() {
    let module = stored_module();
    for args in [[0, 7, 3, 5], [41, 255, 17, 8], [200, 0, 0, 1]] {
        let values = [Ty::U64, Ty::U8, Ty::U64, Ty::U64]
            .into_iter()
            .zip(args)
            .map(|(ty, value)| InterpretValue::int(ty, value).unwrap())
            .collect::<Vec<_>>();
        let result = Interpreter::with_module(&module)
            .execute_function(
                module.function_by_name("stored_runtime_closure").unwrap(),
                values,
            )
            .unwrap();
        assert_eq!(result.host_calls, 0);
        assert_eq!(
            result.returns[0].as_int().unwrap().as_unsigned(),
            (args.iter().sum::<i128>() + 1) as u128 * 1001
        );
    }
    let driver = r#"
#include <stdint.h>
extern uint64_t stored_runtime_closure(uint64_t, uint8_t, uint64_t, uint64_t);
int main(void) {
    const uint64_t cases[][4] = {{0,7,3,5},{41,255,17,8},{200,0,0,1}};
    for (unsigned i=0;i<3;i++) {
        const uint64_t *a=cases[i];
        uint64_t expected=(a[0]+a[1]+a[2]+a[3]+1)*1001;
        if (stored_runtime_closure(a[0],a[1],a[2],a[3]) != expected) return 1;
    }
    return 0;
}

"#;
    for opt in [OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::O3] {
        let object = native::compile(&module, opt);
        record_native_execution(&format!("stored_runtime_closure_{opt:?}"), &object, driver);
    }
}

#[test]
fn stored_closure_load_refuses_conflicting_targets_and_changed_layout() {
    let mut module = stored_module();
    let mut alternate = module.function_by_name("captured_bump").unwrap().clone();
    alternate.id = trust_ir::FuncId::new(module.functions.len() as u32);
    alternate.name = "other_captured_bump".into();
    let other = alternate.id;
    module.functions.push(alternate);
    let constructor = module
        .functions
        .iter_mut()
        .flat_map(|function| &mut function.blocks)
        .flat_map(|block| &mut block.body)
        .find_map(|node| match &mut node.inst {
            Inst::MakeClosure { func, .. } => Some(func),
            _ => None,
        })
        .unwrap();
    *constructor = other;
    assert!(
        module
            .closure_storage_binding(trust_ir::ClosureTyId::new(0))
            .is_err()
    );
    assert!(native::try_compile(&module, OptLevel::O0).is_err());

    let mut module = stored_module();
    module.closure_layouts[0].capture_offsets[0] = 1;
    assert!(
        module
            .closure_storage_binding(trust_ir::ClosureTyId::new(0))
            .is_err()
    );
    assert!(native::try_compile(&module, OptLevel::O0).is_err());
}

#[test]
fn zero_capture_stored_closure_calls_original_pointer_body_natively() {
    let mut module = sweep_module("zero_capture_stored_frame");
    let apparent = module
        .add_func_type(trust_ir::FuncTy {
            params: vec![Ty::Ptr],
            returns: vec![Ty::U64],
            abi: None,
            is_vararg: false,
        })
        .unwrap();
    let closure = trust_ir::ClosureTyId::new(0);
    module.closure_types.push(ClosureTy {
        func: apparent,
        captures: vec![],
    });
    module.closure_layouts.push(ClosureLayoutDescriptor {
        origin: Some(trust_ir::ty::TypeOrigin::Clean {
            decl: "ZeroCapture.StoredFrame".into(),
            env_digest: trust_ir::proof::ProofDigest::sha256([19; 32]),
        }),
        closure,
        size: 0,
        align: 1,
        capture_offsets: vec![],
    });
    let mut body = Body::new();
    let context = body.param(Ty::Ptr);
    let old = body.emit(Inst::Load {
        ty: Ty::U64,
        ptr: context,
        volatile: false,
        align: None,
    });
    let seven = constant(&mut body, 7);
    let changed = add(&mut body, old, seven);
    body.effect(Inst::Store {
        ty: Ty::U64,
        ptr: context,
        value: changed,
        volatile: false,
        align: None,
    });
    body.effect(Inst::Return {
        values: vec![changed],
    });
    let target = define(
        &mut module,
        "zero_frame_pointer_body",
        vec![Ty::Ptr],
        vec![Ty::U64],
        body,
    );
    module.functions[target.as_usize()].linkage = trust_ir::Linkage::Internal;
    let mut body = Body::new();
    let initial = body.param(Ty::U64);
    let context = body.emit(Inst::Alloca {
        ty: Ty::U64,
        count: None,
        align: None,
    });
    body.effect(Inst::Store {
        ty: Ty::U64,
        ptr: context,
        value: initial,
        volatile: false,
        align: None,
    });
    let environment = body.emit(Inst::MakeClosure {
        ty: closure,
        func: target,
        captures: vec![],
    });
    let home = body.emit(Inst::Alloca {
        ty: Ty::Closure(closure),
        count: None,
        align: None,
    });
    body.effect(Inst::Store {
        ty: Ty::Closure(closure),
        ptr: home,
        value: environment,
        volatile: false,
        align: None,
    });
    let loaded = body.emit(Inst::Load {
        ty: Ty::Closure(closure),
        ptr: home,
        volatile: false,
        align: None,
    });
    let returned = body.emit(Inst::CallIndirect {
        callee: loaded,
        sig: apparent,
        args: vec![context],
        calling_conv: CallingConv::C,
    });
    let observed = body.emit(Inst::Load {
        ty: Ty::U64,
        ptr: context,
        volatile: false,
        align: None,
    });
    let thousand = constant(&mut body, 1000);
    let weighted = body.emit(Inst::BinOp {
        op: BinOp::Mul,
        ty: Ty::U64,
        lhs: returned,
        rhs: thousand,
    });
    let result = add(&mut body, weighted, observed);
    body.effect(Inst::Return {
        values: vec![result],
    });
    define(
        &mut module,
        "zero_capture_stored_frame",
        vec![Ty::U64],
        vec![Ty::U64],
        body,
    );
    for initial in [0, 41, 200] {
        let result = Interpreter::with_module(&module)
            .execute_function(
                module
                    .function_by_name("zero_capture_stored_frame")
                    .unwrap(),
                vec![InterpretValue::int(Ty::U64, initial).unwrap()],
            )
            .unwrap();
        assert_eq!(result.host_calls, 0);
        assert_eq!(
            result.returns[0].as_int().unwrap().as_unsigned(),
            ((initial + 7) * 1001) as u128
        );
    }
    let driver = r#"
#include <stdint.h>
extern uint64_t zero_capture_stored_frame(uint64_t);
int main(void) {
    const uint64_t cases[] = {0,41,200};
    for (unsigned i=0;i<3;i++) {
        if (zero_capture_stored_frame(cases[i]) != (cases[i]+7)*1001) return 1;
    }
    return 0;
}
"#;
    for opt in [OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::O3] {
        let object = native::compile(&module, opt);
        record_native_execution(
            &format!("zero_capture_stored_frame_{opt:?}"),
            &object,
            driver,
        );
    }
}
