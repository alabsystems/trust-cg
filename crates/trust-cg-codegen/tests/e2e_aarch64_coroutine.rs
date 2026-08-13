// E2E: AArch64 coroutine FOUNDATION — a 2-state generator built on the
// `Inst::CoroSuspend` terminator, verified at two levels: the trust-ir
// interpreter AND a linked-and-run aarch64-apple-darwin Mach-O binary.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// ----------------------------------------------------------------------------
// WHAT THIS PINS
// ----------------------------------------------------------------------------
// A coroutine in a *verified* backend is compiled by STATE-MACHINE LOWERING:
//
//   * the coroutine's persistent state lives in an explicit FRAME object (here:
//     an `i64[2]` the caller owns and passes by pointer — `frame[0]` is the
//     resume STATE INDEX);
//   * each `resume` is a plain call that DISPATCHES on the state index
//     (`Switch`) to the correct continuation;
//   * each `yield` is the `Inst::CoroSuspend { frame, state_slot, next_state,
//     value }` terminator, whose backend lowering MACRO-EXPANDS into the
//     already-verified `Store(next_state)` + `Return(value)` primitives.
//
// The load-bearing claim of the coroutine design is that `CoroSuspend` needs no
// new machine codegen: it lowers entirely through the existing I64 store +
// return paths that trust-cg already proves per-instruction on aarch64. This
// test PINS that claim end-to-end. The generator is:
//
//   _gen_step(frame: *i64) -> i64        // one resume of the generator
//
//   bb0:  state = frame[0]
//         switch state { 0 => bb1, _ => bb2 }
//   bb1:  coro_suspend frame, slot=0, next=1, value=42  // first resume: yield 42
//   bb2:  frame[0] = 2; return -1                       // thereafter: completed
//
// The matching `resume` dispatch (`load frame[0]; switch`) is plain trust-ir.

use std::fs;
use std::process::Command;

use trust_cg_codegen::compiler::{Compiler, CompilerConfig};
use trust_cg_codegen::pipeline::OptLevel;
use trust_ir::{
    Block as TrustIrBlock, BlockId, Constant, FuncId, FuncTy, Function as TrustIrFunction, Inst,
    InstrNode, Interpreter, Module as TrustIrModule, SwitchCase, Ty, ValueId,
};

fn can_link_and_run_aarch64_macho() -> bool {
    cfg!(all(target_os = "macos", target_arch = "aarch64"))
}

// ----------------------------------------------------------------------------
// The generator function `_gen_step(frame: *i64) -> i64`.
//
// `state_slot = 0`: the resume state index is `frame[0]` (an I64 element).
// The yield in bb1 is the `CoroSuspend` terminator under test; its lowering
// must record `next_state = 1` into `frame[0]` and return the yielded `42`.
// ----------------------------------------------------------------------------
fn build_gen_step(module: &mut TrustIrModule, func_id: u32, name: &str) {
    let ft = module.add_func_type(FuncTy {
        params: vec![Ty::Ptr],  // frame pointer
        returns: vec![Ty::I64], // yielded value (or -1 sentinel when done)
        is_vararg: false,
    });

    let mut func = TrustIrFunction::new(FuncId::new(func_id), name, ft, BlockId::new(0));
    func.blocks = vec![
        // bb0 (entry): load the resume state from frame[0], dispatch on it.
        TrustIrBlock {
            id: BlockId::new(0),
            params: vec![(ValueId::new(0), Ty::Ptr)],
            body: vec![
                // &frame[0]  (GEP with a single zero index = base + 0*8)
                InstrNode::new(Inst::Const {
                    ty: Ty::I64,
                    value: Constant::Int(0),
                })
                .with_result(ValueId::new(100)),
                InstrNode::new(Inst::GEP {
                    pointee_ty: Ty::I64,
                    base: ValueId::new(0),
                    indices: vec![ValueId::new(100)],
                    inbounds: false,
                })
                .with_result(ValueId::new(1)),
                // state = *(&frame[0])
                InstrNode::new(Inst::Load {
                    ty: Ty::I64,
                    ptr: ValueId::new(1),
                    volatile: false,
                    align: None,
                })
                .with_result(ValueId::new(2)),
                // switch state { 0 => bb1 (yield 42), _ => bb2 (done) }
                InstrNode::new(Inst::Switch {
                    value: ValueId::new(2),
                    default: BlockId::new(2),
                    default_args: vec![],
                    cases: vec![SwitchCase {
                        value: Constant::Int(0),
                        target: BlockId::new(1),
                        args: vec![],
                    }],
                    exhaustive_enum_unreachable: false,
                }),
            ],
        },
        // bb1 (state 0): YIELD 42 via the CoroSuspend terminator under test.
        // Lowering must store next_state=1 into frame[0] and return 42.
        TrustIrBlock {
            id: BlockId::new(1),
            params: vec![],
            body: vec![
                InstrNode::new(Inst::Const {
                    ty: Ty::I64,
                    value: Constant::Int(42),
                })
                .with_result(ValueId::new(11)),
                InstrNode::new(Inst::CoroSuspend {
                    frame: ValueId::new(0),
                    state_slot: 0,
                    next_state: 1,
                    value: ValueId::new(11),
                }),
            ],
        },
        // bb2 (done): record done state (2) into frame[0], return -1 sentinel.
        TrustIrBlock {
            id: BlockId::new(2),
            params: vec![],
            body: vec![
                InstrNode::new(Inst::Const {
                    ty: Ty::I64,
                    value: Constant::Int(2),
                })
                .with_result(ValueId::new(20)),
                InstrNode::new(Inst::Store {
                    ty: Ty::I64,
                    ptr: ValueId::new(1),
                    value: ValueId::new(20),
                    volatile: false,
                    align: None,
                }),
                InstrNode::new(Inst::Const {
                    ty: Ty::I64,
                    value: Constant::Int(-1),
                })
                .with_result(ValueId::new(21)),
                InstrNode::new(Inst::Return {
                    values: vec![ValueId::new(21)],
                }),
            ],
        },
    ];
    module.add_function(func);
}

/// Module containing only `_gen_step` — the backend compilation target.
fn build_generator_module() -> TrustIrModule {
    let mut module = TrustIrModule::new("coroutine");
    build_gen_step(&mut module, 0, "_gen_step");
    module
}

/// Module containing `gen_step` plus a `drive` function the trust-ir
/// interpreter runs in a single shot. `drive` allocates the frame, zeroes the
/// state slot, resumes the generator twice, and returns a checksum that is only
/// correct if the first resume yielded 42 and the frame state advanced 0->1->2:
///
///     checksum = y1 * 10000 + s1 * 100 + s2
///              = 42 * 10000 + 1 * 100 + 2 = 420102
///
/// where `y1` is the first yielded value, `s1`/`s2` the state index after the
/// first / second resume. This pins the CoroSuspend semantics (state save +
/// value return) through the interpreter.
fn build_interpreter_drive_module() -> TrustIrModule {
    let mut module = TrustIrModule::new("coroutine_interp");
    // gen_step is FuncId 1; drive (the entry we execute) is FuncId 0.
    build_gen_step(&mut module, 1, "_gen_step");

    let drive_ft = module.add_func_type(FuncTy {
        params: vec![],
        returns: vec![Ty::I64],
        is_vararg: false,
    });
    let mut drive = TrustIrFunction::new(FuncId::new(0), "_drive", drive_ft, BlockId::new(0));
    drive.blocks = vec![TrustIrBlock {
        id: BlockId::new(0),
        params: vec![],
        body: vec![
            // frame = alloca i64 x 2
            InstrNode::new(Inst::Const {
                ty: Ty::I64,
                value: Constant::Int(2),
            })
            .with_result(ValueId::new(0)),
            InstrNode::new(Inst::Alloca {
                ty: Ty::I64,
                count: Some(ValueId::new(0)),
                align: Some(8),
            })
            .with_result(ValueId::new(1)), // frame ptr
            // frame[0] = 0 (start state)
            InstrNode::new(Inst::Const {
                ty: Ty::I64,
                value: Constant::Int(0),
            })
            .with_result(ValueId::new(2)),
            InstrNode::new(Inst::Store {
                ty: Ty::I64,
                ptr: ValueId::new(1),
                value: ValueId::new(2),
                volatile: false,
                align: None,
            }),
            // y1 = gen_step(frame)  -- first resume, expect 42
            InstrNode::new(Inst::Call {
                callee: FuncId::new(1),
                args: vec![ValueId::new(1)],
            })
            .with_result(ValueId::new(3)),
            // s1 = frame[0]  -- expect 1
            InstrNode::new(Inst::Load {
                ty: Ty::I64,
                ptr: ValueId::new(1),
                volatile: false,
                align: None,
            })
            .with_result(ValueId::new(4)),
            // y2 = gen_step(frame)  -- second resume, expect -1 (unused in sum)
            InstrNode::new(Inst::Call {
                callee: FuncId::new(1),
                args: vec![ValueId::new(1)],
            })
            .with_result(ValueId::new(5)),
            // s2 = frame[0]  -- expect 2
            InstrNode::new(Inst::Load {
                ty: Ty::I64,
                ptr: ValueId::new(1),
                volatile: false,
                align: None,
            })
            .with_result(ValueId::new(6)),
            // checksum = y1 * 10000 + s1 * 100 + s2
            InstrNode::new(Inst::Const {
                ty: Ty::I64,
                value: Constant::Int(10000),
            })
            .with_result(ValueId::new(7)),
            InstrNode::new(Inst::BinOp {
                op: trust_ir::BinOp::Mul,
                ty: Ty::I64,
                lhs: ValueId::new(3), // y1
                rhs: ValueId::new(7), // 10000
            })
            .with_result(ValueId::new(8)),
            InstrNode::new(Inst::Const {
                ty: Ty::I64,
                value: Constant::Int(100),
            })
            .with_result(ValueId::new(9)),
            InstrNode::new(Inst::BinOp {
                op: trust_ir::BinOp::Mul,
                ty: Ty::I64,
                lhs: ValueId::new(4), // s1
                rhs: ValueId::new(9), // 100
            })
            .with_result(ValueId::new(10)),
            InstrNode::new(Inst::BinOp {
                op: trust_ir::BinOp::Add,
                ty: Ty::I64,
                lhs: ValueId::new(8),
                rhs: ValueId::new(10),
            })
            .with_result(ValueId::new(12)),
            InstrNode::new(Inst::BinOp {
                op: trust_ir::BinOp::Add,
                ty: Ty::I64,
                lhs: ValueId::new(12),
                rhs: ValueId::new(6), // s2
            })
            .with_result(ValueId::new(13)),
            InstrNode::new(Inst::Return {
                values: vec![ValueId::new(13)],
            }),
        ],
    }];
    module.add_function(drive);
    module
}

/// Compile the hand-authored module to a Mach-O object at O0.
fn compile_to_obj(module: &TrustIrModule) -> Vec<u8> {
    let compiler = Compiler::new(CompilerConfig {
        opt_level: OptLevel::O0,
        ..CompilerConfig::default()
    });
    let result = compiler
        .compile(module)
        .expect("generator compilation should succeed");
    assert!(
        !result.object_code.is_empty(),
        "generator must produce non-empty object code"
    );
    // Mach-O 64-bit magic.
    let obj = &result.object_code;
    let magic = u32::from_le_bytes([obj[0], obj[1], obj[2], obj[3]]);
    assert_eq!(magic, 0xFEED_FACF, "must be valid Mach-O");
    result.object_code
}

// =============================================================================
// Level (a): trust-ir INTERPRETER runs the generator (fast corroboration).
// =============================================================================

#[test]
fn coroutine_generator_interpreter_yields_sequence() {
    let module = build_interpreter_drive_module();
    let outcome = Interpreter::with_module(&module)
        .execute_func(FuncId::new(0), [])
        .expect("interpreter should run the coroutine driver");

    let checksum = outcome.returns[0]
        .as_int()
        .expect("drive returns an i64")
        .as_signed();

    // y1=42, s1=1, s2=2  ->  42*10000 + 1*100 + 2 = 420102.
    assert_eq!(
        checksum,
        420102,
        "interpreter: first resume must yield 42 (got y1={}), \
         frame state must advance 0->1->2 (got s1={}, s2={})",
        checksum / 10000,
        (checksum / 100) % 100,
        checksum % 100,
    );
}

// =============================================================================
// Level (b): BACKEND lowers to aarch64 Mach-O, links with cc, and RUNS.
// =============================================================================

#[test]
fn coroutine_generator_compiles_to_valid_macho() {
    // Compile-only path: exercises the CoroSuspend lowering on every host.
    let module = build_generator_module();
    let _obj = compile_to_obj(&module);
}

#[test]
fn coroutine_generator_links_runs_and_yields_sequence() {
    if !can_link_and_run_aarch64_macho() {
        eprintln!("SKIP: requires an aarch64-apple-darwin host");
        return;
    }

    let module = build_generator_module();
    let obj_bytes = compile_to_obj(&module);

    let test_dir = std::env::temp_dir().join("trust_cg_e2e_coroutine");
    let _ = fs::remove_dir_all(&test_dir);
    fs::create_dir_all(&test_dir).expect("create temp dir");

    let obj_path = test_dir.join("gen_step.o");
    fs::write(&obj_path, &obj_bytes).expect("write object file");

    // C driver: own the frame, drive the coroutine three times, assert the
    // yielded sequence is exactly 42 (first resume), then -1, -1 (completed),
    // and that the frame state index advances 0 -> 1 -> 2.
    let driver_path = test_dir.join("driver.c");
    let driver_src = r#"
#include <stdio.h>
#include <stdint.h>

extern int64_t _gen_step(int64_t *frame);

int main(void) {
    int64_t frame[2] = {0, 0};   /* state = 0 (start), reserved local slot = 0 */

    int64_t y1 = _gen_step(frame);    /* first resume: yields 42, state -> 1 */
    int64_t s1 = frame[0];
    int64_t y2 = _gen_step(frame);    /* second resume: completed (-1), state -> 2 */
    int64_t s2 = frame[0];
    int64_t y3 = _gen_step(frame);    /* third resume: still completed (-1) */
    int64_t s3 = frame[0];

    printf("y=[%lld,%lld,%lld] state=[%lld,%lld,%lld]\n",
           (long long)y1, (long long)y2, (long long)y3,
           (long long)s1, (long long)s2, (long long)s3);

    if (y1 != 42) return 1;   /* first resume must yield 42 */
    if (s1 != 1)  return 2;   /* CoroSuspend saved next_state=1 into frame[0] */
    if (y2 != -1) return 3;   /* second resume completes */
    if (s2 != 2)  return 4;   /* state advanced to done (2) */
    if (y3 != -1) return 5;   /* completed coroutine stays completed */
    if (s3 != 2)  return 6;   /* done state is stable */
    return 0;
}
"#;
    fs::write(&driver_path, driver_src).expect("write driver source");

    let binary_path = test_dir.join("test_gen");

    let link_output = Command::new("cc")
        .args([
            driver_path.to_str().unwrap(),
            obj_path.to_str().unwrap(),
            "-o",
            binary_path.to_str().unwrap(),
        ])
        .output()
        .expect("cc should be available");

    if !link_output.status.success() {
        panic!(
            "Linking failed:\n{}",
            String::from_utf8_lossy(&link_output.stderr)
        );
    }

    let run_output = Command::new(binary_path.to_str().unwrap())
        .output()
        .expect("should be able to run the binary");

    let stdout = String::from_utf8_lossy(&run_output.stdout);
    eprintln!("coroutine generator stdout: {}", stdout.trim());

    let exit_code = run_output.status.code().unwrap_or(-1);
    assert_eq!(
        exit_code, 0,
        "generator drive failed (exit {}). \
         1=y1!=42, 2=s1!=1, 3=y2!=-1, 4=s2!=2, 5=y3!=-1, 6=s3!=2. stdout: {}",
        exit_code, stdout
    );

    assert_eq!(
        stdout.trim(),
        "y=[42,-1,-1] state=[1,2,2]",
        "generator must yield 42 then complete, advancing state 0->1->2"
    );

    let _ = fs::remove_dir_all(&test_dir);
}
