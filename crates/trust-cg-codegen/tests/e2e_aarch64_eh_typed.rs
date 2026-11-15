// E2E: AArch64 macOS TYPED catches, catch-all after typed, and a module that
// mixes the C++ and Rust personalities, through CG-owned landing pads driven
// from trust-ir `Inst::Invoke` / `Inst::LandingPad` (ledger L03-P11).
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// ----------------------------------------------------------------------------
// WHAT THIS PINS
// ----------------------------------------------------------------------------
// trust-ir names catch clauses by `catch_type_indices` only. The compiler
// binds index `k` to the `k`-th entry of the module's reserved
// `__trust_cg_eh_type_table` global (an array of `SymbolAddr` typeinfo
// symbols), emits identity TType slots (slot `k` == catch type index `k`)
// relocated `ARM64_RELOC_POINTER_TO_GOT`, and, under `__gxx_personality_v0`,
// delivers the matched catch type index as the landing pad's selector. The
// catch-all NULL slot is `N + 1` for the `N`-entry table in a function that
// catches a typed exception (`1` in one that does not), whichever pads
// survive optimization.
//
// 1. Typed catch: a C++ `throw 7` (int) is caught by a CG pad catching only
//    `_ZTIi`; a `throw 2.5` (double) does NOT match and propagates to the C++
//    caller's own `catch (double)`. A typed catch WITH a cleanup
//    (`catch_int_or_cleanup`) still catches the int, and for a non-matching
//    type runs its cleanup exactly once and resumes to that enclosing handler.
// 2. Multi-typed pads: `[int, double]` dispatches on the selector (42 / 43),
//    and `[char, int]` binds the non-contiguous indices 3 and 1 (slot 2 is an
//    inert NULL), so its selectors are the identity, not a compact renumbering.
// 3. Typed then catch-all: `[int, catch-all]` returns 42 for int and 44 for
//    everything else; its twin keeps a second pad catching `char` in an
//    unreachable invoke region that the optimizer prunes at O1+ but not at
//    O0, and still sees the catch-all selector `N + 1` at every level.
// 4. Two personalities in ONE module: a C++ frame (typed catch under
//    `__gxx_personality_v0`) and a Rust frame (cleanup + resume under
//    `rust_eh_personality`, selected by `Producer::TRust`) are linked into a
//    `rustc` driver; a Rust panic resumes through the Rust frame to
//    `catch_unwind` with its cleanup counted, and a C++ exception is caught by
//    the C++ frame.
// 5. The same two crossings through runtime-sized frames compact unwind
//    cannot describe: both functions defer to `__eh_frame` FDEs under one
//    zPLR CIE per personality (pinned in the object), and the unwinder reads
//    each frame's personality and LSDA from its own CIE and FDE.
// 6. The in-memory JIT refuses typed catches and mixed personalities by name;
//    an unbound catch type index, an ELF typed catch and a typed catch under
//    `rust_eh_personality` (which ignores the type table and delivers
//    selector 0) are refused by name.
//
// Native controls run at O0-O3 on AArch64 macOS only (compile-time gated, so
// a Linux run of this target executes the object-level and refusal tests and
// prints no SKIP). Execution uses a polling deadline and
// nonblocking termination requests. Kernel-blocked children can survive a
// timeout; host cleanup is not guaranteed. This is native execution evidence,
// not a proof of the exception tables.

mod common;

#[cfg(all(target_arch = "aarch64", any(target_os = "macos", target_os = "linux")))]
use std::collections::HashMap;
#[cfg(all(target_arch = "aarch64", target_os = "macos"))]
use std::fs;
use std::path::Path;
#[cfg(all(target_arch = "aarch64", target_os = "macos"))]
use std::path::PathBuf;
use std::process::Command;
use std::time::Duration;

use trust_cg_codegen::compiler::{Compiler, CompilerConfig};
use trust_cg_codegen::macho::linker::MachOParser;
use trust_cg_codegen::macho::reloc::AArch64RelocKind;
use trust_cg_codegen::pipeline::OptLevel;
use trust_cg_codegen::target::TargetSpec;
use trust_cg_lower::function::EH_TYPE_TABLE_GLOBAL;
use trust_ir::{
    Block as TrustIrBlock, BlockId, Constant, FuncId, FuncTy, Function as TrustIrFunction, Global,
    ICmpOp, Inst, InstrNode, Linkage, Module as TrustIrModule, Producer, Ty, ValueId,
};

#[path = "common/native_host.rs"]
mod native_host;

const OPT_LEVELS: [OptLevel; 4] = [OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::O3];

// ---------------------------------------------------------------------------
// TrustIR module builders
// ---------------------------------------------------------------------------

fn b(index: u32) -> BlockId {
    BlockId::new(index)
}

fn f(index: u32) -> FuncId {
    FuncId::new(index)
}

fn v(index: u32) -> ValueId {
    ValueId::new(index)
}

fn declare(module: &mut TrustIrModule, id: u32, name: &str, params: Vec<Ty>, returns: Vec<Ty>) {
    let signature = module
        .add_func_type(FuncTy {
            params,
            returns,
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut function = TrustIrFunction::new(f(id), name, signature, b(0));
    function.linkage = Linkage::External;
    module
        .try_add_function(function)
        .expect("Module::try_add_function: test fixture");
}

/// The reserved EH type table: catch type index `k` binds to `symbols[k - 1]`.
fn add_eh_type_table(module: &mut TrustIrModule, symbols: &[&str]) {
    let pointer = module
        .add_type(Ty::Ptr)
        .expect("Module::add_type: test fixture");
    module.globals.push(Global {
        name: EH_TYPE_TABLE_GLOBAL.to_string(),
        ty: Ty::Array(pointer, symbols.len() as u64),
        mutable: false,
        initializer: Some(Constant::Array(
            symbols
                .iter()
                .map(|symbol| Constant::SymbolAddr {
                    symbol: (*symbol).to_string(),
                    addend: 0,
                })
                .collect(),
        )),
        linkage: Linkage::Internal,
        tls: None,
        align: None,
        section: None,
        visibility: Default::default(),
        retained: false,
    });
}

fn constant_return(block: u32, value: i128, result: u32) -> TrustIrBlock {
    TrustIrBlock {
        id: b(block),
        params: vec![],
        body: vec![
            InstrNode::new(Inst::Const {
                ty: Ty::I32,
                value: Constant::Int(value),
            })
            .with_result(v(result)),
            InstrNode::new(Inst::Return {
                values: vec![v(result)],
            }),
        ],
    }
}

/// Entries of the module's reserved EH type table (`0` without one).
fn eh_type_table_len(module: &TrustIrModule) -> u32 {
    module
        .globals
        .iter()
        .find(|global| global.name == EH_TYPE_TABLE_GLOBAL)
        .map_or(0, |global| match &global.initializer {
            Some(Constant::Array(entries)) => entries.len() as u32,
            other => panic!("test type table initializer {other:?}"),
        })
}

/// The selector a function whose pads catch `function_catch_types` receives
/// for catch type index `index` under `__gxx_personality_v0`: the index
/// itself, or, for the catch-all (`0`), `N + 1` for the module's `N`-entry
/// table when the function catches any typed exception and `1` otherwise.
fn selector_for(table_len: u32, function_catch_types: &[u32], index: u32) -> i128 {
    match index {
        0 if function_catch_types.iter().any(|&k| k != 0) => i128::from(table_len) + 1,
        0 => 1,
        typed => i128::from(typed),
    }
}

/// `LandingPad` whose selector is compared against each of `handlers` in
/// order (a match claims the exception and returns the handler's value),
/// falling through to `fallthrough`. Returns the dispatch blocks (the first
/// one begins with the pad, whose results are `v(exn)` / `v(exn + 1)`)
/// followed by the handler blocks, numbered from `first_block`; `values`
/// numbers fresh values.
#[allow(clippy::too_many_arguments)]
fn pad_dispatch_blocks(
    first_block: u32,
    pad: Inst,
    exn: u32,
    handlers: &[(u32, i128)],
    selectors: &[i128],
    fallthrough: u32,
    begin_catch: u32,
    end_catch: u32,
    values: &mut u32,
) -> Vec<TrustIrBlock> {
    let handler_base = first_block + handlers.len() as u32;
    let mut blocks = Vec::new();
    for (position, selector) in selectors.iter().enumerate() {
        let position = position as u32;
        let mut body = Vec::new();
        if position == 0 {
            body.push(InstrNode::new(pad.clone()).with_results(vec![v(exn), v(exn + 1)]));
        }
        let expected = *values;
        let matched = *values + 1;
        *values += 2;
        body.push(
            InstrNode::new(Inst::Const {
                ty: Ty::I32,
                value: Constant::Int(*selector),
            })
            .with_result(v(expected)),
        );
        body.push(
            InstrNode::new(Inst::ICmp {
                op: ICmpOp::Eq,
                ty: Ty::I32,
                lhs: v(exn + 1),
                rhs: v(expected),
            })
            .with_result(v(matched)),
        );
        let else_target = if position + 1 < handlers.len() as u32 {
            first_block + position + 1
        } else {
            fallthrough
        };
        body.push(InstrNode::new(Inst::CondBr {
            cond: v(matched),
            then_target: b(handler_base + position),
            then_args: vec![],
            else_target: b(else_target),
            else_args: vec![],
        }));
        blocks.push(TrustIrBlock {
            id: b(first_block + position),
            params: vec![],
            body,
        });
    }
    for (position, (_, value)) in handlers.iter().enumerate() {
        let position = position as u32;
        let claimed = *values;
        let result = *values + 1;
        *values += 2;
        blocks.push(TrustIrBlock {
            id: b(handler_base + position),
            params: vec![],
            body: vec![
                InstrNode::new(Inst::Call {
                    callee: f(begin_catch),
                    args: vec![v(exn)],
                })
                .with_result(v(claimed)),
                InstrNode::new(Inst::Call {
                    callee: f(end_catch),
                    args: vec![],
                }),
                InstrNode::new(Inst::Const {
                    ty: Ty::I32,
                    value: Constant::Int(*value),
                })
                .with_result(v(result)),
                InstrNode::new(Inst::Return {
                    values: vec![v(result)],
                }),
            ],
        });
    }
    blocks
}

/// `invoke callee() to bb1(ret 0) unwind bb2`, where bb2 is a landing pad
/// catching `handlers[*].0` (0 == catch-all). The pad compares the selector
/// against each handler's catch type index in order; a match claims the
/// exception (`__cxa_begin_catch` / `__cxa_end_catch`) and returns the
/// handler's value; the tail calls `cleanup` (when the pad is also a cleanup)
/// and resumes. Without a cleanup the tail is never reached (the personality
/// only enters the pad for a matching action); with one, the personality
/// enters the pad in the cleanup phase for every non-matching exception.
#[allow(clippy::too_many_arguments)] // Each argument is one column of the catch-shape table.
fn typed_catch_function(
    module: &mut TrustIrModule,
    id: u32,
    name: &str,
    callee: u32,
    handlers: &[(u32, i128)],
    begin_catch: u32,
    end_catch: u32,
    cleanup: Option<u32>,
) {
    let signature = module
        .add_func_type(FuncTy {
            params: vec![],
            returns: vec![Ty::I32],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut function = TrustIrFunction::new(f(id), name, signature, b(0));
    let catch_types: Vec<u32> = handlers.iter().map(|(index, _)| *index).collect();
    let table_len = eh_type_table_len(module);
    let selectors: Vec<i128> = catch_types
        .iter()
        .map(|&index| selector_for(table_len, &catch_types, index))
        .collect();
    let mut blocks = vec![
        TrustIrBlock {
            id: b(0),
            params: vec![],
            body: vec![InstrNode::new(Inst::Invoke {
                callee: f(callee),
                args: vec![],
                normal_dest: b(1),
                normal_args: vec![],
                unwind_dest: b(2),
            })],
        },
        constant_return(1, 0, 10),
    ];
    // Dispatch blocks 2.. compare the selector; handler blocks follow them.
    let resume_block = 2 + 2 * handlers.len() as u32;
    let mut next_value = 100u32;
    blocks.extend(pad_dispatch_blocks(
        2,
        Inst::LandingPad {
            is_cleanup: cleanup.is_some(),
            catch_type_indices: catch_types.clone(),
        },
        20,
        handlers,
        &selectors,
        resume_block,
        begin_catch,
        end_catch,
        &mut next_value,
    ));
    let mut resume_body = Vec::new();
    if let Some(drop_fn) = cleanup {
        resume_body.push(InstrNode::new(Inst::Call {
            callee: f(drop_fn),
            args: vec![],
        }));
    }
    resume_body.push(InstrNode::new(Inst::Resume { exn: v(20) }));
    blocks.push(TrustIrBlock {
        id: b(resume_block),
        params: vec![],
        body: resume_body,
    });
    function.blocks = blocks;
    module
        .try_add_function(function)
        .expect("Module::try_add_function: test fixture");
}

/// `catch_int_then_all` with a second invoke region the optimizer prunes:
///
/// ```text
/// bb0: condbr false, bb1, bb3      ; bb1 never runs (dead, not unreachable)
/// bb1: invoke callee() to bb2 unwind bb9
/// bb2: ret 0
/// bb3: invoke callee() to bb2 unwind bb4
/// bb4..: pad [int, catch-all] -> 42 / 44, else resume
/// bb9..: pad [char] -> 45, else resume
/// ```
///
/// At O0 both pads (and the `char` typeinfo slot) reach the LSDA; at O1+ the
/// unreachable region and its pad are pruned. The reachable pad's catch-all
/// selector is `N + 1` either way: the table the function carries, not the
/// pads that survive, fixes it.
fn catch_int_then_all_pruned_function(
    module: &mut TrustIrModule,
    id: u32,
    name: &str,
    callee: u32,
    begin_catch: u32,
    end_catch: u32,
) {
    let signature = module
        .add_func_type(FuncTy {
            params: vec![],
            returns: vec![Ty::I32],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut function = TrustIrFunction::new(f(id), name, signature, b(0));
    let table_len = eh_type_table_len(module);
    let function_catch_types = [1u32, 0, 3];
    let invoke = |unwind: u32| {
        InstrNode::new(Inst::Invoke {
            callee: f(callee),
            args: vec![],
            normal_dest: b(2),
            normal_args: vec![],
            unwind_dest: b(unwind),
        })
    };
    let mut blocks = vec![
        // `if false { bb1 } else { bb3 }`: the bb1 region never runs but stays
        // structurally reachable (trust-ir refuses a block no edge reaches,
        // `UnreachableBlock`, and since WS7.3 every ingestion entry refuses
        // what the validator refuses); constant-branch folding prunes it.
        TrustIrBlock {
            id: b(0),
            params: vec![],
            body: vec![
                InstrNode::new(Inst::Const {
                    ty: Ty::Bool,
                    value: Constant::Bool(false),
                })
                .with_result(v(99)),
                InstrNode::new(Inst::CondBr {
                    cond: v(99),
                    then_target: b(1),
                    then_args: vec![],
                    else_target: b(3),
                    else_args: vec![],
                }),
            ],
        },
        TrustIrBlock {
            id: b(1),
            params: vec![],
            body: vec![invoke(9)],
        },
        constant_return(2, 0, 10),
        TrustIrBlock {
            id: b(3),
            params: vec![],
            body: vec![invoke(4)],
        },
    ];
    let mut next_value = 100u32;
    // Reachable pad: blocks 4, 5 dispatch; 6, 7 handle; 8 resumes.
    let reachable = [(1u32, 42i128), (0, 44)];
    let selectors: Vec<i128> = reachable
        .iter()
        .map(|&(index, _)| selector_for(table_len, &function_catch_types, index))
        .collect();
    blocks.extend(pad_dispatch_blocks(
        4,
        Inst::LandingPad {
            is_cleanup: false,
            catch_type_indices: vec![1, 0],
        },
        20,
        &reachable,
        &selectors,
        8,
        begin_catch,
        end_catch,
        &mut next_value,
    ));
    blocks.push(TrustIrBlock {
        id: b(8),
        params: vec![],
        body: vec![InstrNode::new(Inst::Resume { exn: v(20) })],
    });
    // Unreachable pad: block 9 dispatches, 10 handles, 11 resumes; its
    // results are `v(30)` / `v(31)`.
    blocks.extend(pad_dispatch_blocks(
        9,
        Inst::LandingPad {
            is_cleanup: false,
            catch_type_indices: vec![3],
        },
        30,
        &[(3, 45)],
        &[selector_for(table_len, &function_catch_types, 3)],
        11,
        begin_catch,
        end_catch,
        &mut next_value,
    ));
    blocks.push(TrustIrBlock {
        id: b(11),
        params: vec![],
        body: vec![InstrNode::new(Inst::Resume { exn: v(30) })],
    });
    function.blocks = blocks;
    module
        .try_add_function(function)
        .expect("Module::try_add_function: test fixture");
}

/// `invoke callee() to bb1(ret 0) unwind cleanup-pad { drop_fn(); resume }`.
fn cleanup_function(module: &mut TrustIrModule, id: u32, name: &str, callee: u32, drop_fn: u32) {
    let signature = module
        .add_func_type(FuncTy {
            params: vec![],
            returns: vec![Ty::I32],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut function = TrustIrFunction::new(f(id), name, signature, b(0));
    // The Rust frontend's provenance selects `rust_eh_personality` for this
    // function alone; the module's other functions keep the C++ default.
    function.producer = Some(Producer::TRust);
    function.blocks = vec![
        TrustIrBlock {
            id: b(0),
            params: vec![],
            body: vec![InstrNode::new(Inst::Invoke {
                callee: f(callee),
                args: vec![],
                normal_dest: b(1),
                normal_args: vec![],
                unwind_dest: b(2),
            })],
        },
        constant_return(1, 0, 10),
        TrustIrBlock {
            id: b(2),
            params: vec![],
            body: vec![
                InstrNode::new(Inst::LandingPad {
                    is_cleanup: true,
                    catch_type_indices: vec![],
                })
                .with_results(vec![v(20), v(21)]),
                InstrNode::new(Inst::Call {
                    callee: f(drop_fn),
                    args: vec![],
                }),
                InstrNode::new(Inst::Resume { exn: v(20) }),
            ],
        },
    ];
    module
        .try_add_function(function)
        .expect("Module::try_add_function: test fixture");
}

const TYPED_FUNCTIONS: [&str; 6] = [
    "catch_int",
    "catch_int_or_double",
    "catch_int_then_all",
    "catch_int_or_cleanup",
    "catch_char_or_int",
    "catch_int_then_all_pruned",
];

/// C++ typed-catch module over the table `[int, double, char]` (`N == 3`):
/// six CG functions invoking `cxx_throw`, catching `[int]`,
/// `[int, double]`, `[int, catch-all]`, `[int]` with a cleanup
/// (`record_cleanup`), `[char, int]` (indices 3 and 1: slot 2 is an inert
/// NULL) and `[int, catch-all]` beside a pruned `[char]` pad respectively.
fn typed_module() -> TrustIrModule {
    let mut module = TrustIrModule::new("eh_typed");
    module.target_info = Some(native_host::target_info());
    declare(&mut module, 0, "cxx_throw", vec![], vec![]);
    declare(
        &mut module,
        1,
        "__cxa_begin_catch",
        vec![Ty::Ptr],
        vec![Ty::Ptr],
    );
    declare(&mut module, 2, "__cxa_end_catch", vec![], vec![]);
    declare(&mut module, 6, "record_cleanup", vec![], vec![]);
    add_eh_type_table(&mut module, &["_ZTIi", "_ZTId", "_ZTIc"]);
    typed_catch_function(
        &mut module,
        3,
        TYPED_FUNCTIONS[0],
        0,
        &[(1, 42)],
        1,
        2,
        None,
    );
    typed_catch_function(
        &mut module,
        4,
        TYPED_FUNCTIONS[1],
        0,
        &[(1, 42), (2, 43)],
        1,
        2,
        None,
    );
    typed_catch_function(
        &mut module,
        5,
        TYPED_FUNCTIONS[2],
        0,
        &[(1, 42), (0, 44)],
        1,
        2,
        None,
    );
    typed_catch_function(
        &mut module,
        7,
        TYPED_FUNCTIONS[3],
        0,
        &[(1, 42)],
        1,
        2,
        Some(6),
    );
    typed_catch_function(
        &mut module,
        8,
        TYPED_FUNCTIONS[4],
        0,
        &[(3, 45), (1, 42)],
        1,
        2,
        None,
    );
    catch_int_then_all_pruned_function(&mut module, 9, TYPED_FUNCTIONS[5], 0, 1, 2);
    module
}

/// Mixed-personality module: `cg_cxx_catch_int` (C++ personality, typed
/// catch of `int`) and `cg_rust_cleanup` (Rust personality, cleanup + resume).
fn two_personality_module() -> TrustIrModule {
    let mut module = TrustIrModule::new("eh_two_personalities");
    module.target_info = Some(native_host::target_info());
    declare(&mut module, 0, "cxx_throw_int", vec![], vec![]);
    declare(
        &mut module,
        1,
        "__cxa_begin_catch",
        vec![Ty::Ptr],
        vec![Ty::Ptr],
    );
    declare(&mut module, 2, "__cxa_end_catch", vec![], vec![]);
    declare(&mut module, 3, "rust_thrower", vec![], vec![]);
    declare(&mut module, 4, "record_cleanup", vec![], vec![]);
    add_eh_type_table(&mut module, &["_ZTIi"]);
    typed_catch_function(
        &mut module,
        5,
        "cg_cxx_catch_int",
        0,
        &[(1, 42)],
        1,
        2,
        None,
    );
    cleanup_function(&mut module, 6, "cg_rust_cleanup", 3, 4);
    module
}

/// `f(n: i64) -> i32`: a runtime-sized `Alloca { count: Some(n) }` handed to
/// `invoke callee(buffer)`. The variable-size frame is one compact unwind
/// cannot describe (`UNWIND_ARM64_MODE_DWARF`), so the Mach-O planner gives
/// the function a DWARF FDE under the zPLR CIE of its own personality. The
/// landing pad either catches `int` (catch type index 1: claim it and return
/// 42) or, with `cleanup_callee`, is a pure cleanup that calls it and resumes.
fn dynamic_frame_function(
    module: &mut TrustIrModule,
    id: u32,
    name: &str,
    callee: u32,
    cleanup_callee: Option<u32>,
    producer: Option<Producer>,
) {
    let signature = module
        .add_func_type(FuncTy {
            params: vec![Ty::I64],
            returns: vec![Ty::I32],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut function = TrustIrFunction::new(f(id), name, signature, b(0));
    function.producer = producer;
    let pad = match cleanup_callee {
        Some(drop_fn) => vec![
            InstrNode::new(Inst::LandingPad {
                is_cleanup: true,
                catch_type_indices: vec![],
            })
            .with_results(vec![v(20), v(21)]),
            InstrNode::new(Inst::Call {
                callee: f(drop_fn),
                args: vec![],
            }),
            InstrNode::new(Inst::Resume { exn: v(20) }),
        ],
        None => vec![
            InstrNode::new(Inst::LandingPad {
                is_cleanup: false,
                catch_type_indices: vec![1],
            })
            .with_results(vec![v(20), v(21)]),
            InstrNode::new(Inst::Const {
                ty: Ty::I32,
                value: Constant::Int(1),
            })
            .with_result(v(22)),
            InstrNode::new(Inst::ICmp {
                op: ICmpOp::Eq,
                ty: Ty::I32,
                lhs: v(21),
                rhs: v(22),
            })
            .with_result(v(23)),
            InstrNode::new(Inst::CondBr {
                cond: v(23),
                then_target: b(3),
                then_args: vec![],
                else_target: b(4),
                else_args: vec![],
            }),
        ],
    };
    let mut blocks = vec![
        TrustIrBlock {
            id: b(0),
            params: vec![(v(1), Ty::I64)],
            body: vec![
                InstrNode::new(Inst::Alloca {
                    ty: Ty::I8,
                    count: Some(v(1)),
                    align: None,
                })
                .with_result(v(2)),
                InstrNode::new(Inst::Invoke {
                    callee: f(callee),
                    args: vec![v(2)],
                    normal_dest: b(1),
                    normal_args: vec![],
                    unwind_dest: b(2),
                }),
            ],
        },
        constant_return(1, 0, 10),
        TrustIrBlock {
            id: b(2),
            params: vec![],
            body: pad,
        },
    ];
    if cleanup_callee.is_none() {
        blocks.push(TrustIrBlock {
            id: b(3),
            params: vec![],
            body: vec![
                InstrNode::new(Inst::Call {
                    callee: f(1),
                    args: vec![v(20)],
                })
                .with_result(v(30)),
                InstrNode::new(Inst::Call {
                    callee: f(2),
                    args: vec![],
                }),
                InstrNode::new(Inst::Const {
                    ty: Ty::I32,
                    value: Constant::Int(42),
                })
                .with_result(v(31)),
                InstrNode::new(Inst::Return {
                    values: vec![v(31)],
                }),
            ],
        });
        blocks.push(TrustIrBlock {
            id: b(4),
            params: vec![],
            body: vec![InstrNode::new(Inst::Resume { exn: v(20) })],
        });
    }
    function.blocks = blocks;
    module
        .try_add_function(function)
        .expect("Module::try_add_function: test fixture");
}

/// Mixed-personality module whose two EH frames both need the DWARF
/// fallback: `cg_cxx_catch_int_dyn` (C++ personality, typed catch of `int`;
/// `__cxa_begin_catch` / `__cxa_end_catch` are ids 1 and 2) and
/// `cg_rust_cleanup_dyn` (Rust personality, cleanup + resume), so
/// `__eh_frame` carries one zPLR CIE per personality.
fn two_personality_dwarf_module() -> TrustIrModule {
    let mut module = TrustIrModule::new("eh_two_personalities_dwarf");
    module.target_info = Some(native_host::target_info());
    declare(&mut module, 0, "cxx_throw_int_into", vec![Ty::Ptr], vec![]);
    declare(
        &mut module,
        1,
        "__cxa_begin_catch",
        vec![Ty::Ptr],
        vec![Ty::Ptr],
    );
    declare(&mut module, 2, "__cxa_end_catch", vec![], vec![]);
    declare(&mut module, 3, "rust_thrower_into", vec![Ty::Ptr], vec![]);
    declare(&mut module, 4, "record_cleanup", vec![], vec![]);
    add_eh_type_table(&mut module, &["_ZTIi"]);
    dynamic_frame_function(&mut module, 5, "cg_cxx_catch_int_dyn", 0, None, None);
    dynamic_frame_function(
        &mut module,
        6,
        "cg_rust_cleanup_dyn",
        3,
        Some(4),
        Some(Producer::TRust),
    );
    module
}

fn compile_for(module: &TrustIrModule, opt_level: OptLevel, triple: &str) -> Vec<u8> {
    let spec = TargetSpec::parse(triple).expect("triple parses");
    let result = Compiler::new_for_target_spec(
        CompilerConfig {
            opt_level,
            ..CompilerConfig::default()
        },
        spec,
    )
    .with_codegen_license(permit_unlicensed())
    .compile(module)
    .unwrap_or_else(|error| panic!("{opt_level:?} {triple}: {error}"));
    result.object_code
}

fn contains(haystack: &[u8], needle: &[u8]) -> bool {
    haystack.windows(needle.len()).any(|w| w == needle)
}

// ---------------------------------------------------------------------------
// Object-level control (every host): GOT-relocated TType entries
// ---------------------------------------------------------------------------

fn read_uleb(bytes: &[u8], at: &mut usize) -> u64 {
    let mut value = 0u64;
    let mut shift = 0;
    loop {
        let byte = bytes[*at];
        *at += 1;
        value |= u64::from(byte & 0x7f) << shift;
        shift += 7;
        if byte & 0x80 == 0 {
            return value;
        }
    }
}

fn read_sleb(bytes: &[u8], at: &mut usize) -> i64 {
    let mut value = 0i64;
    let mut shift = 0;
    loop {
        let byte = bytes[*at];
        *at += 1;
        value |= i64::from(byte & 0x7f) << shift;
        shift += 7;
        if byte & 0x80 == 0 {
            if shift < 64 && byte & 0x40 != 0 {
                value |= -1i64 << shift;
            }
            return value;
        }
    }
}

/// One function's LSDA decoded from the object: the action chains (type
/// filters in order, `0` = cleanup) its call sites name, in first-use order,
/// and the section offset of its TType base.
struct DecodedLsda {
    chains: Vec<Vec<i64>>,
    ttype_base: usize,
}

/// Decode the LSDA starting at `start` of `__gcc_except_tab`, independently
/// of the emitter: header, ULEB128 call-site table, action chains.
fn decode_lsda(section: &[u8], start: usize) -> DecodedLsda {
    assert_eq!(section[start], 0xff, "LPStart omitted");
    assert_eq!(section[start + 1], 0x9b, "indirect|pcrel|sdata4 TType");
    let mut at = start + 2;
    let ttype_offset = read_uleb(section, &mut at) as usize;
    let ttype_base = at + ttype_offset;
    assert_eq!(section[at], 0x01, "ULEB128 call-site encoding");
    at += 1;
    let call_sites_len = read_uleb(section, &mut at) as usize;
    let call_sites_end = at + call_sites_len;
    let mut action_offsets = Vec::new();
    while at < call_sites_end {
        for _ in 0..3 {
            read_uleb(section, &mut at);
        }
        let action = read_uleb(section, &mut at) as usize;
        if action != 0 && !action_offsets.contains(&action) {
            action_offsets.push(action);
        }
    }
    assert_eq!(at, call_sites_end, "call-site table tiles its length");
    let chains = action_offsets
        .into_iter()
        .map(|action| {
            let mut record = call_sites_end + action - 1;
            let mut chain = Vec::new();
            loop {
                let mut cursor = record;
                chain.push(read_sleb(section, &mut cursor));
                let next_field = cursor;
                let next = read_sleb(section, &mut cursor);
                if next == 0 {
                    break chain;
                }
                record = (next_field as i64 + next) as usize;
            }
        })
        .collect();
    DecodedLsda { chains, ttype_base }
}

/// Every typed slot of every LSDA is an `ARM64_RELOC_POINTER_TO_GOT`
/// (pc-relative, 4 bytes, extern) against its typeinfo symbol, the reserved
/// type-table global is consumed rather than emitted, and only the C++
/// personality is imported. Decoding each function's LSDA from the object
/// pins the selector contract: every relocated slot `k` is catch type index
/// `k` (the non-contiguous `[char, int]` pad names filters 3 and 1, not a
/// compact renumbering), and both catch-all chains name slot `N + 1 == 4` at
/// every level, although the pruned twin's `char` pad (and its `_ZTIc` slot)
/// reaches the LSDA at some levels and not at others.
#[test]
fn typed_catch_objects_carry_got_relocated_typeinfo_entries() {
    let module = typed_module();
    let table = ["_ZTIi", "_ZTId", "_ZTIc"];
    let mut pruned_shapes = std::collections::BTreeSet::new();
    for opt_level in OPT_LEVELS {
        let obj = compile_for(&module, opt_level, "aarch64-apple-darwin");
        native_host::assert_macho_arm64_object(&obj);
        let parsed = MachOParser::parse(&obj).expect("parse Mach-O object");
        let lsda = parsed
            .sections
            .iter()
            .find(|section| section.name == "__gcc_except_tab")
            .expect("typed-catch object carries __gcc_except_tab");
        let mut starts: Vec<(usize, &str)> = parsed
            .symbols
            .iter()
            .filter_map(|symbol| {
                let function = symbol
                    .name
                    .as_str()
                    .trim_start_matches('_')
                    .strip_prefix("GCC_except_table_")?;
                Some(((symbol.value - lsda.addr) as usize, function))
            })
            .collect();
        starts.sort_unstable();
        assert_eq!(
            starts.len(),
            TYPED_FUNCTIONS.len(),
            "{opt_level:?}: one LSDA per EH function"
        );
        for reloc in &lsda.relocations {
            assert_eq!(reloc.kind, AArch64RelocKind::PointerToGot, "{opt_level:?}");
            assert!(reloc.pc_relative, "{opt_level:?}");
            assert_eq!(reloc.length, 2, "{opt_level:?}: 4-byte sdata4 slot");
            assert!(reloc.is_extern, "{opt_level:?}");
            assert_eq!(
                &lsda.data[reloc.offset as usize..reloc.offset as usize + 4],
                &[0, 0, 0, 0],
                "{opt_level:?}: the slot is a zero placeholder the linker fills"
            );
        }
        for (position, &(start, function)) in starts.iter().enumerate() {
            let end = starts
                .get(position + 1)
                .map_or(lsda.data.len(), |&(next, _)| next);
            let decoded = decode_lsda(&lsda.data, start);
            // Each relocated slot `k` (TType base - 4k) names table[k - 1].
            let mut bound: Vec<(i64, String)> = lsda
                .relocations
                .iter()
                .filter(|reloc| (start..end).contains(&(reloc.offset as usize)))
                .map(|reloc| {
                    let back = decoded.ttype_base - reloc.offset as usize;
                    assert_eq!(back % 4, 0, "{opt_level:?} {function}: slot alignment");
                    let slot = (back / 4) as i64;
                    let target = parsed.symbols[reloc.symbol_index as usize].name.as_str();
                    assert_eq!(
                        target,
                        format!("_{}", table[slot as usize - 1]),
                        "{opt_level:?} {function}: identity slot {slot}"
                    );
                    (slot, target.to_owned())
                })
                .collect();
            bound.sort_unstable();
            let bound_slots: Vec<i64> = bound.iter().map(|(slot, _)| *slot).collect();
            let expected_chains: Vec<Vec<i64>> = match function {
                "catch_int" => vec![vec![1]],
                "catch_int_or_double" => vec![vec![1, 2]],
                "catch_int_then_all" => vec![vec![1, 4]],
                "catch_int_or_cleanup" => vec![vec![1, 0]],
                "catch_char_or_int" => vec![vec![3, 1]],
                "catch_int_then_all_pruned" => {
                    assert!(
                        decoded.chains.contains(&vec![1, 4])
                            && decoded
                                .chains
                                .iter()
                                .all(|chain| *chain == [1, 4] || *chain == [3]),
                        "{opt_level:?}: the surviving catch-all is slot N + 1 and the \
                         only other pad catches char: {:?}",
                        decoded.chains
                    );
                    pruned_shapes.insert(decoded.chains.len());
                    decoded.chains.clone()
                }
                other => panic!("unexpected LSDA owner {other}"),
            };
            assert_eq!(
                decoded.chains, expected_chains,
                "{opt_level:?} {function}: action chains"
            );
            // Exactly the typed indices the chains name are relocated.
            let mut named: Vec<i64> = decoded
                .chains
                .iter()
                .flatten()
                .copied()
                .filter(|&filter| (1..=3).contains(&filter))
                .collect();
            named.sort_unstable();
            named.dedup();
            assert_eq!(bound_slots, named, "{opt_level:?} {function}: bound slots");
        }
        assert!(
            parsed
                .symbols
                .iter()
                .any(|symbol| symbol.name == "___gxx_personality_v0"),
            "{opt_level:?}: C++ personality imported"
        );
        assert!(
            !parsed
                .symbols
                .iter()
                .any(|symbol| symbol.name.contains(EH_TYPE_TABLE_GLOBAL)),
            "{opt_level:?}: the reserved type table is a compiler input, not a data object"
        );
        assert!(
            !contains(&obj, b"rust_eh_personality"),
            "{opt_level:?}: a C++-only module imports no Rust personality"
        );
    }
    // The pruned twin exercises what it exists for: its unreachable `char`
    // pad reaches the LSDA at some level (O0) and is pruned at another (O1+),
    // while its catch-all selector stays `N + 1`. If the optimizer stops (or
    // starts) pruning at every level, move the control, do not drop it.
    assert_eq!(
        pruned_shapes.into_iter().collect::<Vec<_>>(),
        [1, 2],
        "the pruned twin must see both LSDA shapes across O0-O3"
    );
}

/// The mixed module binds each function's compact-unwind entry to its own
/// personality: both routines are imported, each exactly once.
#[test]
fn two_personality_objects_import_both_personalities() {
    let module = two_personality_module();
    for opt_level in OPT_LEVELS {
        let obj = compile_for(&module, opt_level, "aarch64-apple-darwin");
        native_host::assert_macho_arm64_object(&obj);
        let parsed = MachOParser::parse(&obj).expect("parse Mach-O object");
        let count = |name: &str| {
            parsed
                .symbols
                .iter()
                .filter(|symbol| symbol.name == name)
                .count()
        };
        assert_eq!(count("___gxx_personality_v0"), 1, "{opt_level:?}");
        assert_eq!(count("_rust_eh_personality"), 1, "{opt_level:?}");
        let compact_unwind = parsed
            .sections
            .iter()
            .find(|section| section.name == "__compact_unwind")
            .expect("module carries __LD,__compact_unwind");
        // Two EH entries, each relocating its own personality (+ function
        // and LSDA), and neither DWARF fallback.
        let personality_targets: Vec<&str> = compact_unwind
            .relocations
            .iter()
            .map(|reloc| parsed.symbols[reloc.symbol_index as usize].name.as_str())
            .filter(|name| name.contains("personality"))
            .collect();
        assert_eq!(
            personality_targets.len(),
            2,
            "{opt_level:?}: {personality_targets:?}"
        );
        assert!(
            personality_targets.contains(&"___gxx_personality_v0")
                && personality_targets.contains(&"_rust_eh_personality"),
            "{opt_level:?}: {personality_targets:?}"
        );
    }
}

/// `UNWIND_ARM64_MODE_DWARF`: the compact-unwind mode that defers to a FDE.
const UNWIND_ARM64_MODE_DWARF: u32 = 0x0300_0000;

/// The CIE records of a Mach-O object's `__eh_frame` (no terminator: ld64
/// rejects one), as `(section offset, augmentation string)`.
fn eh_frame_cies(eh_frame: &[u8]) -> Vec<(usize, String)> {
    let mut cies = Vec::new();
    let mut at = 0usize;
    while at + 8 <= eh_frame.len() {
        let length = u32::from_le_bytes(eh_frame[at..at + 4].try_into().unwrap()) as usize;
        assert!(
            length != 0 && length != 0xffff_ffff,
            "unexpected record length {length:#x} at {at}"
        );
        let id = u32::from_le_bytes(eh_frame[at + 4..at + 8].try_into().unwrap());
        if id == 0 {
            // version byte, then the NUL-terminated augmentation string.
            let augmentation_start = at + 9;
            let augmentation_end = augmentation_start
                + eh_frame[augmentation_start..]
                    .iter()
                    .position(|&byte| byte == 0)
                    .expect("CIE augmentation is NUL-terminated");
            cies.push((
                at,
                String::from_utf8_lossy(&eh_frame[augmentation_start..augmentation_end])
                    .into_owned(),
            ));
        }
        at += 4 + length;
    }
    assert_eq!(at, eh_frame.len(), "__eh_frame records tile the section");
    cies
}

/// Both frames of the DWARF-fallback mixed module defer to `__eh_frame`
/// (`UNWIND_ARM64_MODE_DWARF`), and `__eh_frame` carries exactly two zPLR
/// CIEs whose personality pointers are GOT-relocated against the two
/// routines, plus the typed catch's GOT-relocated TType slot. This pins
/// that the native control below exercises the per-personality CIEs, not
/// compact-unwind personality fields.
#[test]
fn two_personality_dwarf_fallback_objects_carry_one_cie_per_personality() {
    let module = two_personality_dwarf_module();
    for opt_level in OPT_LEVELS {
        let obj = compile_for(&module, opt_level, "aarch64-apple-darwin");
        native_host::assert_macho_arm64_object(&obj);
        let parsed = MachOParser::parse(&obj).expect("parse Mach-O object");
        let section = |name: &str| {
            parsed
                .sections
                .iter()
                .find(|section| section.name == name)
                .unwrap_or_else(|| panic!("{opt_level:?}: object carries {name}"))
        };
        let compact_unwind = section("__compact_unwind");
        assert_eq!(compact_unwind.data.len() % 32, 0, "{opt_level:?}");
        let modes: Vec<u32> = compact_unwind
            .data
            .as_chunks::<32>()
            .0
            .iter()
            .map(|entry| u32::from_le_bytes(entry[12..16].try_into().unwrap()) & 0x0f00_0000)
            .collect();
        assert_eq!(
            modes,
            [UNWIND_ARM64_MODE_DWARF, UNWIND_ARM64_MODE_DWARF],
            "{opt_level:?}: both runtime-sized frames defer to their FDE"
        );
        let eh_frame = section("__eh_frame");
        let cies = eh_frame_cies(&eh_frame.data);
        assert_eq!(
            cies.iter()
                .map(|(_, augmentation)| augmentation.as_str())
                .collect::<Vec<_>>(),
            ["zPLR", "zPLR"],
            "{opt_level:?}: one zPLR CIE per personality"
        );
        let mut got_targets: Vec<&str> = eh_frame
            .relocations
            .iter()
            .filter(|reloc| reloc.kind == AArch64RelocKind::PointerToGot)
            .map(|reloc| parsed.symbols[reloc.symbol_index as usize].name.as_str())
            .collect();
        got_targets.sort_unstable();
        assert_eq!(
            got_targets,
            ["___gxx_personality_v0", "_rust_eh_personality"],
            "{opt_level:?}: each CIE names its own personality"
        );
        let lsda = section("__gcc_except_tab");
        let ttype_targets: Vec<&str> = lsda
            .relocations
            .iter()
            .map(|reloc| {
                assert_eq!(reloc.kind, AArch64RelocKind::PointerToGot, "{opt_level:?}");
                parsed.symbols[reloc.symbol_index as usize].name.as_str()
            })
            .collect();
        assert_eq!(ttype_targets, ["__ZTIi"], "{opt_level:?}");

        // Every FDE sits under the CIE of its own function's personality,
        // and every self-relative pointer (subtractor `EH_Frame` + unsigned
        // target) stores the addend `-(section offset of the field)`: a CIE
        // group laid out after the first one must fold its base into both.
        let data = &eh_frame.data;
        fn target<'a>(
            parsed: &'a trust_cg_codegen::macho::linker::ParsedObject,
            reloc: &trust_cg_codegen::macho::reloc::Relocation,
        ) -> &'a str {
            parsed.symbols[reloc.symbol_index as usize].name.as_str()
        }
        let symbol_name =
            |reloc: &trust_cg_codegen::macho::reloc::Relocation| target(&parsed, reloc);
        let mut subtractor_offsets = Vec::new();
        for reloc in &eh_frame.relocations {
            if reloc.kind == AArch64RelocKind::Subtractor {
                assert_eq!(symbol_name(reloc), "EH_Frame", "{opt_level:?}");
                let offset = reloc.offset as usize;
                let addend = i64::from_le_bytes(data[offset..offset + 8].try_into().unwrap());
                assert_eq!(
                    addend,
                    -(offset as i64),
                    "{opt_level:?}: self-relative field at {offset:#x} must store -(its \
                     section offset)"
                );
                subtractor_offsets.push(offset);
            }
        }
        let cie_personality = |cie_at: usize| {
            let length = u32::from_le_bytes(data[cie_at..cie_at + 4].try_into().unwrap()) as usize;
            let personalities: Vec<&str> = eh_frame
                .relocations
                .iter()
                .filter(|reloc| {
                    reloc.kind == AArch64RelocKind::PointerToGot
                        && (cie_at..cie_at + 4 + length).contains(&(reloc.offset as usize))
                })
                .map(symbol_name)
                .collect();
            assert_eq!(personalities.len(), 1, "{opt_level:?}: CIE at {cie_at:#x}");
            personalities[0]
        };
        let mut at = 0usize;
        let mut fdes = Vec::new();
        while at < data.len() {
            let length = u32::from_le_bytes(data[at..at + 4].try_into().unwrap()) as usize;
            let id = u32::from_le_bytes(data[at + 4..at + 8].try_into().unwrap()) as usize;
            if id != 0 {
                let cie_at = at + 4 - id;
                assert!(
                    cies.iter().any(|(offset, _)| *offset == cie_at),
                    "{opt_level:?}: FDE at {at:#x} points at a CIE"
                );
                // The FDE's two self-relative pointers: pc-begin (a function)
                // and the LSDA (that function's `GCC_except_table`).
                let targets: Vec<&str> = eh_frame
                    .relocations
                    .iter()
                    .filter(|reloc| {
                        reloc.kind == AArch64RelocKind::Unsigned
                            && (at..at + 4 + length).contains(&(reloc.offset as usize))
                    })
                    .map(|reloc| {
                        assert!(
                            subtractor_offsets.contains(&(reloc.offset as usize)),
                            "{opt_level:?}: unsigned leg at {:#x} pairs with a subtractor",
                            reloc.offset
                        );
                        symbol_name(reloc)
                    })
                    .collect();
                let function = targets
                    .iter()
                    .copied()
                    .find(|name| !name.contains("GCC_except_table"))
                    .expect("FDE pc-begin relocation");
                assert!(
                    targets.contains(&format!("_GCC_except_table{function}").as_str()),
                    "{opt_level:?}: FDE of {function} carries its own LSDA: {targets:?}"
                );
                fdes.push((function.to_owned(), cie_personality(cie_at).to_owned()));
            }
            at += 4 + length;
        }
        fdes.sort_unstable();
        assert_eq!(
            fdes,
            [
                (
                    "_cg_cxx_catch_int_dyn".to_owned(),
                    "___gxx_personality_v0".to_owned()
                ),
                (
                    "_cg_rust_cleanup_dyn".to_owned(),
                    "_rust_eh_personality".to_owned()
                ),
            ],
            "{opt_level:?}: each FDE under its own personality's CIE"
        );
    }
}

// ---------------------------------------------------------------------------
// Fail-closed controls (every host)
// ---------------------------------------------------------------------------

/// A catch type index the module's table does not bind is refused by name at
/// lowering; a typed catch without any table is refused the same way.
#[test]
fn unbound_catch_type_index_is_refused_by_name() {
    let mut module = typed_module();
    // catch_int catches index 1; shrink the table to zero entries.
    module
        .globals
        .retain(|global| global.name != EH_TYPE_TABLE_GLOBAL);
    add_eh_type_table(&mut module, &[]);
    let spec = TargetSpec::parse("aarch64-apple-darwin").expect("triple parses");
    let error = Compiler::new_for_target_spec(CompilerConfig::default(), spec)
        .with_codegen_license(permit_unlicensed())
        .compile(&module)
        .expect_err("an unbound catch type index must not emit a NULL (catch-all) slot");
    let message = format!("{error}");
    assert!(
        message.contains("[TCG-EH-TTYPE]") && message.contains("not bound"),
        "{message}"
    );

    module
        .globals
        .retain(|global| global.name != EH_TYPE_TABLE_GLOBAL);
    let error = Compiler::new_for_target_spec(CompilerConfig::default(), spec)
        .with_codegen_license(permit_unlicensed())
        .compile(&module)
        .expect_err("a typed catch without a type table must be refused");
    let message = format!("{error}");
    assert!(
        message.contains("[TCG-EH-TTYPE]") && message.contains(EH_TYPE_TABLE_GLOBAL),
        "{message}"
    );
}

/// The AArch64 ELF emitter carries no `.gcc_except_table` typeinfo relocation
/// yet: a typed catch headed for Linux is refused by name (catch-all and
/// cleanup pads keep their ELF path).
#[test]
fn elf_typed_catch_is_refused_by_name() {
    let module = typed_module();
    let spec = TargetSpec::parse("aarch64-unknown-linux-gnu").expect("triple parses");
    let error = Compiler::new_for_target_spec(CompilerConfig::default(), spec)
        .with_codegen_license(permit_unlicensed())
        .compile(&module)
        .expect_err("an ELF typed catch must not ship an unrelocated TType slot");
    let message = format!("{error}");
    assert!(
        message.contains("[TCG-EH-TTYPE]") && message.contains("Mach-O-only"),
        "{message}"
    );
}

/// `rust_eh_personality` ignores the LSDA type table: it enters the pad for
/// any positive first action and delivers selector 0, so a typed catch under
/// it would silently catch every exception with a selector that matches no
/// handler. Both routes that select the Rust personality refuse it by name at
/// lowering: a function stamped `Producer::TRust`, and a module that declares
/// `rust_eh_personality` (its module default).
#[test]
fn typed_catch_under_the_rust_personality_is_refused_by_name() {
    let spec = TargetSpec::parse("aarch64-apple-darwin").expect("triple parses");
    let mut stamped = typed_module();
    stamped
        .functions
        .iter_mut()
        .find(|function| function.name == "catch_int")
        .expect("catch_int")
        .producer = Some(Producer::TRust);
    let mut declared = typed_module();
    declare(&mut declared, 10, "rust_eh_personality", vec![], vec![]);
    for (route, module) in [("Producer::TRust", stamped), ("declared", declared)] {
        for opt_level in [OptLevel::O0, OptLevel::O2] {
            let error = Compiler::new_for_target_spec(
                CompilerConfig {
                    opt_level,
                    ..CompilerConfig::default()
                },
                spec,
            )
            .with_codegen_license(permit_unlicensed())
            .compile(&module)
            .expect_err("a typed catch under rust_eh_personality must not compile");
            let message = format!("{error}");
            assert!(
                message.contains("[TCG-EH-TTYPE]")
                    && message.contains("rust_eh_personality")
                    && message.contains("ignores the LSDA type table"),
                "{route} {opt_level:?}: {message}"
            );
        }
    }
}

/// The in-memory JIT publishes catch-all and cleanup LSDAs only: a typed
/// catch is refused by name before any table is published.
#[cfg(all(target_arch = "aarch64", any(target_os = "macos", target_os = "linux")))]
#[test]
fn jit_refuses_typed_catches_by_name() {
    extern "C" fn stub() {}
    fn address<T: Copy>(function: T) -> *const u8 {
        assert_eq!(std::mem::size_of::<T>(), std::mem::size_of::<*const u8>());
        // SAFETY: `T` is a function-pointer type of pointer size.
        unsafe { std::mem::transmute_copy::<T, *const u8>(&function) }
    }
    let module = typed_module();
    let externs: HashMap<String, *const u8> = [
        "cxx_throw",
        "__cxa_begin_catch",
        "__cxa_end_catch",
        "record_cleanup",
        "__gxx_personality_v0",
        "_Unwind_Resume",
    ]
    .into_iter()
    .map(|name| (name.to_owned(), address(stub as extern "C" fn())))
    .collect();
    let error = Compiler::new(CompilerConfig {
        opt_level: OptLevel::O1,
        parallel: false,
        ..CompilerConfig::for_host_jit_unchecked()
    })
    .with_codegen_license(permit_unlicensed())
    .compile_module_to_jit(&module, &externs)
    .expect_err("the JIT must refuse typed catches rather than publish a NULL slot");
    let message = format!("{error}");
    assert!(
        message.contains("cannot bind typed-catch typeinfo symbols") && message.contains("_ZTIi"),
        "{message}"
    );
}

/// The in-memory JIT publishes one CIE: a trust-ir module whose provenance
/// selects two personalities (a C++ catch-all frame beside a
/// `Producer::TRust` cleanup frame, no typed catch) is refused by name before
/// any table is published, although the Mach-O objects above carry both.
#[cfg(all(target_arch = "aarch64", any(target_os = "macos", target_os = "linux")))]
#[test]
fn jit_refuses_mixed_personalities_by_name() {
    extern "C" fn stub() {}
    fn address<T: Copy>(function: T) -> *const u8 {
        assert_eq!(std::mem::size_of::<T>(), std::mem::size_of::<*const u8>());
        // SAFETY: `T` is a function-pointer type of pointer size.
        unsafe { std::mem::transmute_copy::<T, *const u8>(&function) }
    }
    let mut module = TrustIrModule::new("eh_two_personalities_jit");
    module.target_info = Some(native_host::target_info());
    declare(&mut module, 0, "cxx_throw_int", vec![], vec![]);
    declare(
        &mut module,
        1,
        "__cxa_begin_catch",
        vec![Ty::Ptr],
        vec![Ty::Ptr],
    );
    declare(&mut module, 2, "__cxa_end_catch", vec![], vec![]);
    declare(&mut module, 3, "rust_thrower", vec![], vec![]);
    declare(&mut module, 4, "record_cleanup", vec![], vec![]);
    typed_catch_function(
        &mut module,
        5,
        "cg_cxx_catch_all",
        0,
        &[(0, 44)],
        1,
        2,
        None,
    );
    cleanup_function(&mut module, 6, "cg_rust_cleanup", 3, 4);
    let externs: HashMap<String, *const u8> = [
        "cxx_throw_int",
        "__cxa_begin_catch",
        "__cxa_end_catch",
        "rust_thrower",
        "record_cleanup",
        "__gxx_personality_v0",
        "rust_eh_personality",
        "_Unwind_Resume",
    ]
    .into_iter()
    .map(|name| (name.to_owned(), address(stub as extern "C" fn())))
    .collect();
    let error = Compiler::new(CompilerConfig {
        opt_level: OptLevel::O1,
        parallel: false,
        ..CompilerConfig::for_host_jit_unchecked()
    })
    .with_codegen_license(permit_unlicensed())
    .compile_module_to_jit(&module, &externs)
    .expect_err("the JIT must refuse a module whose frames name two personalities");
    let message = format!("{error}");
    assert!(
        message.contains("support one personality routine per module")
            && message.contains("__gxx_personality_v0")
            && message.contains("rust_eh_personality"),
        "{message}"
    );
}

// ---------------------------------------------------------------------------
// Native controls (AArch64 macOS only)
// ---------------------------------------------------------------------------
//
// The native controls are compiled only for AArch64 macOS: the AArch64 ELF
// emitter refuses typed catches and mixed personalities by name (see
// `elf_typed_catch_is_refused_by_name`), so a Linux GNU host keeps the
// object-level and refusal coverage of this file, and no runtime SKIP line
// reaches a floor transcript.

#[cfg(all(target_arch = "aarch64", target_os = "macos"))]
fn fresh_dir(name: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(name);
    let _ = fs::remove_dir_all(&dir);
    fs::create_dir_all(&dir).expect("create test dir");
    dir
}

#[cfg(all(target_arch = "aarch64", target_os = "macos"))]
fn run_checked(command: &mut Command, what: &str) {
    let output = command
        .output()
        .unwrap_or_else(|error| panic!("{what}: {error}"));
    assert!(
        output.status.success(),
        "{what} failed:\n{}\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
}

/// C++ driver exercising every (thrown type, CG function) pair. Each CG
/// function is called inside the driver's own handlers so a non-matching
/// typed catch is observed falling through to the ENCLOSING C++ handler, and
/// the cleanup pad's `record_cleanup` calls are counted.
#[cfg(all(target_arch = "aarch64", target_os = "macos"))]
const TYPED_DRIVER: &str = r#"
#include <cstdio>
extern "C" int catch_int();
extern "C" int catch_int_or_double();
extern "C" int catch_int_then_all();
extern "C" int catch_int_or_cleanup();
extern "C" int catch_char_or_int();
extern "C" int catch_int_then_all_pruned();
static int mode = 0;
static int cleanups = 0;
extern "C" void record_cleanup() { ++cleanups; }
extern "C" void cxx_throw() {
    if (mode == 1) throw 7;
    if (mode == 2) throw 2.5;
    if (mode == 3) throw 'c';
}
static int guarded(int (*cg)()) {
    try { return cg(); }
    catch (double) { return 200; }
    catch (char) { return 300; }
    catch (...) { return 400; }
}
int main() {
    // Columns: catch_int, catch_int_or_double, catch_int_then_all,
    // catch_int_or_cleanup, catch_char_or_int, catch_int_then_all_pruned.
    static const int expected[4][6] = {
        {0, 0, 0, 0, 0, 0},              // no throw: the normal edge
        {42, 42, 42, 42, 42, 42},        // int: every pad catches it (no cleanup runs)
        {200, 43, 44, 200, 200, 44},     // double: falls through / typed / catch-all / cleanup + falls through / falls through / catch-all
        {300, 300, 44, 300, 45, 44},     // char: falls through / falls through / catch-all / cleanup + falls through / identity slot 3 / catch-all
    };
    int failures = 0;
    for (mode = 0; mode <= 3; ++mode) {
        int got[6] = {guarded(catch_int), guarded(catch_int_or_double), guarded(catch_int_then_all),
                      guarded(catch_int_or_cleanup), guarded(catch_char_or_int),
                      guarded(catch_int_then_all_pruned)};
        printf("mode=%d got=%d,%d,%d,%d,%d,%d expected=%d,%d,%d,%d,%d,%d\n", mode, got[0], got[1],
               got[2], got[3], got[4], got[5], expected[mode][0], expected[mode][1],
               expected[mode][2], expected[mode][3], expected[mode][4], expected[mode][5]);
        for (int i = 0; i < 6; ++i) failures += got[i] != expected[mode][i];
    }
    // The cleanup pad ran exactly once per non-matching throw (double, char)
    // and never for the matching int or the normal edge.
    printf("cleanups=%d expected=2\n", cleanups);
    failures += cleanups != 2;
    printf("typed_catch failures=%d\n", failures);
    return failures == 0 ? 0 : 1;
}
"#;

/// Typed catch, selector dispatch (including the non-contiguous identity
/// slots of `[char, int]`), catch-all-after-typed (including the twin whose
/// unreachable `char` pad is pruned at O1+ only) and a typed catch with a
/// cleanup (non-matching types run the cleanup and resume to the enclosing
/// handler), natively at O0-O3 through the host `c++` driver.
#[cfg(all(target_arch = "aarch64", target_os = "macos"))]
#[test]
fn typed_catch_link_and_run_matching_and_fallthrough() {
    let module = typed_module();
    let dir = fresh_dir("trust_cg_eh_typed_e2e");
    let driver_path = dir.join("driver.cpp");
    fs::write(&driver_path, TYPED_DRIVER).expect("write driver");
    for opt_level in OPT_LEVELS {
        let obj = compile_for(&module, opt_level, native_host::TRIPLE);
        native_host::assert_native_object(&obj);
        let obj_path = dir.join(format!("typed_{opt_level:?}.o"));
        fs::write(&obj_path, &obj).expect("write .o");
        let bin_path = dir.join(format!("typed_{opt_level:?}"));
        run_checked(
            Command::new("c++")
                .arg(&driver_path)
                .arg(&obj_path)
                .arg("-o")
                .arg(&bin_path),
            &format!("{opt_level:?}: link typed-catch driver with c++"),
        );
        let (exit_code, stdout, stderr, timed_out) = run_with_timeout(
            &bin_path,
            common::rosetta::exec_timeout(Duration::from_secs(10)),
        );
        assert!(
            !timed_out,
            "{opt_level:?}: typed-catch binary exceeded its polling deadline. \
             stdout: {stdout}\nstderr: {stderr}"
        );
        assert_eq!(
            exit_code,
            Some(0),
            "{opt_level:?}: expected every (thrown type, pad) pair to dispatch as modelled \
             (134 = libc++abi terminate). exit={exit_code:?}\nstdout: {stdout}\nstderr: {stderr}"
        );
        assert!(
            stdout.contains("typed_catch failures=0") && stdout.contains("cleanups=2 expected=2"),
            "{opt_level:?}: stdout: {stdout}\nstderr: {stderr}"
        );
        eprintln!(
            "typed-catch e2e {opt_level:?} PASSED on {}",
            native_host::HOST
        );
    }
    let _ = fs::remove_dir_all(&dir);
}

/// Rust driver: a Rust panic raised below `cg_rust_cleanup` (Rust
/// personality) must run its cleanup pad and resume to `catch_unwind` with
/// the original payload, while `cg_cxx_catch_int` (C++ personality) catches
/// the C++ `throw 7` -- both from ONE CG object.
#[cfg(all(target_arch = "aarch64", target_os = "macos"))]
const TWO_PERSONALITY_DRIVER: &str = r#"
use std::panic::{catch_unwind, resume_unwind};
use std::sync::atomic::{AtomicUsize, Ordering};

static CLEANUPS: AtomicUsize = AtomicUsize::new(0);

#[derive(Debug, PartialEq)]
struct Marker(u32);

#[no_mangle]
pub extern "C-unwind" fn rust_thrower() {
    resume_unwind(Box::new(Marker(7)));
}

#[no_mangle]
pub extern "C" fn record_cleanup() {
    CLEANUPS.fetch_add(1, Ordering::SeqCst);
}

extern "C-unwind" {
    fn cg_rust_cleanup() -> i32;
    fn cg_cxx_catch_int() -> i32;
}

fn main() {
    let mut markers = 0usize;
    for _ in 0..16 {
        let payload = catch_unwind(|| unsafe { cg_rust_cleanup() })
            .expect_err("the panic must resume past the CG cleanup frame");
        if payload.downcast_ref::<Marker>() == Some(&Marker(7)) {
            markers += 1;
        }
    }
    let cleanups = CLEANUPS.load(Ordering::SeqCst);
    let cxx = unsafe { cg_cxx_catch_int() };
    println!("two_personality markers={markers} cleanups={cleanups} cxx={cxx}");
    std::process::exit(if markers == 16 && cleanups == 16 && cxx == 42 { 0 } else { 1 });
}
"#;

#[cfg(all(target_arch = "aarch64", target_os = "macos"))]
const TWO_PERSONALITY_CXX: &str = r#"
extern "C" void cxx_throw_int() { throw 7; }
"#;

/// The installed Trust package's `trustc` (or `$RUSTC`). Callers run it in the
/// explicit unverified lane through `trust_rustc`.
#[cfg(all(target_arch = "aarch64", target_os = "macos"))]
fn rustc_path() -> PathBuf {
    std::env::var_os("RUSTC")
        .map(PathBuf::from)
        .unwrap_or_else(|| PathBuf::from("trustc"))
}

/// `trustc -Ztrust-verify=off` without the TRUST_CG_*/TCG_* controls trustc
/// refuses to run under (a gate may export them to this test).
#[cfg(all(target_arch = "aarch64", target_os = "macos"))]
fn trust_rustc() -> Command {
    let mut command = Command::new(rustc_path());
    for (key, _) in std::env::vars_os() {
        let key_text = key.to_string_lossy();
        if key_text.starts_with("TRUST_CG_") || key_text.starts_with("TCG_") {
            command.env_remove(&key);
        }
    }
    command.arg("-Ztrust-verify=off");
    command
}

/// One module, two personalities, both crossed natively at O0-O3: a Rust
/// panic through the Rust-personality cleanup frame to `catch_unwind`, and a
/// C++ exception into the C++-personality typed catch.
#[cfg(all(target_arch = "aarch64", target_os = "macos"))]
#[test]
fn two_personality_module_rust_panic_and_cxx_exception_cross_their_own_frames() {
    let module = two_personality_module();
    let dir = fresh_dir("trust_cg_eh_two_personality_e2e");
    let driver_path = dir.join("driver.rs");
    fs::write(&driver_path, TWO_PERSONALITY_DRIVER).expect("write Rust driver");
    let cxx_path = dir.join("thrower.cpp");
    fs::write(&cxx_path, TWO_PERSONALITY_CXX).expect("write C++ thrower");
    let cxx_obj = dir.join("thrower.o");
    run_checked(
        Command::new("c++")
            .args(["-c", "-O1"])
            .arg(&cxx_path)
            .arg("-o")
            .arg(&cxx_obj),
        "compile the C++ thrower",
    );
    for opt_level in OPT_LEVELS {
        let obj = compile_for(&module, opt_level, native_host::TRIPLE);
        native_host::assert_native_object(&obj);
        let obj_path = dir.join(format!("two_{opt_level:?}.o"));
        fs::write(&obj_path, &obj).expect("write .o");
        let bin_path = dir.join(format!("two_{opt_level:?}"));
        run_checked(
            trust_rustc()
                .args(["--edition", "2021", "-C", "panic=unwind", "-O"])
                .arg(&driver_path)
                .arg("-o")
                .arg(&bin_path)
                .arg(format!("-Clink-arg={}", obj_path.display()))
                .arg(format!("-Clink-arg={}", cxx_obj.display()))
                .args(["-l", "c++"]),
            &format!("{opt_level:?}: link the two-personality driver with trustc"),
        );
        let (exit_code, stdout, stderr, timed_out) = run_with_timeout(
            &bin_path,
            common::rosetta::exec_timeout(Duration::from_secs(10)),
        );
        assert!(
            !timed_out,
            "{opt_level:?}: two-personality binary exceeded its polling deadline. \
             stdout: {stdout}\nstderr: {stderr}"
        );
        assert_eq!(
            exit_code,
            Some(0),
            "{opt_level:?}: expected the panic to resume through the Rust-personality \
             frame (cleanup counted) and the C++ throw to be caught by the C++-personality \
             frame. exit={exit_code:?}\nstdout: {stdout}\nstderr: {stderr}"
        );
        assert!(
            stdout.contains("two_personality markers=16 cleanups=16 cxx=42"),
            "{opt_level:?}: stdout: {stdout}\nstderr: {stderr}"
        );
        eprintln!(
            "two-personality e2e {opt_level:?} PASSED on {}",
            native_host::HOST
        );
    }
    let _ = fs::remove_dir_all(&dir);
}

/// Rust driver for the DWARF-fallback mixed module: the same two crossings
/// as `TWO_PERSONALITY_DRIVER`, through runtime-sized frames of several
/// sizes, so the unwinder reads each frame's CFA, personality and LSDA from
/// its `__eh_frame` FDE and CIE rather than from compact unwind.
#[cfg(all(target_arch = "aarch64", target_os = "macos"))]
const TWO_PERSONALITY_DWARF_DRIVER: &str = r#"
use std::panic::{catch_unwind, resume_unwind};
use std::sync::atomic::{AtomicUsize, Ordering};

static CLEANUPS: AtomicUsize = AtomicUsize::new(0);

#[derive(Debug, PartialEq)]
struct Marker(u32);

#[no_mangle]
pub extern "C-unwind" fn rust_thrower_into(buffer: *mut u8) {
    unsafe { buffer.write(7) };
    resume_unwind(Box::new(Marker(7)));
}

#[no_mangle]
pub extern "C" fn record_cleanup() {
    CLEANUPS.fetch_add(1, Ordering::SeqCst);
}

extern "C-unwind" {
    fn cg_rust_cleanup_dyn(n: i64) -> i32;
    fn cg_cxx_catch_int_dyn(n: i64) -> i32;
}

fn main() {
    let sizes = [1i64, 16, 100, 4000, 70000];
    let mut markers = 0usize;
    let mut caught = 0usize;
    for round in 0..4 {
        for &n in &sizes {
            let payload = catch_unwind(|| unsafe { cg_rust_cleanup_dyn(n + round) })
                .expect_err("the panic must resume past the CG cleanup frame");
            if payload.downcast_ref::<Marker>() == Some(&Marker(7)) {
                markers += 1;
            }
            if unsafe { cg_cxx_catch_int_dyn(n + round) } == 42 {
                caught += 1;
            }
        }
    }
    let cleanups = CLEANUPS.load(Ordering::SeqCst);
    println!("two_personality_dwarf markers={markers} cleanups={cleanups} caught={caught}");
    std::process::exit(if markers == 20 && cleanups == 20 && caught == 20 { 0 } else { 1 });
}
"#;

#[cfg(all(target_arch = "aarch64", target_os = "macos"))]
const TWO_PERSONALITY_DWARF_CXX: &str = r#"
extern "C" void cxx_throw_int_into(char *buffer) {
    buffer[0] = 7;
    throw 7;
}
"#;

/// One module, two personalities, both frames DWARF-fallback: a Rust panic
/// crosses the Rust-personality cleanup frame to `catch_unwind` and a C++
/// `int` is caught by the C++-personality typed catch, each located through
/// its own zPLR CIE in `__eh_frame`, natively at O0-O3.
#[cfg(all(target_arch = "aarch64", target_os = "macos"))]
#[test]
fn two_personality_dwarf_fallback_frames_unwind_natively() {
    let module = two_personality_dwarf_module();
    let dir = fresh_dir("trust_cg_eh_two_personality_dwarf_e2e");
    let driver_path = dir.join("driver.rs");
    fs::write(&driver_path, TWO_PERSONALITY_DWARF_DRIVER).expect("write Rust driver");
    let cxx_path = dir.join("thrower.cpp");
    fs::write(&cxx_path, TWO_PERSONALITY_DWARF_CXX).expect("write C++ thrower");
    let cxx_obj = dir.join("thrower.o");
    run_checked(
        Command::new("c++")
            .args(["-c", "-O1"])
            .arg(&cxx_path)
            .arg("-o")
            .arg(&cxx_obj),
        "compile the C++ thrower",
    );
    for opt_level in OPT_LEVELS {
        let obj = compile_for(&module, opt_level, native_host::TRIPLE);
        native_host::assert_native_object(&obj);
        let obj_path = dir.join(format!("two_dwarf_{opt_level:?}.o"));
        fs::write(&obj_path, &obj).expect("write .o");
        let bin_path = dir.join(format!("two_dwarf_{opt_level:?}"));
        run_checked(
            trust_rustc()
                .args(["--edition", "2021", "-C", "panic=unwind", "-O"])
                .arg(&driver_path)
                .arg("-o")
                .arg(&bin_path)
                .arg(format!("-Clink-arg={}", obj_path.display()))
                .arg(format!("-Clink-arg={}", cxx_obj.display()))
                .args(["-l", "c++"]),
            &format!("{opt_level:?}: link the DWARF-fallback two-personality driver with trustc"),
        );
        let (exit_code, stdout, stderr, timed_out) = run_with_timeout(
            &bin_path,
            common::rosetta::exec_timeout(Duration::from_secs(10)),
        );
        assert!(
            !timed_out,
            "{opt_level:?}: DWARF-fallback two-personality binary exceeded its polling deadline. \
             stdout: {stdout}\nstderr: {stderr}"
        );
        assert_eq!(
            exit_code,
            Some(0),
            "{opt_level:?}: expected both crossings through the DWARF-fallback frames. \
             exit={exit_code:?}\nstdout: {stdout}\nstderr: {stderr}"
        );
        assert!(
            stdout.contains("two_personality_dwarf markers=20 cleanups=20 caught=20"),
            "{opt_level:?}: stdout: {stdout}\nstderr: {stderr}"
        );
        eprintln!(
            "DWARF-fallback two-personality e2e {opt_level:?} PASSED on {}",
            native_host::HOST
        );
    }
    let _ = fs::remove_dir_all(&dir);
}

/// The in-repo standalone linker binds the typed-catch TType relocations the
/// same way ld64 does: it links the typed object into a dylib whose GOT
/// carries a bind for each typeinfo symbol (the LSDA slots are the object's
/// only references to `__ZTIi` / `__ZTId`), and `dyld_info` validates the
/// image. This is an image-level control: the standalone linker loads no
/// `__LD,__compact_unwind` and synthesizes no `__unwind_info`, so no CG
/// landing pad (typed or not) is reachable at run time through a
/// standalone-linked image yet.
#[cfg(all(target_arch = "aarch64", target_os = "macos"))]
#[test]
fn standalone_linker_binds_typed_catch_typeinfo_through_the_got() {
    use std::collections::HashSet;
    use trust_cg_codegen::macho::linker::{DylibConfig, link_dylib};

    const PROVIDER_INSTALL_NAME: &str = "@loader_path/libprov.dylib";
    const CXX_ABI_INSTALL_NAME: &str = "/usr/lib/libc++abi.dylib";
    const LIBSYSTEM_INSTALL_NAME: &str = "/usr/lib/libSystem.B.dylib";
    let cxx_abi: HashSet<String> = [
        "___gxx_personality_v0",
        "___cxa_begin_catch",
        "___cxa_end_catch",
        "__ZTIi",
        "__ZTId",
    ]
    .into_iter()
    .map(String::from)
    .collect();
    let provider: HashSet<String> = ["_cxx_throw", "_record_cleanup"]
        .into_iter()
        .map(String::from)
        .collect();

    let module = typed_module();
    let dir = fresh_dir("trust_cg_eh_typed_standalone");
    for opt_level in OPT_LEVELS {
        let obj = compile_for(&module, opt_level, "aarch64-apple-darwin");
        let parsed = MachOParser::parse(&obj).expect("parse Mach-O object");
        // Every other import (`__Unwind_Resume`, stack-protector hooks) is
        // libSystem's; derive the set from the object so nothing is guessed.
        let libsystem: HashSet<String> = parsed
            .symbols
            .iter()
            .filter(|symbol| symbol.is_undefined())
            .map(|symbol| symbol.name.as_str().to_owned())
            .filter(|name| !cxx_abi.contains(name) && !provider.contains(name))
            .collect();
        let mut config = DylibConfig::new();
        config.add_dylib(LIBSYSTEM_INSTALL_NAME, libsystem);
        config.add_dylib(PROVIDER_INSTALL_NAME, provider.clone());
        config.add_dylib(CXX_ABI_INSTALL_NAME, cxx_abi.clone());
        let image = link_dylib(&[parsed], &config, "@loader_path/libcg.dylib")
            .unwrap_or_else(|error| panic!("{opt_level:?}: standalone typed-catch dylib: {error}"));
        let path = dir.join(format!("libcg_{opt_level:?}.dylib"));
        fs::write(&path, &image).expect("write dylib");

        let validate = Command::new("/usr/bin/dyld_info")
            .arg("-validate_only")
            .arg(&path)
            .output()
            .expect("dyld_info is part of the macOS toolchain");
        let report = String::from_utf8_lossy(&validate.stdout).to_ascii_lowercase()
            + &String::from_utf8_lossy(&validate.stderr).to_ascii_lowercase();
        assert!(
            validate.status.success() && !report.contains("malformed") && !report.contains("error"),
            "{opt_level:?}: dyld_info rejected the standalone typed-catch dylib: {report}"
        );
        let fixups = Command::new("/usr/bin/dyld_info")
            .arg("-fixups")
            .arg(&path)
            .output()
            .expect("dyld_info -fixups");
        let fixups = String::from_utf8_lossy(&fixups.stdout).into_owned();
        for symbol in ["libc++abi/__ZTIi", "libc++abi/__ZTId"] {
            assert!(
                fixups.contains(symbol),
                "{opt_level:?}: the standalone image must bind `{symbol}` (the GOT slot the \
                 LSDA TType entries point at) -- fixups:\n{fixups}"
            );
        }
        // The personality is referenced only from `__LD,__compact_unwind`,
        // which the standalone linker does not load: no bind for it is the
        // pre-existing unwind-table gap, not a typeinfo binding defect.
        assert!(
            !fixups.contains("___gxx_personality_v0"),
            "{opt_level:?}: the standalone linker started loading compact-unwind personalities; \
             promote this control to a run-time typed catch -- fixups:\n{fixups}"
        );
        eprintln!(
            "standalone typed-catch dylib {opt_level:?} validated and bound on {}",
            native_host::HOST
        );
    }
    let _ = fs::remove_dir_all(&dir);
}

#[cfg(unix)]
#[path = "common/direct_timeout_contract.rs"]
mod direct_timeout_contract;

#[cfg(unix)]
#[test]
fn eh_supervisor_preserves_direct_status_and_timeout_observations() {
    direct_timeout_contract::check(run_with_timeout);
}

/// Preserve direct-child exit codes with the shared polling/termination boundary.
/// A timeout requests termination; it does not guarantee child/host cleanup.
fn run_with_timeout(bin: &Path, timeout: Duration) -> (Option<i32>, String, String, bool) {
    let result = common::rosetta::command_output_with_timeout(&mut Command::new(bin), timeout)
        .expect("run supervised EH binary");
    (
        if result.timed_out {
            None
        } else {
            result.output.status.code()
        },
        String::from_utf8_lossy(&result.output.stdout).into_owned(),
        String::from_utf8_lossy(&result.output.stderr).into_owned(),
        result.timed_out,
    )
}

/// This file's fixtures are hand-built and carry no codegen license
/// (`body_gate: None`), which trust-cg REFUSES by default (roadmap WS7.5,
/// decision gate DG-73). Its compiles state `Permit` explicitly, so no EH
/// refusal asserted here is the license's refusal in disguise.
fn permit_unlicensed() -> trust_cg_lower::CodegenLicensePolicy {
    trust_cg_lower::CodegenLicensePolicy::default()
        .with_unlicensed(trust_cg_lower::UnlicensedBodyPolicy::Permit)
}
