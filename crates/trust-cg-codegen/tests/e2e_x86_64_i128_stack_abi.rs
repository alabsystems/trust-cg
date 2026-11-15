// trust-cg-codegen/tests/e2e_x86_64_i128_stack_abi.rs
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! SysV AMD64 stack-passed `i128` ABI coverage.
//!
//! Two layouts matter:
//! * after five integer arguments, an `i128` cannot fit in the lone remaining
//!   GPR, so the whole pair rolls back to the stack and a following scalar must
//!   still use `R9`;
//! * after seven integer arguments, the first stack scalar occupies offset 0
//!   and the `i128` must skip offset 8 to start at a 16-byte boundary.
//!
//! The structural test pins both layouts after Trust IR adaptation. The
//! differential test crosses the real C ABI in both directions at every
//! register-exhaustion position (k = 0..=7 leading `u64`s, then the `i128` and
//! two trailing `u64`s): C calls trust-cg formals, and trust-cg callers invoke
//! C callees. Every host compiles the module and checks the emitted object
//! defines every trust-cg entry and imports every C callee; the link/run leg
//! runs wherever `common::rosetta::x86_64_link_run` proves an x86-64 driver
//! (natively on x86-64, under the repository's opt-in Rosetta harness on Apple
//! silicon, or with a cross driver plus binfmt_misc/qemu-user).
//!
//! # The oracle is the psABI, spelled in `u64`s
//!
//! The C side declares every stack-crossing signature as the list of `u64`
//! eightbytes the psABI places there (`psabi_u64_spelling`), not as `__int128`.
//! A host C compiler's own `__int128` lowering is not an oracle for this ABI:
//! Apple clang 14.0.3 (LLVM 15) passes a rolled-back `__int128`'s low half in
//! R9 and its high half on the stack, and aligns a stack `__int128` to 8, not
//! 16 (both measured 2026-10-02 on x86_64-apple-darwin22.6). With that compiler
//! as the oracle this test failed against a psABI-correct backend, and it
//! would have passed a backend that copied the split. GCC 16 and the LLVM 22
//! that `trustc` uses place the whole value on the stack at a 16-byte boundary,
//! as the spelling does; Rust code reaches that LLVM placement, which the rustc
//! bridge's `m149_x86_i128_stack_arg_xback` checks across the backend boundary
//! (reports/2026-10-02-x86-i128-stack-abi).

mod common;

#[path = "common/pinned_target.rs"]
mod pinned_target;

use common::rosetta::x86_64_link_run_or_skip;
use common::x86_64_corpus::{compile_trust_ir_module_x86_64, x86_64_differential_test};
use common::x86_64_object::assert_host_x86_64_object;
use trust_cg_ir::x86_64_ops::X86Opcode;
use trust_cg_ir::x86_64_regs::{R9, RBP, RSP, X86PReg};
use trust_cg_lower::instructions::Block;
use trust_cg_lower::x86_64_isel::{X86ISelFunction, X86ISelOperand, X86InstructionSelector};
use trust_ir::{
    BinOp, Block as TrustIrBlock, BlockId, CastOp, Constant, FuncId, FuncTy,
    Function as TrustIrFunction, Inst, InstrNode, Linkage, Module as TrustIrModule, Ty, ValueId,
};

fn v(id: u32) -> ValueId {
    ValueId::new(id)
}

/// The x86-64 triple this host's x86-64 objects are compiled for, the one
/// `compile_trust_ir_module_x86_64` resolves for `Target::X86_64` (Mach-O on
/// macOS, ELF elsewhere). A module with a bodyless `External` declaration
/// crosses an FFI boundary, so trust-ir refuses it without a pinned target
/// (`TargetInfoRequired`), and every trust-cg ingestion entry refuses what
/// trust-ir refuses (WS7.3): each module here pins this triple.
fn x86_64_object_triple() -> &'static str {
    if cfg!(target_os = "macos") {
        "x86_64-apple-darwin"
    } else {
        "x86_64-unknown-linux-gnu"
    }
}

fn add_external(module: &mut TrustIrModule, id: u32, name: &str, params: Vec<Ty>) -> FuncId {
    let ty = module
        .add_func_type(FuncTy {
            params,
            returns: vec![Ty::I128],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut function = TrustIrFunction::new(FuncId::new(id), name, ty, BlockId::new(0));
    function.blocks.clear();
    function.linkage = Linkage::External;
    let id = function.id;
    module
        .try_add_function(function)
        .expect("Module::try_add_function: test fixture");
    id
}

/// Add a function that returns `wide ^ zext(mix)`.
fn add_formal_probe(
    module: &mut TrustIrModule,
    id: u32,
    name: &str,
    params: Vec<Ty>,
    wide_index: u32,
    mix_index: u32,
) {
    let ty = module
        .add_func_type(FuncTy {
            params: params.clone(),
            returns: vec![Ty::I128],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut function = TrustIrFunction::new(FuncId::new(id), name, ty, BlockId::new(0));
    function.blocks = vec![TrustIrBlock {
        id: BlockId::new(0),
        params: params
            .into_iter()
            .enumerate()
            .map(|(index, ty)| (v(index as u32), ty))
            .collect(),
        body: vec![
            InstrNode::new(Inst::Cast {
                op: CastOp::ZExt,
                src_ty: Ty::I64,
                dst_ty: Ty::I128,
                operand: v(mix_index),
            })
            .with_result(v(100)),
            InstrNode::new(Inst::BinOp {
                op: BinOp::Xor,
                ty: Ty::I128,
                lhs: v(wide_index),
                rhs: v(100),
            })
            .with_result(v(101)),
            InstrNode::new(Inst::Return {
                values: vec![v(101)],
            }),
        ],
    }];
    module
        .try_add_function(function)
        .expect("Module::try_add_function: test fixture");
}

fn add_i64_const(body: &mut Vec<InstrNode>, id: u32, value: i128) -> ValueId {
    let result = v(id);
    body.push(
        InstrNode::new(Inst::Const {
            ty: Ty::I64,
            value: Constant::Int(value),
        })
        .with_result(result),
    );
    result
}

fn add_rollback_caller(module: &mut TrustIrModule, id: u32, callee: FuncId) {
    let ty = module
        .add_func_type(FuncTy {
            params: vec![Ty::I128, Ty::I64],
            returns: vec![Ty::I128],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut body = Vec::new();
    let mut args = Vec::new();
    for (index, value) in [11, 22, 33, 44, 55].into_iter().enumerate() {
        args.push(add_i64_const(&mut body, 10 + index as u32, value));
    }
    args.extend([v(0), v(1)]);
    body.push(InstrNode::new(Inst::Call { callee, args }).with_result(v(30)));
    body.push(InstrNode::new(Inst::Return {
        values: vec![v(30)],
    }));

    let mut function =
        TrustIrFunction::new(FuncId::new(id), "_call_i128_rollback", ty, BlockId::new(0));
    function.blocks = vec![TrustIrBlock {
        id: BlockId::new(0),
        params: vec![(v(0), Ty::I128), (v(1), Ty::I64)],
        body,
    }];
    module
        .try_add_function(function)
        .expect("Module::try_add_function: test fixture");
}

fn add_aligned_caller(module: &mut TrustIrModule, id: u32, callee: FuncId) {
    let ty = module
        .add_func_type(FuncTy {
            params: vec![Ty::I128],
            returns: vec![Ty::I128],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut body = Vec::new();
    let mut args = Vec::new();
    for (index, value) in [11, 22, 33, 44, 55, 66, 77].into_iter().enumerate() {
        args.push(add_i64_const(&mut body, 10 + index as u32, value));
    }
    args.push(v(0));
    body.push(InstrNode::new(Inst::Call { callee, args }).with_result(v(30)));
    body.push(InstrNode::new(Inst::Return {
        values: vec![v(30)],
    }));

    let mut function =
        TrustIrFunction::new(FuncId::new(id), "_call_i128_aligned", ty, BlockId::new(0));
    function.blocks = vec![TrustIrBlock {
        id: BlockId::new(0),
        params: vec![(v(0), Ty::I128)],
        body,
    }];
    module
        .try_add_function(function)
        .expect("Module::try_add_function: test fixture");
}

fn build_module() -> TrustIrModule {
    let rollback_params = {
        let mut params = vec![Ty::I64; 5];
        params.extend([Ty::I128, Ty::I64]);
        params
    };
    let aligned_params = {
        let mut params = vec![Ty::I64; 7];
        params.push(Ty::I128);
        params
    };

    let mut module = TrustIrModule::new("sysv_stack_i128_abi");
    pinned_target::pin(&mut module, x86_64_object_triple());
    let native_rollback = add_external(
        &mut module,
        0,
        "_native_i128_rollback",
        rollback_params.clone(),
    );
    let native_aligned = add_external(
        &mut module,
        1,
        "_native_i128_aligned",
        aligned_params.clone(),
    );
    add_formal_probe(
        &mut module,
        2,
        "_formal_i128_rollback",
        rollback_params,
        5,
        6,
    );
    add_formal_probe(&mut module, 3, "_formal_i128_aligned", aligned_params, 7, 6);
    add_rollback_caller(&mut module, 4, native_rollback);
    add_aligned_caller(&mut module, 5, native_aligned);
    module
}

fn select_function(module: &TrustIrModule, name: &str) -> X86ISelFunction {
    let function = module
        .functions
        .iter()
        .find(|function| function.name == name)
        .unwrap_or_else(|| panic!("missing function {name}"));
    let (lir, _) =
        trust_cg_lower::translate_function_with_license(function, module, &permit_unlicensed())
            .expect("adapter must lower ABI probe");
    let mut isel = X86InstructionSelector::new(lir.name.clone(), lir.signature.clone());
    isel.seed_value_types(&lir.value_types);
    isel.seed_function_value_use_counts(&lir);
    isel.lower_formal_arguments(&lir.signature, lir.entry_block)
        .expect("formal arguments must lower");

    let mut blocks: Vec<Block> = lir.blocks.keys().copied().collect();
    blocks.sort_by_key(|block| {
        if *block == lir.entry_block {
            0
        } else {
            block.0 + 1
        }
    });
    for block in blocks {
        let lir_block = &lir.blocks[&block];
        isel.select_block(block, &lir_block.instructions)
            .expect("ABI probe must select");
    }
    isel.finalize()
}

fn memory_displacements(function: &X86ISelFunction, opcode: X86Opcode, base: X86PReg) -> Vec<i32> {
    function
        .blocks
        .values()
        .flat_map(|block| &block.insts)
        .filter(|inst| inst.opcode == opcode)
        .flat_map(|inst| &inst.operands)
        .filter_map(|operand| match operand {
            X86ISelOperand::MemAddr {
                base: address_base,
                disp,
            } if **address_base == X86ISelOperand::PReg(base) => Some(*disp),
            _ => None,
        })
        .collect()
}

fn has_move_from(function: &X86ISelFunction, register: X86PReg) -> bool {
    function
        .blocks
        .values()
        .flat_map(|block| &block.insts)
        .any(|inst| {
            inst.opcode == X86Opcode::MovRR
                && matches!(
                    inst.operands.get(1),
                    Some(X86ISelOperand::PReg(source)) if *source == register
                )
        })
}

fn has_move_to(function: &X86ISelFunction, register: X86PReg) -> bool {
    function
        .blocks
        .values()
        .flat_map(|block| &block.insts)
        .any(|inst| {
            inst.opcode == X86Opcode::MovRR
                && matches!(
                    inst.operands.first(),
                    Some(X86ISelOperand::PReg(destination)) if *destination == register
                )
        })
}

#[test]
fn sysv_stack_i128_layout_survives_trust_ir_adaptation() {
    let module = build_module();

    let formal_rollback = select_function(&module, "_formal_i128_rollback");
    assert_eq!(
        memory_displacements(&formal_rollback, X86Opcode::MovRM, RBP),
        vec![16, 24]
    );
    assert!(
        has_move_from(&formal_rollback, R9),
        "tail scalar must retain the final argument GPR"
    );

    let formal_aligned = select_function(&module, "_formal_i128_aligned");
    assert_eq!(
        memory_displacements(&formal_aligned, X86Opcode::MovRM, RBP),
        vec![16, 32, 40],
        "stack scalar at +16 must be followed by padding and i128 at +32"
    );

    let call_rollback = select_function(&module, "_call_i128_rollback");
    assert_eq!(
        memory_displacements(&call_rollback, X86Opcode::MovMR, RSP),
        vec![0, 8]
    );
    assert!(
        has_move_to(&call_rollback, R9),
        "tail scalar must use R9 after the i128 rolls back"
    );

    let call_aligned = select_function(&module, "_call_i128_aligned");
    assert_eq!(
        memory_displacements(&call_aligned, X86Opcode::MovMR, RSP),
        vec![0, 16, 24],
        "outgoing scalar at +0 must be followed by padding and i128 at +16"
    );
}

// ---------------------------------------------------------------------------
// C differential at every register-exhaustion position
// ---------------------------------------------------------------------------

/// Leading `u64` counts the differential sweeps: k = 0..=7 puts the `i128` in
/// every register state, from RDI:RSI (k = 0) through the R8:R9 pair (k = 4),
/// the rollback past R9 (k = 5), a full register file (k = 6) and the padded
/// 16-byte stack boundary (k = 7).
const SWEEP_KS: std::ops::RangeInclusive<usize> = 0..=7;

/// The leading `u64` values the callers pass, `0x1111_1111_1111_1111 * (i + 1)`.
const SWEEP_A: [i128; 7] = [
    0x1111_1111_1111_1111,
    0x2222_2222_2222_2222,
    0x3333_3333_3333_3333,
    0x4444_4444_4444_4444,
    0x5555_5555_5555_5555,
    0x6666_6666_6666_6666,
    0x7777_7777_7777_7777,
];

/// FNV-1a's 64-bit prime: `mix` is `h = h * P ^ v` over the scalars in order, so
/// a scalar read from the wrong eightbyte changes the result.
const MIX_PRIME: i128 = 0x0000_0100_0000_01b3;

fn sweep_params(k: usize) -> Vec<Ty> {
    let mut params = vec![Ty::I64; k];
    params.extend([Ty::I128, Ty::I64, Ty::I64]);
    params
}

fn add_function(
    module: &mut TrustIrModule,
    id: u32,
    name: &str,
    params: Vec<Ty>,
    body: Option<Vec<InstrNode>>,
) -> FuncId {
    let ty = module
        .add_func_type(FuncTy {
            params: params.clone(),
            returns: vec![Ty::I128],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut function = TrustIrFunction::new(FuncId::new(id), name, ty, BlockId::new(0));
    match body {
        Some(body) => {
            function.blocks = vec![TrustIrBlock {
                id: BlockId::new(0),
                params: params
                    .into_iter()
                    .enumerate()
                    .map(|(index, ty)| (v(index as u32), ty))
                    .collect(),
                body,
            }];
        }
        None => {
            function.blocks.clear();
            function.linkage = Linkage::External;
        }
    }
    let id = function.id;
    module
        .try_add_function(function)
        .expect("Module::try_add_function: test fixture");
    id
}

/// `_formal_k<k>(a_0..a_{k-1}: i64, wide: i128, y: i64, z: i64) -> i128`
/// returns `wide ^ zext(mix(a_0, .., a_{k-1}, y, z))`.
fn formal_body(k: usize) -> Vec<InstrNode> {
    let k = k as u32;
    let wide = v(k);
    let scalars: Vec<ValueId> = (0..k).map(v).chain([v(k + 1), v(k + 2)]).collect();
    let mut body = Vec::new();
    let prime = add_i64_const(&mut body, 100, MIX_PRIME);
    let mut hash = add_i64_const(&mut body, 101, 0);
    let mut next = 102;
    for scalar in scalars {
        body.push(
            InstrNode::new(Inst::BinOp {
                op: BinOp::Mul,
                ty: Ty::I64,
                lhs: hash,
                rhs: prime,
            })
            .with_result(v(next)),
        );
        body.push(
            InstrNode::new(Inst::BinOp {
                op: BinOp::Xor,
                ty: Ty::I64,
                lhs: v(next),
                rhs: scalar,
            })
            .with_result(v(next + 1)),
        );
        hash = v(next + 1);
        next += 2;
    }
    body.push(
        InstrNode::new(Inst::Cast {
            op: CastOp::ZExt,
            src_ty: Ty::I64,
            dst_ty: Ty::I128,
            operand: hash,
        })
        .with_result(v(next)),
    );
    body.push(
        InstrNode::new(Inst::BinOp {
            op: BinOp::Xor,
            ty: Ty::I128,
            lhs: wide,
            rhs: v(next),
        })
        .with_result(v(next + 1)),
    );
    body.push(InstrNode::new(Inst::Return {
        values: vec![v(next + 1)],
    }));
    body
}

/// `_call_k<k>(wide: i128, y: i64, z: i64) -> i128` returns
/// `_native_k<k>(A_0, .., A_{k-1}, wide, y, z)`.
fn caller_body(k: usize, callee: FuncId) -> Vec<InstrNode> {
    let mut body = Vec::new();
    let mut args: Vec<ValueId> = SWEEP_A[..k]
        .iter()
        .enumerate()
        .map(|(index, &value)| add_i64_const(&mut body, 10 + index as u32, value))
        .collect();
    args.extend([v(0), v(1), v(2)]);
    body.push(InstrNode::new(Inst::Call { callee, args }).with_result(v(30)));
    body.push(InstrNode::new(Inst::Return {
        values: vec![v(30)],
    }));
    body
}

fn build_sweep_module() -> TrustIrModule {
    let mut module = TrustIrModule::new("sysv_stack_i128_sweep");
    // Every `_native_k<k>` is a bodyless external declaration.
    pinned_target::pin(&mut module, x86_64_object_triple());
    for k in SWEEP_KS {
        let id = 3 * k as u32;
        let native = add_function(
            &mut module,
            id,
            &format!("_native_k{k}"),
            sweep_params(k),
            None,
        );
        add_function(
            &mut module,
            id + 1,
            &format!("_formal_k{k}"),
            sweep_params(k),
            Some(formal_body(k)),
        );
        add_function(
            &mut module,
            id + 2,
            &format!("_call_k{k}"),
            vec![Ty::I128, Ty::I64, Ty::I64],
            Some(caller_body(k, native)),
        );
    }
    module
}

/// The C spelling of `(a_0..a_{k-1}: u64, wide: u128, y: u64, z: u64)` under
/// the AMD64 psABI, as `u64` parameter names: the six INTEGER argument
/// registers in order, then the stack eightbytes in order.
///
/// This restates psABI 3.2.3 for INTEGER-class arguments, independently of
/// the backend's classifier: each `u64` takes the next free register, else the
/// next stack eightbyte; the `u128`'s two eightbytes take two consecutive
/// registers only when two remain, and otherwise go WHOLLY to the stack at a
/// 16-byte boundary (`pad` fills a skipped eightbyte), leaving any remaining
/// register to the arguments after it. Every C compiler places a list of
/// `u64`s the same way, so the C side of the differential does not depend on
/// how its compiler lowers `__int128`.
fn psabi_u64_spelling(k: usize) -> Vec<String> {
    const INTEGER_ARGUMENT_REGISTERS: usize = 6;
    let mut registers: Vec<String> = Vec::new();
    let mut stack: Vec<String> = Vec::new();
    let scalar = |name: String, registers: &mut Vec<String>, stack: &mut Vec<String>| {
        if registers.len() < INTEGER_ARGUMENT_REGISTERS {
            registers.push(name);
        } else {
            stack.push(name);
        }
    };
    for index in 0..k {
        scalar(format!("a{index}"), &mut registers, &mut stack);
    }
    if registers.len() + 2 <= INTEGER_ARGUMENT_REGISTERS {
        registers.extend(["lo".to_owned(), "hi".to_owned()]);
    } else {
        if stack.len() % 2 == 1 {
            stack.push("pad".to_owned());
        }
        stack.extend(["lo".to_owned(), "hi".to_owned()]);
    }
    scalar("y".to_owned(), &mut registers, &mut stack);
    scalar("z".to_owned(), &mut registers, &mut stack);
    registers.extend(stack);
    registers
}

fn c_params(k: usize) -> String {
    psabi_u64_spelling(k)
        .iter()
        .map(|name| format!("uint64_t {name}"))
        .collect::<Vec<_>>()
        .join(", ")
}

/// The arguments for [`c_params`]: the leading scalars from the array `a`, the
/// 128-bit value from `wide`, `y` and `z` by name, and a zero padding
/// eightbyte.
fn c_args(k: usize, a: &str, wide: &str) -> String {
    psabi_u64_spelling(k)
        .iter()
        .map(|name| match name.as_str() {
            "lo" => format!("(uint64_t){wide}"),
            "hi" => format!("(uint64_t)({wide} >> 64)"),
            "pad" => "0".to_owned(),
            "y" | "z" => name.clone(),
            leading => format!("{a}[{}]", &leading[1..]),
        })
        .collect::<Vec<_>>()
        .join(", ")
}

fn c_leading_array(k: usize) -> String {
    if k == 0 {
        "const uint64_t *a = 0;".to_owned()
    } else {
        let names: Vec<String> = (0..k).map(|index| format!("a{index}")).collect();
        format!("const uint64_t a[] = {{{}}};", names.join(", "))
    }
}

const C_PRELUDE: &str = r#"
#include <stdint.h>
#include <stdio.h>
typedef unsigned __int128 u128;
#define WIDE(lo, hi) ((((u128)(hi)) << 64) | (u128)(lo))
static const uint64_t A[7] = {
    UINT64_C(0x1111111111111111), UINT64_C(0x2222222222222222), UINT64_C(0x3333333333333333),
    UINT64_C(0x4444444444444444), UINT64_C(0x5555555555555555), UINT64_C(0x6666666666666666),
    UINT64_C(0x7777777777777777)};
static uint64_t mix(const uint64_t *a, int k, uint64_t y, uint64_t z) {
    uint64_t h = 0;
    for (int i = 0; i < k; i++) h = h * UINT64_C(0x100000001b3) ^ a[i];
    h = h * UINT64_C(0x100000001b3) ^ y;
    return h * UINT64_C(0x100000001b3) ^ z;
}
"#;

/// The C model of the trust-cg module: every `_formal_k<k>` with its psABI
/// spelling, and every `_call_k<k>` calling the driver's `_native_k<k>`
/// through it.
fn c_reference() -> String {
    let mut src = String::from(C_PRELUDE);
    for k in SWEEP_KS {
        let params = c_params(k);
        let leading = c_leading_array(k);
        let call_args = c_args(k, "A", "wide");
        src.push_str(&format!(
            "extern u128 _native_k{k}({params});\n\
             u128 _formal_k{k}({params}) {{\n    {leading}\n    (void)a;\n    \
             return WIDE(lo, hi) ^ (u128)mix(a, {k}, y, z);\n}}\n\
             u128 _call_k{k}(u128 wide, uint64_t y, uint64_t z) {{\n    \
             return _native_k{k}({call_args});\n}}\n"
        ));
    }
    src
}

/// The driver: calls every `_formal_k<k>` through its psABI spelling, defines
/// every `_native_k<k>` (which checks its leading scalars) and calls every
/// `_call_k<k>`. It prints every result before exiting, so a failing run shows
/// every misplaced position, not only the first.
fn c_driver() -> String {
    let mut src = String::from(C_PRELUDE);
    src.push_str(
        "static u128 bad(void) {\n    \
         return ((u128)UINT64_MAX << 64) | UINT64_C(0xbad0bad0bad0bad0);\n}\n\
         static int check(const char *name, u128 got, u128 expected) {\n    \
         printf(\"%s=%016llx:%016llx\\n\", name, (unsigned long long)(got >> 64), \
         (unsigned long long)got);\n    \
         if (got == expected) return 0;\n    \
         fprintf(stderr, \"%s mismatch: expected %016llx:%016llx\\n\", name, \
         (unsigned long long)(expected >> 64), (unsigned long long)expected);\n    \
         return 1;\n}\n",
    );
    for k in SWEEP_KS {
        let params = c_params(k);
        let leading = c_leading_array(k);
        src.push_str(&format!(
            "extern u128 _formal_k{k}({params});\n\
             extern u128 _call_k{k}(u128, uint64_t, uint64_t);\n\
             u128 _native_k{k}({params}) {{\n    {leading}\n    \
             for (int i = 0; i < {k}; i++) if (a[i] != A[i]) return bad();\n    \
             return WIDE(lo, hi) ^ (u128)mix(a, {k}, y, z);\n}}\n"
        ));
    }
    src.push_str(
        "int main(void) {\n    \
         const u128 x0 = WIDE(UINT64_C(0x99aabbccddeeff00), UINT64_C(0x1122334455667788));\n    \
         const u128 x1 = WIDE(UINT64_C(0x0123456789abcdef), UINT64_C(0xfedcba9876543210));\n    \
         const uint64_t y = UINT64_C(0x8877665544332211);\n    \
         const uint64_t z = UINT64_C(0x0f0e0d0c0b0a0908);\n    \
         int failures = 0;\n",
    );
    for k in SWEEP_KS {
        let formal_args = c_args(k, "A", "x0");
        src.push_str(&format!(
            "    failures += check(\"formal_k{k}\", _formal_k{k}({formal_args}), \
             x0 ^ (u128)mix(A, {k}, y, z));\n    \
             failures += check(\"call_k{k}\", _call_k{k}(x1, y, z), \
             x1 ^ (u128)mix(A, {k}, y, z));\n"
        ));
    }
    src.push_str("    return failures != 0;\n}\n");
    src
}

/// The psABI spelling at the two layouts the structural test pins, the
/// rollback (k = 5: `y` back-fills R9, the `u128` at stack +0/+8, `z` at +16)
/// and the padded boundary (k = 7: `a6` at +0, padding at +8, the `u128` at
/// +16/+24), and where the `u128` still fits in registers.
#[test]
fn psabi_u64_spelling_states_the_sysv_layouts() {
    let spelled = |k| psabi_u64_spelling(k).join(",");
    assert_eq!(spelled(0), "lo,hi,y,z");
    assert_eq!(spelled(3), "a0,a1,a2,lo,hi,y,z");
    assert_eq!(spelled(4), "a0,a1,a2,a3,lo,hi,y,z");
    assert_eq!(spelled(5), "a0,a1,a2,a3,a4,y,lo,hi,z");
    assert_eq!(spelled(6), "a0,a1,a2,a3,a4,a5,lo,hi,y,z");
    assert_eq!(spelled(7), "a0,a1,a2,a3,a4,a5,a6,pad,lo,hi,y,z");
}

#[test]
fn sysv_stack_i128_crosses_c_abi_in_both_directions() {
    let module = build_sweep_module();
    // Link-facing contract of the object the differential links: the C driver
    // calls every trust-cg formal and caller, and every caller calls out to the
    // C callee the driver defines.
    let object = compile_trust_ir_module_x86_64(&module);
    let defines: Vec<String> = SWEEP_KS
        .flat_map(|k| [format!("_formal_k{k}"), format!("_call_k{k}")])
        .collect();
    let imports: Vec<String> = SWEEP_KS.map(|k| format!("_native_k{k}")).collect();
    assert_host_x86_64_object(
        "sysv_stack_i128_sweep",
        &object,
        &defines.iter().map(String::as_str).collect::<Vec<_>>(),
        &imports.iter().map(String::as_str).collect::<Vec<_>>(),
    );
    if !x86_64_link_run_or_skip(
        "sysv_stack_i128_crosses_c_abi_in_both_directions",
        "x86-64 C ABI differential link/run leg",
    ) {
        return;
    }
    x86_64_differential_test(
        "sysv_stack_i128_sweep",
        &module,
        &c_reference(),
        &c_driver(),
    )
    .unwrap_or_else(|error| panic!("SysV stack i128 differential failed: {error}"));
}

/// This file's fixtures are hand-built and carry no codegen license
/// (`body_gate: None`), which trust-cg REFUSES by default (roadmap WS7.5,
/// decision gate DG-73). Its compiles state `Permit` explicitly, so none of
/// them passes because it was silently refused.
fn permit_unlicensed() -> trust_cg_lower::CodegenLicensePolicy {
    trust_cg_lower::CodegenLicensePolicy::default()
        .with_unlicensed(trust_cg_lower::UnlicensedBodyPolicy::Permit)
}
