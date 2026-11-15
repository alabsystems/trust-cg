// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0
//! End-to-end x86-64 source-bound body lane: the proof-required AOT compile of
//! slice-1 bodies (`add`, `ident`, a constant return and the `black_box` copy
//! chain), slice-2 bodies (pointer casts, narrow carriers, arithmetic beyond
//! congruence) and slice-3 bodies (direct calls: wrappers of a module function
//! and of an external one, a value live across a call, a void call and a
//! diverging call), slice-4 bodies (loads and stores through pointer
//! parameters, a field, a private stack slot, memory threaded through a call)
//! and slice-5 bodies (a RAX:RDX pair return, a call returning a pair, the
//! masked `bool` lane of a pair call, a global's address and a load through
//! it, branch-free compares) and slice-6 bodies (acyclic control flow: a
//! diamond with a join, an early return, a panic arm that calls and traps, a
//! switch compare chain, a `cmov` select, and a slot written on one path
//! only) and slice-7 bodies (calls through memory: a return buffer, a `&mut`
//! out-parameter, a `&` argument the callee reads, an `Option<u64>`
//! out-parameter) and slice-8 bodies (aggregates in general-purpose
//! registers: a four-byte parameter's field, a `[u64; 2]` parameter passed on
//! by value to an external callee, an external callee's two-`u32` result read
//! back), slice-9 bodies (acyclic control flow past the slice-6 bounds, stated
//! over the DAG: five conditional calls, five conditional `xor`s joined, five
//! conditional stores), slice-10 bodies
//! (instruction coverage: checked addition, `not`, `popcnt`, a shift by CL
//! and a call through a register) and slice-11 bodies (`u128` register pairs
//! and float bit patterns: a `u128` add and compare, a `u128` passed to and
//! returned by an external callee, `f64::to_bits`, `f32::from_bits` and an
//! `f64` passed through an external callee), slice-12 bodies (loops cut at
//! their headers: a counting loop, a loop calling an external function each
//! iteration, and a counter kept in a private slot), slice-13 bodies (memory
//! and values: a local's address stored through an out-pointer, a seventh
//! parameter read from the incoming stack area, a seventh argument stored to
//! the outgoing one, a `Memcpy` called as `memcpy`, and an `Acquire` atomic
//! load) and slice-15 bodies (the value, call and observable residue: an `f64`
//! constant, `-x` and `x.abs()`, a `bool` parameter forwarded to an external
//! callee, a load through the pointer a callee returned after a local
//! escaped to it, and a `u128` parameter in the incoming stack area), and
//! `bool as u8` (of a parameter, of a compare's result, and in `core`'s
//! `u8::carrying_add`), and the sign extension of a `bool` (LLVM's `sext i1`,
//! `-zext(b)`: of a parameter into every width, of a compare's result, and
//! pr68376-2's `x ^ sext(x < 0)`), and slice-21 bodies (floating-point
//! operations as paired rounding events: an `f64` product, an `f32`
//! quotient, an unordered not-equal compare, the saturating `f64 as i64`,
//! `i64 as f64` and `pow2_to_pow10`; and the atomic exchange and the `u128`
//! atomic load), and slice-22 bodies (an `i128` division as the call of its
//! runtime routine behind rustc's zero check, an `i128` remainder, the `I128`
//! divide-by-zero guard, the 128-bit multiply-overflow check of two widened
//! `u64`s), 128-bit shifts by a constant amount, folded into immediate
//! shifts of the halves (OD-215), and the division-free 128-bit checked
//! multiply of two full operands (OD-224), on `x86_64-apple-darwin` and
//! `x86_64-unknown-linux-gnu`.
//!
//! With the identity-admitted AY and a capable Clean/Carcara checker (explicit
//! or found by the default discovery) the compile must promote, and every covered row must carry the replayed
//! whole-body theorem as its export payload. Without an independently checked
//! proof the same compile must be refused by name, and a body outside the
//! lane keeps today's refusal. The tool-gated test SKIPS, printing why, when
//! either tool is absent.
#![cfg(feature = "verify")]

#[path = "common/pinned_target.rs"]
mod pinned_target;

use trust_cg_codegen::compiler::{CompilationResult, CompileError, Compiler, CompilerConfig};
use trust_cg_codegen::pipeline::OptLevel;
use trust_cg_codegen::target::{Target, TargetSpec};
use trust_cg_verify::x86_source_bound_body::{X86_BODY_NEEDS_REPLAY, X86_BODY_OBLIGATION_NAME};
use trust_ir::{BinOp, CastOp, FieldDef, StructDef, StructId, StructRepr, Ty, UnOp};
use trust_ir_build::ModuleBuilder;

const TRIPLES: [&str; 2] = ["x86_64-apple-darwin", "x86_64-unknown-linux-gnu"];
const SLICE_ONE: [&str; 4] = ["add", "ident", "const_four", "black_box"];
const SLICE_TWO: [&str; 13] = [
    "ptr_cast",
    "ptr_addr",
    "u8_ident",
    "bool_false",
    "bool_ident",
    "zext_u8",
    "sext_i32",
    "trunc_bool",
    "i8_as_u8",
    "add_u8",
    "add_imm",
    "xor",
    "shl_imm",
];
const SLICE_THREE: [&str; 6] = [
    "call_module",
    "call_extern",
    "call_swap",
    "call_after",
    "call_void",
    "call_diverge",
];
const SLICE_FOUR: [&str; 6] = [
    "mem_load",
    "mem_store",
    "mem_field",
    "mem_local",
    "mem_store_then_load",
    "mem_store_call",
];
const SLICE_FIVE: [&str; 7] = [
    "pair_swap",
    "pair_call_sum",
    "pair_call_bool",
    "global_addr",
    "global_load",
    "cmp_lt",
    "cmp_sge_i8",
];
const SLICE_SIX: [&str; 6] = [
    "branch_min",
    "branch_early_return",
    "branch_panic_arm",
    "branch_switch",
    "branch_select",
    "branch_partial_init",
];
const SLICE_SEVEN: [&str; 4] = [
    "through_sret_sum",
    "through_out_param",
    "through_read_ref",
    "through_option_out",
];
// No slice-8 aggregate result built in a slot (the former `agg_result_pair`):
// no valid trust-ir spelling of one is inside the body lane (decision record
// DR-X86-BODY-E2E-TYPED-FIXTURE-20261015).
const SLICE_EIGHT: [&str; 3] = ["agg_param_field", "agg_call_arg", "agg_call_result"];
const SLICE_NINE: [&str; 3] = ["dag_calls", "dag_xors", "dag_stores"];
const SLICE_TEN: [&str; 5] = [
    "insn_overflowing_add",
    "insn_not",
    "insn_count_ones",
    "insn_shr",
    "insn_indirect",
];
const SLICE_ELEVEN: [&str; 6] = [
    "wide_add",
    "wide_lt",
    "wide_call",
    "float_to_bits",
    "float_from_bits",
    "float_call",
];
const SLICE_TWELVE: [&str; 3] = ["loop_count", "loop_call_each", "loop_slot_counter"];

/// Loops cut at their headers: `while i < n { i += 1 } i`, a sum of an
/// external function's results over `0..n` (one call per iteration), and a
/// counter kept in a private slot, loaded and stored each iteration.
fn add_slice_twelve(builder: &mut ModuleBuilder) {
    use trust_ir::ICmpOp;
    let unary = builder.add_func_type(vec![Ty::U64], vec![Ty::U64]);
    let ext_step = builder.declare_function("ext_step", unary);
    for name in ["loop_count", "loop_call_each"] {
        let mut f = builder.function(name, unary);
        let entry = f.create_block();
        let n = f.add_block_param(entry, Ty::U64);
        let (header, body, exit) = (f.create_block(), f.create_block(), f.create_block());
        let i = f.add_block_param(header, Ty::U64);
        let s = f.add_block_param(header, Ty::U64);
        f.switch_to_block(entry);
        let zero = f.iconst(Ty::U64, 0);
        f.br(header, vec![zero, zero]);
        f.switch_to_block(header);
        let go = f.icmp(ICmpOp::Ult, Ty::U64, i, n);
        f.condbr(go, body, vec![], exit, vec![]);
        f.switch_to_block(body);
        let one = f.iconst(Ty::U64, 1);
        let next = f.add(Ty::U64, i, one);
        let sum = if name == "loop_call_each" {
            let y = f.call(ext_step, vec![i]);
            f.add(Ty::U64, s, y)
        } else {
            s
        };
        f.br(header, vec![next, sum]);
        f.switch_to_block(exit);
        f.ret(vec![if name == "loop_count" { i } else { s }]);
        f.build();
    }
    let mut f = builder.function("loop_slot_counter", unary);
    let entry = f.create_block();
    let n = f.add_block_param(entry, Ty::U64);
    let (header, body, exit) = (f.create_block(), f.create_block(), f.create_block());
    f.switch_to_block(entry);
    let counter = f.alloca(Ty::U64);
    let zero = f.iconst(Ty::U64, 0);
    f.store(Ty::U64, counter, zero);
    f.br(header, vec![]);
    f.switch_to_block(header);
    let value = f.load(Ty::U64, counter);
    let go = f.icmp(ICmpOp::Ult, Ty::U64, value, n);
    f.condbr(go, body, vec![], exit, vec![]);
    f.switch_to_block(body);
    let two = f.iconst(Ty::U64, 2);
    let next = f.add(Ty::U64, value, two);
    f.store(Ty::U64, counter, next);
    f.br(header, vec![]);
    f.switch_to_block(exit);
    f.ret(vec![value]);
    f.build();
}

const SLICE_THIRTEEN: [&str; 5] = [
    "addr_out",
    "stack_param",
    "stack_arg",
    "mem_copy",
    "atomic_acquire",
];
const SLICE_FOURTEEN: [&str; 5] = [
    "div_checked",
    "rem_guarded",
    "div_by_eight",
    "shared_sign",
    "table_holes",
];
const SLICE_FIFTEEN: [&str; 6] = [
    "float_const",
    "float_neg",
    "float_abs",
    "bool_forward",
    "derived_load",
    "wide_stack_param",
];
/// `bool as u8` (LIR `Uextend B1 -> I8`), which the selector once refused:
/// of a parameter, of a compare's result, and in `u8::carrying_add`.
const BOOL_TO_BYTE: [&str; 3] = ["bool_as_u8", "lt_as_u8", "carrying_add_u8"];

/// Floating-point operations as paired rounding events (rulings OD-198 to
/// OD-200) and the remaining atomics (OD-201).
const SLICE_TWENTY_ONE: [&str; 8] = [
    "float_mul",
    "float_div32",
    "float_une",
    "float_to_i64",
    "i64_to_float",
    "pow2_to_pow10",
    "xchg_u64",
    "atomic_load_u128",
];

/// The `i128` division class (ruling OD-202): an `I128` division as the call
/// of its runtime routine behind rustc's zero check, a remainder of `i128`
/// operands, the `I128` divide-by-zero guard and the adapter's 128-bit
/// multiply-overflow check of two widened `u64` operands (a division by an
/// operand when slice 22 landed; the division-free limb check since OD-224).
const SLICE_TWENTY_TWO: [&str; 4] = [
    "u128_div_checked",
    "i128_rem_checked",
    "u128_div_guarded",
    "u64_widening_mul_overflows",
];

/// 128-bit shifts by a constant amount (ruling OD-215), which the selector
/// folds into immediate shifts of the halves: `(x >> 64) as u64` (the
/// high-limb extraction of `u128::widening_mul` and Display), `x >> 1`,
/// `(x: i128) >> 65` (a sign fill) and `x << 127`.
const I128_CONST_SHIFT: [&str; 4] = [
    "u128_high_limb",
    "u128_shr_1",
    "i128_sar_65",
    "u128_shl_127",
];

fn add_i128_const_shift(builder: &mut ModuleBuilder) {
    function(
        builder,
        "u128_high_limb",
        vec![Ty::U128],
        Ty::U64,
        |f, a| {
            let sixty_four = f.iconst(Ty::U128, 64);
            let high = f.binop(BinOp::LShr, Ty::U128, a[0], sixty_four);
            f.trunc(Ty::U128, Ty::U64, high)
        },
    );
    for (name, ty, op, amount) in [
        ("u128_shr_1", Ty::U128, BinOp::LShr, 1),
        ("i128_sar_65", Ty::I128, BinOp::AShr, 65),
        ("u128_shl_127", Ty::U128, BinOp::Shl, 127),
    ] {
        function(builder, name, vec![ty.clone()], ty.clone(), |f, a| {
            let count = f.iconst(ty.clone(), amount);
            f.binop(op, ty, a[0], count)
        });
    }
}

/// The division-free 128-bit checked multiply (ruling OD-224): the flag of
/// `u128::checked_mul` and of `i128::overflowing_mul` of two full operands,
/// two flag-setting `mul` rows and a carry compare (on the magnitudes plus a
/// sign check for `i128`), no runtime routine.
const I128_MULO: [&str; 2] = ["u128_checked_mul_overflows", "i128_overflowing_mul_flag"];

fn add_i128_mulo(builder: &mut ModuleBuilder) {
    for (name, ty) in [
        ("u128_checked_mul_overflows", Ty::U128),
        ("i128_overflowing_mul_flag", Ty::I128),
    ] {
        function(
            builder,
            name,
            vec![ty.clone(), ty.clone()],
            Ty::Bool,
            |f, a| {
                f.overflow(trust_ir::OverflowOp::MulOverflow, ty, a[0], a[1])
                    .1
            },
        );
    }
}

/// The sign extension of a `bool` (LIR `Sextend` from `B1`, ruling
/// OD-BODY-SEXT-BOOL-20261016), which the selector computed as +1 for `true`
/// and the lane refused: of a parameter into every width, of a compare's
/// result, and `x ^ sext(x < 0)`.
const SEXT_BOOL: [&str; 7] = [
    "sext_bool_i8",
    "sext_bool_i16",
    "sext_bool_i32",
    "sext_bool_i64",
    "sext_bool_i128",
    "sext_lt_i64",
    "flip_if_negative_i32",
];

fn add_sext_bool(builder: &mut ModuleBuilder) {
    for (name, to) in [
        ("sext_bool_i8", Ty::I8),
        ("sext_bool_i16", Ty::I16),
        ("sext_bool_i32", Ty::I32),
        ("sext_bool_i64", Ty::I64),
        ("sext_bool_i128", Ty::I128),
    ] {
        function(builder, name, vec![Ty::Bool], to.clone(), |f, a| {
            f.sext(Ty::Bool, to, a[0])
        });
    }
    function(
        builder,
        "sext_lt_i64",
        vec![Ty::I64, Ty::I64],
        Ty::I64,
        |f, a| {
            let less = f.icmp(trust_ir::ICmpOp::Slt, Ty::I64, a[0], a[1]);
            f.sext(Ty::Bool, Ty::I64, less)
        },
    );
    function(
        builder,
        "flip_if_negative_i32",
        vec![Ty::I32],
        Ty::I32,
        |f, a| {
            let zero = f.iconst(Ty::I32, 0);
            let negative = f.icmp(trust_ir::ICmpOp::Slt, Ty::I32, a[0], zero);
            let mask = f.sext(Ty::Bool, Ty::I32, negative);
            f.binop(BinOp::Xor, Ty::I32, a[0], mask)
        },
    );
}

/// `bool as u8` of a parameter and of a compare's result, and `core`'s
/// `u8::carrying_add` (`(a + b + carry as u8, carry out)`).
fn add_bool_to_byte(builder: &mut ModuleBuilder) {
    function(builder, "bool_as_u8", vec![Ty::Bool], Ty::U8, |f, a| {
        f.zext(Ty::Bool, Ty::U8, a[0])
    });
    function(
        builder,
        "lt_as_u8",
        vec![Ty::U64, Ty::U64],
        Ty::U8,
        |f, a| {
            let less = f.icmp(trust_ir::ICmpOp::Ult, Ty::U64, a[0], a[1]);
            f.zext(Ty::Bool, Ty::U8, less)
        },
    );
    let carrying = builder.add_func_type(vec![Ty::U8, Ty::U8, Ty::Bool], vec![Ty::U8, Ty::Bool]);
    let mut f = builder.function("carrying_add_u8", carrying);
    let entry = f.create_block();
    let a = f.add_block_param(entry, Ty::U8);
    let b = f.add_block_param(entry, Ty::U8);
    let c = f.add_block_param(entry, Ty::Bool);
    f.switch_to_block(entry);
    let s = f.add(Ty::U8, a, b);
    let c1 = f.icmp(trust_ir::ICmpOp::Ult, Ty::U8, s, a);
    let carry_in = f.zext(Ty::Bool, Ty::U8, c);
    let t = f.add(Ty::U8, s, carry_in);
    let c2 = f.icmp(trust_ir::ICmpOp::Ult, Ty::U8, t, s);
    let carry_out = f.binop(BinOp::Or, Ty::Bool, c1, c2);
    f.ret(vec![t, carry_out]);
    f.build();
}

/// The fixture, bound to the `triple` it is compiled for: it declares
/// bodyless external functions (an FFI boundary, `TargetInfoRequired`), and
/// its `memcpy` length is the pinned target's `usize`.
fn module(triple: &str) -> trust_ir::Module {
    let mut builder = ModuleBuilder::new_with_target_info(
        "x86_source_bound_body_e2e",
        pinned_target::target_info(triple),
    );
    let binary = builder.add_func_type(vec![Ty::U64, Ty::U64], vec![Ty::U64]);
    let unary = builder.add_func_type(vec![Ty::U64], vec![Ty::U64]);
    let nullary = builder.add_func_type(vec![], vec![Ty::U64]);

    let mut f = builder.function("add", binary);
    let entry = f.create_block();
    let a = f.add_block_param(entry, Ty::U64);
    let b = f.add_block_param(entry, Ty::U64);
    f.switch_to_block(entry);
    let sum = f.add(Ty::U64, a, b);
    f.ret(vec![sum]);
    f.build();

    let mut f = builder.function("ident", unary);
    let entry = f.create_block();
    let x = f.add_block_param(entry, Ty::U64);
    f.switch_to_block(entry);
    f.ret(vec![x]);
    let ident = f.build();

    let mut f = builder.function("const_four", nullary);
    let entry = f.create_block();
    f.switch_to_block(entry);
    let four = f.iconst(Ty::U64, 4);
    f.ret(vec![four]);
    f.build();

    let mut f = builder.function("black_box", unary);
    let entry = f.create_block();
    let tail = f.create_block();
    let x = f.add_block_param(entry, Ty::U64);
    f.switch_to_block(entry);
    let copied = f.copy(Ty::U64, x);
    f.br(tail, vec![]);
    f.switch_to_block(tail);
    f.ret(vec![copied]);
    f.build();

    add_slice_two(&mut builder);
    add_slice_three(&mut builder, ident);
    add_slice_four(&mut builder);
    add_slice_five(&mut builder);
    add_slice_six(&mut builder);
    add_slice_seven(&mut builder);
    add_slice_eight(&mut builder);
    add_slice_nine(&mut builder);
    add_slice_ten(&mut builder);
    add_slice_eleven(&mut builder);
    add_slice_twelve(&mut builder);
    add_slice_thirteen(&mut builder);
    add_slice_fourteen(&mut builder);
    add_slice_fifteen(&mut builder);
    add_bool_to_byte(&mut builder);
    add_sext_bool(&mut builder);
    add_slice_twenty_one(&mut builder);
    add_slice_twenty_two(&mut builder);
    add_i128_const_shift(&mut builder);
    add_i128_mulo(&mut builder);
    let mut module = builder.build().expect("ModuleBuilder::build: test fixture");
    // The `u128` atomic load needs its function's `cmpxchg16b` claim (the
    // adapter refuses a 128-bit atomic without it, `[TCG-ATOMIC128-CX16]`).
    module
        .functions
        .iter_mut()
        .find(|function| function.name == "atomic_load_u128")
        .expect("the u128 atomic load")
        .attrs
        .target_features = vec!["cmpxchg16b".to_owned()];
    // The return-buffer callee carries the `sret` attribute on its leading
    // pointer parameter, as the bridge declares a `PassMode::Indirect` return.
    let make3 = module
        .functions
        .iter_mut()
        .find(|function| function.name == "ext_make3")
        .expect("the return-buffer callee");
    make3.attrs.params = vec![
        trust_ir::ParamAttrs {
            sret: true,
            ..trust_ir::ParamAttrs::default()
        },
        trust_ir::ParamAttrs::default(),
    ];
    module
}

/// Acyclic control flow past the slice-6 bounds, stated over the DAG (16
/// blocks, 32 paths each): five `bool`s each choosing whether an external
/// function is called, five `bool`s each choosing whether a constant is
/// xored into a `u64` (joined into one value), and five bits of a `u64`
/// each choosing whether it is stored through a pointer.
fn add_slice_nine(builder: &mut ModuleBuilder) {
    use trust_ir::ICmpOp;
    let nothing = builder.add_func_type(vec![], vec![]);
    let tick = builder.declare_function("ext_tick", nothing);
    let flags = builder.add_func_type(vec![Ty::Bool; 5], vec![]);
    let mut f = builder.function("dag_calls", flags);
    let entry = f.create_block();
    let conditions: Vec<_> = (0..5).map(|_| f.add_block_param(entry, Ty::Bool)).collect();
    f.switch_to_block(entry);
    for c in conditions {
        let (call, done) = (f.create_block(), f.create_block());
        f.condbr(c, call, vec![], done, vec![]);
        f.switch_to_block(call);
        f.call_void(tick, vec![]);
        f.br(done, vec![]);
        f.switch_to_block(done);
    }
    f.ret(vec![]);
    f.build();

    let xors = builder.add_func_type(
        vec![Ty::U64, Ty::Bool, Ty::Bool, Ty::Bool, Ty::Bool, Ty::Bool],
        vec![Ty::U64],
    );
    let mut f = builder.function("dag_xors", xors);
    let entry = f.create_block();
    let mut acc = f.add_block_param(entry, Ty::U64);
    let conditions: Vec<_> = (0..5).map(|_| f.add_block_param(entry, Ty::Bool)).collect();
    f.switch_to_block(entry);
    for (i, c) in conditions.into_iter().enumerate() {
        let (then, other, join) = (f.create_block(), f.create_block(), f.create_block());
        let next = f.add_block_param(join, Ty::U64);
        f.condbr(c, then, vec![], other, vec![]);
        f.switch_to_block(then);
        let k = f.iconst(Ty::U64, 1 << (8 * i));
        let flipped = f.binop(BinOp::Xor, Ty::U64, acc, k);
        f.br(join, vec![flipped]);
        f.switch_to_block(other);
        f.br(join, vec![acc]);
        f.switch_to_block(join);
        acc = next;
    }
    f.ret(vec![acc]);
    f.build();

    let stores = builder.add_func_type(vec![Ty::PtrMut(Box::new(Ty::U64)), Ty::U64], vec![]);
    let mut f = builder.function("dag_stores", stores);
    let entry = f.create_block();
    let p = f.add_block_param(entry, Ty::PtrMut(Box::new(Ty::U64)));
    let x = f.add_block_param(entry, Ty::U64);
    f.switch_to_block(entry);
    for i in 0..5 {
        let (store, done) = (f.create_block(), f.create_block());
        let mask = f.iconst(Ty::U64, 1 << i);
        let bit = f.binop(BinOp::And, Ty::U64, x, mask);
        let zero = f.iconst(Ty::U64, 0);
        let set = f.icmp(ICmpOp::Ne, Ty::U64, bit, zero);
        f.condbr(set, store, vec![], done, vec![]);
        f.switch_to_block(store);
        let offset = f.iconst(Ty::U64, i);
        let value = f.add(Ty::U64, x, offset);
        f.store(Ty::U64, p, value);
        f.br(done, vec![]);
        f.switch_to_block(done);
    }
    f.ret(vec![]);
    f.build();
}

/// Instruction coverage: `u64::overflowing_add` (checked arithmetic: `add`
/// and the carry `setb` reads, a RAX:DL pair), `!x` of a `u64` (`not`),
/// `u32::count_ones` (`popcnt`), an unchecked `u64` shift right by a variable
/// amount (`shr r64, cl`) and a call through a function pointer (`call
/// r64`).
fn add_slice_ten(builder: &mut ModuleBuilder) {
    let pair = builder.add_func_type(vec![Ty::U64, Ty::U64], vec![Ty::U64, Ty::Bool]);
    let mut f = builder.function("insn_overflowing_add", pair);
    let entry = f.create_block();
    let a = f.add_block_param(entry, Ty::U64);
    let b = f.add_block_param(entry, Ty::U64);
    f.switch_to_block(entry);
    let (sum, carry) = f.overflow(trust_ir::OverflowOp::AddOverflow, Ty::U64, a, b);
    f.ret(vec![sum, carry]);
    f.build();

    let unary = builder.add_func_type(vec![Ty::U64], vec![Ty::U64]);
    let mut f = builder.function("insn_not", unary);
    let entry = f.create_block();
    let x = f.add_block_param(entry, Ty::U64);
    f.switch_to_block(entry);
    let not = f.unop(trust_ir::UnOp::Not, Ty::U64, x);
    f.ret(vec![not]);
    f.build();

    let count = builder.add_func_type(vec![Ty::U32], vec![Ty::U32]);
    let mut f = builder.function("insn_count_ones", count);
    let entry = f.create_block();
    let x = f.add_block_param(entry, Ty::U32);
    f.switch_to_block(entry);
    let ones = f.ctpop(Ty::U32, x);
    f.ret(vec![ones]);
    f.build();

    let binary = builder.add_func_type(vec![Ty::U64, Ty::U64], vec![Ty::U64]);
    let mut f = builder.function("insn_shr", binary);
    let entry = f.create_block();
    let x = f.add_block_param(entry, Ty::U64);
    let n = f.add_block_param(entry, Ty::U64);
    f.switch_to_block(entry);
    let shifted = f.binop(BinOp::LShr, Ty::U64, x, n);
    f.ret(vec![shifted]);
    f.build();

    let through = builder.add_func_type(vec![Ty::Ptr, Ty::U64], vec![Ty::U64]);
    let mut f = builder.function("insn_indirect", through);
    let entry = f.create_block();
    let callee = f.add_block_param(entry, Ty::Ptr);
    let x = f.add_block_param(entry, Ty::U64);
    f.switch_to_block(entry);
    let y = f.call_indirect(callee, unary, vec![x]);
    f.ret(vec![y]);
    f.build();
}

/// Register pairs and float bit patterns: a `u128` add (`add; adc`) and an
/// unsigned `u128` compare (the halves' compares combined), a `u128` passed
/// to and returned by an external callee (RDI:RSI, RAX:RDX), `f64::to_bits`
/// (`movq` from XMM0), `f32::from_bits` (`movd` to XMM0), and an `f64`
/// passed through an external callee (XMM0 both ways).
fn add_slice_eleven(builder: &mut ModuleBuilder) {
    let wide = builder.add_func_type(vec![Ty::U128], vec![Ty::U128]);
    let ext_wide = builder.declare_function("ext_wide", wide);
    let float = builder.add_func_type(vec![Ty::F64], vec![Ty::F64]);
    let ext_float = builder.declare_function("ext_float", float);
    function(
        builder,
        "wide_add",
        vec![Ty::U128, Ty::U128],
        Ty::U128,
        |f, a| f.add(Ty::U128, a[0], a[1]),
    );
    function(
        builder,
        "wide_lt",
        vec![Ty::U128, Ty::U128],
        Ty::Bool,
        |f, a| f.icmp(trust_ir::ICmpOp::Ult, Ty::U128, a[0], a[1]),
    );
    function(builder, "wide_call", vec![Ty::U128], Ty::U128, |f, a| {
        f.call(ext_wide, vec![a[0]])
    });
    function(builder, "float_to_bits", vec![Ty::F64], Ty::U64, |f, a| {
        f.cast(CastOp::Bitcast, Ty::F64, Ty::U64, a[0])
    });
    function(
        builder,
        "float_from_bits",
        vec![Ty::U32],
        Ty::F32,
        |f, a| f.cast(CastOp::Bitcast, Ty::U32, Ty::F32, a[0]),
    );
    function(builder, "float_call", vec![Ty::F64], Ty::F64, |f, a| {
        f.call(ext_float, vec![a[0]])
    });
}

/// Memory and values: the address of a local stored through an out-pointer
/// (the slot escapes at the store), `fn(a, .., g) -> a + g` (the seventh
/// parameter at `[rbp + 16]`), a call passing seven `u64`s (the seventh at
/// `[rsp]`), a `Memcpy` (a call to `memcpy`) and a `u32` `Acquire` load.
fn add_slice_thirteen(builder: &mut ModuleBuilder) {
    let ptr_u64 = Ty::PtrMut(Box::new(Ty::U64));
    let ptr_ptr = Ty::PtrMut(Box::new(ptr_u64.clone()));
    let seven = builder.add_func_type(vec![Ty::U64; 7], vec![Ty::U64]);
    let ext_seven = builder.declare_function("ext_seven", seven);

    let out = builder.add_func_type(vec![ptr_ptr.clone(), Ty::U64], vec![]);
    let mut f = builder.function("addr_out", out);
    let entry = f.create_block();
    let p = f.add_block_param(entry, ptr_ptr);
    let x = f.add_block_param(entry, Ty::U64);
    f.switch_to_block(entry);
    let v = f.alloca(Ty::U64);
    f.store(Ty::U64, v, x);
    let address = retype(&mut f, v, ptr_u64.clone());
    f.store(ptr_u64, p, address);
    f.ret(vec![]);
    f.build();

    function(builder, "stack_param", vec![Ty::U64; 7], Ty::U64, |f, a| {
        f.add(Ty::U64, a[0], a[6])
    });
    function(builder, "stack_arg", vec![Ty::U64], Ty::U64, |f, a| {
        f.call(ext_seven, vec![a[0]; 7])
    });

    // The byte count of a `MemCopy` is the pinned target's `usize`.
    let copy = builder.add_func_type(vec![Ty::Ptr, Ty::Ptr, Ty::Usize], vec![]);
    let mut f = builder.function("mem_copy", copy);
    let entry = f.create_block();
    let dst = f.add_block_param(entry, Ty::Ptr);
    let src = f.add_block_param(entry, Ty::Ptr);
    let len = f.add_block_param(entry, Ty::Usize);
    f.switch_to_block(entry);
    f.memcopy(dst, src, len, false);
    f.ret(vec![]);
    f.build();

    function(builder, "atomic_acquire", vec![Ty::Ptr], Ty::U32, |f, a| {
        f.atomic_load(Ty::U32, a[0], trust_ir::Ordering::Acquire)
    });
}

/// The value, call and observable residue: `fn() -> f64 { 1.5 }` (a
/// constant-pool load), `fn(x: f64) -> f64 { -x }` (`pxor` with the sign
/// mask), `fn(x: f32) -> f32 { x.abs() }` (`andps`), `fn(b: bool) -> bool {
/// ext_flip(b) }` (the entry `movzx` forwarded), `fn(x: u64) -> u64 { let v
/// = x; *ext_id(&v) }` (a load through the pointer a callee returned after
/// `v` escaped to it) and `fn(a: u64, b: u128, c: u128, d: u128) -> u128 {
/// d }` (`d` in two eightbytes at `[rbp + 16]`).
/// Definedness and dispatch: a `u64` division after the bridge's
/// divide-by-zero check, an `i32` remainder annotated `DivNonZero` (its
/// guard's trap carrier), a division by a power of two (the magic multiply;
/// a division by another constant is a recorded replayer gap), a
/// `match` whose two cases share an arm (`43 | 45`), and a `u32` jump table
/// with a hole the default shares.
fn add_slice_fourteen(builder: &mut ModuleBuilder) {
    let binary = builder.add_func_type(vec![Ty::U64, Ty::U64], vec![Ty::U64]);
    let mut f = builder.function("div_checked", binary);
    let entry = f.create_block();
    let a = f.add_block_param(entry, Ty::U64);
    let b = f.add_block_param(entry, Ty::U64);
    let (trap, go) = (f.create_block(), f.create_block());
    f.switch_to_block(entry);
    let zero = f.iconst(Ty::U64, 0);
    let is_zero = f.icmp(trust_ir::ICmpOp::Eq, Ty::U64, b, zero);
    f.condbr(is_zero, trap, vec![], go, vec![]);
    f.switch_to_block(trap);
    f.unreachable();
    f.switch_to_block(go);
    let q = f.binop(BinOp::UDiv, Ty::U64, a, b);
    f.ret(vec![q]);
    f.build();

    function(
        builder,
        "rem_guarded",
        vec![Ty::I32, Ty::I32],
        Ty::I32,
        |f, a| {
            f.binop_proven(
                BinOp::SRem,
                Ty::I32,
                a[0],
                a[1],
                vec![trust_ir::ProofAnnotation::DivNonZero],
            )
        },
    );
    function(builder, "div_by_eight", vec![Ty::U64], Ty::U64, |f, a| {
        let eight = f.iconst(Ty::U64, 8);
        f.binop(BinOp::UDiv, Ty::U64, a[0], eight)
    });

    for (name, ty, cases, targets, arms) in [
        (
            "shared_sign",
            Ty::U8,
            &[43i128, 45][..],
            &[0usize, 0][..],
            2usize,
        ),
        (
            "table_holes",
            Ty::U32,
            &[0, 1, 3, 4][..],
            &[0, 1, 2, 3][..],
            4,
        ),
    ] {
        let signature = builder.add_func_type(vec![ty.clone()], vec![Ty::U64]);
        let mut f = builder.function(name, signature);
        let entry = f.create_block();
        let x = f.add_block_param(entry, ty);
        let blocks: Vec<_> = (0..arms).map(|_| f.create_block()).collect();
        f.switch_to_block(entry);
        f.switch(
            x,
            cases
                .iter()
                .zip(targets)
                .map(|(value, target)| trust_ir::SwitchCase {
                    value: trust_ir::Constant::Int(*value),
                    target: blocks[*target],
                    args: vec![],
                })
                .collect(),
            blocks[arms - 1],
            vec![],
        );
        for (k, block) in blocks.iter().enumerate() {
            f.switch_to_block(*block);
            let value = f.iconst(Ty::U64, 10 + k as i128);
            f.ret(vec![value]);
        }
        f.build();
    }
}

fn add_slice_fifteen(builder: &mut ModuleBuilder) {
    let ptr_u64 = Ty::PtrMut(Box::new(Ty::U64));
    let flip = builder.add_func_type(vec![Ty::Bool], vec![Ty::Bool]);
    let ext_flip = builder.declare_function("ext_flip", flip);
    let id = builder.add_func_type(vec![ptr_u64.clone()], vec![ptr_u64.clone()]);
    let ext_id = builder.declare_function("ext_id", id);

    let constant = builder.add_func_type(vec![], vec![Ty::F64]);
    let mut f = builder.function("float_const", constant);
    let entry = f.create_block();
    f.switch_to_block(entry);
    let value = f.fconst(Ty::F64, 1.5);
    f.ret(vec![value]);
    f.build();

    function(builder, "float_neg", vec![Ty::F64], Ty::F64, |f, a| {
        f.unop(UnOp::FNeg, Ty::F64, a[0])
    });
    function(builder, "float_abs", vec![Ty::F32], Ty::F32, |f, a| {
        f.unop(UnOp::FAbs, Ty::F32, a[0])
    });
    function(builder, "bool_forward", vec![Ty::Bool], Ty::Bool, |f, a| {
        f.call(ext_flip, vec![a[0]])
    });
    function(builder, "derived_load", vec![Ty::U64], Ty::U64, |f, a| {
        let v = f.alloca(Ty::U64);
        f.store(Ty::U64, v, a[0]);
        let address = retype(f, v, ptr_u64.clone());
        let pointer = f.call(ext_id, vec![address]);
        f.load(Ty::U64, pointer)
    });
    function(
        builder,
        "wide_stack_param",
        vec![Ty::U64, Ty::U128, Ty::U128, Ty::U128],
        Ty::U128,
        |_, a| a[3],
    );
}

/// Floating-point operations as paired rounding events (rulings OD-198 to
/// OD-200: an `f64` product, an `f32` quotient, `une`, the saturating `f64 as
/// i64`, `i64 as f64` and core's `pow2_to_pow10`) and the remaining atomics
/// (OD-201: the exchange, and the `u128` atomic load through the `cmpxchg16b`
/// pseudo row).
fn add_slice_twenty_two(builder: &mut ModuleBuilder) {
    for (name, ty, op) in [
        ("u128_div_checked", Ty::U128, BinOp::UDiv),
        ("i128_rem_checked", Ty::I128, BinOp::SRem),
    ] {
        let binary = builder.add_func_type(vec![ty.clone(), ty.clone()], vec![ty.clone()]);
        let mut f = builder.function(name, binary);
        let entry = f.create_block();
        let a = f.add_block_param(entry, ty.clone());
        let b = f.add_block_param(entry, ty.clone());
        let (trap, go) = (f.create_block(), f.create_block());
        f.switch_to_block(entry);
        let zero = f.iconst(ty.clone(), 0);
        let is_zero = f.icmp(trust_ir::ICmpOp::Eq, ty.clone(), b, zero);
        f.condbr(is_zero, trap, vec![], go, vec![]);
        f.switch_to_block(trap);
        f.unreachable();
        f.switch_to_block(go);
        let q = f.binop(op, ty, a, b);
        f.ret(vec![q]);
        f.build();
    }
    function(
        builder,
        "u128_div_guarded",
        vec![Ty::U128, Ty::U128],
        Ty::U128,
        |f, a| {
            f.binop_proven(
                BinOp::UDiv,
                Ty::U128,
                a[0],
                a[1],
                vec![trust_ir::ProofAnnotation::DivNonZero],
            )
        },
    );
    function(
        builder,
        "u64_widening_mul_overflows",
        vec![Ty::U64, Ty::U64],
        Ty::Bool,
        |f, a| {
            let x = f.zext(Ty::U64, Ty::U128, a[0]);
            let y = f.zext(Ty::U64, Ty::U128, a[1]);
            f.overflow(trust_ir::OverflowOp::MulOverflow, Ty::U128, x, y)
                .1
        },
    );
}

fn add_slice_twenty_one(builder: &mut ModuleBuilder) {
    function(
        builder,
        "float_mul",
        vec![Ty::F64, Ty::F64],
        Ty::F64,
        |f, a| f.fmul(Ty::F64, a[0], a[1]),
    );
    function(
        builder,
        "float_div32",
        vec![Ty::F32, Ty::F32],
        Ty::F32,
        |f, a| f.binop(BinOp::FDiv, Ty::F32, a[0], a[1]),
    );
    function(
        builder,
        "float_une",
        vec![Ty::F64, Ty::F64],
        Ty::Bool,
        |f, a| f.fcmp(trust_ir::FCmpOp::UNe, Ty::F64, a[0], a[1]),
    );
    function(builder, "float_to_i64", vec![Ty::F64], Ty::I64, |f, a| {
        f.cast(CastOp::FPToSISat, Ty::F64, Ty::I64, a[0])
    });
    function(builder, "i64_to_float", vec![Ty::I64], Ty::F64, |f, a| {
        f.cast(CastOp::SIToFP, Ty::I64, Ty::F64, a[0])
    });
    function(builder, "pow2_to_pow10", vec![Ty::I64], Ty::I64, |f, a| {
        let x = f.cast(CastOp::SIToFP, Ty::I64, Ty::F64, a[0]);
        let log = f.fconst(Ty::F64, std::f64::consts::LOG2_10);
        let q = f.binop(BinOp::FDiv, Ty::F64, x, log);
        f.cast(CastOp::FPToSISat, Ty::F64, Ty::I64, q)
    });
    let ptr_u64 = Ty::PtrMut(Box::new(Ty::U64));
    function(
        builder,
        "xchg_u64",
        vec![ptr_u64, Ty::U64],
        Ty::U64,
        |f, a| {
            f.atomic_rmw(
                trust_ir::AtomicRMWOp::Xchg,
                Ty::U64,
                a[0],
                a[1],
                trust_ir::Ordering::SeqCst,
            )
        },
    );
    let ptr_u128 = Ty::PtrMut(Box::new(Ty::U128));
    function(
        builder,
        "atomic_load_u128",
        vec![ptr_u128],
        Ty::U128,
        |f, a| f.atomic_load(Ty::U128, a[0], trust_ir::Ordering::Acquire),
    );
}

/// Aggregates in general-purpose registers: a four-byte parameter's field
/// (EDI's third byte), a `[u64; 2]` parameter (RDI:RSI) passed on by value to
/// an external callee, and an external callee's two-`u32` result (RAX) whose
/// two fields are combined.
///
/// The two bodies that read lanes spell their aggregate as a lane TUPLE
/// (`(u8, u8, u8, u8)`, `(u32, u32)`), the rustc bridge's other spelling of a
/// slot's lane image (`memory_slot_lane_ty`; the two are interchangeable byte
/// for byte), read with `extract_field`. trust-ir defines `extract_field`
/// over no array, and an array's lane read, `extract_element`, lowers to an
/// `ArrayGep` the body lane does not admit. The tuple spelling keeps the
/// machine stream the array one had under the adapter's legacy reading.
///
/// A result built field by field in a slot and returned is not here: its
/// valid spellings (`make_aggregate`, or the bridge's `load` of the slot at
/// the return edge) give the slot address the aggregate's type, which the
/// body lane refuses (decision record DR-X86-BODY-E2E-TYPED-FIXTURE-20261015).
fn add_slice_eight(builder: &mut ModuleBuilder) {
    let u64x2 = Ty::Array(builder.add_type(Ty::U64), 2);
    let u8x4 = Ty::Tuple(vec![Ty::U8; 4]);
    let u32x2 = Ty::Tuple(vec![Ty::U32; 2]);
    let take = builder.add_func_type(vec![u64x2.clone()], vec![Ty::U64]);
    let take2 = builder.declare_function("ext_take2", take);
    let give = builder.add_func_type(vec![Ty::U64], vec![u32x2]);
    let give2 = builder.declare_function("ext_give2", give);

    let field = builder.add_func_type(vec![u8x4.clone()], vec![Ty::U8]);
    let mut f = builder.function("agg_param_field", field);
    let entry = f.create_block();
    let a = f.add_block_param(entry, u8x4);
    f.switch_to_block(entry);
    let byte = f.extract_field(Ty::U8, a, 2);
    f.ret(vec![byte]);
    f.build();

    let mut f = builder.function("agg_call_arg", take);
    let entry = f.create_block();
    let p = f.add_block_param(entry, u64x2);
    f.switch_to_block(entry);
    let result = f.call(take2, vec![p]);
    f.ret(vec![result]);
    f.build();

    let unary = builder.add_func_type(vec![Ty::U64], vec![Ty::U32]);
    let mut f = builder.function("agg_call_result", unary);
    let entry = f.create_block();
    let x = f.add_block_param(entry, Ty::U64);
    f.switch_to_block(entry);
    let both = f.call(give2, vec![x]);
    let a = f.extract_field(Ty::U32, both, 0);
    let b = f.extract_field(Ty::U32, both, 1);
    let mixed = f.binop(BinOp::Sub, Ty::U32, a, b);
    f.ret(vec![mixed]);
    f.build();
}

/// Calls through memory: a return buffer (an external `sret` callee writes
/// a three-word struct into a private slot, which is read back), a `&mut`
/// out-parameter, a `&` argument the callee reads, and an `Option<u64>`
/// out-parameter whose tag is branched on.
fn add_slice_seven(builder: &mut ModuleBuilder) {
    use trust_ir::ICmpOp;
    // Its own id: the module resolves a struct type by id, and slice 2's
    // `Pair` is id 0.
    let three = Ty::Struct(
        builder.add_struct(StructDef {
            origin: None,
            id: StructId::new(1),
            name: "Three".into(),
            fields: ["a", "b", "c"]
                .map(|name| FieldDef {
                    name: name.into(),
                    ty: Ty::U64,
                    offset: None,
                })
                .to_vec(),
            size: None,
            align: None,
            repr: StructRepr::C,
        }),
    );
    let unary = builder.add_func_type(vec![Ty::U64], vec![Ty::U64]);
    let buffer = builder.add_func_type(vec![Ty::Ptr, Ty::U64], vec![]);
    let make3 = builder.declare_function("ext_make3", buffer);
    let out = builder.add_func_type(vec![Ty::PtrMut(Box::new(Ty::U64))], vec![]);
    let bump = builder.declare_function("ext_bump", out);
    let fill = builder.declare_function("ext_fill", out);
    let read = builder.add_func_type(vec![Ty::PtrConst(Box::new(Ty::U64))], vec![Ty::U64]);
    let peek = builder.declare_function("ext_peek", read);

    let mut f = builder.function("through_sret_sum", unary);
    let entry = f.create_block();
    let x = f.add_block_param(entry, Ty::U64);
    f.switch_to_block(entry);
    let t = f.alloca(three.clone());
    f.call_void(make3, vec![t, x]);
    let a = f.load(Ty::U64, t);
    let pc = f.gep_byte_offset(t, 16);
    let c = f.load(Ty::U64, pc);
    let sum = f.add(Ty::U64, a, c);
    f.ret(vec![sum]);
    f.build();

    let mut f = builder.function("through_out_param", unary);
    let entry = f.create_block();
    let x = f.add_block_param(entry, Ty::U64);
    f.switch_to_block(entry);
    let v = f.alloca(Ty::U64);
    f.store(Ty::U64, v, x);
    let address = retype(&mut f, v, Ty::PtrMut(Box::new(Ty::U64)));
    f.call_void(bump, vec![address]);
    let back = f.load(Ty::U64, v);
    f.ret(vec![back]);
    f.build();

    let mut f = builder.function("through_read_ref", unary);
    let entry = f.create_block();
    let x = f.add_block_param(entry, Ty::U64);
    f.switch_to_block(entry);
    let v = f.alloca(Ty::U64);
    f.store(Ty::U64, v, x);
    let address = retype(&mut f, v, Ty::PtrConst(Box::new(Ty::U64)));
    let seen = f.call(peek, vec![address]);
    f.ret(vec![seen]);
    f.build();

    let mut f = builder.function("through_option_out", unary);
    let (entry, some, other, join) = (
        f.create_block(),
        f.create_block(),
        f.create_block(),
        f.create_block(),
    );
    let fallback = f.add_block_param(entry, Ty::U64);
    let result = f.add_block_param(join, Ty::U64);
    f.switch_to_block(entry);
    let o = f.alloca(Ty::U64);
    let payload_slot = f.alloca(three);
    let none = f.iconst(Ty::U64, 0);
    f.store(Ty::U64, payload_slot, none);
    let address = retype(&mut f, payload_slot, Ty::PtrMut(Box::new(Ty::U64)));
    f.call_void(fill, vec![address]);
    let tag = f.load(Ty::U64, payload_slot);
    let zero = f.iconst(Ty::U64, 0);
    let is_some = f.icmp(ICmpOp::Ne, Ty::U64, tag, zero);
    f.condbr(is_some, some, vec![], other, vec![]);
    f.switch_to_block(some);
    let payload = f.gep_byte_offset(payload_slot, 8);
    let value = f.load(Ty::U64, payload);
    f.br(join, vec![value]);
    f.switch_to_block(other);
    f.store(Ty::U64, o, fallback);
    let kept = f.load(Ty::U64, o);
    f.br(join, vec![kept]);
    f.switch_to_block(join);
    f.ret(vec![result]);
    f.build();
}

/// Acyclic control flow: a diamond whose join takes a block parameter, an
/// early return, a panic arm (a diverging call, then a trap), a switch
/// compare chain, a `cmov` select, and a slot written on one path only.
fn add_slice_six(builder: &mut ModuleBuilder) {
    use trust_ir::ICmpOp;
    let binary = builder.add_func_type(vec![Ty::U64, Ty::U64], vec![Ty::U64]);
    let unary = builder.add_func_type(vec![Ty::U64], vec![Ty::U64]);
    let fail = builder.add_func_type(vec![Ty::U64, Ty::U64], vec![]);
    let panic = builder.declare_function("ext_panic_at", fail);

    let mut f = builder.function("branch_min", binary);
    let (entry, then, other, join) = (
        f.create_block(),
        f.create_block(),
        f.create_block(),
        f.create_block(),
    );
    let a = f.add_block_param(entry, Ty::U64);
    let b = f.add_block_param(entry, Ty::U64);
    let result = f.add_block_param(join, Ty::U64);
    f.switch_to_block(entry);
    let less = f.icmp(ICmpOp::Ult, Ty::U64, a, b);
    f.condbr(less, then, vec![], other, vec![]);
    f.switch_to_block(then);
    f.br(join, vec![a]);
    f.switch_to_block(other);
    f.br(join, vec![b]);
    f.switch_to_block(join);
    f.ret(vec![result]);
    f.build();

    let mut f = builder.function("branch_early_return", unary);
    let (entry, early, rest) = (f.create_block(), f.create_block(), f.create_block());
    let x = f.add_block_param(entry, Ty::U64);
    f.switch_to_block(entry);
    let zero = f.iconst(Ty::U64, 0);
    let is_zero = f.icmp(ICmpOp::Eq, Ty::U64, x, zero);
    f.condbr(is_zero, early, vec![], rest, vec![]);
    f.switch_to_block(early);
    let seven = f.iconst(Ty::U64, 7);
    f.ret(vec![seven]);
    f.switch_to_block(rest);
    let one = f.iconst(Ty::U64, 1);
    let next = f.add(Ty::U64, x, one);
    f.ret(vec![next]);
    f.build();

    let mut f = builder.function("branch_panic_arm", binary);
    let (entry, failed, ok) = (f.create_block(), f.create_block(), f.create_block());
    let i = f.add_block_param(entry, Ty::U64);
    let n = f.add_block_param(entry, Ty::U64);
    f.switch_to_block(entry);
    let out_of_bounds = f.icmp(ICmpOp::Uge, Ty::U64, i, n);
    f.condbr(out_of_bounds, failed, vec![], ok, vec![]);
    f.switch_to_block(failed);
    f.call_void(panic, vec![i, n]);
    f.unreachable();
    f.switch_to_block(ok);
    f.ret(vec![i]);
    f.build();

    let mut f = builder.function("branch_switch", unary);
    let entry = f.create_block();
    let x = f.add_block_param(entry, Ty::U64);
    let targets: Vec<_> = (0..3).map(|_| f.create_block()).collect();
    let default = f.create_block();
    f.switch_to_block(entry);
    f.switch(
        x,
        [1, 2, 7]
            .iter()
            .zip(&targets)
            .map(|(value, target)| trust_ir::SwitchCase {
                value: trust_ir::Constant::Int(*value),
                target: *target,
                args: vec![],
            })
            .collect(),
        default,
        vec![],
    );
    for (result, target) in [10, 20, 70].iter().zip(&targets) {
        f.switch_to_block(*target);
        let value = f.iconst(Ty::U64, *result);
        f.ret(vec![value]);
    }
    f.switch_to_block(default);
    let zero = f.iconst(Ty::U64, 0);
    f.ret(vec![zero]);
    f.build();

    function(
        builder,
        "branch_select",
        vec![Ty::U64, Ty::U64],
        Ty::U64,
        |f, a| {
            let less = f.icmp(ICmpOp::Ult, Ty::U64, a[0], a[1]);
            f.select(Ty::U64, less, a[0], a[1])
        },
    );

    let tagged = builder.add_func_type(vec![Ty::U64, Ty::Bool], vec![Ty::U64, Ty::U64]);
    let mut f = builder.function("branch_partial_init", tagged);
    let (entry, some, none, join) = (
        f.create_block(),
        f.create_block(),
        f.create_block(),
        f.create_block(),
    );
    let x = f.add_block_param(entry, Ty::U64);
    let present = f.add_block_param(entry, Ty::Bool);
    f.switch_to_block(entry);
    let tag = f.alloca(Ty::U64);
    let payload = f.alloca(Ty::U64);
    f.condbr(present, some, vec![], none, vec![]);
    f.switch_to_block(some);
    let one = f.iconst(Ty::U64, 1);
    f.store(Ty::U64, tag, one);
    f.store(Ty::U64, payload, x);
    f.br(join, vec![]);
    f.switch_to_block(none);
    let zero = f.iconst(Ty::U64, 0);
    f.store(Ty::U64, tag, zero);
    f.br(join, vec![]);
    f.switch_to_block(join);
    let tag = f.load(Ty::U64, tag);
    let payload = f.load(Ty::U64, payload);
    f.ret(vec![tag, payload]);
    f.build();
}

/// Scalar pairs (a RAX:RDX return, a call returning a pair, and the `bool`
/// lane of a pair call, which defines bit 0 alone and is masked), a global's
/// address and a load through it, and branch-free compares.
fn add_slice_five(builder: &mut ModuleBuilder) {
    builder.add_global(trust_ir::Global {
        name: "s5_counter".into(),
        ty: Ty::U64,
        mutable: true,
        initializer: Some(trust_ir::Constant::Int(0)),
        linkage: trust_ir::Linkage::External,
        tls: None,
        align: None,
        section: None,
        visibility: Default::default(),
        retained: false,
    });
    let counter = trust_ir::value::GlobalId::new(0);
    let pair = builder.add_func_type(vec![Ty::U64, Ty::U64], vec![Ty::U64, Ty::U64]);
    let mut f = builder.function("pair_swap", pair);
    let entry = f.create_block();
    let a = f.add_block_param(entry, Ty::U64);
    let b = f.add_block_param(entry, Ty::U64);
    f.switch_to_block(entry);
    f.ret(vec![b, a]);
    f.build();
    let split = builder.add_func_type(vec![Ty::U64], vec![Ty::U64, Ty::U64]);
    let ext_pair = builder.declare_function("ext_pair", split);
    function(builder, "pair_call_sum", vec![Ty::U64], Ty::U64, |f, a| {
        let [x, y] = f.call_results::<2>(ext_pair, vec![a[0]]);
        f.add(Ty::U64, x, y)
    });
    let split_bool = builder.add_func_type(vec![Ty::U64], vec![Ty::U64, Ty::Bool]);
    let ext_pair_bool = builder.declare_function("ext_pair_bool", split_bool);
    function(builder, "pair_call_bool", vec![Ty::U64], Ty::U64, |f, a| {
        let [_, lane] = f.call_results::<2>(ext_pair_bool, vec![a[0]]);
        f.zext(Ty::Bool, Ty::U64, lane)
    });
    // `GlobalAddr` yields an opaque `ptr`, the type this function returns
    // (a `*const u64` return is `ReturnTypeMismatch`; WS7.3 admission).
    function(builder, "global_addr", vec![], Ty::Ptr, |f, _| {
        f.global_addr(counter)
    });
    function(builder, "global_load", vec![], Ty::U64, |f, _| {
        let address = f.global_addr(counter);
        f.load(Ty::U64, address)
    });
    function(
        builder,
        "cmp_lt",
        vec![Ty::U64, Ty::U64],
        Ty::Bool,
        |f, a| f.icmp(trust_ir::ICmpOp::Ult, Ty::U64, a[0], a[1]),
    );
    function(
        builder,
        "cmp_sge_i8",
        vec![Ty::I8, Ty::I8],
        Ty::Bool,
        |f, a| f.icmp(trust_ir::ICmpOp::Sge, Ty::I8, a[0], a[1]),
    );
}

/// Memory: incoming loads and stores through pointer parameters (which may
/// alias), a field at a constant offset, a private stack slot, and memory
/// threaded through a call.
fn add_slice_four(builder: &mut ModuleBuilder) {
    let pointer = || Ty::PtrMut(Box::new(Ty::U64));
    let unary = builder.add_func_type(vec![Ty::U64], vec![Ty::U64]);
    let ext = builder.declare_function("ext_mem_unary", unary);
    function(builder, "mem_load", vec![pointer()], Ty::U64, |f, a| {
        f.load(Ty::U64, a[0])
    });
    let store = builder.add_func_type(vec![pointer(), Ty::U64], vec![]);
    let mut f = builder.function("mem_store", store);
    let entry = f.create_block();
    let p = f.add_block_param(entry, pointer());
    let v = f.add_block_param(entry, Ty::U64);
    f.switch_to_block(entry);
    f.store(Ty::U64, p, v);
    f.ret(vec![]);
    f.build();
    function(builder, "mem_field", vec![pointer()], Ty::U64, |f, a| {
        let field = f.gep_byte_offset(a[0], 8);
        f.load(Ty::U64, field)
    });
    function(builder, "mem_local", vec![Ty::U64], Ty::U64, |f, a| {
        let slot = f.alloca(Ty::U64);
        f.store(Ty::U64, slot, a[0]);
        f.load(Ty::U64, slot)
    });
    function(
        builder,
        "mem_store_then_load",
        vec![pointer(), pointer(), Ty::U64],
        Ty::U64,
        |f, a| {
            f.store(Ty::U64, a[0], a[2]);
            f.load(Ty::U64, a[1])
        },
    );
    function(
        builder,
        "mem_store_call",
        vec![pointer(), Ty::U64],
        Ty::U64,
        |f, a| {
            f.store(Ty::U64, a[0], a[1]);
            f.call(ext, vec![a[1]])
        },
    );
}

/// Direct calls: to a function of this module (an exact-module binding) and
/// to an external declaration (bound by symbol).
fn add_slice_three(builder: &mut ModuleBuilder, ident: trust_ir::FuncId) {
    let unary = builder.add_func_type(vec![Ty::U64], vec![Ty::U64]);
    let binary = builder.add_func_type(vec![Ty::U64, Ty::U64], vec![Ty::U64]);
    let consume = builder.add_func_type(vec![Ty::U64], vec![]);
    let ext = builder.declare_function("ext_unary", unary);
    let ext2 = builder.declare_function("ext_binary", binary);
    let sink = builder.declare_function("ext_sink", consume);
    function(builder, "call_module", vec![Ty::U64], Ty::U64, |f, a| {
        f.call(ident, vec![a[0]])
    });
    function(builder, "call_extern", vec![Ty::U64], Ty::U64, |f, a| {
        f.call(ext, vec![a[0]])
    });
    function(
        builder,
        "call_swap",
        vec![Ty::U64, Ty::U64],
        Ty::U64,
        |f, a| f.call(ext2, vec![a[1], a[0]]),
    );
    function(builder, "call_after", vec![Ty::U64], Ty::U64, |f, a| {
        let y = f.call(ext, vec![a[0]]);
        f.add(Ty::U64, y, a[0])
    });
    let mut f = builder.function("call_void", consume);
    let entry = f.create_block();
    let x = f.add_block_param(entry, Ty::U64);
    f.switch_to_block(entry);
    f.call_void(sink, vec![x]);
    f.ret(vec![]);
    f.build();
    let mut f = builder.function("call_diverge", consume);
    let entry = f.create_block();
    let x = f.add_block_param(entry, Ty::U64);
    f.switch_to_block(entry);
    f.call_void(sink, vec![x]);
    f.unreachable();
    f.build();
}

/// The opaque address `address` (an `alloca`'s `ptr`) re-typed as the thin
/// pointer type `ty` its consumer declares (a `*mut u64` or `*const u64`
/// parameter, or a slot holding a `*mut u64`):
/// `PtrToPtr`, the rustc bridge's spelling of such an edge
/// (`abi_edges::legalize_abi_edges`). It changes no address and lowers to
/// the register move a `Copy` does.
fn retype(
    f: &mut trust_ir_build::FunctionBuilder<'_>,
    address: trust_ir::ValueId,
    ty: Ty,
) -> trust_ir::ValueId {
    f.cast(CastOp::PtrToPtr, Ty::Ptr, ty, address)
}

/// One single-block function `name(params) -> result` whose body `body`
/// builds from the parameters.
fn function(
    builder: &mut ModuleBuilder,
    name: &str,
    params: Vec<Ty>,
    result: Ty,
    body: impl FnOnce(
        &mut trust_ir_build::FunctionBuilder<'_>,
        &[trust_ir::ValueId],
    ) -> trust_ir::ValueId,
) {
    let signature = builder.add_func_type(params.clone(), vec![result]);
    let mut f = builder.function(name, signature);
    let entry = f.create_block();
    let args: Vec<_> = params
        .into_iter()
        .map(|ty| f.add_block_param(entry, ty))
        .collect();
    f.switch_to_block(entry);
    let value = body(&mut f, &args);
    f.ret(vec![value]);
    f.build();
}

fn add_slice_two(builder: &mut ModuleBuilder) {
    let pair = Ty::Struct(builder.add_struct(StructDef {
        origin: None,
        id: StructId::new(0),
        name: "Pair".into(),
        fields: vec![
            FieldDef {
                name: "first".into(),
                ty: Ty::U64,
                offset: None,
            },
            FieldDef {
                name: "second".into(),
                ty: Ty::U64,
                offset: None,
            },
        ],
        size: None,
        align: None,
        repr: StructRepr::C,
    }));
    let pair_ptr = Ty::PtrMut(Box::new(pair));
    let byte_ptr = Ty::PtrMut(Box::new(Ty::U8));
    let (from, to) = (pair_ptr.clone(), byte_ptr.clone());
    function(
        builder,
        "ptr_cast",
        vec![pair_ptr],
        byte_ptr.clone(),
        |f, a| f.cast(CastOp::PtrToPtr, from, to, a[0]),
    );
    // `ptrtoint` takes an opaque `ptr` (trust-ir refuses it from a typed
    // pointer, `CastIncompatible`; WS7.3 admission).
    function(builder, "ptr_addr", vec![Ty::Ptr], Ty::Usize, |f, a| {
        f.cast(CastOp::PtrToInt, Ty::Ptr, Ty::Usize, a[0])
    });
    function(builder, "u8_ident", vec![Ty::U8], Ty::U8, |_, a| a[0]);
    function(builder, "bool_false", vec![], Ty::Bool, |f, _| {
        f.bool_const(false)
    });
    function(builder, "bool_ident", vec![Ty::Bool], Ty::Bool, |_, a| a[0]);
    function(builder, "zext_u8", vec![Ty::U8], Ty::U64, |f, a| {
        f.zext(Ty::U8, Ty::U64, a[0])
    });
    function(builder, "sext_i32", vec![Ty::I32], Ty::I64, |f, a| {
        f.sext(Ty::I32, Ty::I64, a[0])
    });
    function(builder, "trunc_bool", vec![Ty::U64], Ty::Bool, |f, a| {
        f.trunc(Ty::U64, Ty::Bool, a[0])
    });
    function(builder, "i8_as_u8", vec![Ty::I8], Ty::U8, |f, a| {
        f.cast(CastOp::Bitcast, Ty::I8, Ty::U8, a[0])
    });
    function(builder, "add_u8", vec![Ty::U8, Ty::U8], Ty::U8, |f, a| {
        f.add(Ty::U8, a[0], a[1])
    });
    function(builder, "add_imm", vec![Ty::U64], Ty::U64, |f, a| {
        let five = f.iconst(Ty::U64, 5);
        f.add(Ty::U64, a[0], five)
    });
    function(builder, "xor", vec![Ty::U64, Ty::U64], Ty::U64, |f, a| {
        f.binop(BinOp::Xor, Ty::U64, a[0], a[1])
    });
    function(builder, "shl_imm", vec![Ty::U64], Ty::U64, |f, a| {
        let three = f.iconst(Ty::U64, 3);
        f.binop(BinOp::Shl, Ty::U64, a[0], three)
    });
}

/// A body outside the lane: a `u128` shift by a variable amount (slice 11
/// admits register pairs, but not a variable shift of one, which the
/// selector does not reduce modulo 128).
fn out_of_lane_module() -> trust_ir::Module {
    let mut builder = ModuleBuilder::new("x86_source_bound_body_e2e_outside");
    function(
        &mut builder,
        "shl_u128",
        vec![Ty::U128, Ty::U128],
        Ty::U128,
        |f, a| f.binop(BinOp::Shl, Ty::U128, a[0], a[1]),
    );
    builder.build().expect("ModuleBuilder::build: test fixture")
}

/// A body inside the lane whose theorem the qualification host's replayer
/// may not certify: a 32-bit multiply. AY build 10530's strict certification
/// rejects its own proof (since slice 11 a signed shift right certifies);
/// AY build 12713 certifies it through the one-shot solve in 0.1 s, but its
/// resident route, which a compile asks first, runs past the 30 s deadline.
/// AY build 13556, the qualification AY since 2026-10-19, takes the
/// word-level path on the resident route too (AY DR-49), and the compile
/// promotes it Formal on both triples (the test's second branch).
fn uncertified_module() -> trust_ir::Module {
    let mut builder = ModuleBuilder::new("x86_source_bound_body_e2e_uncertified");
    function(
        &mut builder,
        "mul_u32",
        vec![Ty::U32, Ty::U32],
        Ty::U32,
        |f, a| f.binop(BinOp::Mul, Ty::U32, a[0], a[1]),
    );
    builder.build().expect("ModuleBuilder::build: test fixture")
}

/// A lane-shaped `u32` add, compiled for Win64 (outside the lane by its
/// calling convention).
fn win64_module() -> trust_ir::Module {
    let mut builder = ModuleBuilder::new("x86_source_bound_body_e2e_win64");
    function(
        &mut builder,
        "add_u32",
        vec![Ty::U32, Ty::U32],
        Ty::U32,
        |f, a| f.add(Ty::U32, a[0], a[1]),
    );
    builder.build().expect("ModuleBuilder::build: test fixture")
}

#[allow(clippy::result_large_err)] // Returns the compiler's own error type unchanged.
fn compile_module(
    triple: &'static str,
    module: trust_ir::Module,
) -> Result<CompilationResult, CompileError> {
    compile_module_in_link_unit(triple, module, &[])
}

/// [`compile_module`] in a link unit whose other compile units define
/// `link_unit` (`CompilerConfig::link_unit_definitions`, ruling OD-216): what
/// the rustc bridge names for a codegen unit of a crate that defines them.
#[allow(clippy::result_large_err)] // Returns the compiler's own error type unchanged.
fn compile_module_in_link_unit(
    triple: &'static str,
    module: trust_ir::Module,
    link_unit: &[&str],
) -> Result<CompilationResult, CompileError> {
    let link_unit_definitions = link_unit.iter().map(|name| (*name).to_owned()).collect();
    // A fixture that calls bodyless declarations or casts pointers to
    // `usize` needs the pinned target (`TargetInfoRequired`, and `usize` has
    // no width without one; WS7.3 ingestion admission). [`module`] is built
    // pinned to `triple`, which this keeps; the single-function modules are
    // pinned here.
    let module = pinned_target::pinned(&module, triple);
    let environment = trust_cg_codegen::env_lock::EnvOverrideSnapshot::capture_current_thread();
    std::thread::Builder::new()
        .stack_size(64 * 1024 * 1024)
        .spawn(move || {
            environment.run(|| {
                let spec = TargetSpec::parse(triple).expect("x86-64 triple");
                let compiler = Compiler::new_for_target_spec(
                    CompilerConfig {
                        opt_level: OptLevel::O0,
                        target: Target::X86_64,
                        emit_proofs: true,
                        parallel: false,
                        link_unit_definitions,
                        ..CompilerConfig::default()
                    },
                    spec,
                )
                .with_codegen_license(permit_unlicensed());
                compiler.compile(&module)
            })
        })
        .expect("spawn compile thread")
        .join()
        .expect("compile thread")
}

#[allow(clippy::result_large_err)] // Returns the compiler's own error type unchanged.
fn compile(triple: &'static str) -> Result<CompilationResult, CompileError> {
    compile_module(triple, module(triple))
}

/// Why the replay tools are unavailable, or `None` when both are present.
///
/// The tools are exactly the ones a production compile would bind: the
/// identity-admitted AY paired with a capable Clean/Carcara checker, where
/// the checker is `TCG_EXTERNAL_CLEAN_CHECKER` when set and otherwise the
/// default discovery's capability-probed package (`store/clean/current`) or
/// Trust sysroot `clean`. No explicit override is required, so a correctly
/// provisioned host runs this test in its default environment (where the JIT
/// outer cache also stays enabled).
fn replay_tools_unavailable() -> Option<String> {
    if std::env::var_os("TCG_REFINE_SOLVER").is_some_and(|value| value == "0") {
        return Some("TCG_REFINE_SOLVER=0 refuses live replay".into());
    }
    let Some(ay) = trust_cg_verify::ay_bridge::admitted_proof_solver() else {
        return Some(
            trust_cg_verify::ay_bridge::proof_toolchain_unavailable_reason()
                .unwrap_or_else(|| "no admitted AY with a capable checker".into()),
        );
    };
    eprintln!(
        "X86_BODY_E2E_REPLAY_IDENTITY ay=[{}] clean=[{}]",
        ay.describe(),
        std::env::var_os("TCG_EXTERNAL_CLEAN_CHECKER")
            .map(|path| std::path::PathBuf::from(path).display().to_string())
            .unwrap_or_else(|| "default discovery (capability-probed)".into())
    );
    None
}

#[test]
fn slice_one_to_ten_functions_promote_with_replayed_body_theorems() {
    if let Some(reason) = replay_tools_unavailable() {
        eprintln!("SKIP slice_one_to_nine_functions_promote_with_replayed_body_theorems: {reason}");
        return;
    }
    for triple in TRIPLES {
        let result = compile(triple).unwrap_or_else(|error| panic!("{triple}: {error}"));
        let proofs = result.proofs.as_ref().expect("proof-required compile");
        assert!(proofs.iter().all(|cert| cert.verified), "{triple}");
        for function in SLICE_ONE
            .iter()
            .chain(&SLICE_TWO)
            .chain(&SLICE_THREE)
            .chain(&SLICE_FOUR)
            .chain(&SLICE_FIVE)
            .chain(&SLICE_SIX)
            .chain(&SLICE_SEVEN)
            .chain(&SLICE_EIGHT)
            .chain(&SLICE_NINE)
            .chain(&SLICE_TEN)
            .chain(&SLICE_ELEVEN)
            .chain(&SLICE_TWELVE)
            .chain(&SLICE_THIRTEEN)
            .chain(&SLICE_FOURTEEN)
            .chain(&SLICE_FIFTEEN)
            .chain(&BOOL_TO_BYTE)
            .chain(&SEXT_BOOL)
            .chain(&SLICE_TWENTY_ONE)
            .chain(&SLICE_TWENTY_TWO)
            .chain(&I128_CONST_SHIFT)
            .chain(&I128_MULO)
        {
            let bodies: Vec<_> = proofs
                .iter()
                .filter(|cert| {
                    cert.function_name == *function && cert.rule_name == X86_BODY_OBLIGATION_NAME
                })
                .collect();
            assert!(!bodies.is_empty(), "{triple}/{function}: no body credit");
            for cert in bodies {
                assert_eq!(cert.strength, "Formal");
                let payload = cert
                    .source_bound_obligation
                    .as_ref()
                    .unwrap_or_else(|| panic!("{triple}/{function}: no exported theorem"));
                assert_eq!(
                    payload.kind(),
                    trust_cg_verify::SourceBoundObligationKind::X86Body
                );
                assert_eq!(payload.function_name(), *function);
                assert_eq!(payload.obligation().name, X86_BODY_OBLIGATION_NAME);
            }
        }
    }
}

/// Replay refused (`TCG_REFINE_SOLVER=0`): the covered rows stay unverified and
/// the proof-required compile is refused, naming the missing replay.
#[test]
fn without_a_replayed_proof_the_compile_is_refused() {
    trust_cg_codegen::env_lock::with_env_overrides(&[("TCG_REFINE_SOLVER", "0")], || {
        for triple in TRIPLES {
            match compile(triple) {
                Err(CompileError::ProofPromotionRejected { reason, .. }) => {
                    assert!(
                        reason.contains(X86_BODY_NEEDS_REPLAY),
                        "{triple}: refusal must name the missing replay: {reason}"
                    );
                    assert!(
                        !reason.contains("TCG-SOURCE-BOUND-X86-MISMATCH"),
                        "{reason}"
                    );
                }
                Err(other) => panic!("{triple}: unexpected error {other}"),
                Ok(_) => panic!("{triple}: promoted without an independently checked proof"),
            }
        }
    });
}

/// A body outside the lane keeps today's refusal on every host: its rows are
/// sampled evidence, never the body theorem's, and never unreplayed-credit.
#[test]
fn an_out_of_lane_body_keeps_its_sampled_refusal() {
    for triple in TRIPLES {
        match compile_module(triple, out_of_lane_module()) {
            Err(CompileError::ProofPromotionRejected { reason, .. }) => {
                assert!(
                    reason.contains(
                        trust_cg_verify::function_verifier::STATISTICAL_EVIDENCE_IS_NOT_CREDIT
                    ),
                    "{triple}: {reason}"
                );
                assert!(!reason.contains(X86_BODY_NEEDS_REPLAY), "{reason}");
                assert!(!reason.contains(X86_BODY_OBLIGATION_NAME), "{reason}");
            }
            Err(other) => panic!("{triple}: unexpected error {other}"),
            Ok(_) => panic!("{triple}: an out-of-lane body promoted"),
        }
    }
}

/// Admission never depends on the replayer. A 32-bit multiply is inside the
/// lane; where the admitted AY/Clean pair does not certify its theorem in a
/// compile (the qualification host, with either AY), the compile is refused
/// as needing a replayed proof, never with sampled evidence, and where a
/// replayer certifies it the rows carry the body theorem.
#[test]
fn a_body_the_replayer_may_not_certify_is_judged_only_by_its_theorem() {
    for triple in TRIPLES {
        match compile_module(triple, uncertified_module()) {
            Err(CompileError::ProofPromotionRejected { reason, .. }) => {
                assert!(reason.contains(X86_BODY_NEEDS_REPLAY), "{triple}: {reason}");
                assert!(
                    !reason.contains(
                        trust_cg_verify::function_verifier::STATISTICAL_EVIDENCE_IS_NOT_CREDIT
                    ),
                    "{triple}: {reason}"
                );
            }
            Err(other) => panic!("{triple}: unexpected error {other}"),
            Ok(result) => {
                let proofs = result.proofs.as_ref().expect("proof-required compile");
                assert!(
                    proofs.iter().any(|cert| cert.function_name == "mul_u32"
                        && cert.rule_name == X86_BODY_OBLIGATION_NAME
                        && cert.strength == "Formal"),
                    "{triple}: a promoted multiply body must carry the body theorem"
                );
            }
        }
    }
}

/// `x86-body-trace` names the actual refusal of a Win64 function: its calling
/// convention, not a missing one. The trace goes to stderr, so the test runs
/// itself in a child process and reads the child's stderr.
#[test]
fn x86_body_trace_names_a_win64_functions_convention() {
    const CHILD: &str = "TCG_X86_BODY_TRACE_WIN64_CHILD";
    const TEST: &str = "x86_body_trace_names_a_win64_functions_convention";
    if std::env::var_os(CHILD).is_some() {
        // Only the trace matters here; the compile's own outcome does not.
        let _ = compile_module("x86_64-pc-windows-msvc", win64_module());
        return;
    }
    let output = std::process::Command::new(std::env::current_exe().expect("test binary"))
        .args(["--exact", TEST, "--nocapture", "--test-threads=1"])
        .env(CHILD, "1")
        .env("TCG_X86_BODY_TRACE", "1")
        .output()
        .expect("run the child test");
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(output.status.success(), "child failed: {stderr}");
    let traced: Vec<&str> = stderr
        .lines()
        .filter(|line| line.contains("[TCG-X86-BODY-TRACE] fn=add_u32"))
        .collect();
    assert!(!traced.is_empty(), "no trace line for add_u32: {stderr}");
    for line in &traced {
        assert!(
            line.contains("calling convention WindowsX64 is outside the lane"),
            "{line}"
        );
        assert!(
            !line.contains("no calling convention was supplied"),
            "{line}"
        );
    }
}

/// The hostile review of slice 22 (ruling OD-210): `div_by_routine(a: u128,
/// b: u128) -> u128 { a / b }` (`DivNonZero`, the `I128` guard) beside the
/// module's own `__udivti3` returning 0 (`defines`), or beside a declaration
/// of it. The division calls `__udivti3`, which the module's definition
/// binds: every quotient is 0.
fn routine_module(defines: bool) -> trust_ir::Module {
    let mut builder = ModuleBuilder::new("x86_source_bound_body_e2e_routine");
    if defines {
        function(
            &mut builder,
            "__udivti3",
            vec![Ty::U128, Ty::U128],
            Ty::U128,
            |f, _| f.iconst(Ty::U128, 0),
        );
    } else {
        let signature = builder.add_func_type(vec![Ty::U128, Ty::U128], vec![Ty::U128]);
        builder.declare_function("__udivti3", signature);
    }
    function(
        &mut builder,
        if defines {
            "div_by_own_routine"
        } else {
            "div_by_declared_routine"
        },
        vec![Ty::U128, Ty::U128],
        Ty::U128,
        |f, a| {
            f.binop_proven(
                BinOp::UDiv,
                Ty::U128,
                a[0],
                a[1],
                vec![trust_ir::ProofAnnotation::DivNonZero],
            )
        },
    );
    builder.build().expect("ModuleBuilder::build: test fixture")
}

/// OD-210 through the compiler: the AOT certificate lane names the module's
/// definitions, so the body theorem of a division by the module's own
/// `__udivti3` is refused by name (`x86-body-trace`), and that of a division
/// by a declared one is built. Before OD-210 both were built (and, with the
/// replay tools, the first promoted Formal:
/// [`a_division_by_the_modules_own_routine_never_promotes`]). Solver-free:
/// the trace names the owner's refusal before any replay. The test runs
/// itself in a child process and reads the child's stderr.
#[test]
fn x86_body_trace_names_a_routine_the_module_defines() {
    const CHILD: &str = "TCG_X86_BODY_TRACE_ROUTINE_CHILD";
    const TEST: &str = "x86_body_trace_names_a_routine_the_module_defines";
    if std::env::var_os(CHILD).is_some() {
        // Only the trace matters here; the compiles' own outcomes do not.
        for defines in [true, false] {
            let _ = compile_module("x86_64-apple-darwin", routine_module(defines));
        }
        return;
    }
    let output = std::process::Command::new(std::env::current_exe().expect("test binary"))
        .args(["--exact", TEST, "--nocapture", "--test-threads=1"])
        .env(CHILD, "1")
        .env("TCG_X86_BODY_TRACE", "1")
        .env("TCG_REFINE_SOLVER", "0")
        .output()
        .expect("run the child test");
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(output.status.success(), "child failed: {stderr}");
    let traced = |function: &str| -> Vec<String> {
        stderr
            .lines()
            .filter(|line| line.contains(&format!("[TCG-X86-BODY-TRACE] fn={function} ")))
            .map(str::to_owned)
            .collect()
    };
    let own = traced("div_by_own_routine");
    assert!(
        !own.is_empty(),
        "no trace line for div_by_own_routine: {stderr}"
    );
    for line in &own {
        assert!(
            line.contains("`__udivti3`")
                && line.contains("the module under proof defines it")
                && line.contains("OD-210"),
            "{line}"
        );
    }
    let declared = traced("div_by_declared_routine");
    assert!(
        declared.iter().any(|line| line.contains("bound rows=")),
        "a division by a declared __udivti3 builds its theorem: {declared:?}\n{stderr}"
    );
    assert!(
        declared.iter().all(|line| !line.contains("OD-210")),
        "{declared:?}"
    );
}

/// OD-210 with the replay tools: a division by the module's own `__udivti3`
/// never promotes (it promoted Formal before OD-210, every quotient 0), while
/// the module's routine itself (it returns 0, no division) is credited by
/// its body theorem; a division by a declared `__udivti3` promotes.
#[test]
fn a_division_by_the_modules_own_routine_never_promotes() {
    if let Some(reason) = replay_tools_unavailable() {
        eprintln!("SKIP a_division_by_the_modules_own_routine_never_promotes: {reason}");
        return;
    }
    for triple in TRIPLES {
        match compile_module(triple, routine_module(true)) {
            Err(CompileError::ProofPromotionRejected { reason, .. }) => {
                assert!(reason.contains("div_by_own_routine"), "{triple}: {reason}");
                assert!(
                    !reason.contains("TCG-SOURCE-BOUND-X86-MISMATCH"),
                    "{reason}"
                );
            }
            Err(other) => panic!("{triple}: unexpected error {other}"),
            Ok(result) => panic!(
                "{triple}: a division by the module's own __udivti3 promoted: {:?}",
                result
                    .proofs
                    .as_deref()
                    .unwrap_or_default()
                    .iter()
                    .filter(|cert| cert.function_name == "div_by_own_routine")
                    .map(|cert| (&cert.rule_name, &cert.strength))
                    .collect::<Vec<_>>()
            ),
        }
        let result = compile_module(triple, routine_module(false))
            .unwrap_or_else(|error| panic!("{triple}: a declared __udivti3: {error}"));
        let proofs = result.proofs.as_ref().expect("proof-required compile");
        assert!(
            proofs
                .iter()
                .any(|cert| cert.function_name == "div_by_declared_routine"
                    && cert.rule_name == X86_BODY_OBLIGATION_NAME
                    && cert.strength == "Formal"),
            "{triple}: a division by a declared __udivti3 carries its body theorem"
        );
    }
}

/// `copy_bytes(dst, src, n) { ptr::copy_nonoverlapping(src, dst, n) }` (a
/// `MemCopy`, the selector's `call memcpy`), in a module that declares
/// nothing: the copy binds to whatever `memcpy` the link defines.
fn copy_module() -> trust_ir::Module {
    let mut builder = ModuleBuilder::new("x86_source_bound_body_e2e_copy");
    let copy = builder.add_func_type(vec![Ty::Ptr, Ty::Ptr, Ty::Usize], vec![]);
    let mut f = builder.function("copy_bytes", copy);
    let entry = f.create_block();
    let dst = f.add_block_param(entry, Ty::Ptr);
    let src = f.add_block_param(entry, Ty::Ptr);
    let len = f.add_block_param(entry, Ty::Usize);
    f.switch_to_block(entry);
    f.memcopy(dst, src, len, false);
    f.ret(vec![]);
    f.build();
    builder.build().expect("ModuleBuilder::build: test fixture")
}

/// OD-216 through the compiler: the module is one compile unit, and a
/// definition in a sibling unit of its link unit (for the rustc bridge,
/// another codegen unit of the crate, or another function of the same one)
/// binds its calls too. Compiled alone, a division by a declared `__udivti3`
/// and a `memcpy` copy build their theorems (as before OD-216, whatever the
/// rest of the crate defined); named in a link unit that defines the routine
/// (`CompilerConfig::link_unit_definitions`), each is refused by name, and a
/// link unit that defines another routine changes nothing. Solver-free: the
/// trace names the owner's refusal before any replay; the test runs itself
/// in a child process and reads the child's stderr.
#[test]
fn x86_body_trace_names_a_routine_the_crate_defines() {
    const CHILD: &str = "TCG_X86_BODY_TRACE_LINK_UNIT_CHILD";
    const TEST: &str = "x86_body_trace_names_a_routine_the_crate_defines";
    if let Some(case) = std::env::var_os(CHILD) {
        // Only the trace matters here; the compiles' own outcomes do not.
        let (module, link_unit): (trust_ir::Module, &[&str]) = match case.to_str().expect("case") {
            "div-alone" => (routine_module(false), &[]),
            "div-crate" => (routine_module(false), &["__udivti3", "main"]),
            "div-other" => (routine_module(false), &["__divti3", "memcpy"]),
            "copy-alone" => (copy_module(), &[]),
            "copy-crate" => (copy_module(), &["memcpy"]),
            "copy-other" => (copy_module(), &["memset", "__udivti3"]),
            other => panic!("unknown case {other}"),
        };
        let _ = compile_module_in_link_unit("x86_64-apple-darwin", module, link_unit);
        return;
    }
    let traced = |case: &str, function: &str| -> Vec<String> {
        let output = std::process::Command::new(std::env::current_exe().expect("test binary"))
            .args(["--exact", TEST, "--nocapture", "--test-threads=1"])
            .env(CHILD, case)
            .env("TCG_X86_BODY_TRACE", "1")
            .env("TCG_REFINE_SOLVER", "0")
            .output()
            .expect("run the child test");
        let stderr = String::from_utf8_lossy(&output.stderr).into_owned();
        assert!(output.status.success(), "{case}: child failed: {stderr}");
        let lines: Vec<String> = stderr
            .lines()
            .filter(|line| line.contains(&format!("[TCG-X86-BODY-TRACE] fn={function} ")))
            .map(str::to_owned)
            .collect();
        assert!(
            !lines.is_empty(),
            "{case}: no trace line for {function}: {stderr}"
        );
        lines
    };
    for (alone, crate_unit, other, function, routine) in [
        (
            "div-alone",
            "div-crate",
            "div-other",
            "div_by_declared_routine",
            "`__udivti3`",
        ),
        (
            "copy-alone",
            "copy-crate",
            "copy-other",
            "copy_bytes",
            "`memcpy`",
        ),
    ] {
        for case in [alone, other] {
            let lines = traced(case, function);
            assert!(
                lines.iter().any(|line| line.contains("bound rows=")),
                "{case}: the theorem is built: {lines:?}"
            );
            assert!(
                lines.iter().all(|line| !line.contains("OD-216")),
                "{case}: {lines:?}"
            );
        }
        for line in traced(crate_unit, function) {
            assert!(
                line.contains(routine)
                    && line.contains("another compile unit of its link unit (crate) defines it")
                    && line.contains("OD-216"),
                "{crate_unit}: {line}"
            );
        }
    }
}

/// OD-216 with the replay tools: a division by a declared `__udivti3` and a
/// `memcpy` copy promote compiled alone, and never promote in a link unit
/// that defines the routine (the rustc bridge names a crate's definitions so).
#[test]
fn a_call_of_a_routine_the_crate_defines_never_promotes() {
    if let Some(reason) = replay_tools_unavailable() {
        eprintln!("SKIP a_call_of_a_routine_the_crate_defines_never_promotes: {reason}");
        return;
    }
    for triple in TRIPLES {
        for (make, function, routine) in [
            (
                (|| routine_module(false)) as fn() -> trust_ir::Module,
                "div_by_declared_routine",
                "__udivti3",
            ),
            (
                copy_module as fn() -> trust_ir::Module,
                "copy_bytes",
                "memcpy",
            ),
        ] {
            let result = compile_module_in_link_unit(triple, make(), &[])
                .unwrap_or_else(|error| panic!("{triple} {function} alone: {error}"));
            let proofs = result.proofs.as_ref().expect("proof-required compile");
            assert!(
                proofs.iter().any(|cert| cert.function_name == function
                    && cert.rule_name == X86_BODY_OBLIGATION_NAME
                    && cert.strength == "Formal"),
                "{triple}: {function} alone carries its body theorem"
            );
            match compile_module_in_link_unit(triple, make(), &[routine]) {
                Err(CompileError::ProofPromotionRejected { reason, .. }) => {
                    assert!(reason.contains(function), "{triple}: {reason}");
                    assert!(
                        !reason.contains("TCG-SOURCE-BOUND-X86-MISMATCH"),
                        "{reason}"
                    );
                }
                Err(other) => panic!("{triple} {function}: unexpected error {other}"),
                Ok(result) => panic!(
                    "{triple}: {function} promoted in a crate defining {routine}: {:?}",
                    result
                        .proofs
                        .as_deref()
                        .unwrap_or_default()
                        .iter()
                        .filter(|cert| cert.function_name == function)
                        .map(|cert| (&cert.rule_name, &cert.strength))
                        .collect::<Vec<_>>()
                ),
            }
        }
    }
}

/// The body of `parts_div` (`(a: u128, b: u128, n: u64) -> u128`, `a / b`
/// after a loop) or `parts_move` (`(dst, src, len, n) -> u64`, a `Memmove`
/// after it), the shape of `core`'s `exp_u128` and `parse_decimal_seq`: a
/// loop whose header two edges outside it enter (the two arms of a branch on
/// `n`), then a chain of [`PARTS_CHAIN`] blocks, past the single-query bounds.
/// The owner states it in parts (a cut interface admits every edge into it),
/// while its whole-body admission refuses it (it admits one), so the AOT
/// certificate lane once routed it down the walk that named no module
/// (OD-210, amended). `defines`: the module also defines the routine the body
/// calls (`__udivti3` returning 0, or a `memmove` that moves nothing).
fn parts_module(division: bool, defines: bool) -> trust_ir::Module {
    use trust_ir::ICmpOp;
    let mut builder = ModuleBuilder::new("x86_source_bound_body_e2e_parts");
    if defines && division {
        function(
            &mut builder,
            "__udivti3",
            vec![Ty::U128, Ty::U128],
            Ty::U128,
            |f, _| f.iconst(Ty::U128, 0),
        );
    } else if defines {
        function(
            &mut builder,
            "memmove",
            vec![Ty::Ptr, Ty::Ptr, Ty::Usize],
            Ty::Ptr,
            |_, a| a[0],
        );
    }
    let (name, params, result) = if division {
        ("parts_div", vec![Ty::U128, Ty::U128, Ty::U64], Ty::U128)
    } else {
        (
            "parts_move",
            vec![Ty::Ptr, Ty::Ptr, Ty::Usize, Ty::U64],
            Ty::U64,
        )
    };
    let signature = builder.add_func_type(params.clone(), vec![result]);
    let mut f = builder.function(name, signature);
    let entry = f.create_block();
    let args: Vec<_> = params
        .into_iter()
        .map(|ty| f.add_block_param(entry, ty))
        .collect();
    let n = *args.last().expect("a trip count");
    let (left, right, header, body) = (
        f.create_block(),
        f.create_block(),
        f.create_block(),
        f.create_block(),
    );
    let i = f.add_block_param(header, Ty::U64);
    let chain: Vec<_> = (0..PARTS_CHAIN).map(|_| f.create_block()).collect();
    let last = f.create_block();
    f.switch_to_block(entry);
    let zero = f.iconst(Ty::U64, 0);
    let none = f.icmp(ICmpOp::Eq, Ty::U64, n, zero);
    f.condbr(none, left, vec![], right, vec![]);
    for (arm, start) in [(left, 0), (right, 1)] {
        f.switch_to_block(arm);
        let start = f.iconst(Ty::U64, start);
        f.br(header, vec![start]);
    }
    f.switch_to_block(header);
    let more = f.icmp(ICmpOp::Ult, Ty::U64, i, n);
    f.condbr(more, body, vec![], chain[0], vec![]);
    f.switch_to_block(body);
    let one = f.iconst(Ty::U64, 1);
    let next = f.add(Ty::U64, i, one);
    f.br(header, vec![next]);
    for (k, block) in chain.iter().enumerate() {
        f.switch_to_block(*block);
        f.br(chain.get(k + 1).copied().unwrap_or(last), vec![]);
    }
    f.switch_to_block(last);
    if division {
        let quotient = f.binop_proven(
            BinOp::UDiv,
            Ty::U128,
            args[0],
            args[1],
            vec![trust_ir::ProofAnnotation::DivNonZero],
        );
        f.ret(vec![quotient]);
    } else {
        f.memcopy(args[0], args[1], args[2], true);
        f.ret(vec![n]);
    }
    f.build();
    builder.build().expect("ModuleBuilder::build: test fixture")
}

/// The blocks after the loop of [`parts_module`]: past the 128 the single
/// query admits.
const PARTS_CHAIN: usize = 130;

/// OD-210, amended, through the compiler: the AOT certificate lane names the
/// module's definitions on both its walks, so a body it states in parts that
/// its whole-body admission refuses is judged against the module like every
/// other. Alone, `parts_div`'s division and `parts_move`'s `Memmove` build
/// their theorems, stated in parts (before, the lane's out-of-lane walk named
/// no module and refused both: "no module was named", as `core`'s `exp_u128`
/// and `parse_decimal_seq` in census-s23final); in a module that defines the
/// routine (`TheModule`) or a link unit that does (`TheLinkUnit`) each is
/// refused by name. Solver-free: the trace names the owner's outcome before
/// any replay; the test runs itself in a child process and reads its stderr.
#[test]
fn x86_body_trace_judges_a_body_stated_in_parts_against_its_module() {
    const CHILD: &str = "TCG_X86_BODY_TRACE_PARTS_CHILD";
    const TEST: &str = "x86_body_trace_judges_a_body_stated_in_parts_against_its_module";
    if let Some(case) = std::env::var_os(CHILD) {
        // Only the trace matters here; the compiles' own outcomes do not.
        let (module, link_unit): (trust_ir::Module, &[&str]) = match case.to_str().expect("case") {
            "div-alone" => (parts_module(true, false), &[]),
            "div-module" => (parts_module(true, true), &[]),
            "div-crate" => (parts_module(true, false), &["__udivti3"]),
            "move-alone" => (parts_module(false, false), &[]),
            "move-module" => (parts_module(false, true), &[]),
            "move-crate" => (parts_module(false, false), &["memmove"]),
            other => panic!("unknown case {other}"),
        };
        let _ = compile_module_in_link_unit("x86_64-apple-darwin", module, link_unit);
        return;
    }
    let traced = |case: &str, function: &str| -> Vec<String> {
        let output = std::process::Command::new(std::env::current_exe().expect("test binary"))
            .args(["--exact", TEST, "--nocapture", "--test-threads=1"])
            .env(CHILD, case)
            .env("TCG_X86_BODY_TRACE", "1")
            .env("TCG_REFINE_SOLVER", "0")
            .output()
            .expect("run the child test");
        let stderr = String::from_utf8_lossy(&output.stderr).into_owned();
        assert!(output.status.success(), "{case}: child failed: {stderr}");
        let lines: Vec<String> = stderr
            .lines()
            .filter(|line| line.contains(&format!("[TCG-X86-BODY-TRACE] fn={function} ")))
            .map(str::to_owned)
            .collect();
        assert!(
            !lines.is_empty(),
            "{case}: no trace line for {function}: {stderr}"
        );
        lines
    };
    for (prefix, function, routine) in [
        ("div", "parts_div", "`__udivti3`"),
        ("move", "parts_move", "`memmove`"),
    ] {
        let alone = traced(&format!("{prefix}-alone"), function);
        assert!(
            alone.iter().any(|line| line.contains("stated in parts="))
                && alone.iter().any(|line| line.contains("bound rows=")),
            "{prefix}-alone: the theorem is built, stated in parts: {alone:?}"
        );
        assert!(
            alone
                .iter()
                .all(|line| !line.contains("no module was named")),
            "{prefix}-alone: the lane named no module: {alone:?}"
        );
        for line in traced(&format!("{prefix}-module"), function) {
            assert!(
                line.contains(routine) && line.contains("the module under proof defines it"),
                "{prefix}-module: {line}"
            );
        }
        for line in traced(&format!("{prefix}-crate"), function) {
            assert!(
                line.contains(routine)
                    && line.contains("another compile unit of its link unit (crate) defines it"),
                "{prefix}-crate: {line}"
            );
        }
    }
}

/// OD-210, amended, with the replay tools: `parts_div` and `parts_move`
/// promote alone, every part of their theorems replayed (before, refused as
/// `Unnamed`, no credit), and never promote in a module that defines the
/// routine their bodies call.
#[test]
fn a_body_stated_in_parts_promotes_only_against_its_module() {
    if let Some(reason) = replay_tools_unavailable() {
        eprintln!("SKIP a_body_stated_in_parts_promotes_only_against_its_module: {reason}");
        return;
    }
    for triple in TRIPLES {
        for (division, function) in [(true, "parts_div"), (false, "parts_move")] {
            let result = compile_module(triple, parts_module(division, false))
                .unwrap_or_else(|error| panic!("{triple} {function} alone: {error}"));
            let proofs = result.proofs.as_ref().expect("proof-required compile");
            assert!(
                proofs.iter().any(|cert| cert.function_name == function
                    && cert.rule_name.starts_with(X86_BODY_OBLIGATION_NAME)
                    && cert.strength == "Formal"),
                "{triple}: {function} alone carries its body theorem"
            );
            match compile_module(triple, parts_module(division, true)) {
                Err(CompileError::ProofPromotionRejected { reason, .. }) => {
                    assert!(reason.contains(function), "{triple}: {reason}");
                    assert!(
                        !reason.contains("TCG-SOURCE-BOUND-X86-MISMATCH"),
                        "{reason}"
                    );
                }
                Err(other) => panic!("{triple} {function}: unexpected error {other}"),
                Ok(_) => panic!("{triple}: {function} promoted beside its module's own routine"),
            }
        }
    }
}

/// This file's fixture is hand-built and carries no codegen license
/// (`body_gate: None`), which trust-cg REFUSES by default (roadmap WS7.5,
/// decision gate DG-73). Its compile states `Permit` explicitly, so the
/// refusal asserted above is the missing replay, never the license.
fn permit_unlicensed() -> trust_cg_lower::CodegenLicensePolicy {
    trust_cg_lower::CodegenLicensePolicy::default()
        .with_unlicensed(trust_cg_lower::UnlicensedBodyPolicy::Permit)
}
