// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! Slice 12 of the x86-64 source-bound body theorem: loops. A source with
//! back edges is cut at its loop headers; each region (the blocks a run
//! reaches from a cut point before it reaches one again) is a DAG stated
//! with slice 9's machinery from its cut point's assumption, and every cut
//! edge states the cut-point relation of the header it enters: each header
//! parameter's value against the low bits of the machine register paired
//! with it, and each private byte the loop may change against the
//! machine's (`build_theorem`, `cut_edge_relation`).
//!
//! Fixtures are real: LIR from the trust-ir adapter, the machine stream from
//! the real x86-64 instruction selector (`super::select`). Every test here
//! runs without a solver (the `x86_source_bound_body::tests::slice12::`
//! library gate); the replay on AY and Clean is in `slice12_qualification`.

use super::slice5::describe;
use super::slice6::describe_lir;
use super::slice9::{dag_holds_on_samples, dag_refuted_on_samples};
use super::*;
use trust_ir::{BinOp, Constant, ICmpOp, SwitchCase};

/// Slice-12 fixture shapes: each a source with at least one loop.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum LoopShape {
    /// `let mut i = 0; while i < n { i += 1 } i`.
    CountUp,
    /// `let (mut i, mut s) = (0, 0); while i < n { s += i; i += 1 } s`: two
    /// loop-carried values.
    SumBelow,
    /// `(a, b) = (b, a + b)` `n` times, then `a`: a carried value copied from
    /// another one on the back edge.
    Fib,
    /// `(a, b) = (b, a)` `n` times, then `a - b`: a cycle of edge copies.
    Swap,
    /// `fn(n: u32, b: bool) -> bool { while n != 0 { b ^= true; n -= 1 } b }`:
    /// a 32-bit and a `bool` carried value (the clean-bool walk).
    BoolToggle,
    /// `fn(x: u8) -> u8 { let mut k = 0; while k < x { k += 3 } k }`: a
    /// narrow carried value.
    NarrowCount,
    /// `while i < n { s = g1(i) + s; i += 1 } s`: a call per iteration.
    CallEach,
    /// `fn(p: *const u64, n: u64) -> u64 { while i < n { s += p[i] } s }`:
    /// an incoming load per iteration.
    LoadSum,
    /// `fn(p: *mut u64, n: u64) { while i < n { p[i] = 3 * i } }`: an
    /// incoming store per iteration.
    StoreFill,
    /// A counter kept in a private stack slot, loaded and stored each
    /// iteration: the slot's bytes are header bytes.
    SlotCounter,
    /// `while i < n { j = 0; while j < i { s += j; j += 1 } i += 1 } s`:
    /// nested loops.
    Nested,
    /// `while i < n { if 3 * i == m { return i } i += 1 } n`: two exits.
    EarlyExit,
    /// Two loops in sequence, the second bounded by the first's result.
    TwoLoops,
    /// A sparse `match i` in the loop body (a compare chain).
    SwitchLoop,
    /// `loop { i += 2; if i >= n { break } } i`: the test at the end, the
    /// back edge and the exit both through copy blocks.
    DoWhile,
    /// `let mut it = n; while step(&mut it) { s += 1 } s + it`: a private
    /// slot whose address escapes to a call in the loop.
    EscapeLoop,
    /// `while i < n { if i >= m { panic_at(i, m) } s += i; i += 1 } s`: a
    /// trap exit in the loop.
    TrapLoop,
    /// `let b = n; while i < b { i += 1 } i`, the bound kept in a private
    /// slot the loop reads and does not write.
    SlotBound,
    /// `let mut odd = false; while i < n { take_bool(odd); odd = i & 1 != 0;
    /// i += 1 } i`: a `bool` the loop computes, carried in a register and
    /// passed to a callee each iteration (`core`'s `Big32x40::add_small`
    /// carries its `carry` so); the register is zero above the `bool` on
    /// every edge, which the header assumes (under the psABI walk too).
    BoolCarriedToCall,
    /// `let mut c = 0u8; let mut carry = false; while i < n { take_bool(carry);
    /// c = (i & 1) as u8; carry = *(&c as *const u8 as *const bool); i += 1 }
    /// i`: the carried `bool` is read back from a byte stored as `u8` (slice
    /// 13), which the selector computes as `(byte + 255) >> 8`, as
    /// `Big32x40::add_small` does with its `carry`.
    ByteBoolCarried,
}

/// The sparse case values of the switch fixture (contiguous ones make a
/// jump table, which no slice admits).
const SWITCH_CASES: [i128; 3] = [1, 9, 33];

/// Every slice-12 fixture shape.
pub(crate) const SLICE_TWELVE: [LoopShape; 20] = [
    LoopShape::CountUp,
    LoopShape::SumBelow,
    LoopShape::Fib,
    LoopShape::Swap,
    LoopShape::BoolToggle,
    LoopShape::NarrowCount,
    LoopShape::CallEach,
    LoopShape::LoadSum,
    LoopShape::StoreFill,
    LoopShape::SlotCounter,
    LoopShape::Nested,
    LoopShape::EarlyExit,
    LoopShape::TwoLoops,
    LoopShape::SwitchLoop,
    LoopShape::DoWhile,
    LoopShape::EscapeLoop,
    LoopShape::TrapLoop,
    LoopShape::SlotBound,
    LoopShape::BoolCarriedToCall,
    LoopShape::ByteBoolCarried,
];

impl LoopShape {
    pub(crate) fn name(self) -> String {
        let name = format!("{self:?}");
        let mut snake = String::from("s12_");
        for (i, c) in name.chars().enumerate() {
            if c.is_ascii_uppercase() && i > 0 {
                snake.push('_');
            }
            snake.push(c.to_ascii_lowercase());
        }
        snake
    }
}

type Builder<'a> = trust_ir_build::FunctionBuilder<'a>;
type V = trust_ir::value::ValueId;

/// `while test(i, carried) { body }` from the current block: a header with
/// parameters `(i, carried...)` from `init`, `test` computed in the header,
/// `step` the body's next parameters. Returns the header's parameters with
/// the exit block current.
fn while_loop(
    f: &mut Builder<'_>,
    tys: &[Ty],
    init: Vec<V>,
    test: &mut dyn FnMut(&mut Builder<'_>, &[V]) -> V,
    step: &mut dyn FnMut(&mut Builder<'_>, &[V]) -> Vec<V>,
) -> Vec<V> {
    let (header, body, exit) = (f.create_block(), f.create_block(), f.create_block());
    let params: Vec<V> = tys
        .iter()
        .map(|ty| f.add_block_param(header, ty.clone()))
        .collect();
    f.br(header, init);
    f.switch_to_block(header);
    let go = test(f, &params);
    f.condbr(go, body, vec![], exit, vec![]);
    f.switch_to_block(body);
    let next = step(f, &params);
    f.br(header, next);
    f.switch_to_block(exit);
    params
}

/// The LIR the trust-ir adapter produces for a slice-12 shape.
pub(crate) fn slice12_lir(shape: LoopShape) -> Function {
    use LoopShape::*;
    let mut builder = ModuleBuilder::new("x86_source_bound_body_slice12");
    let mut declare = |name: &str, params: Vec<Ty>, results: Vec<Ty>| {
        let ty = builder.add_func_type(params, results);
        builder.declare_function(name, ty)
    };
    let g1 = declare("g1", vec![Ty::U64], vec![Ty::U64]);
    let panic = declare("panic_at", vec![Ty::U64, Ty::U64], vec![]);
    let ptr = Ty::PtrMut(Box::new(Ty::U64));
    let step_fn = declare("step", vec![ptr.clone()], vec![Ty::Bool]);
    let take_bool = declare("take_bool", vec![Ty::Bool], vec![]);
    let (params, results): (Vec<Ty>, Vec<Ty>) = match shape {
        CountUp | SumBelow | Fib | CallEach | SlotCounter | DoWhile | EscapeLoop | SlotBound
        | BoolCarriedToCall | ByteBoolCarried => (vec![Ty::U64], vec![Ty::U64]),
        Swap => (vec![Ty::U64, Ty::U64, Ty::U64], vec![Ty::U64]),
        BoolToggle => (vec![Ty::U32, Ty::Bool], vec![Ty::Bool]),
        NarrowCount => (vec![Ty::U8], vec![Ty::U8]),
        LoadSum => (vec![ptr.clone(), Ty::U64], vec![Ty::U64]),
        StoreFill => (vec![ptr.clone(), Ty::U64], vec![]),
        Nested | EarlyExit | TwoLoops | SwitchLoop | TrapLoop => {
            (vec![Ty::U64, Ty::U64], vec![Ty::U64])
        }
    };
    let signature = builder.add_func_type(params.clone(), results.clone());
    let mut f = builder.function(shape.name(), signature);
    let entry = f.create_block();
    let args: Vec<V> = params
        .iter()
        .map(|ty| f.add_block_param(entry, ty.clone()))
        .collect();
    f.switch_to_block(entry);
    let u64s = |n: usize| vec![Ty::U64; n];
    match shape {
        CountUp => {
            let zero = f.iconst(Ty::U64, 0);
            let n = args[0];
            let out = while_loop(
                &mut f,
                &u64s(1),
                vec![zero],
                &mut |f, p| f.icmp(ICmpOp::Ult, Ty::U64, p[0], n),
                &mut |f, p| {
                    let one = f.iconst(Ty::U64, 1);
                    vec![f.add(Ty::U64, p[0], one)]
                },
            );
            f.ret(vec![out[0]]);
        }
        SumBelow => {
            let zero = f.iconst(Ty::U64, 0);
            let n = args[0];
            let out = while_loop(
                &mut f,
                &u64s(2),
                vec![zero, zero],
                &mut |f, p| f.icmp(ICmpOp::Ult, Ty::U64, p[0], n),
                &mut |f, p| {
                    let one = f.iconst(Ty::U64, 1);
                    let s = f.add(Ty::U64, p[1], p[0]);
                    vec![f.add(Ty::U64, p[0], one), s]
                },
            );
            f.ret(vec![out[1]]);
        }
        Fib => {
            let (zero, one) = (f.iconst(Ty::U64, 0), f.iconst(Ty::U64, 1));
            let n = args[0];
            let out = while_loop(
                &mut f,
                &u64s(3),
                vec![zero, zero, one],
                &mut |f, p| f.icmp(ICmpOp::Ult, Ty::U64, p[0], n),
                &mut |f, p| {
                    let one = f.iconst(Ty::U64, 1);
                    let sum = f.add(Ty::U64, p[1], p[2]);
                    vec![f.add(Ty::U64, p[0], one), p[2], sum]
                },
            );
            f.ret(vec![out[1]]);
        }
        Swap => {
            let zero = f.iconst(Ty::U64, 0);
            let n = args[2];
            let out = while_loop(
                &mut f,
                &u64s(3),
                vec![zero, args[0], args[1]],
                &mut |f, p| f.icmp(ICmpOp::Ult, Ty::U64, p[0], n),
                &mut |f, p| {
                    let one = f.iconst(Ty::U64, 1);
                    vec![f.add(Ty::U64, p[0], one), p[2], p[1]]
                },
            );
            let difference = f.sub(Ty::U64, out[1], out[2]);
            f.ret(vec![difference]);
        }
        BoolToggle => {
            let out = while_loop(
                &mut f,
                &[Ty::U32, Ty::Bool],
                vec![args[0], args[1]],
                &mut |f, p| {
                    let zero = f.iconst(Ty::U32, 0);
                    f.icmp(ICmpOp::Ne, Ty::U32, p[0], zero)
                },
                &mut |f, p| {
                    let one = f.iconst(Ty::U32, 1);
                    let yes = f.bool_const(true);
                    let flipped = f.binop(BinOp::Xor, Ty::Bool, p[1], yes);
                    vec![f.sub(Ty::U32, p[0], one), flipped]
                },
            );
            f.ret(vec![out[1]]);
        }
        NarrowCount => {
            let zero = f.iconst(Ty::U8, 0);
            let x = args[0];
            let out = while_loop(
                &mut f,
                &[Ty::U8],
                vec![zero],
                &mut |f, p| f.icmp(ICmpOp::Ult, Ty::U8, p[0], x),
                &mut |f, p| {
                    let three = f.iconst(Ty::U8, 3);
                    vec![f.add(Ty::U8, p[0], three)]
                },
            );
            f.ret(vec![out[0]]);
        }
        CallEach => {
            let zero = f.iconst(Ty::U64, 0);
            let n = args[0];
            let out = while_loop(
                &mut f,
                &u64s(2),
                vec![zero, zero],
                &mut |f, p| f.icmp(ICmpOp::Ult, Ty::U64, p[0], n),
                &mut |f, p| {
                    let one = f.iconst(Ty::U64, 1);
                    let y = f.call(g1, vec![p[0]]);
                    let s = f.add(Ty::U64, y, p[1]);
                    vec![f.add(Ty::U64, p[0], one), s]
                },
            );
            f.ret(vec![out[1]]);
        }
        LoadSum | StoreFill => {
            let zero = f.iconst(Ty::U64, 0);
            let (p, n) = (args[0], args[1]);
            let out = while_loop(
                &mut f,
                &u64s(2),
                vec![zero, zero],
                &mut |f, c| f.icmp(ICmpOp::Ult, Ty::U64, c[0], n),
                &mut |f, c| {
                    let one = f.iconst(Ty::U64, 1);
                    let at = f.gep(Ty::U64, p, vec![c[0]]);
                    let s = if shape == LoadSum {
                        let x = f.load(Ty::U64, at);
                        f.add(Ty::U64, c[1], x)
                    } else {
                        let three = f.iconst(Ty::U64, 3);
                        let value = f.mul(Ty::U64, c[0], three);
                        f.store(Ty::U64, at, value);
                        c[1]
                    };
                    vec![f.add(Ty::U64, c[0], one), s]
                },
            );
            if shape == LoadSum {
                f.ret(vec![out[1]]);
            } else {
                f.ret(vec![]);
            }
        }
        SlotCounter => {
            let n = args[0];
            let counter = f.alloca(Ty::U64);
            let zero = f.iconst(Ty::U64, 0);
            f.store(Ty::U64, counter, zero);
            let (header, body, exit) = (f.create_block(), f.create_block(), f.create_block());
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
        }
        Nested => {
            let zero = f.iconst(Ty::U64, 0);
            let n = args[0];
            let out = while_loop(
                &mut f,
                &u64s(2),
                vec![zero, zero],
                &mut |f, p| f.icmp(ICmpOp::Ult, Ty::U64, p[0], n),
                &mut |f, p| {
                    let zero = f.iconst(Ty::U64, 0);
                    let i = p[0];
                    let inner = while_loop(
                        f,
                        &u64s(2),
                        vec![zero, p[1]],
                        &mut |f, q| f.icmp(ICmpOp::Ult, Ty::U64, q[0], i),
                        &mut |f, q| {
                            let one = f.iconst(Ty::U64, 1);
                            let s = f.add(Ty::U64, q[1], q[0]);
                            vec![f.add(Ty::U64, q[0], one), s]
                        },
                    );
                    let one = f.iconst(Ty::U64, 1);
                    vec![f.add(Ty::U64, i, one), inner[1]]
                },
            );
            f.ret(vec![out[1]]);
        }
        EarlyExit => {
            let zero = f.iconst(Ty::U64, 0);
            let (n, m) = (args[0], args[1]);
            let (header, body, found, next, exit) = (
                f.create_block(),
                f.create_block(),
                f.create_block(),
                f.create_block(),
                f.create_block(),
            );
            let i = f.add_block_param(header, Ty::U64);
            f.br(header, vec![zero]);
            f.switch_to_block(header);
            let go = f.icmp(ICmpOp::Ult, Ty::U64, i, n);
            f.condbr(go, body, vec![], exit, vec![]);
            f.switch_to_block(body);
            let three = f.iconst(Ty::U64, 3);
            let triple = f.mul(Ty::U64, i, three);
            let hit = f.icmp(ICmpOp::Eq, Ty::U64, triple, m);
            f.condbr(hit, found, vec![], next, vec![]);
            f.switch_to_block(found);
            f.ret(vec![i]);
            f.switch_to_block(next);
            let one = f.iconst(Ty::U64, 1);
            let i1 = f.add(Ty::U64, i, one);
            f.br(header, vec![i1]);
            f.switch_to_block(exit);
            f.ret(vec![n]);
        }
        TwoLoops => {
            let zero = f.iconst(Ty::U64, 0);
            let n = args[0];
            let first = while_loop(
                &mut f,
                &u64s(1),
                vec![zero],
                &mut |f, p| f.icmp(ICmpOp::Ult, Ty::U64, p[0], n),
                &mut |f, p| {
                    let one = f.iconst(Ty::U64, 1);
                    vec![f.add(Ty::U64, p[0], one)]
                },
            );
            let bound = f.add(Ty::U64, first[0], args[1]);
            let zero = f.iconst(Ty::U64, 0);
            let second = while_loop(
                &mut f,
                &u64s(1),
                vec![zero],
                &mut |f, p| f.icmp(ICmpOp::Ult, Ty::U64, p[0], bound),
                &mut |f, p| {
                    let three = f.iconst(Ty::U64, 3);
                    vec![f.add(Ty::U64, p[0], three)]
                },
            );
            f.ret(vec![second[0]]);
        }
        SwitchLoop => {
            let zero = f.iconst(Ty::U64, 0);
            let n = args[0];
            let x = args[1];
            let out = while_loop(
                &mut f,
                &u64s(2),
                vec![zero, zero],
                &mut |f, p| f.icmp(ICmpOp::Ult, Ty::U64, p[0], n),
                &mut |f, p| {
                    let arms: Vec<_> = (0..SWITCH_CASES.len()).map(|_| f.create_block()).collect();
                    let (default, join) = (f.create_block(), f.create_block());
                    let s = f.add_block_param(join, Ty::U64);
                    let selector = f.add(Ty::U64, x, p[0]);
                    f.switch(
                        selector,
                        arms.iter()
                            .enumerate()
                            .map(|(k, target)| SwitchCase {
                                value: Constant::Int(SWITCH_CASES[k]),
                                target: *target,
                                args: vec![],
                            })
                            .collect(),
                        default,
                        vec![],
                    );
                    for (k, arm) in arms.iter().enumerate() {
                        f.switch_to_block(*arm);
                        let k = f.iconst(Ty::U64, 3 * k as i128 + 1);
                        let value = f.add(Ty::U64, p[1], k);
                        f.br(join, vec![value]);
                    }
                    f.switch_to_block(default);
                    let five = f.iconst(Ty::U64, 5);
                    let value = f.binop(BinOp::Xor, Ty::U64, p[1], five);
                    f.br(join, vec![value]);
                    f.switch_to_block(join);
                    let one = f.iconst(Ty::U64, 1);
                    vec![f.add(Ty::U64, p[0], one), s]
                },
            );
            f.ret(vec![out[1]]);
        }
        DoWhile => {
            let zero = f.iconst(Ty::U64, 0);
            let n = args[0];
            let (header, exit) = (f.create_block(), f.create_block());
            let i = f.add_block_param(header, Ty::U64);
            let out = f.add_block_param(exit, Ty::U64);
            f.br(header, vec![zero]);
            f.switch_to_block(header);
            let two = f.iconst(Ty::U64, 2);
            let next = f.add(Ty::U64, i, two);
            let again = f.icmp(ICmpOp::Ult, Ty::U64, next, n);
            f.condbr(again, header, vec![next], exit, vec![next]);
            f.switch_to_block(exit);
            f.ret(vec![out]);
        }
        EscapeLoop => {
            let it = f.alloca(Ty::U64);
            f.store(Ty::U64, it, args[0]);
            let zero = f.iconst(Ty::U64, 0);
            let out = while_loop(
                &mut f,
                &u64s(1),
                vec![zero],
                &mut |f, _| f.call(step_fn, vec![it]),
                &mut |f, p| {
                    let one = f.iconst(Ty::U64, 1);
                    vec![f.add(Ty::U64, p[0], one)]
                },
            );
            let left = f.load(Ty::U64, it);
            let total = f.add(Ty::U64, out[0], left);
            f.ret(vec![total]);
        }
        SlotBound => {
            let bound = f.alloca(Ty::U64);
            f.store(Ty::U64, bound, args[0]);
            let zero = f.iconst(Ty::U64, 0);
            let out = while_loop(
                &mut f,
                &u64s(1),
                vec![zero],
                &mut |f, p| {
                    let limit = f.load(Ty::U64, bound);
                    f.icmp(ICmpOp::Ult, Ty::U64, p[0], limit)
                },
                &mut |f, p| {
                    let one = f.iconst(Ty::U64, 1);
                    vec![f.add(Ty::U64, p[0], one)]
                },
            );
            f.ret(vec![out[0]]);
        }
        BoolCarriedToCall => {
            let zero = f.iconst(Ty::U64, 0);
            let no = f.bool_const(false);
            let n = args[0];
            let out = while_loop(
                &mut f,
                &[Ty::U64, Ty::Bool],
                vec![zero, no],
                &mut |f, p| f.icmp(ICmpOp::Ult, Ty::U64, p[0], n),
                &mut |f, p| {
                    f.call_void(take_bool, vec![p[1]]);
                    let one = f.iconst(Ty::U64, 1);
                    let low = f.binop(BinOp::And, Ty::U64, p[0], one);
                    let zero = f.iconst(Ty::U64, 0);
                    let odd = f.icmp(ICmpOp::Ne, Ty::U64, low, zero);
                    vec![f.add(Ty::U64, p[0], one), odd]
                },
            );
            f.ret(vec![out[0]]);
        }
        ByteBoolCarried => {
            let byte = f.alloca(Ty::U8);
            let zero = f.iconst(Ty::U64, 0);
            let no = f.bool_const(false);
            let n = args[0];
            let out = while_loop(
                &mut f,
                &[Ty::U64, Ty::Bool],
                vec![zero, no],
                &mut |f, p| f.icmp(ICmpOp::Ult, Ty::U64, p[0], n),
                &mut |f, p| {
                    f.call_void(take_bool, vec![p[1]]);
                    let one = f.iconst(Ty::U64, 1);
                    let low = f.binop(BinOp::And, Ty::U64, p[0], one);
                    let narrow = f.trunc(Ty::U64, Ty::U8, low);
                    f.store(Ty::U8, byte, narrow);
                    let carry = f.load(Ty::Bool, byte);
                    vec![f.add(Ty::U64, p[0], one), carry]
                },
            );
            f.ret(vec![out[0]]);
        }
        TrapLoop => {
            let zero = f.iconst(Ty::U64, 0);
            let (n, m) = (args[0], args[1]);
            let out = while_loop(
                &mut f,
                &u64s(2),
                vec![zero, zero],
                &mut |f, p| f.icmp(ICmpOp::Ult, Ty::U64, p[0], n),
                &mut |f, p| {
                    let (fail, ok) = (f.create_block(), f.create_block());
                    let out = f.icmp(ICmpOp::Uge, Ty::U64, p[0], m);
                    f.condbr(out, fail, vec![], ok, vec![]);
                    f.switch_to_block(fail);
                    f.call_void(panic, vec![p[0], m]);
                    f.unreachable();
                    f.switch_to_block(ok);
                    let one = f.iconst(Ty::U64, 1);
                    let s = f.add(Ty::U64, p[1], p[0]);
                    vec![f.add(Ty::U64, p[0], one), s]
                },
            );
            f.ret(vec![out[1]]);
        }
    }
    f.build();
    let module = builder.build().expect("ModuleBuilder::build: test fixture");
    trust_cg_lower::translate_module_for_arch_with_tls_with_license(
        &module,
        trust_cg_lower::GuardCarrierArch::X86_64,
        trust_cg_lower::TlsDialect::default(),
        &crate::license_test_support::permit_unlicensed(),
    )
    .unwrap_or_else(|error| panic!("{shape:?}: fixture translates: {error:?}"))
    .into_iter()
    .map(|(function, _)| function)
    .find(|function| function.name == shape.name())
    .unwrap_or_else(|| panic!("{shape:?}: no translated function"))
}

/// Two blocks that branch to each other, both entered from the entry block:
/// an irreducible cycle (neither block dominates the other), which slice 12
/// leaves outside the lane by name.
pub(crate) fn irreducible_loop() -> Function {
    let mut builder = ModuleBuilder::new("x86_source_bound_body_slice12");
    let signature = builder.add_func_type(vec![Ty::U64, Ty::U64], vec![Ty::U64]);
    let mut f = builder.function("s12_irreducible", signature);
    let entry = f.create_block();
    let x = f.add_block_param(entry, Ty::U64);
    let n = f.add_block_param(entry, Ty::U64);
    let (a, b, exit) = (f.create_block(), f.create_block(), f.create_block());
    let pa = f.add_block_param(a, Ty::U64);
    let pb = f.add_block_param(b, Ty::U64);
    let result = f.add_block_param(exit, Ty::U64);
    f.switch_to_block(entry);
    let zero = f.iconst(Ty::U64, 0);
    let nonzero = f.icmp(ICmpOp::Ne, Ty::U64, x, zero);
    f.condbr(nonzero, a, vec![x], b, vec![x]);
    f.switch_to_block(a);
    let one = f.iconst(Ty::U64, 1);
    let a1 = f.add(Ty::U64, pa, one);
    let more = f.icmp(ICmpOp::Ult, Ty::U64, a1, n);
    f.condbr(more, b, vec![a1], exit, vec![a1]);
    f.switch_to_block(b);
    let two = f.iconst(Ty::U64, 2);
    let b1 = f.add(Ty::U64, pb, two);
    let more = f.icmp(ICmpOp::Ult, Ty::U64, b1, n);
    f.condbr(more, a, vec![b1], exit, vec![b1]);
    f.switch_to_block(exit);
    f.ret(vec![result]);
    f.build();
    trust_cg_lower::translate_module_for_arch_with_tls_with_license(
        &builder.build().expect("ModuleBuilder::build: test fixture"),
        trust_cg_lower::GuardCarrierArch::X86_64,
        trust_cg_lower::TlsDialect::default(),
        &crate::license_test_support::permit_unlicensed(),
    )
    .unwrap()
    .remove(0)
    .0
}

/// `let it = n; let mut q = p; while step(&mut it) { q = next(q) } *q`: a
/// loop-carried pointer a call returns once a slot escaped, which may then
/// point into the slot (slice 7's retention rule): the load through it after
/// the loop is outside the lane.
pub(crate) fn tainted_carry() -> Function {
    let mut builder = ModuleBuilder::new("x86_source_bound_body_slice12");
    let ptr = Ty::PtrMut(Box::new(Ty::U64));
    let step_ty = builder.add_func_type(vec![ptr.clone()], vec![Ty::Bool]);
    let step_fn = builder.declare_function("step", step_ty);
    let next_ty = builder.add_func_type(vec![ptr.clone()], vec![ptr.clone()]);
    let next_fn = builder.declare_function("next", next_ty);
    let signature = builder.add_func_type(vec![Ty::U64, ptr.clone()], vec![Ty::U64]);
    let mut f = builder.function("s12_tainted_carry", signature);
    let entry = f.create_block();
    let n = f.add_block_param(entry, Ty::U64);
    let p = f.add_block_param(entry, ptr.clone());
    f.switch_to_block(entry);
    let it = f.alloca(Ty::U64);
    f.store(Ty::U64, it, n);
    let out = while_loop(
        &mut f,
        &[ptr],
        vec![p],
        &mut |f, _| f.call(step_fn, vec![it]),
        &mut |f, q| vec![f.call(next_fn, vec![q[0]])],
    );
    let value = f.load(Ty::U64, out[0]);
    f.ret(vec![value]);
    f.build();
    trust_cg_lower::translate_module_for_arch_with_tls_with_license(
        &builder.build().expect("ModuleBuilder::build: test fixture"),
        trust_cg_lower::GuardCarrierArch::X86_64,
        trust_cg_lower::TlsDialect::default(),
        &crate::license_test_support::permit_unlicensed(),
    )
    .unwrap()
    .into_iter()
    .map(|(function, _)| function)
    .find(|function| function.name == "s12_tainted_carry")
    .unwrap()
}

/// `fn(n) -> u64 { let a = n; let b = 0; let mut c = &a; for _ in 0..n { c =
/// &b } *c }`: the loop stores another private address into the slot `c`
/// (slice 13's stored addresses), so the header would assume `c`'s bytes.
pub(crate) fn address_reassigned_in_loop() -> Function {
    let mut builder = ModuleBuilder::new("x86_source_bound_body_slice12");
    let ptr = Ty::PtrMut(Box::new(Ty::U64));
    let signature = builder.add_func_type(vec![Ty::U64], vec![Ty::U64]);
    let mut f = builder.function("s12_address_reassigned", signature);
    let entry = f.create_block();
    let n = f.add_block_param(entry, Ty::U64);
    f.switch_to_block(entry);
    let a = f.alloca(Ty::U64);
    f.store(Ty::U64, a, n);
    let b = f.alloca(Ty::U64);
    let zero = f.iconst(Ty::U64, 0);
    f.store(Ty::U64, b, zero);
    let c = f.alloca(ptr.clone());
    f.store(ptr.clone(), c, a);
    while_loop(
        &mut f,
        &[Ty::U64],
        vec![zero],
        &mut |f, i| f.icmp(ICmpOp::Ult, Ty::U64, i[0], n),
        &mut |f, i| {
            f.store(ptr.clone(), c, b);
            let one = f.iconst(Ty::U64, 1);
            vec![f.add(Ty::U64, i[0], one)]
        },
    );
    let p = f.load(ptr.clone(), c);
    let value = f.load(Ty::U64, p);
    f.ret(vec![value]);
    f.build();
    trust_cg_lower::translate_module_for_arch_with_tls_with_license(
        &builder.build().expect("ModuleBuilder::build: test fixture"),
        trust_cg_lower::GuardCarrierArch::X86_64,
        trust_cg_lower::TlsDialect::default(),
        &crate::license_test_support::permit_unlicensed(),
    )
    .unwrap()
    .into_iter()
    .map(|(function, _)| function)
    .find(|function| function.name == "s12_address_reassigned")
    .unwrap()
}

pub(crate) fn slice12_pair(shape: LoopShape) -> (Function, X86ISelFunction) {
    let source = slice12_lir(shape);
    let machine = select(&source, X86CallAbi::SystemV);
    (source, machine)
}

#[track_caller]
pub(crate) fn owner(source: &Function, machine: &X86ISelFunction, what: &str) -> ProofObligation {
    source_bound_x86_body(source, machine, SYSV)
        .unwrap_or_else(|refusal| {
            panic!(
                "{what}: {refusal}\n{}{}",
                describe_lir(source),
                describe(machine)
            )
        })
        .obligation()
        .clone()
}

/// Every slice-12 shape is a source with a loop, stated over its regions,
/// and its theorem holds on samples.
#[test]
fn owner_builds_every_slice_twelve_shape_over_its_regions() {
    for shape in SLICE_TWELVE {
        let (source, machine) = slice12_pair(shape);
        let cfg = source_cfg(&source).expect("an admitted control flow");
        assert!(!cfg.loops.is_empty(), "{shape:?}: has a loop");
        let obligation = owner(&source, &machine, &format!("{shape:?}"));
        assert!(
            dag_holds_on_samples(&obligation),
            "{shape:?}: the theorem of the selector's stream holds\n{}{}",
            describe_lir(&source),
            describe(&machine)
        );
    }
}

// ---------------------------------------------------------------------------
// Wrong lowerings (no solver)
// ---------------------------------------------------------------------------

/// The walk ordinals of the rows of the machine block that lowers LIR block
/// `lir` (its rows' TV-1 stamps).
fn rows_of(machine: &X86ISelFunction, lir: u32) -> Vec<usize> {
    rows(machine)
        .into_iter()
        .filter(|(_, block, _)| {
            machine.blocks[block]
                .insts
                .iter()
                .filter_map(|inst| inst.lowering_provenance.source_id())
                .any(|id| id.block == lir)
        })
        .map(|(ordinal, _, _)| ordinal)
        .collect()
}

/// The walk ordinal of the `n`-th row of `opcode` in the machine block that
/// lowers LIR block `lir` (counted from the end when negative).
pub(crate) fn row_of(machine: &X86ISelFunction, lir: u32, opcode: X86Opcode, n: isize) -> usize {
    let found: Vec<usize> = rows_of(machine, lir)
        .into_iter()
        .filter(|ordinal| inst(machine, *ordinal).opcode == opcode)
        .collect();
    let index = if n < 0 {
        found.len().checked_sub(n.unsigned_abs())
    } else {
        Some(n.unsigned_abs())
    };
    index
        .and_then(|index| found.get(index).copied())
        .unwrap_or_else(|| {
            panic!(
                "no {opcode:?} #{n} lowering block {lir}\n{}",
                describe(machine)
            )
        })
}

/// A 64-bit virtual register.
fn vreg64(id: u32) -> O {
    O::VReg(trust_cg_ir::regs::VReg::new(id, RegClass::Gpr64))
}

/// The virtual register id at operand `index` of row `ordinal`.
fn vreg_id(machine: &X86ISelFunction, ordinal: usize, index: usize) -> u32 {
    match &inst(machine, ordinal).operands[index] {
        O::VReg(vreg) => vreg.id,
        other => panic!("row {ordinal} operand {index} is {other:?}"),
    }
}

/// Wrong lowerings of slice-12 shapes, each never credited: a wrong
/// increment, an exit taken on the wrong condition, an off-by-one bound (an
/// extra iteration), a missing first iteration, loop-carried registers
/// swapped on the back edge, a counter the latch does not advance, a stale
/// value carried, a cycle of copies run in place, a wrong call argument, the
/// next element loaded, a slot counter advanced by the wrong step, an `or`
/// for an `xor` of a carried `bool`, an inner loop started wrong, a value
/// the inner loop does not carry in, an early exit returning the wrong
/// value, a back edge carrying the old value, a second loop's wrong step, an
/// inverted bounds check, a narrow counter's wrong step, and a slot read
/// after the loop as its value before it.
pub(crate) fn slice_twelve_refutations() -> Vec<(&'static str, Function, X86ISelFunction)> {
    use LoopShape::*;
    use X86Opcode as X;
    use trust_cg_ir::X86CondCode as C;
    let mut cases = Vec::new();
    let mut case =
        |label: &'static str, shape: LoopShape, mutate: &dyn Fn(&mut X86ISelFunction)| {
            let (source, mut machine) = slice12_pair(shape);
            mutate(&mut machine);
            cases.push((label, source, machine));
        };
    case("a wrong increment", CountUp, &|m| {
        let row = row_of(m, 2, X::MovRI, 0);
        inst_mut(m, row).operands[1] = O::Imm(2);
    });
    case("the exit taken on the wrong condition", CountUp, &|m| {
        let row = row_of(m, 1, X::Jcc, 0);
        inst_mut(m, row).operands[0] = O::CondCode(C::E);
    });
    case("an off-by-one bound (an extra iteration)", CountUp, &|m| {
        let row = row_of(m, 1, X::Setcc, 0);
        inst_mut(m, row).operands[1] = O::CondCode(C::BE);
    });
    case("a missing first iteration", CountUp, &|m| {
        let row = row_of(m, 0, X::MovRI, 0);
        inst_mut(m, row).operands[1] = O::Imm(1);
    });
    case(
        "loop-carried registers swapped on the back edge",
        SumBelow,
        &|m| {
            let (a, b) = (row_of(m, 2, X::MovRR, -2), row_of(m, 2, X::MovRR, -1));
            let (da, db) = (
                inst(m, a).operands[0].clone(),
                inst(m, b).operands[0].clone(),
            );
            inst_mut(m, a).operands[0] = db;
            inst_mut(m, b).operands[0] = da;
        },
    );
    case("a counter the latch does not advance", SumBelow, &|m| {
        let row = row_of(m, 2, X::MovRR, -2);
        let destination = inst(m, row).operands[0].clone();
        inst_mut(m, row).operands[1] = destination;
    });
    case("a stale value carried", Fib, &|m| {
        let (stale, sum) = (row_of(m, 2, X::MovRR, -2), row_of(m, 2, X::MovRR, -1));
        let source = inst(m, sum).operands[1].clone();
        inst_mut(m, stale).operands[1] = source;
    });
    case("a cycle of copies run in place", Swap, &|m| {
        let (first, last) = (row_of(m, 2, X::MovRR, -2), row_of(m, 2, X::MovRR, -1));
        let overwritten = inst(m, first).operands[0].clone();
        inst_mut(m, last).operands[1] = overwritten;
    });
    case("a wrong call argument", CallEach, &|m| {
        let setup = row_of(m, 2, X::MovRR, 0);
        let sum = row_of(m, 2, X::MovRR, -1);
        let carried = inst(m, sum).operands[0].clone();
        inst_mut(m, setup).operands[1] = carried;
    });
    case("the next element loaded", LoadSum, &|m| {
        let row = row_of(m, 2, X::MovRM, 0);
        if let O::MemAddr { disp, .. } = &mut inst_mut(m, row).operands[1] {
            *disp = 8;
        }
    });
    case(
        "a slot counter advanced by the wrong step",
        SlotCounter,
        &|m| {
            let row = row_of(m, 2, X::MovRI, 0);
            inst_mut(m, row).operands[1] = O::Imm(1);
        },
    );
    case("an or for the xor of a carried bool", BoolToggle, &|m| {
        let row = row_of(m, 2, X::XorRR, 0);
        inst_mut(m, row).opcode = X::OrRR;
    });
    case("an inner loop started at one", Nested, &|m| {
        let row = row_of(m, 2, X::MovRI, 0);
        inst_mut(m, row).operands[1] = O::Imm(1);
    });
    case("a sum the inner loop does not carry in", Nested, &|m| {
        let (zero, carry) = (row_of(m, 2, X::MovRR, 0), row_of(m, 2, X::MovRR, 1));
        let restart = inst(m, zero).operands[1].clone();
        inst_mut(m, carry).operands[1] = restart;
    });
    case("an early exit returning the bound", EarlyExit, &|m| {
        let row = row_of(m, 4, X::MovRR, 0);
        let bound = vreg_id(m, row_of(m, 0, X::MovRR, 0), 0);
        inst_mut(m, row).operands[1] = vreg64(bound);
    });
    case("a back edge carrying the old value", DoWhile, &|m| {
        let row = row_of(m, 2, X::MovRR, 0);
        let destination = inst(m, row).operands[0].clone();
        inst_mut(m, row).operands[1] = destination;
    });
    case("a second loop's wrong step", TwoLoops, &|m| {
        let row = row_of(m, 5, X::MovRI, 0);
        inst_mut(m, row).operands[1] = O::Imm(4);
    });
    case("an inverted bounds check", TrapLoop, &|m| {
        let row = row_of(m, 2, X::Setcc, 0);
        inst_mut(m, row).operands[1] = O::CondCode(C::B);
    });
    case("a narrow counter's wrong step", NarrowCount, &|m| {
        let row = row_of(m, 2, X::MovRI, 0);
        inst_mut(m, row).operands[1] = O::Imm(4);
    });
    case(
        "a slot read after the loop as its value before it",
        EscapeLoop,
        &|m| {
            let row = row_of(m, 3, X::AddRR, 0);
            let stored = vreg_id(m, row_of(m, 0, X::MovRR, 0), 0);
            inst_mut(m, row).operands[2] = vreg64(stored);
        },
    );
    cases
}

/// A wrong lowering is never credited: the owner names a mismatch, makes no
/// claim, or builds a theorem the sampler refutes. Returns which.
pub(crate) fn never_credited(
    source: &Function,
    machine: &X86ISelFunction,
    what: &str,
) -> &'static str {
    match source_bound_x86_body(source, machine, SYSV) {
        Ok(owner) => {
            assert!(
                dag_refuted_on_samples(owner.obligation()),
                "{what}: a wrong lowering's theorem holds on samples\n{}",
                describe(machine)
            );
            "refuted"
        }
        Err(X86BodyRefusal::Mismatch(_)) => "mismatch",
        Err(X86BodyRefusal::Unsupported(refusal)) => {
            eprintln!("{what}: no claim: {refusal}");
            "no claim"
        }
    }
}

/// Every slice-12 refutation is refuted by its theorem: the relation the
/// cut points state (on a back edge, the entry edge or an inner loop's
/// entry) or the exit and trace items it judges.
#[test]
fn every_slice_twelve_refutation_is_refuted() {
    for (label, source, machine) in slice_twelve_refutations() {
        assert_eq!(
            never_credited(&source, &machine, label),
            "refuted",
            "{label}"
        );
    }
}

// ---------------------------------------------------------------------------
// The cut-point rules (no solver)
// ---------------------------------------------------------------------------

/// A machine register the loop writes and no header parameter pairs is not
/// assumed to hold its entry value at the header: reading it makes no
/// claim. (The latch here also overwrites the bound's register with the
/// counter, so from the second iteration on the machine compares the
/// counter with itself.)
#[test]
fn a_register_the_loop_writes_is_never_assumed_unchanged() {
    let (source, mut machine) = slice12_pair(LoopShape::CountUp);
    let copy = row_of(&machine, 2, X86Opcode::MovRR, -1);
    let bound = vreg_id(&machine, row_of(&machine, 0, X86Opcode::MovRR, 0), 0);
    let mut clobber = inst(&machine, copy).clone();
    clobber.operands[0] = vreg64(bound);
    insert_at(&mut machine, copy + 1, clobber);
    match source_bound_x86_body(&source, &machine, SYSV) {
        Err(X86BodyRefusal::Unsupported(X86BodyUnsupported::MachineRow { detail, .. })) => {
            assert!(detail.contains("paired with no loop-header"), "{detail}")
        }
        other => panic!(
            "a register the loop writes: {:?}",
            other.map(|_| ()).map_err(|e| e.to_string())
        ),
    }
}

/// A private byte the machine's loop changes and the source's does not
/// (no header byte) makes no claim: the region would otherwise assume the
/// machine's byte is still its entry value. (The latch here stores the
/// counter over the bound the source keeps in its slot.)
#[test]
fn a_private_byte_only_the_machine_changes_in_a_loop_makes_no_claim() {
    let (source, mut machine) = slice12_pair(LoopShape::SlotBound);
    let store = row_of(&machine, 0, X86Opcode::MovMR, 0);
    let copy = row_of(&machine, 2, X86Opcode::MovRR, -1);
    let mut clobber = inst(&machine, store).clone();
    clobber.operands[1] = inst(&machine, copy).operands[0].clone();
    clobber.lowering_provenance = inst(&machine, copy).lowering_provenance;
    insert_at(&mut machine, copy + 1, clobber);
    match source_bound_x86_body(&source, &machine, SYSV) {
        Err(X86BodyRefusal::Unsupported(X86BodyUnsupported::MachineFunction(detail))) => {
            assert!(detail.contains("which its LIR source does not"), "{detail}")
        }
        other => panic!(
            "a byte only the machine changes: {:?}",
            other.map(|_| ()).map_err(|e| e.to_string())
        ),
    }
}

/// A loop-carried value a call returns once a slot escaped stays tainted at
/// the header (slice 7's retention rule, carried around the loop): the load
/// through it is an access through a derived address (slice 15, OD-114),
/// which observes the escaped slot's bytes, never a plain incoming load.
#[test]
fn a_value_carried_from_after_an_escape_stays_tainted() {
    let body = admitted_body(&tainted_carry())
        .unwrap_or_else(|refusal| panic!("a tainted carried pointer: {refusal}"));
    let loops = body.loops.as_ref().expect("stated over its regions");
    let accesses: Vec<&SourceAccess> = loops
        .regions
        .iter()
        .flat_map(|region| region.dag.blocks.values())
        .flat_map(|program| program.accesses.iter())
        .collect();
    assert!(!accesses.is_empty(), "the load through the carried pointer");
    assert!(
        accesses.iter().all(|access| access.slot_reads.is_some()),
        "a load through a pointer the loop carries from after an escape observes the \
         escaped slots"
    );
}

/// A private address stored as data (slice 13) in a byte the loop changes is
/// never a free input the header assumes: as at a DAG join of different
/// bytes one of which holds an address, it is a named refusal.
#[test]
fn a_stored_address_a_loop_changes_is_a_named_refusal() {
    let source = address_reassigned_in_loop();
    match admitted_body(&source) {
        Err(X86BodyRefusal::Unsupported(X86BodyUnsupported::SourceDomain(detail))) => {
            assert!(
                detail.contains("one of them a private stack address"),
                "{detail}"
            )
        }
        other => panic!(
            "a stored address the loop changes: {:?}",
            other.map(|_| ()).map_err(|e| e.to_string())
        ),
    }
}

/// A back edge into the entry block (whose parameters are the function's)
/// and a cycle no block dominates are named refusals.
#[test]
fn an_entry_header_and_an_irreducible_cycle_are_named_refusals() {
    let mut source = slice12_lir(LoopShape::CountUp);
    let latch = source.blocks.get_mut(&Block(2)).unwrap();
    let last = latch.instructions.last_mut().unwrap();
    last.opcode = L::Jump { dest: Block(0) };
    match source_cfg(&source) {
        Err(X86BodyRefusal::Unsupported(X86BodyUnsupported::SourceShape(detail))) => {
            assert!(detail.contains("header is the entry block"), "{detail}")
        }
        other => panic!("an entry header: {:?}", other.map(|_| ()).err()),
    }
    match source_cfg(&irreducible_loop()) {
        Err(X86BodyRefusal::Unsupported(X86BodyUnsupported::SourceShape(detail))) => {
            assert!(detail.contains("an irreducible loop"), "{detail}")
        }
        other => panic!("an irreducible cycle: {:?}", other.map(|_| ()).err()),
    }
}

/// A header's free inputs (its parameters' values and, under each walk, the
/// bits a parameter's register holds above them, and its bytes) are
/// declared exactly where the theorem reads them: every header input the
/// rendered query names is declared, none is declared and unread, each
/// names a header of its source, and the fixtures together read every kind.
/// (A relation whose two sides are one term, a parameter both sides only
/// copy, is an identity the theorem drops, so a header may declare none.)
#[test]
fn every_header_input_the_theorem_reads_is_declared() {
    use std::collections::BTreeSet;
    let mut kinds = BTreeSet::new();
    // Slice 18's spelling, then the canonical one (slice 19's drops reads of
    // upper register bits no claim depends on): every header input either
    // reads is declared; the construction declares every kind.
    for groups in [normal::Groups::NONE, normal::Groups::CANONICAL] {
        for shape in SLICE_TWELVE {
            let (source, machine) = slice12_pair(shape);
            let obligation =
                with_normal_groups(groups, || owner(&source, &machine, &format!("{shape:?}")));
            let declared: BTreeSet<&str> = obligation
                .inputs
                .iter()
                .map(|(name, _)| name.as_str())
                .filter(|name| is_header_input(name))
                .collect();
            let smt2 = generate_smt2_query_raw(&obligation, &replay_config());
            let named: BTreeSet<&str> = smt2
                .split(|c: char| !c.is_ascii_alphanumeric() && c != '_')
                .filter(|token| is_header_input(token))
                .collect();
            assert_eq!(declared, named, "{shape:?}");
            let headers: BTreeSet<String> = source_cfg(&source)
                .unwrap()
                .loops
                .iter()
                .map(|lp| format!("x{}", lp.header.0))
                .collect();
            for name in declared {
                let digits = name[1..].chars().take_while(char::is_ascii_digit).count();
                assert!(headers.contains(&name[..=digits]), "{shape:?}: {name}");
                if groups == normal::Groups::NONE {
                    kinds.insert(name[1 + digits..].chars().next().unwrap());
                }
            }
        }
    }
    assert_eq!(kinds, BTreeSet::from(['b', 'c', 't', 'v']));
}

// ---------------------------------------------------------------------------
// Spelling and determinism (no solver)
// ---------------------------------------------------------------------------

const SLICE_TWELVE_SNAPSHOT_SHA256: &str =
    "18a4647c1c574879cd1e8b66dbbf6a37a4dece3a03d0c5cf5a72613cea38e26b";

/// The rendered theorem of every slice-12 fixture, pinned by digest (a
/// change of encoding is a reviewed change), and independent of the
/// function's name.
#[test]
fn slice_twelve_smt2_is_canonical_per_shape() {
    use sha2::{Digest, Sha256};
    const GOLDEN: &str =
        include_str!("../tests/fixtures/x86_source_bound_body/slice12_snapshots.smt2");
    let mut rendered = String::new();
    for shape in SLICE_TWELVE {
        let (source, machine) = slice12_pair(shape);
        let owner = source_bound_x86_body(&source, &machine, SYSV).unwrap();
        let smt2 = generate_smt2_query_raw(owner.obligation(), &replay_config());
        rendered.push_str(&format!(";;;; {shape:?}\n{smt2}\n"));
        let (mut source, mut machine) = (source.clone(), machine.clone());
        source.name = "renamed_function".into();
        machine.name = "renamed_function".into();
        let renamed = source_bound_x86_body(&source, &machine, SYSV).unwrap();
        assert_eq!(
            generate_smt2_query_raw(renamed.obligation(), &replay_config()),
            smt2
        );
    }
    if std::env::var_os("TCG_X86_BODY_SNAPSHOT_WRITE").is_some() {
        let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("tests/fixtures/x86_source_bound_body/slice12_snapshots.smt2");
        std::fs::write(&path, &rendered).unwrap();
        panic!(
            "rewrote {}; review its diff, set SLICE_TWELVE_SNAPSHOT_SHA256 to {:x} and re-run \
             without TCG_X86_BODY_SNAPSHOT_WRITE",
            path.display(),
            Sha256::digest(rendered.as_bytes())
        );
    }
    assert_eq!(
        format!("{:x}", Sha256::digest(GOLDEN.as_bytes())),
        SLICE_TWELVE_SNAPSHOT_SHA256,
        "the golden file changed without the reviewed digest pin"
    );
    assert_eq!(rendered, GOLDEN, "slice-12 snapshots drifted");
}

/// Building the same pair twice gives the same theorem (no hash-map order
/// reaches a name, a claim or a fixpoint's assumption).
#[test]
fn loop_theorems_are_deterministic() {
    for shape in SLICE_TWELVE {
        let (source, machine) = slice12_pair(shape);
        let first = owner(&source, &machine, "first");
        for _ in 0..3 {
            assert_eq!(owner(&source, &machine, "again"), first, "{shape:?}");
        }
    }
}
