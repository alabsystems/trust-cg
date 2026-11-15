// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! Slice 20 of the x86-64 source-bound body theorem: a `Switch`'s
//! binary-search blocks (OD-191), a stored private address dead at a DAG join
//! (OD-192), `I128` loop-carried values and cut items as two 64-bit halves
//! (OD-193), and three singleton rules and two bounds (OD-194).
//!
//! Fixtures are real: LIR from the trust-ir adapter (translated with an
//! explicit `Permit`), the machine stream from the real x86-64 instruction
//! selector (`super::select`). Every test here runs without a solver (the
//! `x86_source_bound_body::tests::slice20::` library gate); the replay on AY
//! and Clean is in `slice20_qualification`.

use super::slice5::describe;
use super::slice6::describe_lir;
use super::slice9::{dag_holds_on_samples, dag_refuted_on_samples};
use super::slice16::{cut_at, every_block, parts_hold, some_part_refuted};
use super::*;
use trust_cg_ir::X86CondCode;
use trust_ir::{BinOp, Constant, ICmpOp, SwitchCase, Ty};

/// Slice-20 fixture shapes: each a source one of the slice's rules admits.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Shape20 {
    /// `fn(c: u32) -> u64 { match c { 9 | 10 | 13 | 34 | 39 => 1, _ => 2 } }`:
    /// five sparse cases of one target (`char::escape_default`'s set), a
    /// binary search of three blocks (OD-191).
    SparseMatch5,
    /// `fn(c: u32) -> u64 { match c { 9 => 10, 10 => 11, 13 => 12, 34 => 13,
    /// 39 => 14, 92 => 15, 200 => 16, _ => 17 } }`: seven targets of one case
    /// each, a source the per-path encoding would state but for its search.
    SparseMatch7,
    /// `char::escape_default`'s `match c { 9 => .., 13 => .., 10 => .., 92 |
    /// 39 | 34 => .., _ => .. }`: shared targets reached by several routes
    /// through the tree (OD-180 through the search).
    SparseMatchShared,
    /// A `u8` selector (`movzx` before the tree): `match b { 1 | 7 | 20 | 33
    /// | 100 | 250 => 1, 3 => 2, _ => 0 }`.
    SparseMatchU8,
    /// A `u32` selector with cases up to `2_000_000_000` (below `2^31`): a
    /// selector with bit 31 set reaches the default through the signed
    /// `jl`.
    SparseMatchHighSelector,
    /// `fn(n: u128) -> u64 { k = 0; while n != 0 { n >>= 1; k += 1 } k }`:
    /// one `I128` loop-header parameter (OD-193).
    U128ShiftLoop,
    /// The `fmt::num` `u128` binary formatter's shape: `buf[curr] = b'0' + (n
    /// & 1)`, `n >>= 1` until `n == 0`, then `finish(&buf, curr)`: an `I128`
    /// carried beside an indexed store (slice 17). The buffer has 16 bytes,
    /// not the formatter's 128 (whose real body writes it through a derived
    /// address, a smaller theorem): with 128 indexed candidates carried
    /// around the loop the qualification AY ran out its 30 s.
    U128RadixLoop,
    /// `fn(x: u128, n: u64) -> u128 { acc = 0; while i < n { acc =
    /// acc.wrapping_add(x); i += 1 } acc }`: `add`/`adc` across the back edge.
    U128AccLoop,
    /// `fn(a: u64, b: u64) -> u128 { x = (a as u128) << 64 | b as u128;
    /// tick(a); x + 1 }`, cut at every block: an `I128` live across a cut.
    U128LiveAcrossCut,
    /// `fn(a: u64, b: u64, c: u64) -> u128 { x = if c != 0 { (a as u128) <<
    /// 64 | b } else { b as u128 }; tick(c); x }`, cut at every block: an
    /// `I128` cut parameter (a block parameter of a cut block).
    U128CutParam,
    /// `fn(e: u64) -> u8 { local = e; t: *const u64 (a slot); match e & 3 { 1
    /// | 2 => { t = &local; r = use_ref(t) } _ => r = 0 } r }`: an arm stores a
    /// local's address in a temporary and passes it to one call; the join
    /// never reads the temporary (OD-192).
    MatchArmTempAddress,
    /// `fn(x: u128, n: u32) -> u128 { x << (n & 127) }` (`u128::
    /// unchecked_shl`'s shape): the variable `I128` shift (OD-194).
    U128ShlMasked,
    /// `x >> (n & 127)` on a `u128`.
    U128LshrMasked,
    /// `x >> (n & 127)` on an `i128`.
    I128AshrMasked,
    /// `fn(a: u64) -> u64 { (v, ok) = probe(a); match a & 3 { 1 | 2 => { slot
    /// = (ok as u8) & 1; tick(v) } _ => slot = ((a >> 1) as u8) & 1 }; if
    /// *(slot as *const bool) { 1 } else { 2 } }`: a `bool` read past a join of
    /// a byte two integer stores wrote (`read_ipv6_addr`'s closure; OD-194).
    CallBoolThroughSlot,
    /// `CallBoolThroughSlot` cut at every block: the bytes are the join's
    /// cut items, read as a `bool` past the cut.
    CallBoolAcrossCut,
    /// `fn(x: f32, n: u64) -> u64 { a = g(n); b = take_f32(x); a + b }`, cut at
    /// every block: the `f32` parameter's register, whose bits above 31 an
    /// entry `movss` leaves undefined, read past a cut (OD-194).
    F32ParamAcrossCut,
    /// `fn(x: u8) -> u8` with 70 one-byte locals, local `k` holding `x + k`,
    /// and locals 0, 35 and 69 read back and summed: more than slice 4's 64
    /// slots (OD-194's total-bytes bound). (Summing all 70 is a theorem the
    /// qualification AY proves and cannot render: `proof-unrenderable`.)
    ManySlots,
    /// `fn(i: u64, x: u8) -> u8 { a: [u8; 800]; a[0] = 1; if i < 784 { a[i]
    /// = x }; a[0] }`: an indexed store with 784 candidate offsets
    /// (`dec2flt::parse_decimal_seq`'s digit array; OD-194's 1024).
    WideIndexedStore,
}

/// Every slice-20 fixture shape the owner states.
pub(crate) const SLICE_TWENTY: [Shape20; 19] = [
    Shape20::SparseMatch5,
    Shape20::SparseMatch7,
    Shape20::SparseMatchShared,
    Shape20::SparseMatchU8,
    Shape20::SparseMatchHighSelector,
    Shape20::U128ShiftLoop,
    Shape20::U128RadixLoop,
    Shape20::U128AccLoop,
    Shape20::U128LiveAcrossCut,
    Shape20::U128CutParam,
    Shape20::MatchArmTempAddress,
    Shape20::U128ShlMasked,
    Shape20::U128LshrMasked,
    Shape20::I128AshrMasked,
    Shape20::CallBoolThroughSlot,
    Shape20::CallBoolAcrossCut,
    Shape20::F32ParamAcrossCut,
    Shape20::ManySlots,
    Shape20::WideIndexedStore,
];

/// Variants of the shapes the rules must refuse (or, built without an
/// admission-only check, refute) rather than state.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Variant20 {
    /// `MatchArmTempAddress` with the temporary read back after the join:
    /// the address is live there, so slice 13's refusal stays, by name.
    MatchArmTempAddressRead,
    /// `fn(x: u128, n: u128) -> u128 { x << n }`: no mask bounds the amount
    /// below 128; the bound finder refuses it (a theorem built without the
    /// finder is refuted at an amount of 128 or more).
    UnmaskedShl,
    /// `fn(x: u128, n: u32) -> u128 { x << (n & 255) }`: a mask, but not
    /// below 128.
    WideMaskShl,
    /// `CallBoolThroughSlot` with the byte left unwritten on one path into
    /// the join: a `bool` read of a byte no store wrote stays refused.
    BoolThroughSlotUnwritten,
    /// `CallBoolThroughSlot` with a stored 2 (`(ok as u8) | 2`): the source
    /// reads `2 != 0`, the true `bool`.
    BoolThroughSlotTwo,
    /// `fn(i: u64, x: u8) -> u8 { a: [u8; 1100]; if i < 1100 { a[i] = x }
    /// a[0] }`: 1100 candidate offsets, past the lane's 1024.
    TooWideIndexedStore,
    /// A sparse switch whose case `0x8000_0000` is above `i32::MAX` (cases
    /// `9 | 10 | 13 | 34 => 1`, `0x8000_0000 => 1`, `_ => 2`): the selector
    /// keeps its compare chain; a hand-built tree over it is judged by the
    /// order of its internal `jcc`.
    SparseMatchAbove2_31,
    /// `fn(x: f32, n: u64) -> u64 { i = 0; loop { y = x; i += 1; if i >= n
    /// { break } } take_f32(y) }`, cut at every block: the `f32` copy is a
    /// machine row INSIDE the loop whose bits above 31 are a fresh
    /// undefined-bits input on every visit, so the register is no closed
    /// term at the exit's cut and its read there makes no claim.
    F32CopyInLoop,
}

/// Every slice-20 variant (printed by `print_slice_twenty_fixtures`).
pub(crate) const SLICE_TWENTY_VARIANTS: [Variant20; 8] = [
    Variant20::MatchArmTempAddressRead,
    Variant20::UnmaskedShl,
    Variant20::WideMaskShl,
    Variant20::BoolThroughSlotUnwritten,
    Variant20::BoolThroughSlotTwo,
    Variant20::TooWideIndexedStore,
    Variant20::SparseMatchAbove2_31,
    Variant20::F32CopyInLoop,
];

trait ShapeName: std::fmt::Debug {
    fn name(&self) -> String {
        let name = format!("{self:?}");
        let mut snake = String::from("s20_");
        for (i, c) in name.chars().enumerate() {
            if c.is_ascii_uppercase() && i > 0 {
                snake.push('_');
            }
            snake.push(c.to_ascii_lowercase());
        }
        snake
    }
}
impl ShapeName for Shape20 {}
impl ShapeName for Variant20 {}

type Builder<'a> = trust_ir_build::FunctionBuilder<'a>;
type V = trust_ir::value::ValueId;

/// `switch x [cases -> blocks[targets]] default blocks[arms - 1]`, each arm
/// returning the `u64` constant `10 + k`.
fn returning_switch(f: &mut Builder<'_>, x: V, cases: &[i128], targets: &[usize], arms: usize) {
    let blocks: Vec<_> = (0..arms).map(|_| f.create_block()).collect();
    f.switch(
        x,
        cases
            .iter()
            .zip(targets)
            .map(|(value, target)| SwitchCase {
                value: Constant::Int(*value),
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
}

/// `while test(params) { params = step(params) }` from the current block, a
/// header with parameters of `tys` from `init`; the exit block current, the
/// header's parameters returned.
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

/// The LIR the trust-ir adapter produces for a slice-20 shape or variant.
fn slice20_function(name: String, shape: Option<Shape20>, variant: Option<Variant20>) -> Function {
    use Shape20::*;
    use Variant20::*;
    let mut builder = ModuleBuilder::new("x86_source_bound_body_slice20");
    let array = |builder: &mut ModuleBuilder, element: Ty, count: u64| {
        let element = builder.add_type(element);
        Ty::Array(element, count)
    };
    let u8x16 = array(&mut builder, Ty::U8, 16);
    let u8x800 = array(&mut builder, Ty::U8, 800);
    let u8x1100 = array(&mut builder, Ty::U8, 1100);
    let ptr_u8 = Ty::PtrMut(Box::new(Ty::U8));
    let ptr_u64 = Ty::PtrMut(Box::new(Ty::U64));
    let mut declare = |name: &str, params: Vec<Ty>, results: Vec<Ty>| {
        let ty = builder.add_func_type(params, results);
        builder.declare_function(name, ty)
    };
    let tick = declare("tick", vec![Ty::U64], vec![]);
    let finish = declare("finish", vec![ptr_u8.clone(), Ty::U64], vec![Ty::U64]);
    let panic = declare("panic_bounds", vec![Ty::U64, Ty::U64], vec![]);
    let use_ref = declare("use_ref", vec![ptr_u64.clone()], vec![Ty::U8]);
    let probe = declare("probe", vec![Ty::U64], vec![Ty::U64, Ty::Bool]);
    let g = declare("g", vec![Ty::U64], vec![Ty::U64]);
    let take_f32 = declare("take_f32", vec![Ty::F32], vec![Ty::U64]);
    let (params, results): (Vec<Ty>, Vec<Ty>) = match (shape, variant) {
        (Some(SparseMatch5 | SparseMatch7 | SparseMatchShared | SparseMatchHighSelector), _)
        | (_, Some(SparseMatchAbove2_31)) => (vec![Ty::U32], vec![Ty::U64]),
        (Some(SparseMatchU8), _) => (vec![Ty::U8], vec![Ty::U64]),
        (Some(U128ShiftLoop), _) => (vec![Ty::U128], vec![Ty::U64]),
        (Some(U128RadixLoop), _) => (vec![Ty::U128], vec![Ty::U64]),
        (Some(U128AccLoop), _) => (vec![Ty::U128, Ty::U64], vec![Ty::U128]),
        (Some(U128LiveAcrossCut), _) => (vec![Ty::U64, Ty::U64], vec![Ty::U128]),
        (Some(U128CutParam), _) => (vec![Ty::U64, Ty::U64, Ty::U64], vec![Ty::U128]),
        (Some(MatchArmTempAddress), _) | (_, Some(MatchArmTempAddressRead)) => {
            (vec![Ty::U64], vec![Ty::U8])
        }
        (Some(U128ShlMasked | U128LshrMasked), _) | (_, Some(WideMaskShl)) => {
            (vec![Ty::U128, Ty::U32], vec![Ty::U128])
        }
        (Some(I128AshrMasked), _) => (vec![Ty::I128, Ty::U32], vec![Ty::I128]),
        (_, Some(UnmaskedShl)) => (vec![Ty::U128, Ty::U128], vec![Ty::U128]),
        (Some(CallBoolThroughSlot | CallBoolAcrossCut), _)
        | (_, Some(BoolThroughSlotUnwritten | BoolThroughSlotTwo)) => {
            (vec![Ty::U64], vec![Ty::U64])
        }
        (Some(F32ParamAcrossCut), _) | (_, Some(F32CopyInLoop)) => {
            (vec![Ty::F32, Ty::U64], vec![Ty::U64])
        }
        (Some(ManySlots), _) => (vec![Ty::U8], vec![Ty::U8]),
        (Some(WideIndexedStore), _) | (_, Some(TooWideIndexedStore)) => {
            (vec![Ty::U64, Ty::U8], vec![Ty::U8])
        }
        other => unreachable!("{other:?}"),
    };
    let signature = builder.add_func_type(params.clone(), results);
    let mut f = builder.function(name.clone(), signature);
    let entry = f.create_block();
    let args: Vec<V> = params
        .iter()
        .map(|ty| f.add_block_param(entry, ty.clone()))
        .collect();
    f.switch_to_block(entry);
    match (shape, variant) {
        (Some(SparseMatch5), _) => {
            returning_switch(&mut f, args[0], &[9, 10, 13, 34, 39], &[0; 5], 2);
        }
        (Some(SparseMatch7), _) => {
            returning_switch(
                &mut f,
                args[0],
                &[9, 10, 13, 34, 39, 92, 200],
                &[0, 1, 2, 3, 4, 5, 6],
                8,
            );
        }
        (Some(SparseMatchShared), _) => {
            returning_switch(
                &mut f,
                args[0],
                &[9, 13, 10, 92, 39, 34],
                &[0, 1, 2, 3, 3, 3],
                5,
            );
        }
        (Some(SparseMatchU8), _) => {
            returning_switch(
                &mut f,
                args[0],
                &[1, 7, 20, 33, 100, 250, 3],
                &[0, 0, 0, 0, 0, 0, 1],
                3,
            );
        }
        (Some(SparseMatchHighSelector), _) => {
            returning_switch(
                &mut f,
                args[0],
                &[5, 17, 1000, 70_000, 2_000_000_000],
                &[0, 1, 2, 3, 4],
                6,
            );
        }
        (_, Some(SparseMatchAbove2_31)) => {
            returning_switch(&mut f, args[0], &[9, 10, 13, 34, 0x8000_0000], &[0; 5], 2);
        }
        (Some(U128ShiftLoop), _) => {
            let zero = f.iconst(Ty::U64, 0);
            let out = while_loop(
                &mut f,
                &[Ty::U128, Ty::U64],
                vec![args[0], zero],
                &mut |f, p| {
                    let none = f.iconst(Ty::U128, 0);
                    f.icmp(ICmpOp::Ne, Ty::U128, p[0], none)
                },
                &mut |f, p| {
                    let one = f.iconst(Ty::U128, 1);
                    let next = f.binop(BinOp::LShr, Ty::U128, p[0], one);
                    let step = f.iconst(Ty::U64, 1);
                    let k = f.add(Ty::U64, p[1], step);
                    vec![next, k]
                },
            );
            f.ret(vec![out[1]]);
        }
        (Some(U128RadixLoop), _) => {
            // buf: [u8; 16]; curr = 16; loop { curr -= 1; buf[curr] = b'0' +
            // (n & 1); n >>= 1; if n == 0 break } finish(&buf, curr).
            let buf = f.alloca(u8x16.clone());
            let start = f.iconst(Ty::U64, 16);
            let (header, store, fail, exit) = (
                f.create_block(),
                f.create_block(),
                f.create_block(),
                f.create_block(),
            );
            let n = f.add_block_param(header, Ty::U128);
            let curr = f.add_block_param(header, Ty::U64);
            f.br(header, vec![args[0], start]);
            f.switch_to_block(header);
            let one = f.iconst(Ty::U64, 1);
            let next = f.sub(Ty::U64, curr, one);
            let limit = f.iconst(Ty::U64, 16);
            let inside = f.icmp(ICmpOp::Ult, Ty::U64, next, limit);
            f.condbr(inside, store, vec![], fail, vec![]);
            f.switch_to_block(fail);
            f.call_void(panic, vec![next, limit]);
            f.unreachable();
            f.switch_to_block(store);
            let one128 = f.iconst(Ty::U128, 1);
            let bit = f.binop(BinOp::And, Ty::U128, n, one128);
            let bit = f.trunc(Ty::U128, Ty::U8, bit);
            let zero_char = f.iconst(Ty::U8, 0x30);
            let digit = f.add(Ty::U8, bit, zero_char);
            let at = f.gep(Ty::U8, buf, vec![next]);
            f.store(Ty::U8, at, digit);
            let shifted = f.binop(BinOp::LShr, Ty::U128, n, one128);
            let none = f.iconst(Ty::U128, 0);
            let done = f.icmp(ICmpOp::Eq, Ty::U128, shifted, none);
            f.condbr(done, exit, vec![], header, vec![shifted, next]);
            f.switch_to_block(exit);
            let out = f.call(finish, vec![buf, next]);
            f.ret(vec![out]);
        }
        (Some(U128AccLoop), _) => {
            let acc0 = f.iconst(Ty::U128, 0);
            let i0 = f.iconst(Ty::U64, 0);
            let x = args[0];
            let n = args[1];
            let out = while_loop(
                &mut f,
                &[Ty::U128, Ty::U64],
                vec![acc0, i0],
                &mut |f, p| f.icmp(ICmpOp::Ult, Ty::U64, p[1], n),
                &mut |f, p| {
                    let acc = f.add(Ty::U128, p[0], x);
                    let one = f.iconst(Ty::U64, 1);
                    let i = f.add(Ty::U64, p[1], one);
                    vec![acc, i]
                },
            );
            f.ret(vec![out[0]]);
        }
        (Some(U128LiveAcrossCut), _) => {
            let a = f.zext(Ty::U64, Ty::U128, args[0]);
            let sixty_four = f.iconst(Ty::U128, 64);
            let high = f.binop(BinOp::Shl, Ty::U128, a, sixty_four);
            let low = f.zext(Ty::U64, Ty::U128, args[1]);
            let x = f.binop(BinOp::Or, Ty::U128, high, low);
            let next = f.create_block();
            f.br(next, vec![]);
            f.switch_to_block(next);
            f.call_void(tick, vec![args[0]]);
            let one = f.iconst(Ty::U128, 1);
            let y = f.add(Ty::U128, x, one);
            f.ret(vec![y]);
        }
        (Some(U128CutParam), _) => {
            let (then, other, join) = (f.create_block(), f.create_block(), f.create_block());
            let x = f.add_block_param(join, Ty::U128);
            let zero = f.iconst(Ty::U64, 0);
            let test = f.icmp(ICmpOp::Ne, Ty::U64, args[2], zero);
            f.condbr(test, then, vec![], other, vec![]);
            f.switch_to_block(then);
            let a = f.zext(Ty::U64, Ty::U128, args[0]);
            let sixty_four = f.iconst(Ty::U128, 64);
            let high = f.binop(BinOp::Shl, Ty::U128, a, sixty_four);
            let low = f.zext(Ty::U64, Ty::U128, args[1]);
            let wide = f.binop(BinOp::Or, Ty::U128, high, low);
            f.br(join, vec![wide]);
            f.switch_to_block(other);
            let narrow = f.zext(Ty::U64, Ty::U128, args[1]);
            f.br(join, vec![narrow]);
            f.switch_to_block(join);
            f.call_void(tick, vec![args[2]]);
            f.ret(vec![x]);
        }
        (Some(MatchArmTempAddress), _) | (_, Some(MatchArmTempAddressRead)) => {
            // local: u64 = e; temp: *const u64 (a slot of its own).
            let local = f.alloca(Ty::U64);
            f.store(Ty::U64, local, args[0]);
            let temp = f.alloca(ptr_u64.clone());
            let three = f.iconst(Ty::U64, 3);
            let low = f.binop(BinOp::And, Ty::U64, args[0], three);
            let (arm, other, join) = (f.create_block(), f.create_block(), f.create_block());
            let r = f.add_block_param(join, Ty::U8);
            // `match e & 3 { 1 | 2 => arm, _ => other }` (`decode_repr`'s
            // `match`): a shared target, so the source is stated over its
            // DAG, whose join merges the temporary's bytes.
            f.switch(
                low,
                [1, 2]
                    .into_iter()
                    .map(|value| SwitchCase {
                        value: Constant::Int(value),
                        target: arm,
                        args: vec![],
                    })
                    .collect(),
                other,
                vec![],
            );
            f.switch_to_block(arm);
            // The temporary holds `&local`, read back and passed by value
            // (`decode_repr`'s `&u64`, which its closure takes).
            f.store(ptr_u64.clone(), temp, local);
            let back = f.load(ptr_u64.clone(), temp);
            let used = f.call(use_ref, vec![back]);
            f.br(join, vec![used]);
            f.switch_to_block(other);
            let none = f.iconst(Ty::U8, 0);
            f.br(join, vec![none]);
            f.switch_to_block(join);
            if variant == Some(MatchArmTempAddressRead) {
                // The temporary read back after the join: live there.
                let back = f.load(ptr_u64.clone(), temp);
                let value = f.load(Ty::U64, back);
                let value = f.trunc(Ty::U64, Ty::U8, value);
                let sum = f.add(Ty::U8, r, value);
                f.ret(vec![sum]);
            } else {
                f.ret(vec![r]);
            }
        }
        (Some(U128ShlMasked | U128LshrMasked | I128AshrMasked), _) | (_, Some(WideMaskShl)) => {
            let mask = if variant == Some(WideMaskShl) {
                255
            } else {
                127
            };
            let mask = f.iconst(Ty::U32, mask);
            let amount = f.binop(BinOp::And, Ty::U32, args[1], mask);
            let ty = if shape == Some(I128AshrMasked) {
                Ty::I128
            } else {
                Ty::U128
            };
            let amount = f.zext(Ty::U32, ty.clone(), amount);
            let op = match shape {
                Some(U128LshrMasked) => BinOp::LShr,
                Some(I128AshrMasked) => BinOp::AShr,
                _ => BinOp::Shl,
            };
            let shifted = f.binop(op, ty, args[0], amount);
            f.ret(vec![shifted]);
        }
        (_, Some(UnmaskedShl)) => {
            let shifted = f.binop(BinOp::Shl, Ty::U128, args[0], args[1]);
            f.ret(vec![shifted]);
        }
        (Some(CallBoolThroughSlot | CallBoolAcrossCut), _)
        | (_, Some(BoolThroughSlotUnwritten | BoolThroughSlotTwo)) => {
            let slot = f.alloca(Ty::U8);
            let [value, ok] = f.call_results::<2>(probe, vec![args[0]]);
            let (arm, other, join) = (f.create_block(), f.create_block(), f.create_block());
            let three = f.iconst(Ty::U64, 3);
            let low = f.binop(BinOp::And, Ty::U64, args[0], three);
            // `match a & 3 { 1 | 2 => arm, _ => other }`: a shared target, so
            // the source is stated over its DAG, whose join merges the byte.
            f.switch(
                low,
                [1, 2]
                    .into_iter()
                    .map(|case| SwitchCase {
                        value: Constant::Int(case),
                        target: arm,
                        args: vec![],
                    })
                    .collect(),
                other,
                vec![],
            );
            f.switch_to_block(arm);
            let byte = f.zext(Ty::Bool, Ty::U8, ok);
            let one = f.iconst(Ty::U8, 1);
            let byte = f.binop(BinOp::And, Ty::U8, byte, one);
            let byte = if variant == Some(BoolThroughSlotTwo) {
                let two = f.iconst(Ty::U8, 2);
                f.binop(BinOp::Or, Ty::U8, byte, two)
            } else {
                byte
            };
            f.store(Ty::U8, slot, byte);
            f.call_void(tick, vec![value]);
            f.br(join, vec![]);
            f.switch_to_block(other);
            if variant != Some(BoolThroughSlotUnwritten) {
                let one64 = f.iconst(Ty::U64, 1);
                let half = f.binop(BinOp::LShr, Ty::U64, args[0], one64);
                let half = f.trunc(Ty::U64, Ty::U8, half);
                let one = f.iconst(Ty::U8, 1);
                let bit = f.binop(BinOp::And, Ty::U8, half, one);
                f.store(Ty::U8, slot, bit);
            }
            f.br(join, vec![]);
            f.switch_to_block(join);
            let flag = f.load(Ty::Bool, slot);
            let (yes, no) = (f.create_block(), f.create_block());
            f.condbr(flag, yes, vec![], no, vec![]);
            f.switch_to_block(yes);
            let one = f.iconst(Ty::U64, 1);
            f.ret(vec![one]);
            f.switch_to_block(no);
            let two = f.iconst(Ty::U64, 2);
            f.ret(vec![two]);
        }
        (Some(F32ParamAcrossCut), _) => {
            let a = f.call(g, vec![args[1]]);
            let next = f.create_block();
            f.br(next, vec![]);
            f.switch_to_block(next);
            let b = f.call(take_f32, vec![args[0]]);
            let sum = f.add(Ty::U64, a, b);
            f.ret(vec![sum]);
        }
        (_, Some(F32CopyInLoop)) => {
            let (header, exit) = (f.create_block(), f.create_block());
            let i = f.add_block_param(header, Ty::U64);
            let zero = f.iconst(Ty::U64, 0);
            f.br(header, vec![zero]);
            f.switch_to_block(header);
            let y = f.copy(Ty::F32, args[0]);
            let one = f.iconst(Ty::U64, 1);
            let next = f.add(Ty::U64, i, one);
            let more = f.icmp(ICmpOp::Ult, Ty::U64, next, args[1]);
            f.condbr(more, header, vec![next], exit, vec![]);
            f.switch_to_block(exit);
            let b = f.call(take_f32, vec![y]);
            f.ret(vec![b]);
        }
        (Some(ManySlots), _) => {
            // 70 one-byte locals, local `k` holding `x + k`; three read back.
            let mut sum = f.iconst(Ty::U8, 0);
            let mut slots = Vec::new();
            for k in 0..70i128 {
                let slot = f.alloca(Ty::U8);
                let c = f.iconst(Ty::U8, k);
                let v = f.add(Ty::U8, args[0], c);
                f.store(Ty::U8, slot, v);
                slots.push(slot);
            }
            for k in [0, 35, 69] {
                let v = f.load(Ty::U8, slots[k]);
                sum = f.add(Ty::U8, sum, v);
            }
            f.ret(vec![sum]);
        }
        (Some(WideIndexedStore), _) | (_, Some(TooWideIndexedStore)) => {
            let (ty, bound) = if variant == Some(TooWideIndexedStore) {
                (u8x1100.clone(), 1100)
            } else {
                (u8x800.clone(), 784)
            };
            let a = f.alloca(ty);
            let one = f.iconst(Ty::U8, 1);
            f.store(Ty::U8, a, one);
            let (store, skip) = (f.create_block(), f.create_block());
            let limit = f.iconst(Ty::U64, bound);
            let inside = f.icmp(ICmpOp::Ult, Ty::U64, args[0], limit);
            f.condbr(inside, store, vec![], skip, vec![]);
            f.switch_to_block(store);
            let at = f.gep(Ty::U8, a, vec![args[0]]);
            f.store(Ty::U8, at, args[1]);
            f.br(skip, vec![]);
            f.switch_to_block(skip);
            let first = f.load(Ty::U8, a);
            f.ret(vec![first]);
        }
        other => unreachable!("{other:?}"),
    }
    f.build();
    let module = builder.build().expect("ModuleBuilder::build: test fixture");
    trust_cg_lower::translate_module_for_arch_with_tls_with_license(
        &module,
        trust_cg_lower::GuardCarrierArch::X86_64,
        trust_cg_lower::TlsDialect::default(),
        &crate::license_test_support::permit_unlicensed(),
    )
    .unwrap_or_else(|error| panic!("{name}: fixture translates: {error:?}"))
    .into_iter()
    .map(|(function, _)| function)
    .find(|function| function.name == name)
    .unwrap_or_else(|| panic!("{name}: no translated function"))
}

pub(crate) fn slice20_lir(shape: Shape20) -> Function {
    slice20_function(shape.name(), Some(shape), None)
}

pub(crate) fn slice20_variant(variant: Variant20) -> Function {
    slice20_function(variant.name(), None, Some(variant))
}

pub(crate) fn slice20_pair(shape: Shape20) -> (Function, X86ISelFunction) {
    let source = slice20_lir(shape);
    let machine = select(&source, X86CallAbi::SystemV);
    (source, machine)
}

pub(crate) fn variant_pair(variant: Variant20) -> (Function, X86ISelFunction) {
    let source = slice20_variant(variant);
    let machine = select(&source, X86CallAbi::SystemV);
    (source, machine)
}

/// The shapes stated in parts by a test policy that cuts at every block
/// (slice 16's [`cut_at`]): a value, parameter or register carried across a
/// cut point.
pub(crate) fn cut_everywhere(shape: Shape20) -> bool {
    matches!(
        shape,
        Shape20::U128LiveAcrossCut
            | Shape20::U128CutParam
            | Shape20::CallBoolAcrossCut
            | Shape20::F32ParamAcrossCut
    )
}

/// The owner of a slice-20 pair: in parts at every block for the
/// [`cut_everywhere`] shapes, else the production owner.
pub(crate) fn slice20_owner<'a>(
    shape: Shape20,
    source: &'a Function,
    machine: &'a X86ISelFunction,
) -> Result<SourceBoundX86Body<'a>, X86BodyRefusal> {
    if cut_everywhere(shape) {
        source_bound_x86_body_in_parts(source, machine, SYSV, &cut_at(every_block(source)))
    } else {
        source_bound_x86_body(source, machine, SYSV)
    }
}

#[track_caller]
fn owner<'a>(
    shape: Shape20,
    source: &'a Function,
    machine: &'a X86ISelFunction,
) -> SourceBoundX86Body<'a> {
    slice20_owner(shape, source, machine).unwrap_or_else(|refusal| {
        panic!(
            "{shape:?}: {refusal}\n{}{}",
            describe_lir(source),
            describe(machine)
        )
    })
}

/// The theorem's query as the replay renders it.
fn text(obligation: &ProofObligation) -> String {
    generate_smt2_query_raw(obligation, &replay_config())
}

/// Whether an owner's theorem (every part, for one stated in parts) holds on
/// slice 9's keyed samples.
fn owner_holds(owner: &SourceBoundX86Body<'_>) -> Result<(), String> {
    if owner.is_stated_in_parts() {
        parts_hold(owner)
    } else if dag_holds_on_samples(owner.obligation()) {
        Ok(())
    } else {
        Err("the theorem is refuted on samples".into())
    }
}

/// Whether an owner's theorem (some part, for one stated in parts) is
/// refuted on samples.
fn owner_refuted(owner: &SourceBoundX86Body<'_>) -> bool {
    if owner.is_stated_in_parts() {
        some_part_refuted(owner)
    } else {
        dag_refuted_on_samples(owner.obligation())
    }
}

/// Every slice-20 shape builds a theorem that holds on samples: the one the
/// library gate states (in parts at every block for the [`cut_everywhere`]
/// shapes) and the production owner's (one query for each of them).
#[test]
fn owner_builds_every_slice_twenty_shape() {
    for shape in SLICE_TWENTY {
        let (source, machine) = slice20_pair(shape);
        let owner = owner(shape, &source, &machine);
        owner_holds(&owner).unwrap_or_else(|why| {
            panic!(
                "{shape:?}: {why}\n{}{}",
                describe_lir(&source),
                describe(&machine)
            )
        });
        if cut_everywhere(shape) {
            let production = source_bound_x86_body(&source, &machine, SYSV)
                .unwrap_or_else(|refusal| panic!("{shape:?} (production): {refusal}"));
            owner_holds(&production).unwrap_or_else(|why| {
                panic!(
                    "{shape:?} (production): {why}\n{}{}",
                    describe_lir(&source),
                    describe(&machine)
                )
            });
        }
    }
}

/// Every slice-20 theorem is the same on every build (no hash order leaks).
#[test]
fn slice_twenty_theorems_are_deterministic() {
    for shape in SLICE_TWENTY {
        let render = || {
            let (source, machine) = slice20_pair(shape);
            let owner = owner(shape, &source, &machine);
            let mut out = text(owner.obligation());
            for part in owner.parts() {
                out.push_str(&text(part));
            }
            out
        };
        assert_eq!(render(), render(), "{shape:?}");
    }
}

// ---------------------------------------------------------------------------
// 20c (OD-191): a switch's binary-search blocks
// ---------------------------------------------------------------------------

/// The binary-search shapes.
const SEARCHES: [Shape20; 5] = [
    Shape20::SparseMatch5,
    Shape20::SparseMatch7,
    Shape20::SparseMatchShared,
    Shape20::SparseMatchU8,
    Shape20::SparseMatchHighSelector,
];

/// The machine blocks of the selector's binary search over the entry block's
/// `Switch`: every laid-out block but the first made only of `cmp r, imm`,
/// `jcc` and a final `jmp` (the arms return, so no other block is).
fn tree_blocks(machine: &X86ISelFunction) -> Vec<Block> {
    machine
        .block_order
        .iter()
        .skip(1)
        .filter(|block| {
            let insts = &machine.blocks[*block].insts;
            insts
                .last()
                .is_some_and(|last| last.opcode == X86Opcode::Jmp)
                && insts[..insts.len() - 1]
                    .iter()
                    .all(|inst| matches!(inst.opcode, X86Opcode::CmpRI | X86Opcode::Jcc))
        })
        .copied()
        .collect()
}

/// The `(block, index)` of the first row of `block` with `opcode` (and, for a
/// `jcc`, condition `cc`).
fn row_in(
    machine: &X86ISelFunction,
    block: Block,
    opcode: X86Opcode,
    cc: Option<X86CondCode>,
) -> usize {
    machine.blocks[&block]
        .insts
        .iter()
        .position(|inst| {
            inst.opcode == opcode
                && cc.is_none_or(|cc| inst.operands.first() == Some(&O::CondCode(cc)))
        })
        .unwrap_or_else(|| panic!("{opcode:?} {cc:?} in {block:?}\n{}", describe(machine)))
}

fn block_target(inst: &X86ISelInst) -> Block {
    match inst.operands.last() {
        Some(O::Block(target)) => *target,
        other => panic!("a transfer's target: {other:?}"),
    }
}

fn set_target(inst: &mut X86ISelInst, to: Block) {
    let last = inst.operands.len() - 1;
    inst.operands[last] = O::Block(to);
}

/// Every binary-search shape's machine has blocks the selector added (the
/// tree), each of which the correspondence takes as a dispatch block of the
/// `Switch`'s block: no LIR block of its own, every route through the tree.
#[test]
fn a_switch_search_is_part_of_its_block() {
    for shape in SEARCHES {
        let (source, machine) = slice20_pair(shape);
        let tree = tree_blocks(&machine);
        assert!(
            !tree.is_empty(),
            "{shape:?}: a binary search\n{}",
            describe(&machine)
        );
        let cfg = source_cfg(&source).expect("a control flow");
        let correspondence = block_correspondence(&source, &machine, &cfg.dead)
            .unwrap_or_else(|reason| panic!("{shape:?}: {reason}"));
        for block in &tree {
            assert!(
                correspondence.search.contains(block),
                "{shape:?}: {block:?} is a search block"
            );
            assert_eq!(
                correspondence.dispatch.get(block),
                Some(&machine.block_order[0]),
                "{shape:?}: {block:?} dispatches the entry block's Switch"
            );
            assert!(!correspondence.origin.contains_key(block), "{shape:?}");
        }
    }
}

/// A source with a `Switch` the selector may search (five or more distinct
/// cases in `[0, i32::MAX]`) is stated over its DAG, whose edges may be
/// reached by several routes (the default by every leaf), even when no two
/// cases share a target and the per-path bounds hold.
#[test]
fn a_searched_switch_is_stated_over_its_dag() {
    let source = slice20_lir(Shape20::SparseMatch7);
    let cfg = source_cfg(&source).expect("a control flow");
    assert!(!cfg.shared_targets, "seven targets, one case each");
    assert!(cfg.order.len() <= MAX_SOURCE_BLOCKS && cfg.paths <= MAX_PATHS);
    assert!(cfg.searched_switch && !cfg.per_path());
    let body = admitted_body(&source).expect("admitted");
    assert!(body.dag.is_some(), "stated over its DAG");
    // A four-case switch is no search (the selector's chain or table).
    let (four, _) = super::slice14::slice14_pair(super::slice14::DefinedShape::JumpTable);
    assert!(!source_cfg(&four).expect("a control flow").searched_switch);
}

/// Wrong searches, each built by the owner and refuted by its theorem: a
/// case placed under the wrong half (the root's `jl` and `jmp` targets
/// swapped), two leaves' targets swapped, a leaf comparing another value, the
/// default taken on a hit, and the selector's signed `jl` over a case above
/// `2^31` (hand-built: the selector keeps a compare chain for one).
pub(crate) fn slice_twenty_search_refutations() -> Vec<(&'static str, Function, X86ISelFunction)> {
    let mut cases = Vec::new();
    // The root's `jl lo` and `jmp hi` swapped: the lower cases are searched
    // in the upper half.
    let (source, mut machine) = slice20_pair(Shape20::SparseMatch7);
    let root = machine.block_order[0];
    let jl = row_in(&machine, root, X86Opcode::Jcc, Some(X86CondCode::L));
    let jmp = row_in(&machine, root, X86Opcode::Jmp, None);
    let (lo, hi) = {
        let insts = &machine.blocks[&root].insts;
        (block_target(&insts[jl]), block_target(&insts[jmp]))
    };
    let insts = &mut machine.blocks.get_mut(&root).unwrap().insts;
    set_target(&mut insts[jl], hi);
    set_target(&mut insts[jmp], lo);
    cases.push(("a case under the wrong half", source, machine));
    // A wrong pivot: the root compares 13, not the median 34 (its `je` and
    // the halves unchanged): 13 reaches 34's block, and 34 the upper half,
    // where no leaf holds it.
    let (source, mut machine) = slice20_pair(Shape20::SparseMatch7);
    let root = machine.block_order[0];
    let cmp = row_in(&machine, root, X86Opcode::CmpRI, None);
    let insts = &mut machine.blocks.get_mut(&root).unwrap().insts;
    assert_eq!(insts[cmp].operands[1], O::Imm(34), "the median");
    insts[cmp].operands[1] = O::Imm(13);
    cases.push(("a wrong pivot", source, machine));
    // Two leaves' `je` targets swapped.
    let (source, mut machine) = slice20_pair(Shape20::SparseMatch7);
    let leaves: Vec<(Block, usize)> = tree_blocks(&machine)
        .into_iter()
        .flat_map(|block| {
            machine.blocks[&block]
                .insts
                .iter()
                .enumerate()
                .filter(|(_, inst)| inst.operands.first() == Some(&O::CondCode(X86CondCode::E)))
                .map(move |(index, _)| (block, index))
                .collect::<Vec<_>>()
        })
        .collect();
    let [(a_block, a), (b_block, b), ..] = leaves.as_slice() else {
        panic!("two leaf compares\n{}", describe(&machine))
    };
    let (ta, tb) = (
        block_target(&machine.blocks[a_block].insts[*a]),
        block_target(&machine.blocks[b_block].insts[*b]),
    );
    set_target(&mut machine.blocks.get_mut(a_block).unwrap().insts[*a], tb);
    set_target(&mut machine.blocks.get_mut(b_block).unwrap().insts[*b], ta);
    for block in [*a_block, *b_block] {
        let mut successors: Vec<Block> = machine.blocks[&block]
            .insts
            .iter()
            .filter(|inst| matches!(inst.opcode, X86Opcode::Jcc | X86Opcode::Jmp))
            .map(block_target)
            .collect();
        successors.sort();
        successors.dedup();
        machine.blocks.get_mut(&block).unwrap().successors = successors;
    }
    cases.push(("two leaves' targets swapped", source, machine));
    // A leaf comparing another value (the case plus one).
    let (source, mut machine) = slice20_pair(Shape20::SparseMatch5);
    let leaf = tree_blocks(&machine)[0];
    let cmp = row_in(&machine, leaf, X86Opcode::CmpRI, None);
    if let O::Imm(value) = &mut machine.blocks.get_mut(&leaf).unwrap().insts[cmp].operands[1] {
        *value += 1;
    }
    cases.push(("a leaf comparing another value", source, machine));
    // The default taken on a hit: a leaf's `je` to the default (the case's
    // target stays a successor through the other cases).
    let (source, mut machine) = slice20_pair(Shape20::SparseMatch5);
    let leaf = tree_blocks(&machine)[0];
    let je = row_in(&machine, leaf, X86Opcode::Jcc, Some(X86CondCode::E));
    let jmp = row_in(&machine, leaf, X86Opcode::Jmp, None);
    let default = block_target(&machine.blocks[&leaf].insts[jmp]);
    set_target(
        &mut machine.blocks.get_mut(&leaf).unwrap().insts[je],
        default,
    );
    let mut successors = machine.blocks[&leaf].successors.clone();
    successors.retain(|block| {
        machine.blocks[&leaf].insts.iter().any(|inst| {
            matches!(inst.opcode, X86Opcode::Jcc | X86Opcode::Jmp) && block_target(inst) == *block
        })
    });
    machine.blocks.get_mut(&leaf).unwrap().successors = successors;
    cases.push(("the default taken on a hit", source, machine));
    // The signed `jl` over a case above `2^31`: `SparseMatch5`'s tree (root
    // 13, leaves 9 10 and 34 39) with its last case made `0x8000_0000`, the
    // source the same `Switch` with that case.
    let source = slice20_variant(Variant20::SparseMatchAbove2_31);
    cases.push((
        "the signed jl over a case above 2^31",
        source.clone(),
        above_2_31_tree(&source, X86CondCode::L),
    ));
    cases
}

/// `SparseMatch5`'s selected tree over `source` (`SparseMatchAbove2_31`):
/// the leaf compare of 39 made `0x8000_0000` (as the 32-bit immediate
/// `i32::MIN`), the root's lower-half `jcc` condition `cc`.
fn above_2_31_tree(source: &Function, cc: X86CondCode) -> X86ISelFunction {
    let (_, mut machine) = slice20_pair(Shape20::SparseMatch5);
    machine.name = source.name.clone();
    let root = machine.block_order[0];
    let jl = row_in(&machine, root, X86Opcode::Jcc, Some(X86CondCode::L));
    machine.blocks.get_mut(&root).unwrap().insts[jl].operands[0] = O::CondCode(cc);
    let mut found = false;
    for block in tree_blocks(&machine) {
        for inst in &mut machine.blocks.get_mut(&block).unwrap().insts {
            if inst.opcode == X86Opcode::CmpRI && inst.operands[1] == O::Imm(39) {
                inst.operands[1] = O::Imm(i64::from(i32::MIN));
                found = true;
            }
        }
    }
    assert!(found, "the leaf compare of 39\n{}", describe(&machine));
    machine
}

/// Every wrong search is built by the owner and refuted by its theorem.
#[test]
fn every_slice_twenty_search_refutation_is_refuted() {
    for (label, source, machine) in slice_twenty_search_refutations() {
        let owner = source_bound_x86_body(&source, &machine, SYSV)
            .unwrap_or_else(|refusal| panic!("{label}: {refusal}\n{}", describe(&machine)));
        assert!(
            owner_refuted(&owner),
            "{label}: a wrong search's theorem holds on samples\n{}",
            describe(&machine)
        );
    }
}

/// The same hand-built tree with the unsigned `jb` at its root is correct
/// (the solver judges the order, never the recognizer), and so is the
/// selector's own chain for that source.
#[test]
fn a_hand_built_unsigned_search_over_a_case_above_2_31_holds() {
    let source = slice20_variant(Variant20::SparseMatchAbove2_31);
    let machine = above_2_31_tree(&source, X86CondCode::B);
    let owner = source_bound_x86_body(&source, &machine, SYSV)
        .unwrap_or_else(|refusal| panic!("{refusal}\n{}", describe(&machine)));
    assert!(
        dag_holds_on_samples(owner.obligation()),
        "{}",
        describe(&machine)
    );
    let chain = select(&source, X86CallAbi::SystemV);
    assert!(
        tree_blocks(&chain).is_empty(),
        "the selector keeps its chain"
    );
    let owner = source_bound_x86_body(&source, &chain, SYSV).expect("the chain");
    assert!(dag_holds_on_samples(owner.obligation()));
}

/// A block of the tree's shape that another LIR block's machine block also
/// reaches is no dispatch block of the `Switch`, nor is a tree block with any
/// other row or one that branches to itself: the correspondence then fails,
/// by name.
#[test]
fn a_tree_block_outside_the_search_shape_is_no_dispatch_block() {
    // Another row in a leaf (a copy, stamped with the `Switch`).
    let (source, mut machine) = slice20_pair(Shape20::SparseMatch5);
    let leaf = tree_blocks(&machine)[0];
    let stamp = machine.blocks[&leaf].insts[0].lowering_provenance;
    let mut extra = X86ISelInst::new(X86Opcode::MovRI, vec![vreg(900), O::Imm(1)]);
    extra.lowering_provenance = stamp;
    machine
        .blocks
        .get_mut(&leaf)
        .unwrap()
        .insts
        .insert(0, extra);
    let cfg = source_cfg(&source).expect("a control flow");
    let reason = block_correspondence(&source, &machine, &cfg.dead)
        .err()
        .expect("no correspondence");
    assert!(reason.contains("both lower LIR block"), "{reason}");
    // A leaf reached from an arm's block too.
    let (source, mut machine) = slice20_pair(Shape20::SparseMatch7);
    let leaf = tree_blocks(&machine)[0];
    let arm = *machine
        .block_order
        .iter()
        .find(|block| {
            machine.blocks[*block]
                .insts
                .last()
                .is_some_and(|inst| inst.opcode == X86Opcode::Ret)
        })
        .expect("an arm");
    let ret = machine.blocks[&arm].insts.len() - 1;
    machine.blocks.get_mut(&arm).unwrap().insts[ret] =
        X86ISelInst::new(X86Opcode::Jmp, vec![O::Block(leaf)]);
    machine.blocks.get_mut(&arm).unwrap().successors = vec![leaf];
    let cfg = source_cfg(&source).expect("a control flow");
    assert!(block_correspondence(&source, &machine, &cfg.dead).is_err());
    // A leaf that branches to itself (its first `je` retargeted): a block on a
    // cycle is no search block, so it is a second machine block of the
    // switch's LIR block, by name.
    let (source, mut machine) = slice20_pair(Shape20::SparseMatch5);
    let leaf = tree_blocks(&machine)[0];
    let je = row_in(&machine, leaf, X86Opcode::Jcc, Some(X86CondCode::E));
    set_target(&mut machine.blocks.get_mut(&leaf).unwrap().insts[je], leaf);
    let mut successors: Vec<Block> = machine.blocks[&leaf]
        .insts
        .iter()
        .filter(|inst| matches!(inst.opcode, X86Opcode::Jcc | X86Opcode::Jmp))
        .map(block_target)
        .collect();
    successors.sort();
    successors.dedup();
    machine.blocks.get_mut(&leaf).unwrap().successors = successors;
    let cfg = source_cfg(&source).expect("a control flow");
    let reason = block_correspondence(&source, &machine, &cfg.dead)
        .err()
        .unwrap_or_else(|| {
            panic!(
                "a self-looping leaf is a search block\n{}",
                describe(&machine)
            )
        });
    assert!(reason.contains("both lower LIR block"), "{reason}");
}

// ---------------------------------------------------------------------------
// 20d (OD-192): a stored private address dead at a DAG join
// ---------------------------------------------------------------------------

/// The arm's temporary holds `&local` on one path into the join and nothing
/// on the other; no path from the join reads it, so its bytes are dead
/// there on both sides (unreadable), and the body is stated. Read back after
/// the join, it is live: slice 13's refusal stays, by name.
#[test]
fn a_stored_address_dead_at_a_join_leaves_the_relation() {
    let (source, machine) = slice20_pair(Shape20::MatchArmTempAddress);
    let owner = owner(Shape20::MatchArmTempAddress, &source, &machine);
    owner_holds(&owner).unwrap();
    let body = admitted_body(&source).expect("admitted");
    let dag = body.dag.as_ref().expect("a DAG");
    assert!(
        dag.join_dead.values().any(|bytes| bytes.len() == 8),
        "the temporary's eight bytes are dead at the join: {:?}",
        dag.join_dead
    );
    let (source, machine) = variant_pair(Variant20::MatchArmTempAddressRead);
    let refusal = source_bound_x86_body(&source, &machine, SYSV)
        .err()
        .expect("refused");
    assert!(
        refusal
            .to_string()
            .contains("holding different values, one of them a private stack address"),
        "{refusal}"
    );
}

/// A machine read of a byte dead at the join (the temporary's pointer read
/// back at the join, where the source never reads it) makes no claim: the
/// walk refuses at the read, by name, and the machine is never credited.
#[test]
fn a_machine_read_of_a_byte_dead_at_a_join_makes_no_claim() {
    let (source, mut machine) = slice20_pair(Shape20::MatchArmTempAddress);
    // The arm's store of `&local` into the temporary (the LIR `Store` of
    // block 2, the arm), whose address operand names the temporary's slot.
    let rows = stamped_rows_of(&source, &machine, |block, inst| {
        block == Block(2) && matches!(inst.opcode, L::Store { .. })
    });
    let [(block, index)] = rows.as_slice() else {
        panic!("the arm's one store: {rows:?}\n{}", describe(&machine))
    };
    let address = machine.blocks[block].insts[*index].operands[0].clone();
    assert!(
        matches!(&address, O::MemAddr { .. }),
        "{address:?}\n{}",
        describe(&machine)
    );
    // At the start of the join (LIR block 3, whose machine block has the same
    // id), a load of the temporary's eight bytes into a fresh register.
    let join = Block(3);
    assert!(
        machine.blocks.contains_key(&join),
        "the join's machine block\n{}",
        describe(&machine)
    );
    let load = X86ISelInst::new(X86Opcode::MovRM, vec![vreg(900), address]);
    machine.blocks.get_mut(&join).unwrap().insts.insert(0, load);
    let refusal = source_bound_x86_body(&source, &machine, SYSV)
        .err()
        .unwrap_or_else(|| panic!("a read of a dead byte is stated\n{}", describe(&machine)));
    assert!(
        refusal
            .to_string()
            .contains("reads a private stack byte its cut point leaves unreadable"),
        "{refusal}"
    );
    let outcome = super::slice12::never_credited(&source, &machine, "read of a dead join byte");
    assert_ne!(outcome, "credited");
}

// ---------------------------------------------------------------------------
// 20b (OD-193): `I128` loop-carried values and cut items as two halves
// ---------------------------------------------------------------------------

/// The `I128` shapes: each header parameter or cut item is two free 64-bit
/// inputs, `x{H}v{i}l` and `x{H}v{i}h`, no name wider than 64 bits.
const I128_ITEMS: [Shape20; 5] = [
    Shape20::U128ShiftLoop,
    Shape20::U128RadixLoop,
    Shape20::U128AccLoop,
    Shape20::U128LiveAcrossCut,
    Shape20::U128CutParam,
];

#[test]
fn an_i128_item_is_two_named_halves() {
    for shape in I128_ITEMS {
        let (source, machine) = slice20_pair(shape);
        let owner = owner(shape, &source, &machine);
        let texts: Vec<String> = std::iter::once(text(owner.obligation()))
            .chain(owner.parts().iter().map(text))
            .collect();
        let all = texts.join("\n");
        let declared: Vec<&str> = all
            .lines()
            .filter(|line| line.starts_with("(declare-const x"))
            .collect();
        let half = |suffix: char| {
            declared.iter().any(|line| {
                line.split_whitespace().nth(1).is_some_and(|name| {
                    name.ends_with(suffix)
                        && name[1..].split('v').count() == 2
                        && line.ends_with("(_ BitVec 64))")
                })
            })
        };
        assert!(
            half('l') && half('h'),
            "{shape:?}: both halves are 64-bit inputs\n{all}"
        );
        assert!(
            declared.iter().all(|line| !line.contains("(_ BitVec 128)")),
            "{shape:?}: no header input is wider than 64 bits"
        );
    }
}

// ---------------------------------------------------------------------------
// Every wrong lowering, and how its theorem is built
// ---------------------------------------------------------------------------

/// How a refutation's theorem is built.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Built {
    /// By the production owner (in parts when it states it so).
    Owner,
    /// In parts at every block (slice 16's [`cut_at`]).
    EveryBlock,
    /// Without the owner's affine refusal and slice 20's bound on a variable
    /// `I128` shift's amount ([`theorem_without_shift_bound`]).
    WithoutShiftBound,
}

/// The theorems a refutation's wrong lowering builds: the single theorem, or
/// every part.
pub(crate) fn refutation_obligations(
    source: &Function,
    machine: &X86ISelFunction,
    built: Built,
) -> Result<Vec<ProofObligation>, X86BodyRefusal> {
    let of = |owner: SourceBoundX86Body<'_>| {
        if owner.is_stated_in_parts() {
            owner.parts().to_vec()
        } else {
            vec![owner.obligation().clone()]
        }
    };
    match built {
        Built::Owner => source_bound_x86_body(source, machine, SYSV).map(of),
        Built::EveryBlock => {
            source_bound_x86_body_in_parts(source, machine, SYSV, &cut_at(every_block(source)))
                .map(of)
        }
        Built::WithoutShiftBound => {
            theorem_without_shift_bound(source, machine, SYSV).map(|theorem| vec![theorem])
        }
    }
}

/// Every slice-20 wrong lowering: its label, source, machine and how its
/// theorem is built.
pub(crate) fn slice_twenty_refutations() -> Vec<(&'static str, Function, X86ISelFunction, Built)> {
    let mut cases: Vec<(&'static str, Function, X86ISelFunction, Built)> =
        slice_twenty_search_refutations()
            .into_iter()
            .map(|(label, source, machine)| (label, source, machine, Built::Owner))
            .collect();
    cases.extend(slice_twenty_item_refutations());
    cases.extend(slice_twenty_singleton_refutations());
    cases.extend(slice_twenty_admitted_refutations());
    cases
}

/// Wrong lowerings of bodies only slice 20's other rules admit (OD-192's
/// dead join byte, OD-194's closed undefined bits, total slot bytes and
/// candidate bound): each is stated under its rule and refuted.
pub(crate) fn slice_twenty_admitted_refutations()
-> Vec<(&'static str, Function, X86ISelFunction, Built)> {
    let mut cases = Vec::new();
    // OD-192: the local whose address the temporary carries to the call
    // holding another value there: before the switch the machine stores `e &
    // 3` over it, and the call, to which the local escapes, observes it.
    let (source, mut machine) = slice20_pair(Shape20::MatchArmTempAddress);
    let entry = machine.block_order[0];
    let insts = &machine.blocks[&entry].insts;
    let local = insts
        .iter()
        .find_map(|inst| match (inst.opcode, inst.operands.as_slice()) {
            (X86Opcode::Lea, [dst, O::MemAddr { base, disp: 0 }])
                if matches!(base.as_ref(), O::StackSlot(0)) =>
            {
                Some(dst.clone())
            }
            _ => None,
        })
        .unwrap_or_else(|| panic!("the local's address\n{}", describe(&machine)));
    let masked = insts
        .iter()
        .find(|inst| inst.opcode == X86Opcode::AndRR)
        .map(|inst| inst.operands[0].clone())
        .unwrap_or_else(|| panic!("e & 3\n{}", describe(&machine)));
    let at = insts
        .iter()
        .position(|inst| inst.opcode == X86Opcode::CmpRI)
        .unwrap_or_else(|| panic!("the switch's first compare\n{}", describe(&machine)));
    let stamp = insts[at - 1].lowering_provenance;
    let mut store = X86ISelInst::new(
        X86Opcode::MovMR,
        vec![
            O::MemAddr {
                base: Box::new(local),
                disp: 0,
            },
            masked,
        ],
    );
    store.lowering_provenance = stamp;
    machine
        .blocks
        .get_mut(&entry)
        .unwrap()
        .insts
        .insert(at, store);
    cases.push((
        "the local a dead-at-the-join temporary points to holding another value at the call",
        source,
        machine,
        Built::Owner,
    ));
    // OD-194: the `f32` parameter's register overwritten before the cut with
    // the other parameter's bits (`movq`, a closed term too), so the call
    // past the cut is passed their low 32.
    let (source, mut machine) = slice20_pair(Shape20::F32ParamAcrossCut);
    let entry = machine.block_order[0];
    let insts = &mut machine.blocks.get_mut(&entry).unwrap().insts;
    let at = insts.len() - 1;
    let stamp = insts[at].lowering_provenance;
    let mut movd = X86ISelInst::new(
        X86Opcode::MovqToXmm,
        vec![
            O::VReg(VReg::new(0, RegClass::Fpr32)),
            O::VReg(VReg::new(1, RegClass::Gpr64)),
        ],
    );
    movd.lowering_provenance = stamp;
    insts.insert(at, movd);
    cases.push((
        "the f32 parameter's register overwritten with the other parameter before the cut",
        source,
        machine,
        Built::EveryBlock,
    ));
    // OD-194: past 64 slots, local 0's read-back reads local 35.
    let (source, mut machine) = slice20_pair(Shape20::ManySlots);
    let load = find(&machine, X86Opcode::MovzxRM8)[0];
    let next = match &inst(&machine, find(&machine, X86Opcode::MovzxRM8)[1]).operands[1] {
        O::MemAddr { base, .. } => base.as_ref().clone(),
        other => panic!("a load's address: {other:?}"),
    };
    let O::MemAddr { base, .. } = &mut inst_mut(&mut machine, load).operands[1] else {
        panic!("a load's address\n{}", describe(&machine))
    };
    **base = next;
    cases.push((
        "a slot's read-back reading another slot, past 64 slots",
        source,
        machine,
        Built::Owner,
    ));
    // OD-194: the 784-candidate indexed store one byte past its element.
    let (source, mut machine) = slice20_pair(Shape20::WideIndexedStore);
    let store = *find(&machine, X86Opcode::MovMR8)
        .last()
        .unwrap_or_else(|| panic!("the indexed store\n{}", describe(&machine)));
    let O::MemAddr { disp, .. } = &mut inst_mut(&mut machine, store).operands[0] else {
        panic!("the indexed store's address\n{}", describe(&machine))
    };
    *disp += 1;
    cases.push((
        "the 784-candidate indexed store one byte past its element",
        source,
        machine,
        Built::Owner,
    ));
    cases
}

/// Every slice-20 refutation's theorem is refuted on samples, and the
/// production owner never credits its machine.
#[test]
fn every_slice_twenty_refutation_is_refuted() {
    for (label, source, machine, built) in slice_twenty_refutations() {
        let theorems = refutation_obligations(&source, &machine, built)
            .unwrap_or_else(|refusal| panic!("{label}: {refusal}\n{}", describe(&machine)));
        assert!(
            theorems.iter().any(|theorem| {
                dag_refuted_on_samples(theorem)
                    || (0..super::slice10::EDGE_SAMPLES)
                        .any(|seed| !super::slice10::holds_at_edge(theorem, seed))
            }),
            "{label}: a wrong lowering's theorem holds on samples\n{}{}",
            describe_lir(&source),
            describe(&machine)
        );
        let outcome = super::slice12::never_credited(&source, &machine, label);
        assert_ne!(outcome, "credited", "{label}");
    }
}

/// The `(low, high)` registers the rows stamped with the LIR instruction of
/// `source` that `matches` picks (its first) write ([`i128_pair`]), and the
/// machine block holding them.
fn stamped_pair(
    source: &Function,
    machine: &X86ISelFunction,
    matches: impl Fn(&L) -> bool,
) -> (Block, Reg, Reg) {
    let mut blocks: Vec<&Block> = source.blocks.keys().collect();
    blocks.sort();
    for block in blocks {
        for (index, inst) in source.blocks[block].instructions.iter().enumerate() {
            if !matches(&inst.opcode) {
                continue;
            }
            let stamp = trust_cg_ir::provenance::SourceInstId {
                block: block.0,
                index: index as u32,
            };
            for (machine_block, body) in &machine.blocks {
                let stamped: Vec<&X86ISelInst> = body
                    .insts
                    .iter()
                    .filter(|row| row.lowering_provenance.source_id() == Some(stamp))
                    .collect();
                if let Some((low, high)) = i128_pair(&stamped) {
                    return (*machine_block, low, high);
                }
            }
        }
    }
    panic!(
        "no stamped i128 pair\n{}{}",
        describe_lir(source),
        describe(machine)
    )
}

fn gpr_operand(reg: Reg) -> O {
    match reg.root {
        Root::Virtual(id) => O::VReg(VReg::new(id, RegClass::Gpr64)),
        Root::Physical(root) => preg(root),
    }
}

/// `mov dst, src` inserted before the last row of machine block `block` (its
/// transfer).
fn copy_before_exit(machine: &mut X86ISelFunction, block: Block, dst: Reg, src: Reg) {
    let insts = &mut machine.blocks.get_mut(&block).unwrap().insts;
    let at = insts.len() - 1;
    let stamp = insts[at].lowering_provenance;
    let mut copy = X86ISelInst::new(X86Opcode::MovRR, vec![gpr_operand(dst), gpr_operand(src)]);
    copy.lowering_provenance = stamp;
    insts.insert(at, copy);
}

/// The machine `(block, index)` of every row stamped with the first LIR
/// instruction of `source` that `matches` picks (blocks in id order), in
/// row order.
fn stamped_rows_of(
    source: &Function,
    machine: &X86ISelFunction,
    matches: impl Fn(Block, &Instruction) -> bool,
) -> Vec<(Block, usize)> {
    let mut blocks: Vec<&Block> = source.blocks.keys().collect();
    blocks.sort();
    for block in blocks {
        for (index, inst) in source.blocks[block].instructions.iter().enumerate() {
            if !matches(*block, inst) {
                continue;
            }
            let stamp = trust_cg_ir::provenance::SourceInstId {
                block: block.0,
                index: index as u32,
            };
            let rows: Vec<(Block, usize)> = machine
                .block_order
                .iter()
                .flat_map(|machine_block| {
                    machine.blocks[machine_block]
                        .insts
                        .iter()
                        .enumerate()
                        .filter(|(_, row)| row.lowering_provenance.source_id() == Some(stamp))
                        .map(|(row, _)| (*machine_block, row))
                        .collect::<Vec<_>>()
                })
                .collect();
            if !rows.is_empty() {
                return rows;
            }
        }
    }
    panic!(
        "no stamped rows\n{}{}",
        describe_lir(source),
        describe(machine)
    )
}

/// The two `mov`s of the back edge's copy into a loop header's `I128`
/// parameter `param` (the copy in a block other than the entry).
fn back_edge_copy(source: &Function, machine: &X86ISelFunction, param: u32) -> [(Block, usize); 2] {
    let entry = source.entry_block;
    let rows = stamped_rows_of(source, machine, |block, inst| {
        block != entry && matches!(inst.opcode, L::Copy) && inst.results == [Value(param)]
    });
    let [low, high] = rows.as_slice() else {
        panic!("a copy's two movs: {rows:?}\n{}", describe(machine))
    };
    [*low, *high]
}

fn row_mut(machine: &mut X86ISelFunction, (block, index): (Block, usize)) -> &mut X86ISelInst {
    &mut machine.blocks.get_mut(&block).unwrap().insts[index]
}

/// Wrong lowerings of the `I128` items (OD-193).
pub(crate) fn slice_twenty_item_refutations()
-> Vec<(&'static str, Function, X86ISelFunction, Built)> {
    let mut cases = Vec::new();
    // `U128ShiftLoop`'s back edge copies `n >> 1` into the header's pair.
    let (source, mut machine) = slice20_pair(Shape20::U128ShiftLoop);
    let [low, high] = back_edge_copy(&source, &machine, 2);
    let (from_low, from_high) = (
        row_mut(&mut machine, low).operands[1].clone(),
        row_mut(&mut machine, high).operands[1].clone(),
    );
    row_mut(&mut machine, low).operands[1] = from_high.clone();
    row_mut(&mut machine, high).operands[1] = from_low.clone();
    cases.push((
        "an i128's halves swapped on the back edge",
        source,
        machine,
        Built::Owner,
    ));
    let (source, mut machine) = slice20_pair(Shape20::U128ShiftLoop);
    let [_, high] = back_edge_copy(&source, &machine, 2);
    machine
        .blocks
        .get_mut(&high.0)
        .unwrap()
        .insts
        .remove(high.1);
    cases.push((
        "an i128's high half not copied on the back edge",
        source,
        machine,
        Built::Owner,
    ));
    let (source, mut machine) = slice20_pair(Shape20::U128ShiftLoop);
    let [low, high] = back_edge_copy(&source, &machine, 2);
    let from_low = row_mut(&mut machine, low).operands[1].clone();
    row_mut(&mut machine, high).operands[1] = from_low;
    cases.push((
        "an i128's low half copied into both registers on the back edge",
        source,
        machine,
        Built::Owner,
    ));
    // `U128AccLoop`: the accumulator's high register takes the low half of
    // the other `I128`, `x` (its entry register `v0`).
    let (source, mut machine) = slice20_pair(Shape20::U128AccLoop);
    let [_, high] = back_edge_copy(&source, &machine, 4);
    row_mut(&mut machine, high).operands[1] = gpr_operand(Reg {
        root: Root::Virtual(0),
        bits: 64,
    });
    cases.push((
        "the low half of another i128 in an i128's high register",
        source,
        machine,
        Built::Owner,
    ));
    // `U128CutParam`: the else edge's copy into the cut parameter with its
    // halves swapped.
    let (source, mut machine) = slice20_pair(Shape20::U128CutParam);
    let rows = stamped_rows_of(&source, &machine, |block, inst| {
        block == Block(2) && matches!(inst.opcode, L::Copy) && inst.results == [Value(10)]
    });
    let [low, high] = rows.as_slice() else {
        panic!("the else edge's two movs: {rows:?}\n{}", describe(&machine))
    };
    let (from_low, from_high) = (
        row_mut(&mut machine, *low).operands[1].clone(),
        row_mut(&mut machine, *high).operands[1].clone(),
    );
    row_mut(&mut machine, *low).operands[1] = from_high;
    row_mut(&mut machine, *high).operands[1] = from_low;
    cases.push((
        "an i128 cut parameter's halves swapped on one edge",
        source,
        machine,
        Built::EveryBlock,
    ));
    // The live value's high register made its low half before the cut.
    let (source, mut machine) = slice20_pair(Shape20::U128LiveAcrossCut);
    let (block, low, high) = stamped_pair(&source, &machine, |op| matches!(op, L::Bor));
    copy_before_exit(&mut machine, block, high, low);
    cases.push((
        "an i128's high half made its low half before a cut",
        source,
        machine,
        Built::EveryBlock,
    ));
    cases
}

/// Wrong lowerings of the singleton rules (OD-194).
pub(crate) fn slice_twenty_singleton_refutations()
-> Vec<(&'static str, Function, X86ISelFunction, Built)> {
    let mut cases = Vec::new();
    // `x << (n & 127)` with the selector's `shift == 0` select dropped: at
    // an amount of 0 the low half's spill `lo >> (64 - 0)` is `lo` (x86
    // masks the count to 6 bits), ORed into the high half.
    let (source, mut machine) = slice20_pair(Shape20::U128ShlMasked);
    let cmov = find(&machine, X86Opcode::Cmovcc)
        .into_iter()
        .find(|ordinal| {
            inst(&machine, *ordinal).operands.get(2) == Some(&O::CondCode(X86CondCode::E))
        })
        .unwrap_or_else(|| panic!("the shift == 0 cmove\n{}", describe(&machine)));
    let (_, block, index) = rows(&machine)[cmov];
    machine.blocks.get_mut(&block).unwrap().insts.remove(index);
    cases.push((
        "an i128 shift's shift == 0 select dropped",
        source,
        machine,
        Built::Owner,
    ));
    // The two `shift >= 64` selects' sources swapped.
    let (source, mut machine) = slice20_pair(Shape20::U128ShlMasked);
    let ae: Vec<usize> = find(&machine, X86Opcode::Cmovcc)
        .into_iter()
        .filter(|ordinal| {
            inst(&machine, *ordinal).operands.get(2) == Some(&O::CondCode(X86CondCode::AE))
        })
        .collect();
    let [first, second] = ae.as_slice() else {
        panic!("two shift >= 64 cmovs\n{}", describe(&machine))
    };
    let (a, b) = (
        inst(&machine, *first).operands[1].clone(),
        inst(&machine, *second).operands[1].clone(),
    );
    inst_mut(&mut machine, *first).operands[1] = b;
    inst_mut(&mut machine, *second).operands[1] = a;
    cases.push((
        "an i128 shift's shift >= 64 selects swapped",
        source,
        machine,
        Built::Owner,
    ));
    // A `bool` read of a stored 2 or 3 as its bit 0 ([`bit_zero_read`]):
    // the source reads `byte != 0`, true.
    let (source, machine) = variant_pair(Variant20::BoolThroughSlotTwo);
    cases.push((
        "a bool read of a stored 2 or 3 as its bit 0",
        source.clone(),
        bit_zero_read(&machine),
        Built::Owner,
    ));
    // The selector's correct lowering of an unmasked shift, built without the
    // bound finder: not the shift modulo 128 at an amount of 128 or more.
    let (source, machine) = variant_pair(Variant20::UnmaskedShl);
    cases.push((
        "an i128 shift by an unmasked amount (built without the bound finder)",
        source,
        machine,
        Built::WithoutShiftBound,
    ));
    cases
}

/// A variable `I128` shift whose own definition bounds its amount below 128
/// by no mask (no mask at all, or `& 255`) is refused by the bound finder,
/// by name; built without the finder, its theorem is refuted (the selector's
/// lowering is not the shift modulo 128 at an amount of 128 or more).
#[test]
fn an_unbounded_i128_shift_is_refused_and_its_theorem_refutes_it() {
    for variant in [Variant20::UnmaskedShl, Variant20::WideMaskShl] {
        let (source, machine) = variant_pair(variant);
        let refusal = source_bound_x86_body(&source, &machine, SYSV)
            .err()
            .unwrap_or_else(|| panic!("{variant:?}: refused"));
        assert!(
            refusal
                .to_string()
                .contains("shifts an i128 by a non-constant amount that no mask"),
            "{variant:?}: {refusal}"
        );
        let theorem = theorem_without_shift_bound(&source, &machine, SYSV)
            .unwrap_or_else(|refusal| panic!("{variant:?}: {refusal}\n{}", describe(&machine)));
        assert!(
            dag_refuted_on_samples(&theorem),
            "{variant:?}: the unbounded shift's theorem is refuted"
        );
    }
}

// ---------------------------------------------------------------------------
// OD-194: the singleton rules and the bounds
// ---------------------------------------------------------------------------

/// `machine` with its `bool` load's `(byte + 255) >> 8` (the selector's
/// `byte != 0`) replaced by `byte & 1 & 1`: the byte's bit 0.
fn bit_zero_read(machine: &X86ISelFunction) -> X86ISelFunction {
    let mut machine = machine.clone();
    let add = find(&machine, X86Opcode::AddRI)
        .into_iter()
        .find(|ordinal| inst(&machine, *ordinal).operands.get(2) == Some(&O::Imm(255)))
        .unwrap_or_else(|| panic!("the bool load's add 255\n{}", describe(&machine)));
    let shr = add + 1;
    assert_eq!(
        inst(&machine, shr).opcode,
        X86Opcode::ShrRI,
        "{}",
        describe(&machine)
    );
    let row = inst_mut(&mut machine, add);
    row.opcode = X86Opcode::AndRI;
    row.operands[2] = O::Imm(1);
    let row = inst_mut(&mut machine, shr);
    row.opcode = X86Opcode::AndRI;
    row.operands[2] = O::Imm(1);
    machine
}

/// A `bool` read past a join (and past a cut) of a byte two integer stores
/// wrote is trust-ir's `byte != 0`: the theorem holds for the selector's
/// `(byte + 255) >> 8`, and for a machine that reads the byte's bit 0 where
/// every store writes 0 or 1, and refutes that machine where a store writes 2
/// or 3. A byte one path leaves unwritten stays refused, by name.
#[test]
fn a_bool_read_past_a_join_of_an_integer_store_byte_is_byte_not_zero() {
    let (source, machine) = slice20_pair(Shape20::CallBoolThroughSlot);
    let body = admitted_body(&source).expect("admitted");
    assert!(body.dag.is_some(), "stated over its DAG");
    let bit_zero = bit_zero_read(&machine);
    let owner = source_bound_x86_body(&source, &bit_zero, SYSV)
        .unwrap_or_else(|refusal| panic!("{refusal}\n{}", describe(&bit_zero)));
    owner_holds(&owner).expect("bit 0 of a 0 or 1 is the bool");
    let (source, machine) = variant_pair(Variant20::BoolThroughSlotTwo);
    let owner = source_bound_x86_body(&source, &machine, SYSV).expect("the selector's read");
    owner_holds(&owner).expect("(byte + 255) >> 8 is byte != 0");
    let (source, machine) = variant_pair(Variant20::BoolThroughSlotUnwritten);
    let refusal = source_bound_x86_body(&source, &machine, SYSV)
        .err()
        .expect("refused");
    assert!(refusal.to_string().contains("no bool store"), "{refusal}");
}

/// The `f32` parameter's register, whose bits above 31 the entry `movss`
/// leaves a free input `u{k}`, is a closed term at a cut (the entry row runs
/// once), so the call past the cut reads it.
#[test]
fn an_entry_rows_undefined_bits_are_fixed_for_the_run() {
    let (source, machine) = slice20_pair(Shape20::F32ParamAcrossCut);
    let owner = owner(Shape20::F32ParamAcrossCut, &source, &machine);
    assert!(owner.is_stated_in_parts());
    owner_holds(&owner).unwrap();
}

/// Undefined bits a row INSIDE a loop introduces are no input fixed for the
/// run: the loop's `f32` copy leaves its register's bits above 31 a fresh
/// input on every visit, so at the exit's cut the register is carried (not
/// closed) and the call past the cut that reads it makes no claim, by name.
#[test]
fn undefined_bits_a_loop_row_introduces_stay_carried() {
    let (source, machine) = variant_pair(Variant20::F32CopyInLoop);
    let refusal =
        source_bound_x86_body_in_parts(&source, &machine, SYSV, &cut_at(every_block(&source)))
            .err()
            .unwrap_or_else(|| {
                panic!(
                    "the loop row's undefined bits are taken as fixed for the run\n{}{}",
                    describe_lir(&source),
                    describe(&machine)
                )
            });
    assert!(
        refusal
            .to_string()
            .contains("which its loop carries paired with no loop-header parameter"),
        "{refusal}\n{}{}",
        describe_lir(&source),
        describe(&machine)
    );
}

/// The slots are bounded by their bytes in all (OD-194): 70 one-byte slots
/// are admitted, and a frame past `MAX_SLOT_TOTAL_BYTES` is refused by name.
#[test]
fn private_slots_are_bounded_by_their_bytes() {
    let source = slice20_lir(Shape20::ManySlots);
    assert!(source.stack_slots.len() > 64);
    let mut huge = source.clone();
    for _ in 0..64 {
        huge.stack_slots
            .push(trust_cg_lower::StackSlotInfo::new(MAX_SLOT_BYTES, 8));
    }
    let refusal = admitted_body(&huge).err().expect("refused");
    assert!(refusal.to_string().contains("bytes in all"), "{refusal}");
}

/// An indexed store with 784 candidate offsets is admitted, one with 1100
/// is refused by name (OD-194's 1024).
#[test]
fn an_indexed_access_has_at_most_1024_candidates() {
    let (source, machine) = variant_pair(Variant20::TooWideIndexedStore);
    let refusal = source_bound_x86_body(&source, &machine, SYSV)
        .err()
        .expect("refused");
    assert!(
        refusal.to_string().contains("1100 candidate offsets"),
        "{refusal}"
    );
}

// ---------------------------------------------------------------------------
// The golden theorems
// ---------------------------------------------------------------------------

/// SHA-256 of `slice20_snapshots.smt2`. The golden bytes can change only
/// together with this reviewed constant.
const SLICE_TWENTY_SNAPSHOT_SHA256: &str =
    "d8f6c375d0afefef303390bfdff3fba797434a286e02bd23d79ba4612fbbc948";

/// Every slice-20 fixture's theorem (every part of one stated in parts), as
/// the replay renders it (`;;;; <shape>`, `;;;; <shape> | part k of n`).
pub(crate) fn slice_twenty_snapshots() -> String {
    let mut rendered = String::new();
    for shape in SLICE_TWENTY {
        let (source, machine) = slice20_pair(shape);
        let owner = owner(shape, &source, &machine);
        rendered.push_str(&format!(";;;; {shape:?}\n{}\n", text(owner.obligation())));
        let n = owner.parts().len();
        for (k, part) in owner.parts().iter().enumerate() {
            rendered.push_str(&format!(
                ";;;; {shape:?} | part {} of {n}\n{}\n",
                k + 1,
                text(part)
            ));
        }
    }
    rendered
}

/// The rendered theorems of every slice-20 fixture are the reviewed golden
/// text, pinned by digest, and independent of the function's name.
#[test]
fn slice_twenty_smt2_is_canonical_per_shape() {
    use sha2::{Digest, Sha256};
    const GOLDEN: &str =
        include_str!("../tests/fixtures/x86_source_bound_body/slice20_snapshots.smt2");
    let rendered = slice_twenty_snapshots();
    for shape in SLICE_TWENTY {
        let (source, machine) = slice20_pair(shape);
        let (mut renamed_source, mut renamed_machine) = (source.clone(), machine.clone());
        renamed_source.name = "renamed_function".into();
        renamed_machine.name = "renamed_function".into();
        let original = owner(shape, &source, &machine);
        let renamed = owner(shape, &renamed_source, &renamed_machine);
        assert_eq!(
            text(renamed.obligation()),
            text(original.obligation()),
            "{shape:?}"
        );
    }
    if std::env::var_os("TCG_X86_BODY_SNAPSHOT_WRITE").is_some() {
        let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("tests/fixtures/x86_source_bound_body/slice20_snapshots.smt2");
        std::fs::write(&path, &rendered).unwrap();
        panic!(
            "rewrote {}; review its diff, set SLICE_TWENTY_SNAPSHOT_SHA256 to {:x} and re-run \
             without TCG_X86_BODY_SNAPSHOT_WRITE",
            path.display(),
            Sha256::digest(rendered.as_bytes())
        );
    }
    assert_eq!(
        format!("{:x}", Sha256::digest(GOLDEN.as_bytes())),
        SLICE_TWENTY_SNAPSHOT_SHA256,
        "the golden file changed without the reviewed digest pin"
    );
    assert_eq!(rendered, GOLDEN, "slice-20 snapshots drifted");
}
