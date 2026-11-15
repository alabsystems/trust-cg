// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! Slice 17 of the x86-64 source-bound body theorem: private stack accesses
//! at a non-constant offset (ruling OD-183) and the dead bytes a cut point
//! leaves out (ruling OD-184).
//!
//! Fixtures are real: LIR from the trust-ir adapter, the machine stream from
//! the real x86-64 instruction selector (`super::select`). Every test here
//! runs without a solver (the `x86_source_bound_body::tests::slice17::`
//! library gate); the replay on AY and Clean is in `slice17_qualification`.

use super::slice5::describe;
use super::slice6::describe_lir;
use super::slice9::{dag_holds_on_samples, dag_refuted_on_samples};
use super::slice12::never_credited;
use super::slice22::fixture_owner;
use super::*;
use trust_ir::{ICmpOp, Ty};

/// Slice-17 fixture shapes: each a source with an indexed private access.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum IndexShape {
    /// `fn(b: u8) -> u16 { lo[(b >> 4) as usize] | hi[(b & 15) as usize] << 8 }`
    /// over two 16-byte local digit tables (`escape::hex_escape`): the
    /// index's own range bounds it, no guard.
    NibbleTable,
    /// `fn(i: u64) -> u8 { T[i] }`, `T: [u8; 16]`, behind rustc's bounds
    /// check (the panic path a trap): a guard bound.
    BoundsCheckedTable,
    /// `fn(i: u64, x: u32) -> u32 { a[i] }`, `a: [u32; 8]` with `a[k] = x +
    /// k`: the `Imul` by 4 of the index (an `imul` by a constant register),
    /// alignment modulus 4.
    ScaledLoadU32,
    /// `fn(i: u64, x: u64) -> u64 { t[i].0 + t[i].1 }`, `t: [(u64, u64); 3]`:
    /// stride 16 and the base offsets 0 and 8 (`Big8x3::mul_pow5`'s table).
    PairTableFields,
    /// `fn(n: u64, x: u32) -> u32 { a = [0; 40]; i = 0; while i < 40 && i < n
    /// { a[i] = x; i += 1 } a[0] }`: the candidate bytes of a store in a loop
    /// are header bytes (`Big32x40::from_u64`).
    IndexedStoreInLoop,
    /// `fn(i: u64, x: u32) -> u32 { a = [0, 1, 2, 3]; a[i] = x; a[0] + a[1] }`:
    /// the update leaves the bytes it does not select as they were.
    StoreThenConstRead,
    /// `fn(i: u64, j: u64, x: u32) -> u32 { a = [10, 11, 12, 13]; a[i] = x;
    /// a[j] }`: a select over updated bytes, two offsets.
    StoreThenIndexedRead,
    /// `fn(n: u64) -> u64 { buf: [u8; 8]; curr = 8; while curr != 0 { curr -=
    /// 1; write(&mut buf[curr], n as u8) } finish(&buf, curr) }`: the indexed
    /// call argument (`slot{s} + o`), the escape at the call, the observation
    /// at the next (`fmt::num`'s `MaybeUninit::write`).
    IndexedCallArgument,
    /// `fn(i: u64, x: u32) -> u64 { a: [u32; 40]; fill(&mut a); a[i] = x;
    /// sum(&a) }`: call-defined candidate bytes.
    FilledThenIndexed,
    /// `fn(rhs: [u8; 4]) -> u32 { c = rhs (copied byte by byte); for i in
    /// 0..4 { out[i] = c[i] & 0x0f } u32(out) }`: the aggregate parameter's
    /// bytes (slice 8) through a local copy, the `Ipv4Addr` operators' shape.
    OctetsZip,
    /// `fn(i: u64, x: u8) -> u8 { buf: [u8; 8]; buf[0..4] = x; buf[i] }` for
    /// `i < 4`: the never-selected candidates read the frame's initial bytes.
    PartlyWritten,
    /// `fn(i: u64) -> f64 { t: [f64; 32] = [0.0, 1.0, ..]; t[i & 31] }`: a
    /// `movsd` load, a float bit pattern, a mask bound.
    F64Table,
    /// `fn(i: u64, x: u8) -> u8 { a: [[u8; 3]; 4]; a[k][2] = x + k; a[i][2]
    /// }`: the `Imul` by 3 (modulus 1), whatever the selector emits for it.
    ScaleByThree,
    /// `fn(b: u8) -> u8 { T[b as usize] }`, `T: [u8; 256]`: the `movzx` of
    /// the index; 256 candidates.
    NarrowIndex,
    /// `fmt::num`'s loop: `&buf[..]` rebuilt as a (pointer, length) pair in a
    /// slot each iteration, its length read back, the digit written through
    /// an indexed argument: the pair's bytes are dead at the header (OD-184).
    SliceTempInLoop,
    /// `fn(i: u64, c: u64) -> u8 { p = &T[i]; y = if c != 0 { 1 } else { 2 };
    /// *p + y }`: an indexed address live across a join (kept there, never a
    /// joined term).
    IndexedAcrossJoin,
    /// OD-185 and slice 17: `fn(i: u64, x: u64) -> u64 { a: [u64; 4]; a[k]
    /// = x + k; a[i] }` behind rustc's bounds check, every element addressed
    /// by LIR `ArrayGep` (`a.gep[i, 0]`): stride 8, the selector's `lea [b +
    /// i*8]`.
    ArrayGepTable,
    /// `a: [[u8; 3]; 4]`, `a[k][0] = x + k; a[i][0]`: stride 3, the
    /// selector's `lea [b + i*2]; add i`.
    ArrayGepStride3,
    /// `a: [[u32; 3]; 4]`, `a[k][0] = x + k; a[i][0]`: stride 12, the
    /// selector's `imul i, 12; add b`, modulus 4.
    ArrayGepStride12,
    /// `a: [u64; 4] = [x, x + 1, x + 2, x + 3]; a[i] = 7; a[0] + a[3]`:
    /// a store through a variable `ArrayGep` updating the candidates' bytes.
    ArrayGepStore,
}

/// Every slice-17 fixture shape the owner states.
pub(crate) const SLICE_SEVENTEEN: [IndexShape; 20] = [
    IndexShape::NibbleTable,
    IndexShape::BoundsCheckedTable,
    IndexShape::ScaledLoadU32,
    IndexShape::PairTableFields,
    IndexShape::IndexedStoreInLoop,
    IndexShape::StoreThenConstRead,
    IndexShape::StoreThenIndexedRead,
    IndexShape::IndexedCallArgument,
    IndexShape::FilledThenIndexed,
    IndexShape::OctetsZip,
    IndexShape::PartlyWritten,
    IndexShape::F64Table,
    IndexShape::ScaleByThree,
    IndexShape::NarrowIndex,
    IndexShape::SliceTempInLoop,
    IndexShape::IndexedAcrossJoin,
    IndexShape::ArrayGepTable,
    IndexShape::ArrayGepStride3,
    IndexShape::ArrayGepStride12,
    IndexShape::ArrayGepStore,
];

/// Variants of the shapes the rules must refuse rather than state.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum IndexVariant {
    /// `SliceTempInLoop` with the pair's pointer half read back at the top
    /// of the loop body: live at the header, still refused by name (slice
    /// 13's rule).
    LiveSliceTemp,
    /// `BoundsCheckedTable` with the guard `i <= 16` (hand-built LIR): out
    /// of bounds on a defined path at `i = 16`.
    OffByOneGuard,
    /// `BoundsCheckedTable` with no guard: unbounded (`IndexedUnbounded`).
    Unbounded,
    /// The `fmt::num` loop with the pointer half stored before the loop too
    /// and read back after the length each iteration (dead at the header):
    /// the stale-pointer refutation's source.
    PairReadBack,
    /// `BoundsCheckedTable` over a table of one repeated byte: a machine
    /// access that reads the wrong byte of it reads the same value, so only
    /// an in-bounds claim tells.
    UniformTable,
    /// `UniformTable` with the guard `i <= 16`: only the source's in-bounds
    /// claim tells.
    UniformOffByOne,
    /// `a: [u32; 8]` of one repeated value, `a[i]` for `i < 4`: only the
    /// machine's congruence tells a misaligned read.
    UniformScaled,
    /// `a: [bool; 4]` with `a[0..3] = b` (`a[3]` unwritten), `a[i]` for `i <
    /// 3`: a candidate no `bool` store wrote, refused by name.
    BoolTable,
    /// `ArrayGepTable` with the guard `i < 25`: `i + 8 <= 32` holds, `8i + 8
    /// <= 32` does not (the guard counts bytes, the index elements), so the
    /// bound finder, which scales the index by the element stride, refuses
    /// it (`IndexedUnbounded`).
    ArrayGepByteBound,
    /// `a: [*const u64; 4]; fill(&mut a); *a[i]`: the loaded pointer may
    /// derive from the escaped slot (slice 15), so the access through it
    /// observes the slot.
    IndexedTaint,
}

trait ShapeName: std::fmt::Debug {
    fn name(&self) -> String {
        let name = format!("{self:?}");
        let mut snake = String::from("s17_");
        for (i, c) in name.chars().enumerate() {
            if c.is_ascii_uppercase() && i > 0 {
                snake.push('_');
            }
            snake.push(c.to_ascii_lowercase());
        }
        snake
    }
}
impl ShapeName for IndexShape {}
impl ShapeName for IndexVariant {}

type Builder<'a> = trust_ir_build::FunctionBuilder<'a>;
type V = trust_ir::value::ValueId;

/// Store the 16 bytes of `bytes` into the 16-byte local `table`, as two
/// 8-byte constants.
fn store_table16(f: &mut Builder<'_>, table: V, bytes: &[u8; 16]) {
    for half in 0..2 {
        let word = u64::from_le_bytes(bytes[8 * half..8 * half + 8].try_into().unwrap());
        let value = f.iconst(Ty::U64, i128::from(word));
        let at = if half == 0 {
            table
        } else {
            f.gep_byte_offset(table, 8)
        };
        f.store(Ty::U64, at, value);
    }
}

/// `if index < bound { ok } else { panic_bounds(index, bound); trap }`: the
/// ok block current.
fn bounds_check(f: &mut Builder<'_>, panic: trust_ir::FuncId, index: V, bound: u64, op: ICmpOp) {
    let (ok, fail) = (f.create_block(), f.create_block());
    let limit = f.iconst(Ty::U64, i128::from(bound));
    let test = f.icmp(op, Ty::U64, index, limit);
    f.condbr(test, ok, vec![], fail, vec![]);
    f.switch_to_block(fail);
    f.call_void(panic, vec![index, limit]);
    f.unreachable();
    f.switch_to_block(ok);
}

/// The LIR the trust-ir adapter produces for a slice-17 shape or variant.
fn slice17_function(
    name: String,
    shape: Option<IndexShape>,
    variant: Option<IndexVariant>,
) -> Function {
    use IndexShape::*;
    use IndexVariant::*;
    let mut builder = ModuleBuilder::new("x86_source_bound_body_slice17");
    let array = |builder: &mut ModuleBuilder, element: Ty, count: u64| {
        let element = builder.add_type(element);
        Ty::Array(element, count)
    };
    let u8x16 = array(&mut builder, Ty::U8, 16);
    let u8x8 = array(&mut builder, Ty::U8, 8);
    let u8x4 = array(&mut builder, Ty::U8, 4);
    let u8x3 = array(&mut builder, Ty::U8, 3);
    let u8x256 = array(&mut builder, Ty::U8, 256);
    let u32x8 = array(&mut builder, Ty::U32, 8);
    let u32x4 = array(&mut builder, Ty::U32, 4);
    let u32x40 = array(&mut builder, Ty::U32, 40);
    let u64x2 = array(&mut builder, Ty::U64, 2);
    let u64x4 = array(&mut builder, Ty::U64, 4);
    let u32x3 = array(&mut builder, Ty::U32, 3);
    let words3x4 = {
        let element = builder.add_type(u32x3.clone());
        Ty::Array(element, 4)
    };
    let f64x32 = array(&mut builder, Ty::F64, 32);
    let pairs = {
        let element = builder.add_type(u64x2.clone());
        Ty::Array(element, 3)
    };
    let rows3 = {
        let element = builder.add_type(u8x3.clone());
        Ty::Array(element, 4)
    };
    let ptr_u8 = Ty::PtrMut(Box::new(Ty::U8));
    let ptr_u32 = Ty::PtrMut(Box::new(Ty::U32));
    let ptr_u64 = Ty::PtrMut(Box::new(Ty::U64));
    let ptrs4 = {
        let element = builder.add_type(ptr_u64.clone());
        Ty::Array(element, 4)
    };
    let bools4 = {
        let element = builder.add_type(Ty::Bool);
        Ty::Array(element, 4)
    };
    let mut declare = |name: &str, params: Vec<Ty>, results: Vec<Ty>| {
        let ty = builder.add_func_type(params, results);
        builder.declare_function(name, ty)
    };
    let panic = declare("panic_bounds", vec![Ty::U64, Ty::U64], vec![]);
    let write = declare("write_digit", vec![ptr_u8.clone(), Ty::U8], vec![]);
    let finish = declare("finish", vec![ptr_u8.clone(), Ty::U64], vec![Ty::U64]);
    let fill = declare("fill", vec![ptr_u32.clone()], vec![]);
    let sum = declare("sum", vec![ptr_u32.clone()], vec![Ty::U64]);
    let peek = declare("peek", vec![ptr_u8.clone()], vec![]);
    let assume = declare("assume", vec![Ty::Bool], vec![]);
    let fill_ptrs = declare(
        "fill_ptrs",
        vec![Ty::PtrMut(Box::new(ptr_u64.clone()))],
        vec![],
    );
    let fmt_loop = matches!(
        (shape, variant),
        (Some(SliceTempInLoop), _) | (_, Some(LiveSliceTemp | PairReadBack))
    );
    let (params, results): (Vec<Ty>, Vec<Ty>) = match (shape, variant) {
        (Some(NibbleTable), _) => (vec![Ty::U8], vec![Ty::U16]),
        (Some(BoundsCheckedTable), _)
        | (_, Some(OffByOneGuard | Unbounded | UniformTable | UniformOffByOne)) => {
            (vec![Ty::U64], vec![Ty::U8])
        }
        (_, Some(UniformScaled)) => (vec![Ty::U64, Ty::U32], vec![Ty::U32]),
        (_, Some(BoolTable)) => (vec![Ty::U64, Ty::Bool], vec![Ty::Bool]),
        (_, Some(IndexedTaint)) => (vec![Ty::U64], vec![Ty::U64]),
        (Some(ScaledLoadU32 | StoreThenConstRead), _) => (vec![Ty::U64, Ty::U32], vec![Ty::U32]),
        (Some(PairTableFields), _) => (vec![Ty::U64, Ty::U64], vec![Ty::U64]),
        (Some(IndexedStoreInLoop), _) => (vec![Ty::U64, Ty::U32], vec![Ty::U32]),
        (Some(StoreThenIndexedRead), _) => (vec![Ty::U64, Ty::U64, Ty::U32], vec![Ty::U32]),
        (Some(IndexedCallArgument), _) => (vec![Ty::U64], vec![Ty::U64]),
        (Some(FilledThenIndexed), _) => (vec![Ty::U64, Ty::U32], vec![Ty::U64]),
        (Some(OctetsZip), _) => (vec![u8x4.clone()], vec![Ty::U32]),
        (Some(PartlyWritten), _) => (vec![Ty::U64, Ty::U8], vec![Ty::U8]),
        (Some(F64Table), _) => (vec![Ty::U64], vec![Ty::F64]),
        (Some(ScaleByThree), _) => (vec![Ty::U64, Ty::U8], vec![Ty::U8]),
        (Some(NarrowIndex), _) => (vec![Ty::U8], vec![Ty::U8]),
        (Some(IndexedAcrossJoin), _) => (vec![Ty::U64, Ty::U64], vec![Ty::U8]),
        (Some(ArrayGepTable | ArrayGepStore), _) | (_, Some(ArrayGepByteBound)) => {
            (vec![Ty::U64, Ty::U64], vec![Ty::U64])
        }
        (Some(ArrayGepStride3), _) => (vec![Ty::U64, Ty::U8], vec![Ty::U8]),
        (Some(ArrayGepStride12), _) => (vec![Ty::U64, Ty::U32], vec![Ty::U32]),
        _ if fmt_loop => (vec![Ty::U64], vec![Ty::U64]),
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
    let table16 = |f: &mut Builder<'_>| {
        let t = f.alloca(u8x16.clone());
        store_table16(f, t, b"0123456789abcdef");
        t
    };
    if fmt_loop {
        // buf: [u8; 8]; pair: [u64; 2] (`&buf[..]`); curr = 8.
        let buf = f.alloca(u8x8.clone());
        let pair = f.alloca(u64x2.clone());
        let eight = f.iconst(Ty::U64, 8);
        if variant == Some(PairReadBack) {
            f.store(ptr_u8.clone(), pair, buf);
        }
        let (header, body, store, exit) = (
            f.create_block(),
            f.create_block(),
            f.create_block(),
            f.create_block(),
        );
        let curr_param = f.add_block_param(header, Ty::U64);
        f.br(header, vec![eight]);
        f.switch_to_block(header);
        let curr = curr_param;
        let zero = f.iconst(Ty::U64, 0);
        let done = f.icmp(ICmpOp::Eq, Ty::U64, curr, zero);
        f.condbr(done, exit, vec![], body, vec![]);
        f.switch_to_block(body);
        if variant == Some(LiveSliceTemp) {
            // The pointer half read back before it is rebuilt: live.
            let stale = f.load(ptr_u8.clone(), pair);
            f.call_void(peek, vec![stale]);
        }
        let one = f.iconst(Ty::U64, 1);
        let next = f.sub(Ty::U64, curr, one);
        // `&buf[..]`: (pointer, length) into the pair, the length read back.
        f.store(ptr_u8.clone(), pair, buf);
        let len_at = f.gep_byte_offset(pair, 8);
        f.store(Ty::U64, len_at, eight);
        let len = f.load(Ty::U64, len_at);
        if variant == Some(PairReadBack) {
            let pointer = f.load(ptr_u8.clone(), pair);
            f.call_void(peek, vec![pointer]);
        }
        // `hint::assert_unchecked(curr < buf.len())`, then the bounds check
        // against the array's constant length.
        let below = f.icmp(ICmpOp::Ult, Ty::U64, next, len);
        f.call_void(assume, vec![below]);
        let limit = f.iconst(Ty::U64, 8);
        let inside = f.icmp(ICmpOp::Ult, Ty::U64, next, limit);
        let fail = f.create_block();
        f.condbr(inside, store, vec![], fail, vec![]);
        f.switch_to_block(fail);
        f.call_void(panic, vec![next, limit]);
        f.unreachable();
        f.switch_to_block(store);
        let digit = f.trunc(Ty::U64, Ty::U8, args[0]);
        let at = f.gep(Ty::U8, buf, vec![next]);
        f.call_void(write, vec![at, digit]);
        f.br(header, vec![next]);
        f.switch_to_block(exit);
        let out = f.call(finish, vec![buf, curr]);
        f.ret(vec![out]);
    } else {
        match (shape, variant) {
            (Some(NibbleTable), _) => {
                let lo = table16(&mut f);
                let hi = f.alloca(u8x16.clone());
                store_table16(&mut f, hi, b"0123456789ABCDEF");
                let four = f.iconst(Ty::U8, 4);
                let high = f.binop(trust_ir::BinOp::LShr, Ty::U8, args[0], four);
                let fifteen = f.iconst(Ty::U8, 15);
                let low = f.binop(trust_ir::BinOp::And, Ty::U8, args[0], fifteen);
                let i = f.zext(Ty::U8, Ty::U64, high);
                let j = f.zext(Ty::U8, Ty::U64, low);
                let at_i = f.gep(Ty::U8, lo, vec![i]);
                let a = f.load(Ty::U8, at_i);
                let at_j = f.gep(Ty::U8, hi, vec![j]);
                let b = f.load(Ty::U8, at_j);
                let a = f.zext(Ty::U8, Ty::U16, a);
                let b = f.zext(Ty::U8, Ty::U16, b);
                let eight = f.iconst(Ty::U16, 8);
                let b = f.binop(trust_ir::BinOp::Shl, Ty::U16, b, eight);
                let r = f.binop(trust_ir::BinOp::Or, Ty::U16, a, b);
                f.ret(vec![r]);
            }
            (Some(BoundsCheckedTable), _)
            | (_, Some(OffByOneGuard | Unbounded | UniformTable | UniformOffByOne)) => {
                let t = if matches!(variant, Some(UniformTable | UniformOffByOne)) {
                    let t = f.alloca(u8x16.clone());
                    store_table16(&mut f, t, &[0x41; 16]);
                    t
                } else {
                    table16(&mut f)
                };
                match variant {
                    Some(Unbounded) => {}
                    Some(OffByOneGuard | UniformOffByOne) => {
                        bounds_check(&mut f, panic, args[0], 16, ICmpOp::Ule)
                    }
                    _ => bounds_check(&mut f, panic, args[0], 16, ICmpOp::Ult),
                }
                let at = f.gep(Ty::U8, t, vec![args[0]]);
                let v = f.load(Ty::U8, at);
                f.ret(vec![v]);
            }
            (Some(ScaledLoadU32), _) => {
                let a = f.alloca(u32x8.clone());
                for k in 0..8u64 {
                    let c = f.iconst(Ty::U32, i128::from(k));
                    let v = f.add(Ty::U32, args[1], c);
                    let at = if k == 0 {
                        a
                    } else {
                        f.gep_byte_offset(a, 4 * k)
                    };
                    f.store(Ty::U32, at, v);
                }
                bounds_check(&mut f, panic, args[0], 8, ICmpOp::Ult);
                let at = f.gep(Ty::U32, a, vec![args[0]]);
                let v = f.load(Ty::U32, at);
                f.ret(vec![v]);
            }
            (Some(PairTableFields), _) => {
                let t = f.alloca(pairs.clone());
                for (k, field) in [
                    (0u64, None),
                    (1, Some(1)),
                    (2, Some(2)),
                    (3, None),
                    (4, None),
                    (5, Some(3)),
                ] {
                    let v = match field {
                        None => args[1],
                        Some(c) => f.iconst(Ty::U64, c),
                    };
                    let at = if k == 0 {
                        t
                    } else {
                        f.gep_byte_offset(t, 8 * k)
                    };
                    f.store(Ty::U64, at, v);
                }
                bounds_check(&mut f, panic, args[0], 3, ICmpOp::Ult);
                let element = f.gep(u64x2.clone(), t, vec![args[0]]);
                let a = f.load(Ty::U64, element);
                let second = f.gep_byte_offset(element, 8);
                let b = f.load(Ty::U64, second);
                let r = f.add(Ty::U64, a, b);
                f.ret(vec![r]);
            }
            (Some(IndexedStoreInLoop), _) => {
                let a = f.alloca(u32x40.clone());
                let zero8 = f.iconst(Ty::U8, 0);
                let size = f.iconst(Ty::U64, 160);
                f.memset(a, zero8, size);
                let zero = f.iconst(Ty::U64, 0);
                let (header, test, body, exit) = (
                    f.create_block(),
                    f.create_block(),
                    f.create_block(),
                    f.create_block(),
                );
                let i = f.add_block_param(header, Ty::U64);
                f.br(header, vec![zero]);
                f.switch_to_block(header);
                let forty = f.iconst(Ty::U64, 40);
                let inside = f.icmp(ICmpOp::Ult, Ty::U64, i, forty);
                f.condbr(inside, test, vec![], exit, vec![]);
                f.switch_to_block(test);
                let more = f.icmp(ICmpOp::Ult, Ty::U64, i, args[0]);
                f.condbr(more, body, vec![], exit, vec![]);
                f.switch_to_block(body);
                let at = f.gep(Ty::U32, a, vec![i]);
                f.store(Ty::U32, at, args[1]);
                let one = f.iconst(Ty::U64, 1);
                let next = f.add(Ty::U64, i, one);
                f.br(header, vec![next]);
                f.switch_to_block(exit);
                let first = f.load(Ty::U32, a);
                f.ret(vec![first]);
            }
            (Some(StoreThenConstRead | StoreThenIndexedRead), _) => {
                let a = f.alloca(u32x4.clone());
                let start = if shape == Some(StoreThenConstRead) {
                    0
                } else {
                    10
                };
                for k in 0..4u64 {
                    let c = f.iconst(Ty::U32, i128::from(start + k));
                    let at = if k == 0 {
                        a
                    } else {
                        f.gep_byte_offset(a, 4 * k)
                    };
                    f.store(Ty::U32, at, c);
                }
                let x = *args.last().unwrap();
                bounds_check(&mut f, panic, args[0], 4, ICmpOp::Ult);
                if shape == Some(StoreThenIndexedRead) {
                    bounds_check(&mut f, panic, args[1], 4, ICmpOp::Ult);
                }
                let at = f.gep(Ty::U32, a, vec![args[0]]);
                f.store(Ty::U32, at, x);
                if shape == Some(StoreThenConstRead) {
                    let first = f.load(Ty::U32, a);
                    let at1 = f.gep_byte_offset(a, 4);
                    let second = f.load(Ty::U32, at1);
                    let r = f.add(Ty::U32, first, second);
                    f.ret(vec![r]);
                } else {
                    let at = f.gep(Ty::U32, a, vec![args[1]]);
                    let v = f.load(Ty::U32, at);
                    f.ret(vec![v]);
                }
            }
            (Some(IndexedCallArgument), _) => {
                let buf = f.alloca(u8x8.clone());
                let eight = f.iconst(Ty::U64, 8);
                let (header, body, store, exit) = (
                    f.create_block(),
                    f.create_block(),
                    f.create_block(),
                    f.create_block(),
                );
                let curr = f.add_block_param(header, Ty::U64);
                f.br(header, vec![eight]);
                f.switch_to_block(header);
                let zero = f.iconst(Ty::U64, 0);
                let done = f.icmp(ICmpOp::Eq, Ty::U64, curr, zero);
                f.condbr(done, exit, vec![], body, vec![]);
                f.switch_to_block(body);
                let one = f.iconst(Ty::U64, 1);
                let next = f.sub(Ty::U64, curr, one);
                let limit = f.iconst(Ty::U64, 8);
                let inside = f.icmp(ICmpOp::Ult, Ty::U64, next, limit);
                let fail = f.create_block();
                f.condbr(inside, store, vec![], fail, vec![]);
                f.switch_to_block(fail);
                f.call_void(panic, vec![next, limit]);
                f.unreachable();
                f.switch_to_block(store);
                let digit = f.trunc(Ty::U64, Ty::U8, args[0]);
                let at = f.gep(Ty::U8, buf, vec![next]);
                f.call_void(write, vec![at, digit]);
                f.br(header, vec![next]);
                f.switch_to_block(exit);
                let out = f.call(finish, vec![buf, curr]);
                f.ret(vec![out]);
            }
            (Some(FilledThenIndexed), _) => {
                let a = f.alloca(u32x40.clone());
                f.call_void(fill, vec![a]);
                bounds_check(&mut f, panic, args[0], 40, ICmpOp::Ult);
                let at = f.gep(Ty::U32, a, vec![args[0]]);
                f.store(Ty::U32, at, args[1]);
                let r = f.call(sum, vec![a]);
                f.ret(vec![r]);
            }
            (Some(OctetsZip), _) => {
                let copy = f.alloca(u8x4.clone());
                let out = f.alloca(u8x4.clone());
                for k in 0..4u32 {
                    let byte = f.extract_field(Ty::U8, args[0], k);
                    let at = if k == 0 {
                        copy
                    } else {
                        f.gep_byte_offset(copy, u64::from(k))
                    };
                    f.store(Ty::U8, at, byte);
                }
                let zero = f.iconst(Ty::U64, 0);
                let (header, body, exit) = (f.create_block(), f.create_block(), f.create_block());
                let i = f.add_block_param(header, Ty::U64);
                f.br(header, vec![zero]);
                f.switch_to_block(header);
                let four = f.iconst(Ty::U64, 4);
                let inside = f.icmp(ICmpOp::Ult, Ty::U64, i, four);
                f.condbr(inside, body, vec![], exit, vec![]);
                f.switch_to_block(body);
                let from = f.gep(Ty::U8, copy, vec![i]);
                let byte = f.load(Ty::U8, from);
                let mask = f.iconst(Ty::U8, 0x0f);
                let masked = f.binop(trust_ir::BinOp::And, Ty::U8, byte, mask);
                let to = f.gep(Ty::U8, out, vec![i]);
                f.store(Ty::U8, to, masked);
                let one = f.iconst(Ty::U64, 1);
                let next = f.add(Ty::U64, i, one);
                f.br(header, vec![next]);
                f.switch_to_block(exit);
                let word = f.load(Ty::U32, out);
                f.ret(vec![word]);
            }
            (Some(PartlyWritten), _) => {
                let buf = f.alloca(u8x8.clone());
                for k in 0..4u64 {
                    let at = if k == 0 {
                        buf
                    } else {
                        f.gep_byte_offset(buf, k)
                    };
                    f.store(Ty::U8, at, args[1]);
                }
                bounds_check(&mut f, panic, args[0], 4, ICmpOp::Ult);
                let at = f.gep(Ty::U8, buf, vec![args[0]]);
                let v = f.load(Ty::U8, at);
                f.ret(vec![v]);
            }
            (Some(F64Table), _) => {
                let t = f.alloca(f64x32.clone());
                for k in 0..32u64 {
                    let c = f.fconst(Ty::F64, k as f64);
                    let at = if k == 0 {
                        t
                    } else {
                        f.gep_byte_offset(t, 8 * k)
                    };
                    f.store(Ty::F64, at, c);
                }
                let mask = f.iconst(Ty::U64, 31);
                let i = f.binop(trust_ir::BinOp::And, Ty::U64, args[0], mask);
                let at = f.gep(Ty::F64, t, vec![i]);
                let v = f.load(Ty::F64, at);
                f.ret(vec![v]);
            }
            (Some(ScaleByThree), _) => {
                let a = f.alloca(rows3.clone());
                for k in 0..4u64 {
                    let c = f.iconst(Ty::U8, i128::from(k));
                    let v = f.add(Ty::U8, args[1], c);
                    let at = f.gep_byte_offset(a, 3 * k + 2);
                    f.store(Ty::U8, at, v);
                }
                bounds_check(&mut f, panic, args[0], 4, ICmpOp::Ult);
                let row = f.gep(u8x3.clone(), a, vec![args[0]]);
                let at = f.gep_byte_offset(row, 2);
                let v = f.load(Ty::U8, at);
                f.ret(vec![v]);
            }
            (Some(NarrowIndex), _) => {
                let t = f.alloca(u8x256.clone());
                for k in 0..32u64 {
                    let word = (0..8u64).fold(0u64, |word, b| word | ((8 * k + b) << (8 * b)));
                    let c = f.iconst(Ty::U64, i128::from(word));
                    let at = if k == 0 {
                        t
                    } else {
                        f.gep_byte_offset(t, 8 * k)
                    };
                    f.store(Ty::U64, at, c);
                }
                let i = f.zext(Ty::U8, Ty::U64, args[0]);
                let at = f.gep(Ty::U8, t, vec![i]);
                let v = f.load(Ty::U8, at);
                f.ret(vec![v]);
            }
            (Some(IndexedAcrossJoin), _) => {
                let t = table16(&mut f);
                bounds_check(&mut f, panic, args[0], 16, ICmpOp::Ult);
                let at = f.gep(Ty::U8, t, vec![args[0]]);
                let (then, other, join) = (f.create_block(), f.create_block(), f.create_block());
                let y = f.add_block_param(join, Ty::U8);
                let zero = f.iconst(Ty::U64, 0);
                let set = f.icmp(ICmpOp::Ne, Ty::U64, args[1], zero);
                f.condbr(set, then, vec![], other, vec![]);
                f.switch_to_block(then);
                let one = f.iconst(Ty::U8, 1);
                f.br(join, vec![one]);
                f.switch_to_block(other);
                let two = f.iconst(Ty::U8, 2);
                f.br(join, vec![two]);
                f.switch_to_block(join);
                let v = f.load(Ty::U8, at);
                let r = f.add(Ty::U8, v, y);
                f.ret(vec![r]);
            }
            (_, Some(UniformScaled)) => {
                let a = f.alloca(u32x8.clone());
                for k in 0..8u64 {
                    let at = if k == 0 {
                        a
                    } else {
                        f.gep_byte_offset(a, 4 * k)
                    };
                    f.store(Ty::U32, at, args[1]);
                }
                bounds_check(&mut f, panic, args[0], 4, ICmpOp::Ult);
                let at = f.gep(Ty::U32, a, vec![args[0]]);
                let v = f.load(Ty::U32, at);
                f.ret(vec![v]);
            }
            (_, Some(BoolTable)) => {
                let a = f.alloca(bools4.clone());
                for k in 0..3u64 {
                    let at = if k == 0 { a } else { f.gep_byte_offset(a, k) };
                    f.store(Ty::Bool, at, args[1]);
                }
                bounds_check(&mut f, panic, args[0], 3, ICmpOp::Ult);
                let at = f.gep(Ty::Bool, a, vec![args[0]]);
                let v = f.load(Ty::Bool, at);
                f.ret(vec![v]);
            }
            (_, Some(IndexedTaint)) => {
                let a = f.alloca(ptrs4.clone());
                f.call_void(fill_ptrs, vec![a]);
                bounds_check(&mut f, panic, args[0], 4, ICmpOp::Ult);
                let at = f.gep(ptr_u64.clone(), a, vec![args[0]]);
                let p = f.load(ptr_u64.clone(), at);
                let v = f.load(Ty::U64, p);
                f.ret(vec![v]);
            }
            (Some(ArrayGepTable | ArrayGepStride3 | ArrayGepStride12), _)
            | (_, Some(ArrayGepByteBound)) => {
                // `gep(element, a, [index, 0])`: the adapter's two
                // `ArrayGep`s of the element (trust-ir scales every index of
                // the list by the element's size), the second at the
                // constant 0; the element's first scalar is accessed.
                let (element, loaded, slot) = match shape {
                    Some(ArrayGepStride3) => (u8x3.clone(), Ty::U8, rows3.clone()),
                    Some(ArrayGepStride12) => (u32x3.clone(), Ty::U32, words3x4.clone()),
                    _ => (Ty::U64, Ty::U64, u64x4.clone()),
                };
                let bound = if variant == Some(ArrayGepByteBound) {
                    25
                } else {
                    4
                };
                let a = f.alloca(slot);
                let field = f.iconst(Ty::U64, 0);
                for k in 0..4i128 {
                    let index = f.iconst(Ty::U64, k);
                    let offset = f.iconst(loaded.clone(), k);
                    let v = f.add(loaded.clone(), args[1], offset);
                    let at = f.gep(element.clone(), a, vec![index, field]);
                    f.store(loaded.clone(), at, v);
                }
                bounds_check(&mut f, panic, args[0], bound, ICmpOp::Ult);
                let at = f.gep(element.clone(), a, vec![args[0], field]);
                let v = f.load(loaded.clone(), at);
                f.ret(vec![v]);
            }
            (Some(ArrayGepStore), _) => {
                let a = f.alloca(u64x4.clone());
                let zero = f.iconst(Ty::U64, 0);
                for k in 0..4i128 {
                    let index = f.iconst(Ty::U64, k);
                    let v = f.add(Ty::U64, args[1], index);
                    let at = f.gep(Ty::U64, a, vec![index, zero]);
                    f.store(Ty::U64, at, v);
                }
                bounds_check(&mut f, panic, args[0], 4, ICmpOp::Ult);
                let seven = f.iconst(Ty::U64, 7);
                let at = f.gep(Ty::U64, a, vec![args[0], zero]);
                f.store(Ty::U64, at, seven);
                let three = f.iconst(Ty::U64, 3);
                let first = f.gep(Ty::U64, a, vec![zero, zero]);
                let last = f.gep(Ty::U64, a, vec![three, zero]);
                let x = f.load(Ty::U64, first);
                let y = f.load(Ty::U64, last);
                let v = f.add(Ty::U64, x, y);
                f.ret(vec![v]);
            }
            other => unreachable!("{other:?}"),
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
    .unwrap_or_else(|error| panic!("{name}: fixture translates: {error:?}"))
    .into_iter()
    .map(|(function, _)| function)
    .find(|function| function.name == name)
    .unwrap_or_else(|| panic!("{name}: no translated function"))
}

pub(crate) fn slice17_lir(shape: IndexShape) -> Function {
    slice17_function(shape.name(), Some(shape), None)
}

pub(crate) fn slice17_variant(variant: IndexVariant) -> Function {
    slice17_function(variant.name(), None, Some(variant))
}

pub(crate) fn slice17_pair(shape: IndexShape) -> (Function, X86ISelFunction) {
    let source = slice17_lir(shape);
    let machine = select(&source, X86CallAbi::SystemV);
    (source, machine)
}

pub(crate) fn variant_pair(variant: IndexVariant) -> (Function, X86ISelFunction) {
    let source = slice17_variant(variant);
    let machine = select(&source, X86CallAbi::SystemV);
    (source, machine)
}

#[track_caller]
fn owner(source: &Function, machine: &X86ISelFunction, what: &str) -> ProofObligation {
    fixture_owner(source, machine)
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

/// The theorem's query as the replay renders it.
fn text(obligation: &ProofObligation) -> String {
    generate_smt2_query_raw(obligation, &replay_config())
}

/// Every in-bounds claim of a theorem: its Boolean conjuncts that are no
/// equation (each `(bvule ...)` or `(and (bvule ...) ...)`, possibly under
/// `(or (not C) X)`; slice 19's `cmp` spells `(bvule a b)` as `(not (bvult b
/// a))`), counted.
fn in_bounds_claims(obligation: &ProofObligation) -> usize {
    fn conjuncts(mut expr: &E) -> Vec<&E> {
        let mut terms = Vec::new();
        while let E::And { lhs, rhs } = expr {
            terms.push(lhs.as_ref());
            expr = rhs.as_ref();
        }
        terms.push(expr);
        terms
    }
    fn mentions_bvule(expr: &E) -> bool {
        let mut stack = vec![expr];
        while let Some(node) = stack.pop() {
            if matches!(node, E::BvUle { .. }) {
                return true;
            }
            if let E::Not { operand } = node
                && matches!(operand.as_ref(), E::BvUlt { .. })
            {
                return true;
            }
            node.for_each_child(&mut |child| stack.push(child));
        }
        false
    }
    conjuncts(&obligation.aarch64_expr)
        .into_iter()
        .flat_map(|claim| match claim {
            E::Or { rhs, .. } => conjuncts(rhs),
            other => vec![other],
        })
        .filter(|claim| !matches!(claim, E::Eq { .. }) && mentions_bvule(claim))
        .count()
}

// ---------------------------------------------------------------------------
// The exactness lemma (the one spelling both walks use)
// ---------------------------------------------------------------------------

/// The exactness lemma of the trusted select/update spelling, swept against a
/// concrete byte array: for every slot size up to 64 and the sizes 100, 128,
/// 255 and 256 (the class's largest table: a 256-arm low-bit select), width
/// 1, 2, 4 and 8 (and 0, a call argument), alignment modulus 1 to 16 and
/// residue, the claim
/// [`indexed::in_bounds`] holds exactly at the candidates
/// ([`indexed::candidates`]) of every offset tried (each candidate, its
/// neighbours, offsets past the slot and wrapped ones), and where it holds
/// [`indexed::select`] is the bytes at the offset and [`indexed::update`]
/// the store there.
#[test]
fn the_indexed_spelling_is_exact_on_every_candidate() {
    use crate::smt::{EvalEnv, EvalResult};
    let bytes: Vec<u8> = (0..256u32).map(|k| (k * 37 + 11) as u8).collect();
    let stored: u64 = 0xa1b2_c3d4_e5f6_0718;
    let mut checked = 0usize;
    for size in (1..=64u32).chain([100, 128, 255, 256]) {
        for width in [0u32, 1, 2, 4, 8] {
            for modulus in [1u64, 2, 4, 8, 16] {
                for residue in 0..modulus {
                    let candidates = indexed::candidates(size, width, modulus, residue);
                    let offset = E::var("o", 64);
                    let claim = indexed::in_bounds(offset.clone(), size, width, modulus, residue);
                    // The select over the candidates' reads, each the
                    // bytes at that offset (a call argument reads none:
                    // checked through the claim alone).
                    let select = (width > 0 && !candidates.is_empty()).then(|| {
                        indexed::select(
                            &offset,
                            candidates
                                .iter()
                                .map(|k| {
                                    let value = (0..width).rev().fold(0u64, |value, b| {
                                        (value << 8)
                                            | u64::from(bytes[(*k + i64::from(b)) as usize])
                                    });
                                    (*k, E::bv_const(value, 8 * width))
                                })
                                .collect(),
                        )
                    });
                    let mut tried: Vec<u64> = (0..u64::from(size) + 10).collect();
                    tried.extend([u64::MAX, u64::MAX - 1, 1 << 63, (1 << 32) + 1]);
                    for o in tried {
                        let mut env = EvalEnv::default();
                        env.insert("o".into(), o);
                        let holds = matches!(claim.eval(&env), EvalResult::Bool(true));
                        let candidate = o <= u64::from(size) && candidates.contains(&(o as i64));
                        assert_eq!(
                            holds, candidate,
                            "size {size} width {width} modulus {modulus} residue {residue} \
                             offset {o}"
                        );
                        if !holds || width == 0 {
                            continue;
                        }
                        let expected = (0..width).rev().fold(0u64, |value, b| {
                            (value << 8) | u64::from(bytes[(o + u64::from(b)) as usize])
                        });
                        assert!(
                            matches!(select.as_ref().unwrap().eval(&env), EvalResult::Bv(v) if v == expected),
                            "select: size {size} width {width} modulus {modulus} offset {o}"
                        );
                        for position in 0..i64::from(size) {
                            let arms = indexed::covering(&candidates, width, position);
                            let update = indexed::update(
                                &offset,
                                arms.iter()
                                    .map(|(k, byte)| {
                                        (*k, E::bv_const((stored >> (8 * byte)) & 0xff, 8))
                                    })
                                    .collect(),
                                E::bv_const(u64::from(bytes[position as usize]), 8),
                            );
                            let inside =
                                (o as i64) <= position && position < o as i64 + i64::from(width);
                            let expected = if inside {
                                (stored >> (8 * (position - o as i64))) & 0xff
                            } else {
                                u64::from(bytes[position as usize])
                            };
                            assert!(
                                matches!(update.eval(&env), EvalResult::Bv(v) if v == expected),
                                "update: size {size} width {width} modulus {modulus} offset {o} \
                                 position {position}"
                            );
                        }
                        checked += 1;
                    }
                }
            }
        }
    }
    assert!(checked > 10_000, "{checked} in-bounds offsets checked");
}

/// An indexed address's offset term ([`IndexedAddr::offset`]) is `base +
/// delta * stride` at 64 bits, wrapping, for every stride spelling (1, a
/// power of two, OD-185's `v * (s - 1) + v` for 3, 5 and 9, a plain product
/// otherwise), and its alignment modulus ([`indexed::stride_modulus`])
/// divides every such offset minus the base.
#[test]
fn the_indexed_offset_term_is_the_scaled_sum_for_every_stride() {
    use crate::smt::{EvalEnv, EvalResult};
    let mut seed = 0x243f_6a88_85a3_08d3u64;
    for stride in [1u64, 2, 3, 4, 5, 6, 8, 9, 12, 16, 24, 40, 48] {
        for base in [0i64, 3, -8, 1 << 20] {
            let address = IndexedAddr {
                slot: 0,
                base,
                delta: Value(0),
                stride,
                modulus: indexed::stride_modulus(stride, 1),
            };
            let term = address.offset(E::var("d", 64));
            for _ in 0..200 {
                seed = seed.wrapping_mul(6_364_136_223_846_793_005).wrapping_add(1);
                let d = seed ^ (seed >> 29);
                let mut env = EvalEnv::default();
                env.insert("d".into(), d);
                let expected = d.wrapping_mul(stride).wrapping_add(base as u64);
                assert!(
                    matches!(term.eval(&env), EvalResult::Bv(v) if v == expected),
                    "stride {stride} base {base} d {d:#x}"
                );
                assert_eq!(
                    expected.wrapping_sub(base as u64) & (address.modulus - 1),
                    0,
                    "stride {stride}: the modulus divides the scaled index"
                );
            }
        }
    }
    assert_eq!(indexed::stride_modulus(24, 4), 32);
    assert_eq!(indexed::stride_modulus(1 << 40, 1 << 20), 1 << 32);
}

/// The bit-move substitution of slice 17's spelling
/// ([`split::substitute_bit_moves`], with its extract identities): a
/// definition that only moves bits of variables is replaced by its term, one
/// that computes is kept, and the claims mean what they meant on every input
/// tried (each definition evaluated in order, the original against the
/// substituted), an extract of a zero extension and of a constant among
/// them.
#[test]
fn bit_moves_are_substituted_exactly() {
    use crate::smt::{EvalEnv, EvalResult};
    let x = E::var("x", 64);
    let y = E::var("y", 64);
    let definitions = vec![
        ("p1".to_owned(), x.clone().extract(31, 0)),
        ("m0".to_owned(), x.clone().extract(31, 0).zero_ext(32)),
        ("s3".to_owned(), y.clone().bvmul(E::bv_const(4, 64))),
        (
            "b".to_owned(),
            E::var("m0", 64)
                .extract(7, 0)
                .concat(E::var("p1", 32).extract(15, 8)),
        ),
        ("t".to_owned(), E::var("s3", 64).bvadd(E::var("m0", 64))),
    ];
    // Each claim separately, so a false one cannot mask another.
    let claims = [
        E::var("p1", 32)
            .extract(7, 0)
            .eq_expr(E::var("m0", 64).extract(31, 0).extract(7, 0)),
        E::var("b", 16).eq_expr(E::var("t", 64).extract(15, 0)),
        E::var("m0", 64)
            .extract(23, 16)
            .eq_expr(E::var("y", 64).extract(23, 16)),
        E::var("m0", 64)
            .extract(47, 40)
            .eq_expr(E::var("t", 64).extract(47, 40)),
        E::bv_const(0x1234_5678_9abc_def0, 64)
            .extract(23, 16)
            .eq_expr(E::var("p1", 32).extract(15, 8)),
    ];
    let evaluate = |definitions: &[(String, E)], claim: &E, x: u64, y: u64| {
        let mut env = EvalEnv::default();
        env.insert("x".into(), x);
        env.insert("y".into(), y);
        for (name, expr) in definitions {
            let EvalResult::Bv(value) = expr.eval(&env) else {
                panic!("{name} evaluates to a bit-vector")
            };
            env.insert(name.clone(), value);
        }
        matches!(claim.eval(&env), EvalResult::Bool(true))
    };
    let mut differ = 0;
    for claim in &claims {
        let (kept, moved) = split::substitute_bit_moves(definitions.clone(), claim.clone());
        assert_eq!(
            kept.iter()
                .map(|(name, _)| name.as_str())
                .collect::<Vec<_>>(),
            ["s3", "t"],
            "the bit moves are substituted, the computations kept"
        );
        let mut seed = 0x9e37_79b9_7f4a_7c15u64;
        let (mut holds, mut fails) = (0, 0);
        for round in 0..2000u64 {
            seed = seed.wrapping_mul(6_364_136_223_846_793_005).wrapping_add(1);
            // Every fifth input makes the stored byte agree with `y`.
            let x = seed;
            let y = if round % 5 == 0 {
                x
            } else {
                seed.rotate_left(17) ^ 0xff
            };
            let original = evaluate(&definitions, claim, x, y);
            assert_eq!(
                evaluate(&kept, &moved, x, y),
                original,
                "{claim}: x {x:#x} y {y:#x}"
            );
            if original {
                holds += 1;
            } else {
                fails += 1;
            }
        }
        differ += usize::from(holds > 0 && fails > 0);
    }
    assert!(
        differ >= 2,
        "some claims both hold and fail on the inputs tried"
    );
}

// ---------------------------------------------------------------------------
// The fixtures (no solver)
// ---------------------------------------------------------------------------

/// Every slice-17 shape builds a theorem with in-bounds claims on both sides
/// that holds on samples.
#[test]
fn owner_builds_every_slice_seventeen_shape() {
    for shape in SLICE_SEVENTEEN {
        let (source, machine) = slice17_pair(shape);
        let obligation = owner(&source, &machine, &format!("{shape:?}"));
        // Both sides' claims as built (slice 18's spelling: slice 19's
        // states two claims that became one term once, `(and a a)` being
        // `a`).
        let built = with_normal_groups(normal::Groups::NONE, || {
            owner(&source, &machine, &format!("{shape:?}"))
        });
        assert!(
            in_bounds_claims(&built) >= 2,
            "{shape:?}: states in-bounds claims on both sides\n{}",
            text(&built)
        );
        assert!(
            dag_holds_on_samples(&obligation),
            "{shape:?}: the theorem of the selector's stream holds\n{}{}",
            describe_lir(&source),
            describe(&machine)
        );
    }
}

/// A body without an indexed access keeps its theorem: no in-bounds claim,
/// no indexed byte (every earlier slice's golden digest is checked by its own
/// gate; this checks the slice-17 rules add nothing to such a body).
#[test]
fn a_body_without_an_indexed_access_states_no_in_bounds_claim() {
    for shape in super::slice12::SLICE_TWELVE {
        let (source, machine) = super::slice12::slice12_pair(shape);
        let Ok(owner) = fixture_owner(&source, &machine) else {
            continue;
        };
        assert_eq!(in_bounds_claims(owner.obligation()), 0, "{shape:?}");
        assert!(!text(owner.obligation()).contains("ix0"), "{shape:?}");
    }
}

/// The fmt::num shape is stated over its regions with the pair's bytes dead
/// at the header (no header input for them, no refusal), the indexed
/// argument observed as the slot's address plus its offset on both sides.
/// (The value-numbered spelling makes the two sides' argument items one
/// term, an identity it drops; the plain spelling states them.)
#[test]
fn the_slice_temp_bytes_are_dead_at_the_header_and_the_argument_is_observed() {
    let (source, machine) = slice17_pair(IndexShape::SliceTempInLoop);
    let obligation = owner(&source, &machine, "SliceTempInLoop");
    let plain = theorem_with_path_encoding(
        &source,
        &machine,
        SYSV,
        PathEncoding {
            value_number: ValueNumbering::Off,
            ..PathEncoding::CANONICAL
        },
    )
    .expect("the plain spelling");
    for (spelling, text) in [("canonical", text(&obligation)), ("plain", text(&plain))] {
        // The pair is slot 1: none of its bytes is a header input.
        assert!(
            !text.contains("b1o0"),
            "{spelling}: the pair's pointer half is no header input"
        );
        assert!(
            !text.contains("b1o8"),
            "{spelling}: the pair's length half is no header input"
        );
    }
    assert!(
        text(&plain).contains("slot0"),
        "the indexed argument is slot0 plus its offset"
    );
    let body = admitted_body(&source).expect("admitted");
    let loops = body.loops.as_ref().expect("a loop");
    let header = loops.headers.values().next().expect("a header");
    for offset in 0..16 {
        assert!(
            header.dead.contains(&(1, offset)),
            "byte {offset} of the pair is dead"
        );
    }
    assert!(
        !header.dead.iter().any(|(slot, _)| *slot == 0),
        "the buffer (escaped to the calls) is live"
    );
}

/// The pair's pointer half read back at the top of the loop body is live at
/// the header: slice 13's refusal of a header byte holding a stored address
/// stays, by name.
#[test]
fn a_live_stored_address_at_a_header_is_still_refused_by_name() {
    let (source, machine) = variant_pair(IndexVariant::LiveSliceTemp);
    let refusal = fixture_owner(&source, &machine).err().expect("refused");
    let text = refusal.to_string();
    assert!(
        text.contains("one of them a private stack address"),
        "{text}"
    );
}

/// An index no fact of its region bounds is refused (no claim), never
/// refuted; an off-by-one guard is refused too, and so is an `ArrayGep`
/// guarded in bytes rather than elements (the bound finder scales the
/// index by the element stride), while each theorem built without the
/// bound finder is refuted by the source's own in-bounds claim.
#[test]
fn an_unbounded_index_is_refused_and_its_claim_refutes_it() {
    for variant in [
        IndexVariant::Unbounded,
        IndexVariant::OffByOneGuard,
        IndexVariant::ArrayGepByteBound,
    ] {
        let (source, machine) = variant_pair(variant);
        let refusal = fixture_owner(&source, &machine)
            .err()
            .unwrap_or_else(|| panic!("{variant:?}: refused"));
        assert!(
            refusal.to_string().contains("IndexedUnbounded"),
            "{variant:?}: {refusal}"
        );
        let theorem = theorem_without_indexed_bounds(&source, &machine, SYSV)
            .unwrap_or_else(|refusal| panic!("{variant:?}: {refusal}"));
        assert!(
            dag_refuted_on_samples(&theorem),
            "{variant:?}: an out-of-bounds index is refuted by its in-bounds claim"
        );
    }
}

/// The byte liveness at a header: a byte some path reads before a store
/// overwrites it is live, any other dead; a slot that escapes is live
/// wherever a call follows; the selector's own slots are never dead.
#[test]
fn byte_liveness_is_conservative() {
    // The fmt::num shape: the pair (slot 1) is rebuilt before every read.
    let source = slice17_lir(IndexShape::SliceTempInLoop);
    let cfg = source_cfg(&source).expect("a control flow");
    let live = split::live_bytes(&source, &cfg);
    let header = cfg.loops[0].header;
    let dead = split::dead_bytes(&source, &live, header);
    assert!(
        (0..16).all(|offset| dead.contains(&(1, offset))),
        "{dead:?}"
    );
    assert!(!dead.iter().any(|(slot, _)| *slot == 0), "{dead:?}");
    // Read back first: live.
    let source = slice17_variant(IndexVariant::LiveSliceTemp);
    let cfg = source_cfg(&source).expect("a control flow");
    let live = split::live_bytes(&source, &cfg);
    let dead = split::dead_bytes(&source, &live, cfg.loops[0].header);
    assert!(
        (0..8).all(|offset| !dead.contains(&(1, offset))),
        "{dead:?}"
    );
    // Every slice-12 fixture's header: the slot counter, read each iteration
    // before the latch overwrites it, is live; the escaping slot too.
    for shape in [
        super::slice12::LoopShape::SlotCounter,
        super::slice12::LoopShape::EscapeLoop,
        super::slice12::LoopShape::SlotBound,
    ] {
        let source = super::slice12::slice12_lir(shape);
        let cfg = source_cfg(&source).expect("a control flow");
        let live = split::live_bytes(&source, &cfg);
        for lp in &cfg.loops {
            let dead = split::dead_bytes(&source, &live, lp.header);
            assert!(dead.is_empty(), "{shape:?}: {dead:?}");
        }
    }
}

// ---------------------------------------------------------------------------
// Wrong lowerings (no solver)
// ---------------------------------------------------------------------------

/// The ordinal of the n-th frame address plus a variable byte offset, in
/// walk order. Keep AddRR and unit-stride LeaSib in their actual ISA forms.
fn indexed_address(machine: &X86ISelFunction, n: usize) -> usize {
    let lea_slots: HashMap<u32, u32> = rows(machine)
        .into_iter()
        .filter_map(|(ordinal, _, _)| {
            let inst = inst(machine, ordinal);
            match (inst.opcode, inst.operands.as_slice()) {
                (X86Opcode::Lea, [O::VReg(d), O::MemAddr { base, disp: 0 }])
                    if matches!(base.as_ref(), O::StackSlot(_)) =>
                {
                    let O::StackSlot(slot) = base.as_ref() else {
                        unreachable!()
                    };
                    Some((d.id, *slot))
                }
                _ => None,
            }
        })
        .collect();
    // A register is a frame address when a `lea` of a slot or a copy of one
    // writes it.
    let mut frames: HashSet<u32> = lea_slots.keys().copied().collect();
    for (ordinal, _, _) in rows(machine) {
        let inst = inst(machine, ordinal);
        if let (X86Opcode::MovRR, [O::VReg(d), O::VReg(s)]) =
            (inst.opcode, inst.operands.as_slice())
            && frames.contains(&s.id)
        {
            frames.insert(d.id);
        }
    }
    // A register a `mov` of an immediate writes holds a constant (an `add`
    // of one to a frame address is a constant offset).
    let constants: HashSet<u32> = rows(machine)
        .into_iter()
        .filter_map(|(ordinal, _, _)| {
            let inst = inst(machine, ordinal);
            match (inst.opcode, inst.operands.as_slice()) {
                (X86Opcode::MovRI, [O::VReg(d), _]) => Some(d.id),
                _ => None,
            }
        })
        .collect();
    rows(machine)
        .into_iter()
        .map(|(ordinal, _, _)| ordinal)
        .filter(|ordinal| {
            let inst = inst(machine, *ordinal);
            super::memory::byte_address_inputs(inst).is_some_and(|(base, index)| {
                let frame_base = matches!(base, O::VReg(v) if frames.contains(&v.id));
                let frame_index = inst.opcode == X86Opcode::AddRR
                    && matches!(index, O::VReg(v) if frames.contains(&v.id));
                (frame_base || frame_index)
                    && ![base, index]
                        .iter()
                        .any(|operand| matches!(operand, O::VReg(v) if constants.contains(&v.id)))
            })
        })
        .nth(n)
        .unwrap_or_else(|| panic!("no indexed byte address #{n}\n{}", describe(machine)))
}

/// The walk ordinal of the scaled `lea` that forms a private slot's element
/// at a variable index (OD-185's `ArrayGep` at an index no `mov` of an
/// immediate defines).
fn variable_lea(machine: &X86ISelFunction) -> usize {
    let constants: HashSet<u32> = rows(machine)
        .into_iter()
        .filter_map(|(ordinal, _, _)| {
            let inst = inst(machine, ordinal);
            match (inst.opcode, inst.operands.as_slice()) {
                (X86Opcode::MovRI, [O::VReg(d), _]) => Some(d.id),
                _ => None,
            }
        })
        .collect();
    find(machine, X86Opcode::LeaSib)
        .into_iter()
        .find(|ordinal| {
            matches!(
                &inst(machine, *ordinal).operands[1],
                O::SibMemAddr { index, .. }
                    if matches!(index.as_ref(), O::VReg(v) if !constants.contains(&v.id))
            )
        })
        .unwrap_or_else(|| panic!("no variable-index lea\n{}", describe(machine)))
}

/// The scale of the scaled `lea` at walk ordinal `ordinal`.
fn set_scale(machine: &mut X86ISelFunction, ordinal: usize, to: u8) {
    let O::SibMemAddr { scale, .. } = &mut inst_mut(machine, ordinal).operands[1] else {
        panic!("a scaled lea")
    };
    *scale = to;
}

/// The first row after `after` with opcode `opcode`.
fn next_of(machine: &X86ISelFunction, after: usize, opcode: X86Opcode) -> usize {
    find(machine, opcode)
        .into_iter()
        .find(|ordinal| *ordinal > after)
        .unwrap_or_else(|| panic!("no {opcode:?} after {after}\n{}", describe(machine)))
}

/// The ordinal of the `MovRI` that loads constant `value` most recently
/// before `before`.
fn constant_before(machine: &X86ISelFunction, before: usize, value: i64) -> usize {
    find(machine, X86Opcode::MovRI)
        .into_iter()
        .rfind(|ordinal| *ordinal < before && inst(machine, *ordinal).operands[1] == O::Imm(value))
        .unwrap_or_else(|| panic!("no mov of {value} before {before}\n{}", describe(machine)))
}

/// Row `ordinal` given `opcode`, with that opcode's default flags.
fn set_opcode(machine: &mut X86ISelFunction, ordinal: usize, opcode: X86Opcode) {
    let inst = inst_mut(machine, ordinal);
    inst.opcode = opcode;
    inst.flags = opcode.default_flags();
}

/// The memory operand's displacement of row `ordinal` set to `disp`.
fn set_disp(machine: &mut X86ISelFunction, ordinal: usize, disp: i32) {
    for operand in &mut inst_mut(machine, ordinal).operands {
        if let O::MemAddr { disp: d, .. } = operand {
            *d = disp;
        }
    }
}

/// Wrong lowerings of slice-17 shapes, each refuted with a counterexample
/// (§4 of the design): a wrong scale, a wrong base slot, an index off by
/// one, a store to the wrong element, a store clobbering its neighbour, an
/// out-of-bounds source on a defined path (built without the bound finder),
/// a missing and a wrong extension of a narrow index, a misaligned offset, a
/// call argument one element off, and a load moved above the store it must
/// see. Each label, its source, its machine, and whether the theorem is built
/// without the bound finder.
pub(crate) fn slice_seventeen_refutations() -> Vec<(&'static str, Function, X86ISelFunction, bool)>
{
    use IndexShape::*;
    use X86Opcode as X;
    let mut cases = Vec::new();
    let mut case =
        |label: &'static str, shape: IndexShape, mutate: &dyn Fn(&mut X86ISelFunction)| {
            let (source, mut machine) = slice17_pair(shape);
            mutate(&mut machine);
            cases.push((label, source, machine, false));
        };
    case("a wrong scale (2 for a u32 element)", ScaledLoadU32, &|m| {
        let add = indexed_address(m, 0);
        let row = constant_before(m, add, 4);
        inst_mut(m, row).operands[1] = O::Imm(2);
    });
    case("a wrong base slot (the other table)", NibbleTable, &|m| {
        // The second table's indexed address formed from the first table's
        // frame register.
        let first = indexed_address(m, 0);
        let second = indexed_address(m, 1);
        let base = super::memory::byte_address_inputs(inst(m, first))
            .unwrap()
            .0
            .clone();
        super::memory::set_byte_address_base(m, second, base);
    });
    case(
        "an index off by one (the next element)",
        BoundsCheckedTable,
        &|m| {
            let add = indexed_address(m, 0);
            let load = next_of(m, add, X::MovzxRM8);
            set_disp(m, load, 1);
        },
    );
    case("a store to the wrong element", StoreThenIndexedRead, &|m| {
        let add = indexed_address(m, 0);
        let store = next_of(m, add, X::MovMR32);
        set_disp(m, store, -4);
    });
    case(
        "a store clobbering its neighbour (8 bytes for a u32)",
        StoreThenConstRead,
        &|m| {
            let add = indexed_address(m, 0);
            let store = next_of(m, add, X::MovMR32);
            // RSI still holds `x` in its low half (and the caller's bits above).
            set_opcode(m, store, X::MovMR);
            inst_mut(m, store).operands[1] = preg(RSI);
        },
    );
    case(
        "a missing zero extension of a narrow index",
        NarrowIndex,
        &|m| {
            let add = indexed_address(m, 0);
            let extend = find(m, X::Movzx)
                .into_iter()
                .rfind(|ordinal| *ordinal < add)
                .unwrap_or_else(|| panic!("the index's movzx\n{}", describe(m)));
            // The whole argument register: the byte, and the caller's bits above.
            set_opcode(m, extend, X::MovRR);
            inst_mut(m, extend).operands[1] = preg(RDI);
        },
    );
    case("a sign extension for a zero extension", NarrowIndex, &|m| {
        let add = indexed_address(m, 0);
        let extend = find(m, X::Movzx)
            .into_iter()
            .rfind(|ordinal| *ordinal < add)
            .unwrap_or_else(|| panic!("the index's movzx\n{}", describe(m)));
        set_opcode(m, extend, X::MovsxB);
    });
    case("a misaligned offset (4i + 1)", ScaledLoadU32, &|m| {
        let add = indexed_address(m, 0);
        let load = next_of(m, add, X::MovRM32);
        set_disp(m, load, 1);
    });
    case(
        "a call argument one element off",
        IndexedCallArgument,
        &|m| {
            // `add d, frame, i` becomes `lea d, [frame + i*1 + 1]`.
            let add = indexed_address(m, 0);
            let (base, index) = super::memory::byte_address_inputs(inst(m, add))
                .map(|(base, index)| (base.clone(), index.clone()))
                .expect("the indexed byte address");
            set_opcode(m, add, X::LeaSib);
            let inst = inst_mut(m, add);
            inst.operands.truncate(1);
            inst.operands.push(O::SibMemAddr {
                base: Box::new(base),
                index: Box::new(index),
                scale: 1,
                disp: 1,
            });
        },
    );
    case(
        "a load moved above the store it must see",
        StoreThenIndexedRead,
        &|m| {
            // The read's address is formed after the store: read the element
            // the store's register held before it instead (the old byte).
            let store_add = indexed_address(m, 0);
            let store = next_of(m, store_add, X::MovMR32);
            let load = next_of(m, store, X::MovRM32);
            let (block, store_index) = {
                let (_, block, index) = rows(m)[store];
                (block, index)
            };
            let (_, load_block, load_index) = rows(m)[load];
            assert_eq!(block, load_block, "one block");
            // Move the store after the load (the load now reads the old bytes).
            let insts = &mut m.blocks.get_mut(&block).unwrap().insts;
            let moved = insts.remove(store_index);
            insts.insert(load_index, moved);
        },
    );
    case(
        "an indexed store of the wrong value",
        StoreThenConstRead,
        &|m| {
            let add = indexed_address(m, 0);
            let store = next_of(m, add, X::MovMR32);
            let three = constant_before(m, add, 3);
            let register = inst(m, three).operands[0].clone();
            inst_mut(m, store).operands[1] = register;
        },
    );
    // OD-185 and slice 17: an `ArrayGep` element of a private slot at a
    // variable index scaled by the wrong element size (4 for a `u64`), and a
    // stride-3 element whose `lea; add` scales by 1 (the element `2i`).
    case(
        "an ArrayGep element scaled by 4 for a u64",
        ArrayGepTable,
        &|m| {
            let lea = variable_lea(m);
            set_scale(m, lea, 4);
        },
    );
    case(
        "a stride-3 ArrayGep element at 2i (lea [b + i*1]; add i)",
        ArrayGepStride3,
        &|m| {
            let lea = variable_lea(m);
            set_scale(m, lea, 1);
        },
    );
    let mut variant_case = |label: &'static str,
                            variant: IndexVariant,
                            unbounded: bool,
                            mutate: &dyn Fn(&mut X86ISelFunction)| {
        let (source, mut machine) = variant_pair(variant);
        mutate(&mut machine);
        cases.push((label, source, machine, unbounded));
    };
    // The out-of-bounds source: guard `i <= 16`, the selector's correct
    // lowering of it; built without the bound finder, which refuses it.
    variant_case(
        "out of bounds on a defined path (i <= 16 into 16 bytes)",
        IndexVariant::OffByOneGuard,
        true,
        &|_| {},
    );
    // Only the source's claim tells: the machine reads the table's first byte
    // (the same value) wherever the source reads past it. The index register
    // still feeds the bounds check and the panic call, so the branch, the
    // trap and every observable agree: `add d, frame, i` becomes `mov d,
    // frame`.
    variant_case(
        "out of bounds on a defined path, the machine in bounds",
        IndexVariant::UniformOffByOne,
        true,
        &|m| {
            let add = indexed_address(m, 0);
            let base = super::memory::byte_address_inputs(inst(m, add))
                .unwrap()
                .0
                .clone();
            set_opcode(m, add, X::MovRR);
            let inst = inst_mut(m, add);
            inst.operands.truncate(1);
            inst.operands.push(base);
        },
    );
    // Only the machine's claim tells: it reads 64 bytes past the table, where
    // its select reads one of the table's bytes, all the same value.
    variant_case(
        "a machine access past its slot (its select reads a table byte)",
        IndexVariant::UniformTable,
        false,
        &|m| {
            let add = indexed_address(m, 0);
            let load = next_of(m, add, X::MovzxRM8);
            set_disp(m, load, 64);
        },
    );
    // Only the machine's congruence tells: a read at `4i + 1` of a table of
    // one repeated value, within the slot.
    variant_case(
        "a misaligned read inside the slot",
        IndexVariant::UniformScaled,
        false,
        &|m| {
            let add = indexed_address(m, 0);
            let load = next_of(m, add, X::MovRM32);
            set_disp(m, load, 1);
        },
    );
    cases
}

/// Correct machine bodies the selector does not emit at O0 for these
/// sources: the scaled index as one `lea d, [frame + i*4]` (the selector's
/// `ArrayGep` form), and the multiply by 3 as an `imul` (the selector emits
/// `lea s, [x + x*2]`, which the `ScaleByThree` fixture states). The theorem
/// binds them by terms, never by shape.
pub(crate) fn slice_seventeen_machine_variants() -> Vec<(&'static str, Function, X86ISelFunction)> {
    use X86Opcode as X;
    let mut variants = Vec::new();
    // `imul s, i, c; add d, frame, s` -> `lea d, [frame + i*4]`.
    let (source, mut machine) = slice17_pair(IndexShape::ScaledLoadU32);
    let add = indexed_address(&machine, 0);
    let (frame, offset) = super::memory::byte_address_inputs(inst(&machine, add))
        .map(|(base, index)| (base.clone(), index.clone()))
        .expect("the indexed byte address");
    let O::VReg(scaled) = offset else {
        panic!("a vreg index")
    };
    let product = find(&machine, X::ImulRR)
        .into_iter()
        .rfind(|ordinal| {
            *ordinal < add
                && matches!(&inst(&machine, *ordinal).operands[0], O::VReg(d) if d.id == scaled.id)
        })
        .unwrap_or_else(|| panic!("the stride's imul\n{}", describe(&machine)));
    let index = inst(&machine, product).operands[1].clone();
    set_opcode(&mut machine, add, X::LeaSib);
    let row = inst_mut(&mut machine, add);
    row.operands.truncate(1);
    row.operands.push(O::SibMemAddr {
        base: Box::new(frame),
        index: Box::new(index),
        scale: 4,
        disp: 0,
    });
    variants.push(("the scaled index as one lea", source, machine));
    // The selector's `lea s, [x + x*2]` for the multiply by 3 ->
    // `imul s, x, c3` (the constant register it loads just before).
    let (source, mut machine) = slice17_pair(IndexShape::ScaleByThree);
    let product = find(&machine, X::LeaSib)
        .into_iter()
        .find(|ordinal| {
            matches!(
                &inst(&machine, *ordinal).operands[1],
                O::SibMemAddr { base, index, scale: 2, disp: 0 } if base == index
            )
        })
        .unwrap_or_else(|| panic!("the multiply's lea\n{}", describe(&machine)));
    let O::SibMemAddr { index, .. } = inst(&machine, product).operands[1].clone() else {
        panic!("a scaled lea")
    };
    let three = constant_before(&machine, product, 3);
    let constant = inst(&machine, three).operands[0].clone();
    set_opcode(&mut machine, product, X::ImulRR);
    let row = inst_mut(&mut machine, product);
    row.operands.truncate(1);
    row.operands.push(*index);
    row.operands.push(constant);
    variants.push(("the multiply by 3 as imul", source, machine));
    variants
}

/// Each machine variant builds a theorem that holds on samples.
#[test]
fn every_slice_seventeen_machine_variant_holds() {
    for (label, source, machine) in slice_seventeen_machine_variants() {
        let obligation = owner(&source, &machine, label);
        assert!(
            dag_holds_on_samples(&obligation),
            "{label}\n{}",
            describe(&machine)
        );
    }
}

/// Every slice-17 refutation is refuted by its theorem (built without the
/// owner's affine refusal, and the out-of-bounds source without the bound
/// finder) and never credited by the owner.
#[test]
fn every_slice_seventeen_refutation_is_refuted() {
    for (label, source, machine, unbounded) in slice_seventeen_refutations() {
        let theorem = if unbounded {
            theorem_without_indexed_bounds(&source, &machine, SYSV)
        } else {
            theorem_without_affine_refusal(&source, &machine, SYSV)
        }
        .unwrap_or_else(|refusal| panic!("{label}: {refusal}\n{}", describe(&machine)));
        assert!(
            dag_refuted_on_samples(&theorem),
            "{label}: a wrong lowering's theorem holds on samples\n{}",
            describe(&machine)
        );
        let outcome = never_credited(&source, &machine, label);
        assert_ne!(outcome, "credited", "{label}");
    }
}

/// A call argument formed from another slot is the named
/// `CallStackAddress` mismatch.
#[test]
fn an_indexed_argument_into_another_slot_is_a_named_mismatch() {
    let (source, mut machine) = slice17_pair(IndexShape::SliceTempInLoop);
    // The indexed argument's add takes the pair's frame register (slot 1)
    // for the buffer's.
    let add = indexed_address(&machine, 0);
    let pair = rows(&machine)
        .into_iter()
        .find_map(|(ordinal, _, _)| {
            let inst = inst(&machine, ordinal);
            match (inst.opcode, inst.operands.as_slice()) {
                (X86Opcode::Lea, [d @ O::VReg(_), O::MemAddr { base, disp: 0 }])
                    if matches!(base.as_ref(), O::StackSlot(1)) =>
                {
                    Some(d.clone())
                }
                _ => None,
            }
        })
        .expect("the pair's lea");
    super::memory::set_byte_address_base(&mut machine, add, pair);
    let refusal = fixture_owner(&source, &machine).err().expect("refused");
    assert!(
        matches!(
            refusal,
            X86BodyRefusal::Mismatch(X86BodyMismatch::CallStackAddress { .. })
        ),
        "{refusal}"
    );
}

/// The machine reads the dead pointer half of the pair (its rebuild in the
/// loop dropped, the value stored before the loop read back): a read of an
/// unreadable byte, no claim, never a credit.
#[test]
fn a_machine_read_of_a_dead_header_byte_makes_no_claim() {
    let (source, mut machine) = variant_pair(IndexVariant::PairReadBack);
    // The pointer half's rebuild in the loop body (the first 8-byte store of
    // a block other than the entry) becomes a no-op.
    let (lir_block, lir_index) = source
        .layout_order()
        .into_iter()
        .filter(|block| *block != source.entry_block)
        .find_map(|block| {
            source.blocks[&block]
                .instructions
                .iter()
                .position(|inst| matches!(inst.opcode, L::Store { ty: Type::I64, .. }))
                .map(|index| (block, index))
        })
        .expect("the rebuild's LIR store");
    let stamp = trust_cg_ir::provenance::SourceInstId {
        block: lir_block.0,
        index: lir_index as u32,
    };
    let rebuild = rows(&machine)
        .into_iter()
        .map(|(ordinal, _, _)| ordinal)
        .find(|ordinal| {
            let inst = inst(&machine, *ordinal);
            inst.opcode == X86Opcode::MovMR && inst.lowering_provenance.source_id() == Some(stamp)
        })
        .expect("the pointer half's rebuild");
    // The rebuild stores to the length half instead (which the length's own
    // store then overwrites): the pointer half is never rebuilt in the loop.
    set_disp(&mut machine, rebuild, 8);
    let refusal = fixture_owner(&source, &machine).err().expect("no claim");
    assert!(
        matches!(refusal, X86BodyRefusal::Unsupported(_)),
        "{refusal}"
    );
    assert!(refusal.to_string().contains("unreadable"), "{refusal}");
}

/// Each indexed site of a fixture has the source's in-bounds claim and the
/// machine's (two at least per site: a load, a store or an argument).
#[test]
fn every_indexed_site_is_claimed_on_both_sides() {
    for shape in SLICE_SEVENTEEN {
        let (source, machine) = slice17_pair(shape);
        let body = admitted_body(&source).expect("admitted");
        let sites: usize = match (&body.dag, &body.loops) {
            (Some(dag), _) => dag.blocks.values().map(|p| p.indexed.len()).sum(),
            (_, Some(loops)) => loops
                .regions
                .iter()
                .flat_map(|region| region.dag.blocks.values())
                .map(|p| p.indexed.len())
                .sum(),
            _ => body.paths.iter().map(|p| p.indexed.len()).sum(),
        };
        assert!(sites >= 1, "{shape:?}");
        // As built (slice 18's spelling; see `owner_builds_every_slice_seventeen_shape`).
        let obligation = with_normal_groups(normal::Groups::NONE, || {
            owner(&source, &machine, &format!("{shape:?}"))
        });
        assert!(
            in_bounds_claims(&obligation) >= 2 * sites.min(1),
            "{shape:?}: {sites} sites"
        );
    }
}

/// Slice-17 theorems are deterministic: two builds print the same query.
#[test]
fn slice_seventeen_theorems_are_deterministic() {
    for shape in SLICE_SEVENTEEN {
        let (source, machine) = slice17_pair(shape);
        let first = text(&owner(&source, &machine, "first"));
        let second = text(&owner(&source, &machine, "second"));
        assert_eq!(first, second, "{shape:?}");
    }
}

/// A `bool` read through an indexed address whose candidates include a byte
/// no `bool` store wrote is refused by name (slice 7's rule, per candidate).
#[test]
fn an_indexed_bool_read_of_an_unwritten_candidate_is_refused() {
    let (source, machine) = variant_pair(IndexVariant::BoolTable);
    let refusal = fixture_owner(&source, &machine).err().expect("refused");
    assert!(
        refusal
            .to_string()
            .contains("candidate byte no bool store or call wrote"),
        "{refusal}"
    );
}

/// A value an indexed load reads from bytes a call left in an escaped slot
/// may be an address derived from it: an access through it observes the
/// escaped slots (slice 15), and the theorem holds.
#[test]
fn an_access_through_an_indexed_load_of_call_bytes_observes_the_escaped_slots() {
    let (source, machine) = variant_pair(IndexVariant::IndexedTaint);
    let body = admitted_body(&source).expect("admitted");
    let derived = body
        .dag
        .iter()
        .flat_map(|dag| dag.blocks.values())
        .chain(body.paths.iter())
        .flat_map(|program| &program.accesses)
        .any(|access| access.slot_reads.is_some());
    assert!(
        derived,
        "the access through the loaded pointer is a derived one"
    );
    let obligation = owner(&source, &machine, "IndexedTaint");
    assert!(dag_holds_on_samples(&obligation));
}

/// An indexed address live across a DAG join is kept there (every edge
/// leaves it alike) and is never a joined term: stated over its DAG (as
/// slice 9 states one) as well as path by path, the theorem holds.
#[test]
fn an_indexed_address_live_across_a_dag_join_is_kept() {
    let (source, machine) = slice17_pair(IndexShape::IndexedAcrossJoin);
    let dag = PathEncoding {
        dag: Some(true),
        ..PathEncoding::CANONICAL
    };
    let theorem = theorem_with_path_encoding(&source, &machine, SYSV, dag)
        .unwrap_or_else(|refusal| panic!("{refusal}\n{}", describe(&machine)));
    assert!(dag_holds_on_samples(&theorem));
    assert!(in_bounds_claims(&theorem) >= 2);
}
