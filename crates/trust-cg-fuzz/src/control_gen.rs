// trust-cg-fuzz/src/control_gen.rs - Seeded multi-block trust_ir programs
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// The single-block generator (`trust_ir_gen::gen_module`) is a linear chain
// of binops; it can never produce the shapes behind the AArch64 flag and
// loop-test miscompiles fixed in 13c40239d, ce8692b5a and 3b0797875. This one
// builds `fuzz_fn(i64, i64, i64, i64) -> i64` from a spine of segments:
//
// - straight-line wrapping arithmetic (Add/Sub/Mul/And/Or/Xor only, so the
//   interpreter oracle defines every row);
// - compares whose `bool` feeds selects and zero-extensions, also after a
//   call and in later blocks;
// - calls to three helpers: one returns with its own compare's flags live,
//   and one is a loop whose test sits in its entry block, so a back edge
//   re-enters the block its formal arguments arrive in;
// - diamonds whose arms reuse the branch condition;
// - counted loops (constant trip 1..=5, so every program terminates) whose
//   body selects on the loop's own exit test, which stays usable after the
//   loop;
// - narrow-width (i8/i16/i32) arithmetic and compares, zero- or
//   sign-extended back (the dirty-upper-bits class);
// - the i128 overflow idiom (`sext a + sext b != sext (a + b)`) whose bool
//   feeds selects and branches;
// - a call returning `(i64, bool)`;
// - division and remainder by nonzero constants (never -1 for the signed
//   ops), the magic-number strength-reduction class;
// - shifts whose amount is masked into range;
// - the total unary bit operations (`not`, `ctpop`, `ctlz`, `cttz`, `bswap`,
//   `bitreverse`, `neg`);
// - stack-slot round trips at u8/i16/i32/i64, a `bool` reloaded from a
//   stored byte (trust-ir reads it as `byte != 0`), and a store, call, reload;
// - a small `switch` into a merge block;
// - an early-exit search loop (`(i + 1 != K) & (g(i + 1) != key)`) whose
//   exit reads the trip bool, the counter or the computed value;
// - a counted loop with two recurrences, both used after the loop;
// - a 128-byte fill loop carrying a second recurrence, read back after it;
// - an i32 array fill, then a search whose exit reads the index and reloads
//   through it;
// - a forward overlapping copy `a[i + d] = a[i]` (each iteration reads what an
//   earlier one wrote);
// - two pointers into one array at seeded, possibly equal, indices with
//   interleaved stores and loads through both;
// - an i32 stored and read back byte by byte through a byte pointer;
// - a map loop `a[i] op= c` or a reduction `acc red= a[i]` from a constant,
//   runtime or search-stop start to a runtime or search-stop bound (a fully
//   unrolled search leaves one constant def per exit edge), all inside the
//   array (trust-ir's GEP takes no negative index): test-first,
//   bottom-tested and entered unguarded (a start at or past the
//   bound still runs once), or a signed countdown; the exit test is signed or
//   unsigned, a runtime bound an i64 or an extended i32, and the exit reads
//   nothing, the index before or after its step, or the accumulator before
//   or after its update.
//
// The same seed always yields the same module.

use crate::prng::Prng;
use crate::trust_ir_gen::FUZZ_FN_NAME;
use trust_ir::{
    BinOp, CastOp, Constant, FuncId, ICmpOp, Module as TrustIrModule, SwitchCase, Ty, UnOp, ValueId,
};
use trust_ir_build::{BuildError, FunctionBuilder, ModuleBuilder};

const ICMP_OPS: [ICmpOp; 10] = [
    ICmpOp::Eq,
    ICmpOp::Ne,
    ICmpOp::Slt,
    ICmpOp::Sle,
    ICmpOp::Sgt,
    ICmpOp::Sge,
    ICmpOp::Ult,
    ICmpOp::Ule,
    ICmpOp::Ugt,
    ICmpOp::Uge,
];
const NARROW_TYS: [Ty; 3] = [Ty::I8, Ty::I16, Ty::I32];
const DIV_OPS: [BinOp; 4] = [BinOp::UDiv, BinOp::URem, BinOp::SDiv, BinOp::SRem];
/// Divisors: never 0, and never -1 (a signed `INT_MIN / -1` is UB).
const DIVISORS: [i64; 14] = [1, 2, 3, 5, 7, 8, 10, 16, 25, 100, 255, 1000, -3, -16];
const SHIFT_OPS: [BinOp; 3] = [BinOp::Shl, BinOp::LShr, BinOp::AShr];
const BIT_UNOPS: [UnOp; 7] = [
    UnOp::Not,
    UnOp::CtPop,
    UnOp::CtLz,
    UnOp::CtTz,
    UnOp::BSwap,
    UnOp::BitReverse,
    UnOp::Neg,
];
const SLOT_TYS: [Ty; 4] = [Ty::U8, Ty::I16, Ty::I32, Ty::I64];

fn width_of(ty: &Ty) -> u32 {
    match ty {
        Ty::I8 | Ty::U8 => 8,
        Ty::I16 => 16,
        Ty::I32 => 32,
        _ => 64,
    }
}

/// `x` at `ty` (a truncation unless `ty` is i64).
fn at_width(fb: &mut FunctionBuilder<'_>, ty: &Ty, x: ValueId) -> ValueId {
    if *ty == Ty::I64 {
        x
    } else {
        fb.cast(CastOp::Trunc, Ty::I64, ty.clone(), x)
    }
}

/// `x: ty` back at i64, zero- or sign-extended.
fn widen(fb: &mut FunctionBuilder<'_>, rng: &mut Prng, ty: &Ty, x: ValueId) -> ValueId {
    if *ty == Ty::I64 {
        return x;
    }
    let op = if rng.chance(1, 2) {
        CastOp::ZExt
    } else {
        CastOp::SExt
    };
    fb.cast(op, ty.clone(), Ty::I64, x)
}

fn any_width(rng: &mut Prng) -> Ty {
    match rng.gen_range_u32(4) {
        0 => Ty::I8,
        1 => Ty::I16,
        2 => Ty::I32,
        _ => Ty::I64,
    }
}
const ARITH_OPS: [BinOp; 6] = [
    BinOp::Add,
    BinOp::Sub,
    BinOp::Mul,
    BinOp::And,
    BinOp::Or,
    BinOp::Xor,
];

fn pick<T: Copy>(rng: &mut Prng, items: &[T]) -> T {
    items[rng.gen_range_usize(items.len())]
}

/// The values a segment may read: every one is defined in a block that
/// dominates the current insertion point.
struct Pools {
    ints: Vec<ValueId>,
    bools: Vec<ValueId>,
}

impl Pools {
    fn int(&self, rng: &mut Prng) -> ValueId {
        // Favor recent values so data flows through the program.
        let recent = self.ints.len().min(6);
        if rng.chance(3, 4) {
            self.ints[self.ints.len() - 1 - rng.gen_range_usize(recent)]
        } else {
            pick(rng, &self.ints)
        }
    }
}

fn compare(fb: &mut FunctionBuilder<'_>, rng: &mut Prng, pools: &Pools) -> ValueId {
    let lhs = pools.int(rng);
    let rhs = if rng.chance(1, 3) {
        fb.iconst(Ty::I64, i128::from(rng.signed_i64(16)))
    } else {
        pools.int(rng)
    };
    fb.icmp(pick(rng, &ICMP_OPS), Ty::I64, lhs, rhs)
}

fn arith(fb: &mut FunctionBuilder<'_>, rng: &mut Prng, pools: &Pools) -> ValueId {
    let lhs = pools.int(rng);
    let rhs = if rng.chance(1, 4) {
        fb.iconst(Ty::I64, i128::from(rng.signed_i64(1000)))
    } else {
        pools.int(rng)
    };
    fb.binop(pick(rng, &ARITH_OPS), Ty::I64, lhs, rhs)
}

/// A bool from the pool (reused across blocks when one exists) or a fresh
/// compare.
fn condition(fb: &mut FunctionBuilder<'_>, rng: &mut Prng, pools: &mut Pools) -> ValueId {
    if !pools.bools.is_empty() && rng.chance(1, 2) {
        pick(rng, &pools.bools)
    } else {
        let c = compare(fb, rng, pools);
        pools.bools.push(c);
        c
    }
}

fn helper_call(
    fb: &mut FunctionBuilder<'_>,
    rng: &mut Prng,
    pools: &Pools,
    helpers: [FuncId; 3],
) -> ValueId {
    let arg = pools.int(rng);
    fb.call(pick(rng, &helpers), vec![arg])
}

/// Where `j = 1, 2, ..` first equals `key`, or `limit + 1`: an early-exit
/// search with a constant trip count. Fully unrolled, it leaves its result in
/// a register with one constant definition per exit edge, so no single
/// definition names the value every path delivers.
fn search_stop(fb: &mut FunctionBuilder<'_>, key: ValueId, limit: u32) -> ValueId {
    let head = fb.create_block();
    let j = fb.add_block_param(head, Ty::I64);
    let step = fb.create_block();
    let found = fb.create_block();
    let stop = fb.add_block_param(found, Ty::I64);
    let one = fb.iconst(Ty::I64, 1);
    fb.br(head, vec![one]);
    fb.switch_to_block(head);
    let hit = fb.icmp(ICmpOp::Eq, Ty::I64, j, key);
    fb.condbr(hit, found, vec![j], step, vec![]);
    fb.switch_to_block(step);
    let next = fb.add(Ty::I64, j, one);
    let last = fb.iconst(Ty::I64, i128::from(limit));
    let more = fb.icmp(ICmpOp::Ule, Ty::I64, next, last);
    fb.condbr(more, head, vec![next], found, vec![next]);
    fb.switch_to_block(found);
    stop
}

/// `x -> select(x <op> k, x * 3, x - k)`.
fn define_select_helper(mb: &mut ModuleBuilder, id: FuncId, rng: &mut Prng) {
    let mut fb = mb.define_function(id).expect("declared helper");
    let block = fb.create_block();
    let x = fb.add_block_param(block, Ty::I64);
    fb.switch_to_block(block);
    let k = fb.iconst(Ty::I64, i128::from(rng.signed_i64(64)));
    let c = fb.icmp(pick(rng, &ICMP_OPS), Ty::I64, x, k);
    let three = fb.iconst(Ty::I64, 3);
    let tripled = fb.mul(Ty::I64, x, three);
    let shifted = fb.sub(Ty::I64, x, k);
    let chosen = fb.select(Ty::I64, c, tripled, shifted);
    fb.ret(vec![chosen]);
    fb.build();
}

/// `x -> zext(x <op> k)`: returns with that compare's flags live.
fn define_flag_helper(mb: &mut ModuleBuilder, id: FuncId, rng: &mut Prng) {
    let mut fb = mb.define_function(id).expect("declared helper");
    let block = fb.create_block();
    let x = fb.add_block_param(block, Ty::I64);
    fb.switch_to_block(block);
    let k = fb.iconst(Ty::I64, i128::from(rng.signed_i64(64)));
    let c = fb.icmp(pick(rng, &ICMP_OPS), Ty::I64, x, k);
    let widened = fb.cast(CastOp::ZExt, Ty::Bool, Ty::I64, c);
    fb.ret(vec![widened]);
    fb.build();
}

/// `x -> { while x >u k { x >>= s }; x * 3 }` with the loop test in the entry
/// block: the back edge passes the entry block a new `x`, so the formal
/// argument must be read from its ABI register once, not on every trip.
fn define_entry_loop_helper(mb: &mut ModuleBuilder, id: FuncId, rng: &mut Prng) {
    let mut fb = mb.define_function(id).expect("declared helper");
    let entry = fb.create_block();
    let x = fb.add_block_param(entry, Ty::I64);
    let body = fb.create_block();
    let exit = fb.create_block();
    fb.switch_to_block(entry);
    let k = fb.iconst(Ty::I64, i128::from(rng.gen_range_u32(64)));
    let more = fb.icmp(ICmpOp::Ugt, Ty::I64, x, k);
    fb.condbr(more, body, vec![], exit, vec![]);
    fb.switch_to_block(body);
    let s = fb.iconst(Ty::I64, i128::from(1 + rng.gen_range_u32(3)));
    let shifted = fb.binop(BinOp::LShr, Ty::I64, x, s);
    fb.br(entry, vec![shifted]);
    fb.switch_to_block(exit);
    let three = fb.iconst(Ty::I64, 3);
    let r = fb.mul(Ty::I64, x, three);
    fb.ret(vec![r]);
    fb.build();
}

/// `x -> (x ^ k, x <op> k)`: a two-result return with a `bool` lane.
fn define_pair_helper(mb: &mut ModuleBuilder, id: FuncId, rng: &mut Prng) {
    let mut fb = mb.define_function(id).expect("declared helper");
    let block = fb.create_block();
    let x = fb.add_block_param(block, Ty::I64);
    fb.switch_to_block(block);
    let k = fb.iconst(Ty::I64, i128::from(rng.signed_i64(64)));
    let c = fb.icmp(pick(rng, &ICMP_OPS), Ty::I64, x, k);
    let mixed = fb.binop(BinOp::Xor, Ty::I64, x, k);
    fb.ret(vec![mixed, c]);
    fb.build();
}

const FILL_LEN: i128 = 128;
const SEARCH_LEN: i128 = 32;
const ALIAS_LEN: i128 = 64;

/// Build the seeded multi-block module (see the module docs).
pub fn gen_control_module(seed: u64) -> Result<TrustIrModule, BuildError> {
    let mut rng = Prng::new(seed ^ 0xC017_201F_C017_201F);
    let mut mb = ModuleBuilder::new(format!("control_{seed}"));
    let unary = mb.add_func_type(vec![Ty::I64], vec![Ty::I64]);
    let pair = mb.add_func_type(vec![Ty::I64], vec![Ty::I64, Ty::Bool]);
    let main_ty = mb.add_func_type(vec![Ty::I64; 4], vec![Ty::I64]);
    let helpers = [
        mb.declare_function("ctl_select_helper", unary),
        mb.declare_function("ctl_flag_helper", unary),
        mb.declare_function("ctl_entry_loop_helper", unary),
    ];
    let pair_helper = mb.declare_function("ctl_pair_helper", pair);
    define_select_helper(&mut mb, helpers[0], &mut rng);
    define_flag_helper(&mut mb, helpers[1], &mut rng);
    define_entry_loop_helper(&mut mb, helpers[2], &mut rng);
    define_pair_helper(&mut mb, pair_helper, &mut rng);
    let u8_id = mb.add_type(Ty::U8);
    let i32_id = mb.add_type(Ty::I32);
    let fill_array = Ty::Array(u8_id, FILL_LEN as u64);
    let search_array = Ty::Array(i32_id, SEARCH_LEN as u64);
    let i64_id = mb.add_type(Ty::I64);
    let alias_array = Ty::Array(i64_id, ALIAS_LEN as u64);
    let map32_array = Ty::Array(i32_id, ALIAS_LEN as u64);

    let mut fb = mb.function(FUZZ_FN_NAME, main_ty);
    let entry = fb.create_block();
    let params: Vec<ValueId> = (0..4).map(|_| fb.add_block_param(entry, Ty::I64)).collect();
    fb.switch_to_block(entry);
    let mut pools = Pools {
        ints: params,
        bools: Vec::new(),
    };

    for _ in 0..3 + rng.gen_range_u32(5) {
        match rng.gen_range_u32(23) {
            0 => {
                let v = arith(&mut fb, &mut rng, &pools);
                pools.ints.push(v);
            }
            // A select on a condition, possibly with a call between the
            // compare and the select.
            1 => {
                let c = condition(&mut fb, &mut rng, &mut pools);
                if rng.chance(1, 2) {
                    let r = helper_call(&mut fb, &mut rng, &pools, helpers);
                    pools.ints.push(r);
                }
                let (a, b) = (pools.int(&mut rng), pools.int(&mut rng));
                let v = fb.select(Ty::I64, c, a, b);
                pools.ints.push(v);
            }
            // A zero-extended condition in arithmetic, possibly after a call.
            2 => {
                let c = condition(&mut fb, &mut rng, &mut pools);
                if rng.chance(1, 2) {
                    let r = helper_call(&mut fb, &mut rng, &pools, helpers);
                    pools.ints.push(r);
                }
                let widened = fb.cast(CastOp::ZExt, Ty::Bool, Ty::I64, c);
                let other = pools.int(&mut rng);
                let v = fb.binop(pick(&mut rng, &ARITH_OPS), Ty::I64, widened, other);
                pools.ints.push(v);
            }
            3 => {
                let r = helper_call(&mut fb, &mut rng, &pools, helpers);
                pools.ints.push(r);
            }
            // A diamond whose arms may reuse the branch condition.
            4 | 5 => {
                let c = condition(&mut fb, &mut rng, &mut pools);
                let then_block = fb.create_block();
                let else_block = fb.create_block();
                let merge = fb.create_block();
                let merged = fb.add_block_param(merge, Ty::I64);
                fb.condbr(c, then_block, vec![], else_block, vec![]);
                for arm in [then_block, else_block] {
                    fb.switch_to_block(arm);
                    let v = match rng.gen_range_u32(3) {
                        0 => {
                            let (a, b) = (pools.int(&mut rng), pools.int(&mut rng));
                            fb.select(Ty::I64, c, a, b)
                        }
                        1 => helper_call(&mut fb, &mut rng, &pools, helpers),
                        _ => arith(&mut fb, &mut rng, &pools),
                    };
                    fb.br(merge, vec![v]);
                }
                fb.switch_to_block(merge);
                pools.ints.push(merged);
            }
            // Narrow-width arithmetic and a narrow compare, extended back.
            7 => {
                let ty = NARROW_TYS[rng.gen_range_usize(NARROW_TYS.len())].clone();
                let (x, y) = (pools.int(&mut rng), pools.int(&mut rng));
                let a = fb.cast(CastOp::Trunc, Ty::I64, ty.clone(), x);
                let b = fb.cast(CastOp::Trunc, Ty::I64, ty.clone(), y);
                let r = fb.binop(pick(&mut rng, &ARITH_OPS), ty.clone(), a, b);
                let c = fb.icmp(pick(&mut rng, &ICMP_OPS), ty.clone(), r, b);
                pools.bools.push(c);
                let extend = if rng.chance(1, 2) {
                    CastOp::ZExt
                } else {
                    CastOp::SExt
                };
                let wide = fb.cast(extend, ty, Ty::I64, r);
                pools.ints.push(wide);
            }
            // The i128 overflow idiom.
            8 => {
                let (a, b) = (pools.int(&mut rng), pools.int(&mut rng));
                let op = if rng.chance(1, 2) {
                    BinOp::Add
                } else {
                    BinOp::Sub
                };
                let narrow = fb.binop(op, Ty::I64, a, b);
                let wa = fb.cast(CastOp::SExt, Ty::I64, Ty::I128, a);
                let wb = fb.cast(CastOp::SExt, Ty::I64, Ty::I128, b);
                let wide = fb.binop(op, Ty::I128, wa, wb);
                let back = fb.cast(CastOp::SExt, Ty::I64, Ty::I128, narrow);
                let overflowed = fb.icmp(ICmpOp::Ne, Ty::I128, back, wide);
                pools.ints.push(narrow);
                pools.bools.push(overflowed);
            }
            // A call returning (i64, bool).
            9 => {
                let arg = pools.int(&mut rng);
                let [mixed, c] = fb.call_results::<2>(pair_helper, vec![arg]);
                pools.ints.push(mixed);
                pools.bools.push(c);
            }
            // Division or remainder by a constant.
            10 => {
                let ty = any_width(&mut rng);
                let x = pools.int(&mut rng);
                let n = at_width(&mut fb, &ty, x);
                // Only divisors the width can hold (an i8 constant is in
                // [-128, 127]); 1 and 2 always fit.
                let bound = 1i128 << (width_of(&ty) - 1);
                let fitting: Vec<i64> = DIVISORS
                    .into_iter()
                    .filter(|&d| (-bound..bound).contains(&i128::from(d)))
                    .collect();
                let divisor = fb.iconst(ty.clone(), i128::from(pick(&mut rng, &fitting)));
                let q = fb.binop(pick(&mut rng, &DIV_OPS), ty.clone(), n, divisor);
                let wide = widen(&mut fb, &mut rng, &ty, q);
                pools.ints.push(wide);
            }
            // A shift whose amount is masked into range.
            11 => {
                let ty = any_width(&mut rng);
                let (x, y) = (pools.int(&mut rng), pools.int(&mut rng));
                let value = at_width(&mut fb, &ty, x);
                let raw = at_width(&mut fb, &ty, y);
                let mask = fb.iconst(ty.clone(), i128::from(width_of(&ty) - 1));
                let amount = fb.binop(BinOp::And, ty.clone(), raw, mask);
                let shifted = fb.binop(pick(&mut rng, &SHIFT_OPS), ty.clone(), value, amount);
                let wide = widen(&mut fb, &mut rng, &ty, shifted);
                pools.ints.push(wide);
            }
            // A total unary bit operation.
            12 => {
                let ty = any_width(&mut rng);
                let x = pools.int(&mut rng);
                let value = at_width(&mut fb, &ty, x);
                let r = fb.unop(pick(&mut rng, &BIT_UNOPS), ty.clone(), value);
                let wide = widen(&mut fb, &mut rng, &ty, r);
                pools.ints.push(wide);
            }
            // A stack-slot round trip, possibly across a call; a u8 slot is
            // also read back as a bool.
            13 => {
                let ty = SLOT_TYS[rng.gen_range_usize(SLOT_TYS.len())].clone();
                let slot = fb.alloca(ty.clone());
                let x = pools.int(&mut rng);
                let stored = at_width(&mut fb, &ty, x);
                fb.store(ty.clone(), slot, stored);
                if rng.chance(1, 2) {
                    let r = helper_call(&mut fb, &mut rng, &pools, helpers);
                    pools.ints.push(r);
                }
                let loaded = fb.load(ty.clone(), slot);
                let wide = if ty == Ty::U8 {
                    fb.cast(CastOp::ZExt, Ty::U8, Ty::I64, loaded)
                } else {
                    widen(&mut fb, &mut rng, &ty, loaded)
                };
                pools.ints.push(wide);
                if ty == Ty::U8 {
                    let as_bool = fb.load(Ty::Bool, slot);
                    pools.bools.push(as_bool);
                }
            }
            // A switch on a small value into a merge block.
            14 => {
                let x = pools.int(&mut rng);
                let three = fb.iconst(Ty::I64, 3);
                let selector = fb.binop(BinOp::And, Ty::I64, x, three);
                let merge = fb.create_block();
                let merged = fb.add_block_param(merge, Ty::I64);
                let arms: Vec<_> = (0..4).map(|_| fb.create_block()).collect();
                let cases = (0..3)
                    .map(|value| SwitchCase {
                        value: Constant::Int(value),
                        target: arms[value as usize],
                        args: vec![],
                    })
                    .collect();
                fb.switch(selector, cases, arms[3], vec![]);
                for &arm in &arms {
                    fb.switch_to_block(arm);
                    let v = if rng.chance(1, 2) {
                        arith(&mut fb, &mut rng, &pools)
                    } else {
                        let c = compare(&mut fb, &mut rng, &pools);
                        let (a, b) = (pools.int(&mut rng), pools.int(&mut rng));
                        fb.select(Ty::I64, c, a, b)
                    };
                    fb.br(merge, vec![v]);
                }
                fb.switch_to_block(merge);
                pools.ints.push(merged);
            }
            // An early-exit search loop.
            15 => {
                let trips = 2 + rng.gen_range_u32(7);
                let header = fb.create_block();
                let i = fb.add_block_param(header, Ty::I64);
                let test = fb.create_block();
                let exit = fb.create_block();
                let exit_kind = rng.gen_range_u32(3);
                let exit_ty = if exit_kind == 0 { Ty::Bool } else { Ty::I64 };
                let out = fb.add_block_param(exit, exit_ty.clone());
                let key = pools.int(&mut rng);
                let zero = fb.iconst(Ty::I64, 0);
                fb.br(header, vec![zero]);

                fb.switch_to_block(header);
                let one = fb.iconst(Ty::I64, 1);
                let next = fb.add(Ty::I64, i, one);
                let factor = fb.iconst(Ty::I64, i128::from(rng.signed_i64(9)));
                let g = fb.binop(pick(&mut rng, &ARITH_OPS), Ty::I64, next, factor);
                fb.br(test, vec![]);

                fb.switch_to_block(test);
                let bound = fb.iconst(Ty::I64, i128::from(trips));
                let not_done = fb.icmp(ICmpOp::Ne, Ty::I64, next, bound);
                let not_found = fb.icmp(ICmpOp::Ne, Ty::I64, g, key);
                let more = fb.binop(BinOp::BAnd, Ty::Bool, not_done, not_found);
                let carried = match exit_kind {
                    0 => not_done,
                    1 => next,
                    _ => g,
                };
                fb.condbr(more, header, vec![next], exit, vec![carried]);

                fb.switch_to_block(exit);
                if exit_ty == Ty::Bool {
                    pools.bools.push(out);
                } else {
                    pools.ints.push(out);
                }
            }
            // A counted loop with two recurrences, both used after it.
            16 => {
                let trips = 1 + rng.gen_range_u32(6);
                let header = fb.create_block();
                let i = fb.add_block_param(header, Ty::I64);
                let acc = fb.add_block_param(header, Ty::I64);
                let count = fb.add_block_param(header, Ty::I64);
                let exit = fb.create_block();
                let acc_out = fb.add_block_param(exit, Ty::I64);
                let count_out = fb.add_block_param(exit, Ty::I64);
                let zero = fb.iconst(Ty::I64, 0);
                let init = pools.int(&mut rng);
                fb.br(header, vec![zero, init, zero]);

                fb.switch_to_block(header);
                let one = fb.iconst(Ty::I64, 1);
                let next = fb.add(Ty::I64, i, one);
                let other = pools.int(&mut rng);
                let acc2 = fb.binop(pick(&mut rng, &ARITH_OPS), Ty::I64, acc, other);
                let step = fb.iconst(Ty::I64, i128::from(1 + rng.gen_range_u32(7)));
                let count2 = fb.add(Ty::I64, count, step);
                let bound = fb.iconst(Ty::I64, i128::from(trips));
                let more = fb.icmp(ICmpOp::Ult, Ty::I64, next, bound);
                fb.condbr(
                    more,
                    header,
                    vec![next, acc2, count2],
                    exit,
                    vec![acc2, count2],
                );

                fb.switch_to_block(exit);
                pools.ints.push(acc_out);
                pools.ints.push(count_out);
            }
            // A top-tested byte fill loop carrying a second recurrence.
            17 => {
                let array = fb.alloca(fill_array.clone());
                let x = pools.int(&mut rng);
                let byte = fb.cast(CastOp::Trunc, Ty::I64, Ty::U8, x);
                let header = fb.create_block();
                let i = fb.add_block_param(header, Ty::I64);
                let count = fb.add_block_param(header, Ty::I64);
                let body = fb.create_block();
                let exit = fb.create_block();
                let count_out = fb.add_block_param(exit, Ty::I64);
                let zero = fb.iconst(Ty::I64, 0);
                fb.br(header, vec![zero, zero]);

                fb.switch_to_block(header);
                let len = fb.iconst(Ty::I64, FILL_LEN);
                let inside = fb.icmp(ICmpOp::Ult, Ty::I64, i, len);
                fb.condbr(inside, body, vec![], exit, vec![count]);

                fb.switch_to_block(body);
                let slot = fb.gep(Ty::U8, array, vec![i]);
                fb.store(Ty::U8, slot, byte);
                let one = fb.iconst(Ty::I64, 1);
                let next = fb.add(Ty::I64, i, one);
                let step = fb.iconst(Ty::I64, i128::from(1 + rng.gen_range_u32(5)));
                let count2 = fb.add(Ty::I64, count, step);
                fb.br(header, vec![next, count2]);

                fb.switch_to_block(exit);
                let y = pools.int(&mut rng);
                let mask = fb.iconst(Ty::I64, FILL_LEN - 1);
                let j = fb.binop(BinOp::And, Ty::I64, y, mask);
                let read_slot = fb.gep(Ty::U8, array, vec![j]);
                let read = fb.load(Ty::U8, read_slot);
                let wide = fb.cast(CastOp::ZExt, Ty::U8, Ty::I64, read);
                pools.ints.push(wide);
                pools.ints.push(count_out);
            }
            // An i32 array fill, then a search whose exit reads the index.
            18 => {
                let array = fb.alloca(search_array.clone());
                let seed_value = pools.int(&mut rng);
                let factor = fb.iconst(Ty::I64, i128::from(1 + rng.gen_range_u32(5)));
                let fill = fb.create_block();
                let i = fb.add_block_param(fill, Ty::I64);
                let fill_body = fb.create_block();
                let search = fb.create_block();
                let j = fb.add_block_param(search, Ty::I64);
                let probe = fb.create_block();
                let advance = fb.create_block();
                let found = fb.create_block();
                let index = fb.add_block_param(found, Ty::I64);
                let zero = fb.iconst(Ty::I64, 0);
                let len = fb.iconst(Ty::I64, SEARCH_LEN);
                fb.br(fill, vec![zero]);

                fb.switch_to_block(fill);
                let filling = fb.icmp(ICmpOp::Ult, Ty::I64, i, len);
                fb.condbr(filling, fill_body, vec![], search, vec![zero]);

                fb.switch_to_block(fill_body);
                let scaled = fb.mul(Ty::I64, i, factor);
                let value = fb.add(Ty::I64, scaled, seed_value);
                let narrow = fb.cast(CastOp::Trunc, Ty::I64, Ty::I32, value);
                let slot = fb.gep(Ty::I32, array, vec![i]);
                fb.store(Ty::I32, slot, narrow);
                let one = fb.iconst(Ty::I64, 1);
                let next = fb.add(Ty::I64, i, one);
                fb.br(fill, vec![next]);

                fb.switch_to_block(search);
                let searching = fb.icmp(ICmpOp::Ult, Ty::I64, j, len);
                fb.condbr(searching, probe, vec![], found, vec![j]);

                fb.switch_to_block(probe);
                let probe_slot = fb.gep(Ty::I32, array, vec![j]);
                let probed = fb.load(Ty::I32, probe_slot);
                let wanted = pools.int(&mut rng);
                let wanted32 = fb.cast(CastOp::Trunc, Ty::I64, Ty::I32, wanted);
                let hit = fb.icmp(ICmpOp::Eq, Ty::I32, probed, wanted32);
                fb.condbr(hit, found, vec![j], advance, vec![]);

                fb.switch_to_block(advance);
                let one = fb.iconst(Ty::I64, 1);
                let j2 = fb.add(Ty::I64, j, one);
                fb.br(search, vec![j2]);

                fb.switch_to_block(found);
                let last = fb.iconst(Ty::I64, SEARCH_LEN - 1);
                let clamped = fb.binop(BinOp::And, Ty::I64, index, last);
                let again = fb.gep(Ty::I32, array, vec![clamped]);
                let reread = fb.load(Ty::I32, again);
                let wide = fb.cast(CastOp::SExt, Ty::I32, Ty::I64, reread);
                pools.ints.push(index);
                pools.ints.push(wide);
            }
            // A forward overlapping copy within one array.
            19 => {
                let array = fb.alloca(alias_array.clone());
                let x = pools.int(&mut rng);
                let fill = fb.create_block();
                let i = fb.add_block_param(fill, Ty::I64);
                let fill_body = fb.create_block();
                let copy = fb.create_block();
                let j = fb.add_block_param(copy, Ty::I64);
                let copy_body = fb.create_block();
                let done = fb.create_block();
                let zero = fb.iconst(Ty::I64, 0);
                let len = fb.iconst(Ty::I64, ALIAS_LEN);
                fb.br(fill, vec![zero]);

                fb.switch_to_block(fill);
                let filling = fb.icmp(ICmpOp::Ult, Ty::I64, i, len);
                fb.condbr(filling, fill_body, vec![], copy, vec![zero]);

                fb.switch_to_block(fill_body);
                let k = fb.iconst(Ty::I64, i128::from(1 + rng.gen_range_u32(9)));
                let scaled = fb.mul(Ty::I64, i, k);
                let value = fb.binop(BinOp::Xor, Ty::I64, scaled, x);
                let slot = fb.gep(Ty::I64, array, vec![i]);
                fb.store(Ty::I64, slot, value);
                let one = fb.iconst(Ty::I64, 1);
                let next = fb.add(Ty::I64, i, one);
                fb.br(fill, vec![next]);

                // a[j + d] = a[j] for j in 0..64 - d.
                let distance = i128::from(1 + rng.gen_range_u32(4));
                fb.switch_to_block(copy);
                let limit = fb.iconst(Ty::I64, ALIAS_LEN - distance);
                let copying = fb.icmp(ICmpOp::Ult, Ty::I64, j, limit);
                fb.condbr(copying, copy_body, vec![], done, vec![]);

                fb.switch_to_block(copy_body);
                let src = fb.gep(Ty::I64, array, vec![j]);
                let moved = fb.load(Ty::I64, src);
                let d = fb.iconst(Ty::I64, distance);
                let jd = fb.add(Ty::I64, j, d);
                let dst = fb.gep(Ty::I64, array, vec![jd]);
                fb.store(Ty::I64, dst, moved);
                let one = fb.iconst(Ty::I64, 1);
                let j2 = fb.add(Ty::I64, j, one);
                fb.br(copy, vec![j2]);

                fb.switch_to_block(done);
                let y = pools.int(&mut rng);
                let mask = fb.iconst(Ty::I64, ALIAS_LEN - 1);
                let at = fb.binop(BinOp::And, Ty::I64, y, mask);
                let read_slot = fb.gep(Ty::I64, array, vec![at]);
                let read = fb.load(Ty::I64, read_slot);
                pools.ints.push(read);
            }
            // Two pointers into one array, possibly equal, interleaved.
            20 => {
                let array = fb.alloca(alias_array.clone());
                let a = fb.iconst(Ty::I64, i128::from(rng.gen_range_u32(4)));
                let b = fb.iconst(Ty::I64, i128::from(rng.gen_range_u32(4)));
                let p = fb.gep(Ty::I64, array, vec![a]);
                let q = fb.gep(Ty::I64, array, vec![b]);
                let (x, y) = (pools.int(&mut rng), pools.int(&mut rng));
                fb.store(Ty::I64, p, x);
                fb.store(Ty::I64, q, y);
                let via_p = fb.load(Ty::I64, p);
                let z = pools.int(&mut rng);
                fb.store(Ty::I64, p, z);
                let via_q = fb.load(Ty::I64, q);
                pools.ints.push(via_p);
                pools.ints.push(via_q);
            }
            // An i32 stored, then read back byte by byte.
            21 => {
                let slot = fb.alloca(Ty::I32);
                let x = pools.int(&mut rng);
                let word = fb.cast(CastOp::Trunc, Ty::I64, Ty::I32, x);
                fb.store(Ty::I32, slot, word);
                let byte_index = fb.iconst(Ty::U64, i128::from(rng.gen_range_u32(4)));
                let byte_ptr = fb.gep(Ty::U8, slot, vec![byte_index]);
                let byte = fb.load(Ty::U8, byte_ptr);
                let wide = fb.cast(CastOp::ZExt, Ty::U8, Ty::I64, byte);
                pools.ints.push(wide);
            }
            // A map or reduction loop over an initialized array (see the
            // module docs for its starts, bounds, shapes and exit reads); the
            // array is read back through a checksum of every element.
            22 => {
                let (elem, array_ty) = if rng.chance(1, 2) {
                    (Ty::I32, map32_array.clone())
                } else {
                    (Ty::I64, alias_array.clone())
                };
                let array = fb.alloca(array_ty);
                let x = pools.int(&mut rng);
                let zero = fb.iconst(Ty::I64, 0);
                let one = fb.iconst(Ty::I64, 1);
                let len = fb.iconst(Ty::I64, ALIAS_LEN);
                let mask = fb.iconst(Ty::I64, ALIAS_LEN - 1);

                let init = fb.create_block();
                let i = fb.add_block_param(init, Ty::I64);
                let init_body = fb.create_block();
                let setup = fb.create_block();
                fb.br(init, vec![zero]);
                fb.switch_to_block(init);
                let filling = fb.icmp(ICmpOp::Ult, Ty::I64, i, len);
                fb.condbr(filling, init_body, vec![], setup, vec![]);
                fb.switch_to_block(init_body);
                let k = fb.iconst(Ty::I64, i128::from(1 + rng.gen_range_u32(9)));
                let scaled = fb.mul(Ty::I64, i, k);
                let value = fb.binop(BinOp::Xor, Ty::I64, scaled, x);
                let stored = at_width(&mut fb, &elem, value);
                let slot = fb.gep(elem.clone(), array, vec![i]);
                fb.store(elem.clone(), slot, stored);
                let next = fb.add(Ty::I64, i, one);
                fb.br(init, vec![next]);

                fb.switch_to_block(setup);
                let (s_raw, n_raw) = (pools.int(&mut rng), pools.int(&mut rng));
                let small = fb.iconst(Ty::I64, 15);
                // A seeded constant start (the vectorizers' entry-index
                // proofs need one), a runtime one, or where a short search
                // stopped (a constant on each path, a different one per path).
                let start = match rng.gen_range_u32(3) {
                    0 => fb.iconst(Ty::I64, i128::from(rng.gen_range_u32(ALIAS_LEN as u32))),
                    1 => fb.binop(BinOp::And, Ty::I64, s_raw, mask),
                    _ => {
                        let key = fb.binop(BinOp::And, Ty::I64, s_raw, small);
                        search_stop(&mut fb, key, pick(&mut rng, &[4, 8, 16]))
                    }
                };
                // The bound as i64, as an i32 extended back (a 64-bit index
                // compared against a narrow source), or a search's stop.
                let bound = match rng.gen_range_u32(3) {
                    0 => fb.binop(BinOp::And, Ty::I64, n_raw, mask),
                    1 => {
                        let n_masked = fb.binop(BinOp::And, Ty::I64, n_raw, mask);
                        let narrow = fb.cast(CastOp::Trunc, Ty::I64, Ty::I32, n_masked);
                        widen(&mut fb, &mut rng, &Ty::I32, narrow)
                    }
                    _ => {
                        let key = fb.binop(BinOp::And, Ty::I64, n_raw, small);
                        search_stop(&mut fb, key, pick(&mut rng, &[4, 8, 16]))
                    }
                };
                let lt_ops: &[ICmpOp] = &[ICmpOp::Slt, ICmpOp::Ult];
                let ge_ops: &[ICmpOp] = &[ICmpOp::Sge, ICmpOp::Uge];
                let operand_src = pools.int(&mut rng);
                let operand = at_width(&mut fb, &elem, operand_src);
                let op = pick(&mut rng, &ARITH_OPS);
                // A map `a[i] op= c`, or a reduction `acc red= a[i]`.
                let reduce = rng.chance(1, 3);
                let red_op = pick(&mut rng, &[BinOp::Add, BinOp::Xor, BinOp::Or, BinOp::And]);
                let acc_init_src = pools.int(&mut rng);
                let acc_init = at_width(&mut fb, &elem, acc_init_src);
                let body = fb.create_block();
                let iv = fb.add_block_param(body, Ty::I64);
                let acc = reduce.then(|| fb.add_block_param(body, elem.clone()));
                let exit = fb.create_block();
                // What the exit reads: nothing (the vectorizers' plain
                // shape), the index after or before its step, and for a
                // reduction the accumulator after or before this iteration.
                let index_live = rng.gen_range_u32(3);
                let last = (index_live != 0).then(|| fb.add_block_param(exit, Ty::I64));
                let acc_out =
                    (reduce && rng.chance(2, 3)).then(|| fb.add_block_param(exit, elem.clone()));
                let acc_before = rng.chance(1, 2);
                let shape = rng.gen_range_u32(3);
                // while i < n { .. ; i += 1 }: its header block.
                let head = if shape == 0 {
                    let head = fb.create_block();
                    let h = fb.add_block_param(head, Ty::I64);
                    let hacc = reduce.then(|| fb.add_block_param(head, elem.clone()));
                    let mut entry_args = vec![start];
                    entry_args.extend(reduce.then_some(acc_init));
                    fb.br(head, entry_args);
                    fb.switch_to_block(head);
                    let inside = fb.icmp(pick(&mut rng, lt_ops), Ty::I64, h, bound);
                    let mut into_body = vec![h];
                    into_body.extend(hacc);
                    let mut leave = Vec::new();
                    leave.extend(last.map(|_| h));
                    leave.extend(acc_out.and(hacc));
                    fb.condbr(inside, body, into_body, exit, leave);
                    Some(head)
                } else {
                    let mut entry_args = vec![start];
                    entry_args.extend(reduce.then_some(acc_init));
                    fb.br(body, entry_args);
                    None
                };
                fb.switch_to_block(body);
                let p = fb.gep(elem.clone(), array, vec![iv]);
                let old = fb.load(elem.clone(), p);
                let acc_next = match acc {
                    Some(acc) => Some(fb.binop(red_op, elem.clone(), acc, old)),
                    None => {
                        let new = fb.binop(op, elem.clone(), old, operand);
                        fb.store(elem.clone(), p, new);
                        None
                    }
                };
                let stepped = if shape == 2 {
                    fb.binop(BinOp::Sub, Ty::I64, iv, one)
                } else {
                    fb.add(Ty::I64, iv, one)
                };
                let mut again = vec![stepped];
                again.extend(acc_next);
                let mut leave = Vec::new();
                leave.extend(last.map(|_| if index_live == 2 { iv } else { stepped }));
                leave.extend(acc_out.and(if acc_before { acc } else { acc_next }));
                match shape {
                    0 => fb.br(head.expect("test-first header"), again),
                    // do { .. } while i + 1 < n, or exit when i + 1 >= n.
                    1 => {
                        if rng.chance(1, 2) {
                            let more = fb.icmp(pick(&mut rng, lt_ops), Ty::I64, stepped, bound);
                            fb.condbr(more, body, again, exit, leave);
                        } else {
                            let done = fb.icmp(pick(&mut rng, ge_ops), Ty::I64, stepped, bound);
                            fb.condbr(done, exit, leave, body, again);
                        }
                    }
                    // do { .. } while i - 1 >=s n: signed, so a countdown from
                    // the array's first index stops below it.
                    _ => {
                        let more = fb.icmp(ICmpOp::Sge, Ty::I64, stepped, bound);
                        fb.condbr(more, body, again, exit, leave);
                    }
                }

                fb.switch_to_block(exit);
                let sum_head = fb.create_block();
                let j = fb.add_block_param(sum_head, Ty::I64);
                let acc = fb.add_block_param(sum_head, Ty::I64);
                let sum_body = fb.create_block();
                let summed = fb.create_block();
                let total = fb.add_block_param(summed, Ty::I64);
                fb.br(sum_head, vec![zero, zero]);
                fb.switch_to_block(sum_head);
                let reading = fb.icmp(ICmpOp::Ult, Ty::I64, j, len);
                fb.condbr(reading, sum_body, vec![], summed, vec![acc]);
                fb.switch_to_block(sum_body);
                let q = fb.gep(elem.clone(), array, vec![j]);
                let read = fb.load(elem.clone(), q);
                let wide = widen(&mut fb, &mut rng, &elem, read);
                let mult = fb.iconst(Ty::I64, 31);
                let rolled = fb.mul(Ty::I64, acc, mult);
                let acc2 = fb.add(Ty::I64, rolled, wide);
                let j2 = fb.add(Ty::I64, j, one);
                fb.br(sum_head, vec![j2, acc2]);

                fb.switch_to_block(summed);
                pools.ints.push(total);
                pools.ints.extend(last);
                if let Some(acc_out) = acc_out {
                    let wide = widen(&mut fb, &mut rng, &elem, acc_out);
                    pools.ints.push(wide);
                }
            }
            // A counted loop whose body selects on its own exit test.
            _ => {
                let trips = 1 + rng.gen_range_u32(5);
                let header = fb.create_block();
                let i = fb.add_block_param(header, Ty::I64);
                let acc = fb.add_block_param(header, Ty::I64);
                let exit = fb.create_block();
                let out = fb.add_block_param(exit, Ty::I64);
                let zero = fb.iconst(Ty::I64, 0);
                let init = pools.int(&mut rng);
                fb.br(header, vec![zero, init]);

                fb.switch_to_block(header);
                let one = fb.iconst(Ty::I64, 1);
                let next = fb.add(Ty::I64, i, one);
                let bound = fb.iconst(Ty::I64, i128::from(trips));
                let more = fb.icmp(ICmpOp::Ult, Ty::I64, next, bound);
                let (a, b) = (pools.int(&mut rng), pools.int(&mut rng));
                let picked = if rng.chance(2, 3) {
                    fb.select(Ty::I64, more, a, b)
                } else {
                    let widened = fb.cast(CastOp::ZExt, Ty::Bool, Ty::I64, more);
                    fb.add(Ty::I64, widened, a)
                };
                let mut stepped = fb.binop(pick(&mut rng, &ARITH_OPS), Ty::I64, acc, picked);
                if rng.chance(1, 3) {
                    stepped = fb.call(pick(&mut rng, &helpers), vec![stepped]);
                }
                fb.condbr(more, header, vec![next, stepped], exit, vec![stepped]);

                fb.switch_to_block(exit);
                // The header dominates the exit: its test and counter stay usable.
                pools.ints.push(out);
                pools.ints.push(next);
                pools.bools.push(more);
            }
        }
    }

    // Fold the last few values so most of the program reaches the result.
    let mut result = pools.ints[pools.ints.len() - 1];
    for &v in pools.ints.iter().rev().skip(1).take(3) {
        result = fb.binop(BinOp::Xor, Ty::I64, result, v);
    }
    fb.ret(vec![result]);
    fb.build();
    mb.build()
}

#[cfg(all(test, unix, any(target_arch = "aarch64", target_arch = "x86_64")))]
mod tests {
    use super::*;
    use crate::jit_diff::run_reference_oracle_one;
    use crate::trust_ir_gen::sample_inputs;

    /// Every seed builds a module the host JIT accepts at O0: a refused
    /// compile checks nothing, and the Linux lane fails on any refusal.
    #[test]
    fn control_modules_compile_for_the_host_jit() {
        use trust_cg_codegen::compiler::{Compiler, CompilerConfig};
        use trust_cg_codegen::pipeline::OptLevel;
        for seed in 1..=200u64 {
            let module = gen_control_module(seed).expect("the control module builds");
            let mut config = CompilerConfig::for_host_jit();
            config.opt_level = OptLevel::O0;
            if let Err(error) = Compiler::new(config)
                .with_codegen_license(crate::fuzz_license())
                .compile_module_to_jit(&module, &std::collections::HashMap::new())
            {
                panic!("seed {seed}: {error:?}");
            }
        }
    }

    /// Every seed builds a module trust-ir's reference interpreter runs on every
    /// sampled row (no error, no fuel exhaustion), and the same seed always
    /// builds the same module.
    #[test]
    fn control_modules_are_deterministic_and_fully_defined() {
        for seed in 1..=200u64 {
            let module = gen_control_module(seed).expect("the control module builds");
            assert_eq!(
                format!("{module:?}"),
                format!(
                    "{:?}",
                    gen_control_module(seed).expect("the control module builds")
                ),
                "seed {seed} is not deterministic"
            );
            for row in sample_inputs(seed, 4, 6) {
                run_reference_oracle_one(&module, &row)
                    .unwrap_or_else(|error| panic!("seed {seed} row {row:?}: {error}"));
            }
        }
    }
}
