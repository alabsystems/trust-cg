// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! Slice 24a of the x86-64 source-bound body theorem: the exact merged-chain
//! quotient (ruling OD-226). `X86BlockMerge` joins a machine block into its
//! one predecessor when that predecessor ends in `jmp` to it; the merged
//! block lowers rows of several LIR blocks, and the one-to-one block
//! correspondence of slice 6 does not hold. The owner states the theorem
//! over the quotient pair the stamps choose: each chain of argument-free
//! `Jump`s into blocks no other edge enters, contracted into its head, the
//! machine's stamps renumbered into its coordinates; the theorem binds the
//! ORIGINAL pair.
//!
//! Fixtures take their LIR from the trust-ir adapter (translated with an
//! explicit `Permit`) and their machine stream from the real x86-64
//! instruction selector (`super::select`). Nineteen of the 21 shapes are
//! then block-merged by the real `X86BlockMerge` (asserted to merge, so an
//! inherited `TCG_NO_X86_BLOCK_MERGE` cannot hollow a fixture), with a hand
//! edit only where a fixture names one (a silent member, a fallthrough tail,
//! flags across a seam: the edits DCE, CSE and branch layout make). F11 and
//! the encoding test's long-chain variant instead cut a LIR block where its
//! machine block has no seam ([`split_lir`]: the merge's exact inverse), and
//! F17 merges one chain by hand (`merge_machine`) so that its second chain
//! stays apart. Every test here runs
//! without a solver (the `x86_source_bound_body::tests::slice24::` library
//! gate); the replay on AY and Clean is in `slice24_qualification`.
//!
//! Everything above the "Controls" section uses only the slice 1-23 API, so
//! the same fixtures are judged by the code before slice 24a (the
//! fails-before record of the 2026-11-04 report).

use super::slice5::describe;
use super::slice6::describe_lir;
use super::slice9::{dag_holds_on_samples, dag_refuted_on_samples};
use super::slice16::{cut_at, parts_hold, some_part_refuted};
use super::*;
use trust_cg_ir::X86CondCode;
use trust_ir::{BinOp, Constant, ICmpOp, ProofAnnotation, SwitchCase};

// ---------------------------------------------------------------------------
// Fixtures
// ---------------------------------------------------------------------------

/// Slice-24a fixture shapes (design §5.2, F1-F17), each a correct lowering
/// the owner states over its merged-chain quotient.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Shape24 {
    /// F1: `x = a + b; br next; next: if x < b { x } else { a }`: the entry
    /// heads a 2-chain into a `Brif` (per-path encoding).
    EntryChain,
    /// F2: a diamond into a join `j(v)`, then `j -> k -> n`: a 3-chain headed
    /// by a join (two paths). `n` is the last block created, so the largest
    /// LIR id is an absorbed member.
    JoinChain,
    /// F3: `x -> y -> z` with `y = [Jump z]`: the merge pops `y`'s `jmp`, so
    /// no row names `y` (an interior stamp-silent member).
    JumpOnlyMember,
    /// F3c: `y = [t2 = copy t; Jump z]`, its `mov` row deleted and its uses
    /// renamed (copy propagation): a silent member holding a `Copy`.
    SilentCopyMember,
    /// F4: `if c { r } else { x }`, `x = [call sink(a); Jump y]`, `y = [Jump
    /// j]`, the merged block's final `jmp j` deleted (`j` is laid out next: a
    /// fallthrough): a silent TAIL, forward-filled.
    SilentTail,
    /// F5t: `k = c + 1; br s; s: switch k {0..=3}`: a chain into a dense
    /// `Switch` (a jump table, OD-181).
    DenseSwitchTail,
    /// F5s: a chain into five sparse cases (a binary search, OD-191).
    SparseSwitchTail,
    /// F5s with a stamp-silent member `m = [Jump s]` before the `Switch`
    /// tail: the search blocks, which name only `s`, must not claim the chain
    /// first (phase order).
    SparseSwitchSilentMember,
    /// F6: a loop whose body is the chain `b1 -> b2`, `b2` the latch.
    LoopBodyChain,
    /// F7: a loop whose header `h` heads the chain `h -> h2`.
    HeaderChain,
    /// F7b: a loop whose preheader chain `entry -> p` is merged, `p`
    /// defining the value `y` the loop body reads: an item of the header's
    /// cut interface defined in an absorbed member.
    PreheaderChain,
    /// F8: a loop whose latch `b2 = [Copy; Copy; Jump h]` (the header's edge
    /// copies) is the chain's tail.
    LatchTail,
    /// F9: `c = a < b; z = c as u64; br n; n: if a < b {..}`, `n`'s compare
    /// row deleted (CSE): `n`'s `jcc` reads the flags `entry`'s `cmp` set,
    /// across the seam.
    SeamFlags,
    /// F10: calls in two members, a store in `x`, a load in `y`, the load's
    /// value passed to a `u32` call whose result is returned.
    CallsAndMemory,
    /// F11: `q = a / b` (`DivNonZero`), its LIR block cut between the
    /// `GuardDivZero` and the `Udiv` ([`split_lir`]).
    GuardThenDivide,
    /// F12: a diamond into a join `j(v)` heading a 14-block chain whose last
    /// member returns its value times 3 (a claim value numbering does not
    /// discharge: one claim over the join's value in the DAG, one per path
    /// otherwise, so the two spellings differ): 17 LIR blocks (DAG: past the
    /// per-path block bound), 4 in the quotient (which alone would be stated
    /// path by path).
    SeventeenBlocks,
    /// F12p: two 4-block chains: 9 LIR blocks, per path either way.
    PerPathChain,
    /// F13: `r = [Jump m]` entered from a `Brif`: a stamp-silent HEAD,
    /// back-filled from the machine block that names only `m`.
    SilentHead,
    /// F15: a 10-member chain.
    TenMembers,
    /// F16: [`Shape24::SparseSwitchTail`] (a DAG: its cases share a target)
    /// with an unreachable merged chain `d1 -> d2` laid out. (The per-path
    /// encoding refuses any laid-out dead block, before slice 24a and after.)
    DeadChain,
    /// F17: two chains `x -> y` and `c1 -> c2`; only `x` and `y` merged (by
    /// hand), `c1` and `c2` left apart, `c1` falling through to `c2`: only
    /// the chain the stamps choose is contracted.
    PartialMerge,
}

/// Every slice-24a fixture shape (design F1-F17 but F14, the parts route:
/// [`parts_fixtures`]).
pub(crate) const SLICE_TWENTY_FOUR: [Shape24; 21] = [
    Shape24::EntryChain,
    Shape24::JoinChain,
    Shape24::JumpOnlyMember,
    Shape24::SilentCopyMember,
    Shape24::SilentTail,
    Shape24::DenseSwitchTail,
    Shape24::SparseSwitchTail,
    Shape24::SparseSwitchSilentMember,
    Shape24::LoopBodyChain,
    Shape24::HeaderChain,
    Shape24::PreheaderChain,
    Shape24::LatchTail,
    Shape24::SeamFlags,
    Shape24::CallsAndMemory,
    Shape24::GuardThenDivide,
    Shape24::SeventeenBlocks,
    Shape24::PerPathChain,
    Shape24::SilentHead,
    Shape24::TenMembers,
    Shape24::DeadChain,
    Shape24::PartialMerge,
];

/// Further sources: refusal controls (D5, D6, D9), a wrong lowering's base
/// (W8, W13), the one-path control and a constant-pool fixture.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Variant24 {
    /// D5: `x: br y(t); y(p): ..`: the member `y` declares a parameter.
    AbsorbedParams,
    /// D6: `h: v = g(n); br t; t: if v != 0 { br h } else { ret 0 }`: the
    /// chain's tail branches to its head.
    DoWhile,
    /// D9: [`Shape24::JoinChain`] with an unreachable 2-cycle of
    /// single-entry `Jump`s, merged into one self-looping machine block.
    DeadCycle,
    /// D10: [`Shape24::LatchTail`] whose `b1` ends in `tmp = copy t`, read
    /// only by the latch's copy into the header: over the concatenation the
    /// latch's edge-copy run would begin in `b1`.
    CopyAcrossSeam,
    /// W8's base: `x -> s -> y` with `s = [store p, t; Jump y]`.
    SilentStore,
    /// W13's base: `q = a / d` (`DivNonZero`); `br b1; b1: if q == 0 { 1 }
    /// else { q }`.
    GuardBeforeBranch,
    /// A one-path body whose machine has no `jcc`:
    /// `x = a + b; br n; n: y = x * b; y`. Its walk is the machine chain
    /// (no correspondence), so its theorem is today's, byte for byte.
    OnePathChain,
    /// `x: k = 1.5; br y; y: sink(a); ret k`: an `f64` constant, the machine
    /// a constant-pool entry (the builder's const-pool mutant).
    FloatConstChain,
    /// [`Variant24::FloatConstChain`] with the head's constant a NaN and the
    /// other arm's `-0.0`: `f64`'s `==` is not reflexive on the one and
    /// equates the other with `0.0`, so the check compares `Fconst`
    /// immediates by their bits (the census refused `parse_inf_nan` before).
    NanConstChain,
    /// A function of no parameter: `v = g(7); br m; m: if v != 0 { 1 } else
    /// { v }` (the entry heads a 2-chain; the check's entry-clause control
    /// adds a dead `[Jump entry]` in front of it, which no absorbed-parameter
    /// decline can pre-empt).
    NoParamEntry,
    /// `if b == 0 { trap }; q = a / b; br y; y: q ^ a` over `u128`: a merged
    /// chain whose theorem trusts `__udivti3` (OD-202), refused when no
    /// module is named (OD-210).
    RoutineChain,
    /// A diamond into a join `j(v)` heading a chain of [`LONG_CHAIN`] blocks:
    /// past the single-query bounds, so the production route states it in
    /// parts, planning and cutting the one merged machine block.
    LongChain,
}

/// The blocks after [`Variant24::LongChain`]'s join: with its other four,
/// past the 128 LIR blocks the single query admits.
pub(crate) const LONG_CHAIN: usize = 140;

trait ShapeName: std::fmt::Debug {
    fn name(&self) -> String {
        let name = format!("{self:?}");
        let mut snake = String::from("s24_");
        for (i, c) in name.chars().enumerate() {
            if c.is_ascii_uppercase() && i > 0 {
                snake.push('_');
            }
            snake.push(c.to_ascii_lowercase());
        }
        snake
    }
}
impl ShapeName for Shape24 {}
impl ShapeName for Variant24 {}

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

/// `x + k` (`u64`).
fn add_const(f: &mut Builder<'_>, x: V, k: i128) -> V {
    let k = f.iconst(Ty::U64, k);
    f.add(Ty::U64, x, k)
}

/// A chain of `blocks` blocks from the current one's `br`: block `i` adds
/// `i + 1` to the running value; the last returns it.
fn returning_chain(f: &mut Builder<'_>, start: V, blocks: usize) {
    let chain: Vec<_> = (0..blocks).map(|_| f.create_block()).collect();
    f.br(chain[0], vec![]);
    let mut value = start;
    for (i, block) in chain.iter().enumerate() {
        f.switch_to_block(*block);
        value = add_const(f, value, i as i128 + 1);
        if i + 1 < blocks {
            f.br(chain[i + 1], vec![]);
        } else {
            f.ret(vec![value]);
        }
    }
}

/// The unreachable blocks `d1 = [7 + 7; Jump d2]` and `d2 = [9 + 9; ..]`,
/// `d2` jumping back to `d1` (`cycle`) or returning.
fn dead_chain(
    f: &mut Builder<'_>,
    d1: trust_ir::value::BlockId,
    d2: trust_ir::value::BlockId,
    cycle: bool,
) {
    f.switch_to_block(d1);
    let seven = f.iconst(Ty::U64, 7);
    let _ = f.add(Ty::U64, seven, seven);
    f.br(d2, vec![]);
    f.switch_to_block(d2);
    let nine = f.iconst(Ty::U64, 9);
    let y = f.add(Ty::U64, nine, nine);
    if cycle {
        f.br(d1, vec![]);
    } else {
        f.ret(vec![y]);
    }
}

/// The LIR the trust-ir adapter produces for a fixture.
fn slice24_function(name: String, shape: Option<Shape24>, variant: Option<Variant24>) -> Function {
    use Shape24::*;
    use Variant24::*;
    let mut builder = ModuleBuilder::new("x86_source_bound_body_slice24");
    let ptr_u64 = Ty::PtrMut(Box::new(Ty::U64));
    let mut declare = |name: &str, params: Vec<Ty>, results: Vec<Ty>| {
        let ty = builder.add_func_type(params, results);
        builder.declare_function(name, ty)
    };
    let sink = declare("sink", vec![Ty::U64], vec![]);
    let g = declare("g", vec![Ty::U64], vec![Ty::U64]);
    let narrow = declare("narrow", vec![Ty::U64], vec![Ty::U32]);
    let (params, results): (Vec<Ty>, Vec<Ty>) = match (shape, variant) {
        (Some(DenseSwitchTail), _) => (vec![Ty::U8], vec![Ty::U64]),
        (Some(SparseSwitchTail | SparseSwitchSilentMember | DeadChain), _) => {
            (vec![Ty::U32], vec![Ty::U64])
        }
        (Some(LoopBodyChain | HeaderChain | LatchTail), _)
        | (_, Some(DoWhile | CopyAcrossSeam)) => (vec![Ty::U64], vec![Ty::U64]),
        (Some(CallsAndMemory), _) | (_, Some(SilentStore)) => {
            (vec![ptr_u64.clone(), Ty::U64], vec![Ty::U64])
        }
        (_, Some(FloatConstChain | NanConstChain)) => (vec![Ty::U64, Ty::U64], vec![Ty::F64]),
        (_, Some(NoParamEntry)) => (vec![], vec![Ty::U64]),
        (_, Some(RoutineChain)) => (vec![Ty::U128, Ty::U128], vec![Ty::U128]),
        _ => (vec![Ty::U64, Ty::U64], vec![Ty::U64]),
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
        (Some(EntryChain), _) => {
            let (next, t, e) = (f.create_block(), f.create_block(), f.create_block());
            let x = f.add(Ty::U64, args[0], args[1]);
            f.br(next, vec![]);
            f.switch_to_block(next);
            let c = f.icmp(ICmpOp::Ult, Ty::U64, x, args[1]);
            f.condbr(c, t, vec![], e, vec![]);
            f.switch_to_block(t);
            f.ret(vec![x]);
            f.switch_to_block(e);
            f.ret(vec![args[0]]);
        }
        (Some(JoinChain), _) | (_, Some(DeadCycle)) => {
            let (l, r, j, k) = (
                f.create_block(),
                f.create_block(),
                f.create_block(),
                f.create_block(),
            );
            let jv = f.add_block_param(j, Ty::U64);
            let zero = f.iconst(Ty::U64, 0);
            let c = f.icmp(ICmpOp::Eq, Ty::U64, args[0], zero);
            f.condbr(c, l, vec![], r, vec![]);
            f.switch_to_block(l);
            f.br(j, vec![args[0]]);
            f.switch_to_block(r);
            f.br(j, vec![args[1]]);
            f.switch_to_block(j);
            let w = add_const(&mut f, jv, 1);
            f.br(k, vec![]);
            f.switch_to_block(k);
            let m = f.mul(Ty::U64, w, args[1]);
            let dead = (variant == Some(DeadCycle)).then(|| (f.create_block(), f.create_block()));
            let n = f.create_block();
            f.br(n, vec![]);
            f.switch_to_block(n);
            let s = f.sub(Ty::U64, m, args[0]);
            f.ret(vec![s]);
            if let Some((d1, d2)) = dead {
                dead_chain(&mut f, d1, d2, true);
            }
        }
        (Some(JumpOnlyMember | SilentCopyMember), _) => {
            let (x, y, z, r, j) = (
                f.create_block(),
                f.create_block(),
                f.create_block(),
                f.create_block(),
                f.create_block(),
            );
            let jv = f.add_block_param(j, Ty::U64);
            let c = f.icmp(ICmpOp::Ult, Ty::U64, args[0], args[1]);
            f.condbr(c, x, vec![], r, vec![]);
            f.switch_to_block(x);
            let t = add_const(&mut f, args[0], 1);
            f.br(y, vec![]);
            f.switch_to_block(y);
            let t = if shape == Some(SilentCopyMember) {
                f.copy(Ty::U64, t)
            } else {
                t
            };
            f.br(z, vec![]);
            f.switch_to_block(z);
            let u = f.mul(Ty::U64, t, args[1]);
            f.br(j, vec![u]);
            f.switch_to_block(r);
            f.br(j, vec![args[1]]);
            f.switch_to_block(j);
            f.ret(vec![jv]);
        }
        (Some(SilentTail), _) => {
            // The adapter lays blocks out in reverse postorder, the `Brif`'s
            // else edge searched first: `entry, r, x, y, j`, so `j` follows
            // the merged `x` and is its fallthrough once its final `jmp` is
            // deleted.
            let (r, x, y, j) = (
                f.create_block(),
                f.create_block(),
                f.create_block(),
                f.create_block(),
            );
            let c = f.icmp(ICmpOp::Ult, Ty::U64, args[0], args[1]);
            f.condbr(c, r, vec![], x, vec![]);
            f.switch_to_block(r);
            f.br(j, vec![]);
            f.switch_to_block(x);
            f.call_void(sink, vec![args[0]]);
            f.br(y, vec![]);
            f.switch_to_block(y);
            f.br(j, vec![]);
            f.switch_to_block(j);
            f.ret(vec![args[1]]);
        }
        (Some(DenseSwitchTail), _) => {
            let s = f.create_block();
            let one = f.iconst(Ty::U8, 1);
            let k = f.add(Ty::U8, args[0], one);
            f.br(s, vec![]);
            f.switch_to_block(s);
            returning_switch(&mut f, k, &[0, 1, 2, 3], &[0, 1, 2, 3], 5);
        }
        (Some(SparseSwitchTail | SparseSwitchSilentMember | DeadChain), _) => {
            let m = (shape == Some(SparseSwitchSilentMember)).then(|| f.create_block());
            let s = f.create_block();
            let dead = (shape == Some(DeadChain)).then(|| (f.create_block(), f.create_block()));
            let one = f.iconst(Ty::U32, 1);
            let k = f.add(Ty::U32, args[0], one);
            if let Some(m) = m {
                f.br(m, vec![]);
                f.switch_to_block(m);
            }
            f.br(s, vec![]);
            f.switch_to_block(s);
            returning_switch(&mut f, k, &[9, 10, 13, 34, 39], &[0; 5], 2);
            if let Some((d1, d2)) = dead {
                dead_chain(&mut f, d1, d2, false);
            }
        }
        (Some(LoopBodyChain), _) => {
            let (h, b1, b2, x) = (
                f.create_block(),
                f.create_block(),
                f.create_block(),
                f.create_block(),
            );
            let i = f.add_block_param(h, Ty::U64);
            let acc = f.add_block_param(h, Ty::U64);
            let zero = f.iconst(Ty::U64, 0);
            f.br(h, vec![zero, zero]);
            f.switch_to_block(h);
            let c = f.icmp(ICmpOp::Ult, Ty::U64, i, args[0]);
            f.condbr(c, b1, vec![], x, vec![]);
            f.switch_to_block(b1);
            let t = f.add(Ty::U64, acc, i);
            f.br(b2, vec![]);
            f.switch_to_block(b2);
            let three = f.iconst(Ty::U64, 3);
            let u = f.mul(Ty::U64, t, three);
            let i2 = add_const(&mut f, i, 1);
            f.br(h, vec![i2, u]);
            f.switch_to_block(x);
            f.ret(vec![acc]);
        }
        (Some(HeaderChain), _) => {
            let (h, h2, b, x) = (
                f.create_block(),
                f.create_block(),
                f.create_block(),
                f.create_block(),
            );
            let i = f.add_block_param(h, Ty::U64);
            let acc = f.add_block_param(h, Ty::U64);
            let zero = f.iconst(Ty::U64, 0);
            f.br(h, vec![zero, zero]);
            f.switch_to_block(h);
            let t = f.add(Ty::U64, acc, i);
            f.br(h2, vec![]);
            f.switch_to_block(h2);
            let c = f.icmp(ICmpOp::Ult, Ty::U64, i, args[0]);
            f.condbr(c, b, vec![], x, vec![]);
            f.switch_to_block(b);
            let i2 = add_const(&mut f, i, 1);
            f.br(h, vec![i2, t]);
            f.switch_to_block(x);
            f.ret(vec![t]);
        }
        (Some(PreheaderChain), _) => {
            let (p, h, b, x) = (
                f.create_block(),
                f.create_block(),
                f.create_block(),
                f.create_block(),
            );
            let i = f.add_block_param(h, Ty::U64);
            let acc = f.add_block_param(h, Ty::U64);
            let y0 = add_const(&mut f, args[0], 1);
            f.br(p, vec![]);
            f.switch_to_block(p);
            let three = f.iconst(Ty::U64, 3);
            let y = f.mul(Ty::U64, y0, three);
            let zero = f.iconst(Ty::U64, 0);
            f.br(h, vec![zero, zero]);
            f.switch_to_block(h);
            let c = f.icmp(ICmpOp::Ult, Ty::U64, i, args[1]);
            f.condbr(c, b, vec![], x, vec![]);
            f.switch_to_block(b);
            let acc2 = f.add(Ty::U64, acc, y);
            let i2 = add_const(&mut f, i, 1);
            f.br(h, vec![i2, acc2]);
            f.switch_to_block(x);
            f.ret(vec![acc]);
        }
        (Some(LatchTail), _) | (_, Some(CopyAcrossSeam)) => {
            let (h, b1, b2, x) = (
                f.create_block(),
                f.create_block(),
                f.create_block(),
                f.create_block(),
            );
            let i = f.add_block_param(h, Ty::U64);
            let acc = f.add_block_param(h, Ty::U64);
            let zero = f.iconst(Ty::U64, 0);
            f.br(h, vec![zero, zero]);
            f.switch_to_block(h);
            let c = f.icmp(ICmpOp::Ult, Ty::U64, i, args[0]);
            f.condbr(c, b1, vec![], x, vec![]);
            f.switch_to_block(b1);
            let t = f.add(Ty::U64, acc, i);
            let i2 = add_const(&mut f, i, 1);
            let t = if variant == Some(CopyAcrossSeam) {
                f.copy(Ty::U64, t)
            } else {
                t
            };
            f.br(b2, vec![]);
            f.switch_to_block(b2);
            f.br(h, vec![i2, t]);
            f.switch_to_block(x);
            f.ret(vec![acc]);
        }
        (Some(SeamFlags), _) => {
            let (n, t, e) = (f.create_block(), f.create_block(), f.create_block());
            let c = f.icmp(ICmpOp::Ult, Ty::U64, args[0], args[1]);
            let z = f.zext(Ty::Bool, Ty::U64, c);
            f.br(n, vec![]);
            f.switch_to_block(n);
            let c2 = f.icmp(ICmpOp::Ult, Ty::U64, args[0], args[1]);
            f.condbr(c2, t, vec![], e, vec![]);
            f.switch_to_block(t);
            f.ret(vec![z]);
            f.switch_to_block(e);
            let s = f.add(Ty::U64, z, args[0]);
            f.ret(vec![s]);
        }
        (Some(CallsAndMemory), _) => {
            let (x, y, r, j) = (
                f.create_block(),
                f.create_block(),
                f.create_block(),
                f.create_block(),
            );
            let jv = f.add_block_param(j, Ty::U64);
            let zero = f.iconst(Ty::U64, 0);
            let c = f.icmp(ICmpOp::Eq, Ty::U64, args[1], zero);
            f.condbr(c, x, vec![], r, vec![]);
            f.switch_to_block(x);
            f.call_void(sink, vec![args[1]]);
            f.store(Ty::U64, args[0], args[1]);
            f.br(y, vec![]);
            f.switch_to_block(y);
            let v = f.load(Ty::U64, args[0]);
            let w = f.call(narrow, vec![v]);
            let w = f.zext(Ty::U32, Ty::U64, w);
            f.br(j, vec![w]);
            f.switch_to_block(r);
            f.br(j, vec![args[1]]);
            f.switch_to_block(j);
            f.ret(vec![jv]);
        }
        (Some(GuardThenDivide), _) => {
            let (x, r, j) = (f.create_block(), f.create_block(), f.create_block());
            let jv = f.add_block_param(j, Ty::U64);
            let hundred = f.iconst(Ty::U64, 100);
            let c = f.icmp(ICmpOp::Ult, Ty::U64, args[0], hundred);
            f.condbr(c, x, vec![], r, vec![]);
            f.switch_to_block(x);
            let q = f.binop_proven(
                BinOp::UDiv,
                Ty::U64,
                args[0],
                args[1],
                vec![ProofAnnotation::DivNonZero],
            );
            f.br(j, vec![q]);
            f.switch_to_block(r);
            f.br(j, vec![args[0]]);
            f.switch_to_block(j);
            f.ret(vec![jv]);
        }
        (Some(SeventeenBlocks), _) => {
            let (l, r, j) = (f.create_block(), f.create_block(), f.create_block());
            let jv = f.add_block_param(j, Ty::U64);
            let c = f.icmp(ICmpOp::Ult, Ty::U64, args[0], args[1]);
            f.condbr(c, l, vec![], r, vec![]);
            f.switch_to_block(l);
            f.br(j, vec![args[0]]);
            f.switch_to_block(r);
            f.br(j, vec![args[1]]);
            f.switch_to_block(j);
            let w = add_const(&mut f, jv, 1);
            // `returning_chain`, its last member multiplying by 3 before
            // the return.
            let chain: Vec<_> = (0..13).map(|_| f.create_block()).collect();
            f.br(chain[0], vec![]);
            let mut value = w;
            for (i, block) in chain.iter().enumerate() {
                f.switch_to_block(*block);
                value = add_const(&mut f, value, i as i128 + 1);
                if i + 1 < chain.len() {
                    f.br(chain[i + 1], vec![]);
                } else {
                    let three = f.iconst(Ty::U64, 3);
                    let tripled = f.mul(Ty::U64, value, three);
                    f.ret(vec![tripled]);
                }
            }
        }
        (Some(PerPathChain), _) => {
            let length = 4;
            let (l, r) = (f.create_block(), f.create_block());
            let c = f.icmp(ICmpOp::Ult, Ty::U64, args[0], args[1]);
            f.condbr(c, l, vec![], r, vec![]);
            f.switch_to_block(l);
            returning_chain(&mut f, args[0], length - 1);
            f.switch_to_block(r);
            returning_chain(&mut f, args[1], length - 1);
        }
        (Some(SilentHead), _) => {
            let (r, m, e, j) = (
                f.create_block(),
                f.create_block(),
                f.create_block(),
                f.create_block(),
            );
            let jv = f.add_block_param(j, Ty::U64);
            let c = f.icmp(ICmpOp::Ult, Ty::U64, args[0], args[1]);
            f.condbr(c, r, vec![], e, vec![]);
            f.switch_to_block(r);
            f.br(m, vec![]);
            f.switch_to_block(m);
            let three = f.iconst(Ty::U64, 3);
            let x = f.mul(Ty::U64, args[0], three);
            f.br(j, vec![x]);
            f.switch_to_block(e);
            f.br(j, vec![args[1]]);
            f.switch_to_block(j);
            f.ret(vec![jv]);
        }
        (Some(TenMembers), _) => {
            let chain: Vec<_> = (0..10).map(|_| f.create_block()).collect();
            let (r, j) = (f.create_block(), f.create_block());
            let jv = f.add_block_param(j, Ty::U64);
            let c = f.icmp(ICmpOp::Ult, Ty::U64, args[0], args[1]);
            f.condbr(c, chain[0], vec![], r, vec![]);
            let mut value = args[0];
            for (i, block) in chain.iter().enumerate() {
                f.switch_to_block(*block);
                value = add_const(&mut f, value, i as i128 + 1);
                if i + 1 < chain.len() {
                    f.br(chain[i + 1], vec![]);
                } else {
                    f.br(j, vec![value]);
                }
            }
            f.switch_to_block(r);
            f.br(j, vec![args[1]]);
            f.switch_to_block(j);
            f.ret(vec![jv]);
        }
        (Some(PartialMerge), _) => {
            let (x, y, c1, c2, j) = (
                f.create_block(),
                f.create_block(),
                f.create_block(),
                f.create_block(),
                f.create_block(),
            );
            let jv = f.add_block_param(j, Ty::U64);
            let c = f.icmp(ICmpOp::Ult, Ty::U64, args[0], args[1]);
            f.condbr(c, x, vec![], c1, vec![]);
            f.switch_to_block(x);
            let t = add_const(&mut f, args[0], 1);
            f.br(y, vec![]);
            f.switch_to_block(y);
            let u = f.mul(Ty::U64, t, args[1]);
            f.br(j, vec![u]);
            f.switch_to_block(c1);
            let s = f.sub(Ty::U64, args[0], args[1]);
            f.br(c2, vec![]);
            f.switch_to_block(c2);
            let w = add_const(&mut f, s, 7);
            f.br(j, vec![w]);
            f.switch_to_block(j);
            f.ret(vec![jv]);
        }
        (_, Some(AbsorbedParams)) => {
            let (x, y, r, j) = (
                f.create_block(),
                f.create_block(),
                f.create_block(),
                f.create_block(),
            );
            let p = f.add_block_param(y, Ty::U64);
            let jv = f.add_block_param(j, Ty::U64);
            let c = f.icmp(ICmpOp::Ult, Ty::U64, args[0], args[1]);
            f.condbr(c, x, vec![], r, vec![]);
            f.switch_to_block(x);
            let t = add_const(&mut f, args[0], 1);
            f.br(y, vec![t]);
            f.switch_to_block(y);
            let u = f.mul(Ty::U64, p, args[1]);
            f.br(j, vec![u]);
            f.switch_to_block(r);
            f.br(j, vec![args[1]]);
            f.switch_to_block(j);
            f.ret(vec![jv]);
        }
        (_, Some(DoWhile)) => {
            let (h, t, x) = (f.create_block(), f.create_block(), f.create_block());
            f.br(h, vec![]);
            f.switch_to_block(h);
            let v = f.call(g, vec![args[0]]);
            f.br(t, vec![]);
            f.switch_to_block(t);
            let zero = f.iconst(Ty::U64, 0);
            let c = f.icmp(ICmpOp::Ne, Ty::U64, v, zero);
            f.condbr(c, h, vec![], x, vec![]);
            f.switch_to_block(x);
            f.ret(vec![zero]);
        }
        (_, Some(SilentStore)) => {
            let (x, s, y, r, j) = (
                f.create_block(),
                f.create_block(),
                f.create_block(),
                f.create_block(),
                f.create_block(),
            );
            let jv = f.add_block_param(j, Ty::U64);
            let zero = f.iconst(Ty::U64, 0);
            let c = f.icmp(ICmpOp::Eq, Ty::U64, args[1], zero);
            f.condbr(c, x, vec![], r, vec![]);
            f.switch_to_block(x);
            let t = add_const(&mut f, args[1], 1);
            f.br(s, vec![]);
            f.switch_to_block(s);
            f.store(Ty::U64, args[0], t);
            f.br(y, vec![]);
            f.switch_to_block(y);
            let v = f.load(Ty::U64, args[0]);
            f.br(j, vec![v]);
            f.switch_to_block(r);
            f.br(j, vec![args[1]]);
            f.switch_to_block(j);
            f.ret(vec![jv]);
        }
        (_, Some(GuardBeforeBranch)) => {
            let (b1, b2, b3) = (f.create_block(), f.create_block(), f.create_block());
            let q = f.binop_proven(
                BinOp::UDiv,
                Ty::U64,
                args[0],
                args[1],
                vec![ProofAnnotation::DivNonZero],
            );
            f.br(b1, vec![]);
            f.switch_to_block(b1);
            let zero = f.iconst(Ty::U64, 0);
            let c = f.icmp(ICmpOp::Eq, Ty::U64, q, zero);
            f.condbr(c, b2, vec![], b3, vec![]);
            f.switch_to_block(b2);
            let one = f.iconst(Ty::U64, 1);
            f.ret(vec![one]);
            f.switch_to_block(b3);
            f.ret(vec![q]);
        }
        (_, Some(OnePathChain)) => {
            let n = f.create_block();
            let x = f.add(Ty::U64, args[0], args[1]);
            f.br(n, vec![]);
            f.switch_to_block(n);
            let y = f.mul(Ty::U64, x, args[1]);
            f.ret(vec![y]);
        }
        (_, Some(FloatConstChain)) => {
            let (x, y, r) = (f.create_block(), f.create_block(), f.create_block());
            let c = f.icmp(ICmpOp::Ult, Ty::U64, args[0], args[1]);
            f.condbr(c, x, vec![], r, vec![]);
            f.switch_to_block(x);
            let k = f.fconst(Ty::F64, 1.5);
            f.br(y, vec![]);
            f.switch_to_block(y);
            f.call_void(sink, vec![args[0]]);
            f.ret(vec![k]);
            f.switch_to_block(r);
            let k2 = f.fconst(Ty::F64, 2.5);
            f.ret(vec![k2]);
        }
        (_, Some(NanConstChain)) => {
            let (x, y, r) = (f.create_block(), f.create_block(), f.create_block());
            let c = f.icmp(ICmpOp::Ult, Ty::U64, args[0], args[1]);
            f.condbr(c, x, vec![], r, vec![]);
            f.switch_to_block(x);
            let k = f.fconst(Ty::F64, f64::NAN);
            f.br(y, vec![]);
            f.switch_to_block(y);
            f.call_void(sink, vec![args[0]]);
            f.ret(vec![k]);
            f.switch_to_block(r);
            let k2 = f.fconst(Ty::F64, -0.0);
            f.ret(vec![k2]);
        }
        (_, Some(NoParamEntry)) => {
            let (m, t, e) = (f.create_block(), f.create_block(), f.create_block());
            let seven = f.iconst(Ty::U64, 7);
            let v = f.call(g, vec![seven]);
            f.br(m, vec![]);
            f.switch_to_block(m);
            let zero = f.iconst(Ty::U64, 0);
            let c = f.icmp(ICmpOp::Ne, Ty::U64, v, zero);
            f.condbr(c, t, vec![], e, vec![]);
            f.switch_to_block(t);
            let one = f.iconst(Ty::U64, 1);
            f.ret(vec![one]);
            f.switch_to_block(e);
            f.ret(vec![v]);
        }
        (_, Some(RoutineChain)) => {
            let (trap, go, y) = (f.create_block(), f.create_block(), f.create_block());
            let zero = f.iconst(Ty::U128, 0);
            let is_zero = f.icmp(ICmpOp::Eq, Ty::U128, args[1], zero);
            f.condbr(is_zero, trap, vec![], go, vec![]);
            f.switch_to_block(trap);
            f.unreachable();
            f.switch_to_block(go);
            let q = f.binop(BinOp::UDiv, Ty::U128, args[0], args[1]);
            f.br(y, vec![]);
            f.switch_to_block(y);
            let r = f.binop(BinOp::Xor, Ty::U128, q, args[0]);
            f.ret(vec![r]);
        }
        (_, Some(LongChain)) => {
            let (l, r, j) = (f.create_block(), f.create_block(), f.create_block());
            let jv = f.add_block_param(j, Ty::U64);
            let c = f.icmp(ICmpOp::Ult, Ty::U64, args[0], args[1]);
            f.condbr(c, l, vec![], r, vec![]);
            f.switch_to_block(l);
            f.br(j, vec![args[0]]);
            f.switch_to_block(r);
            f.br(j, vec![args[1]]);
            f.switch_to_block(j);
            let w = add_const(&mut f, jv, 1);
            returning_chain(&mut f, w, LONG_CHAIN);
        }
        other => unreachable!("{other:?}"),
    }
    f.build();
    let _ = g;
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

pub(crate) fn slice24_lir(shape: Shape24) -> Function {
    slice24_function(shape.name(), Some(shape), None)
}

pub(crate) fn slice24_variant_lir(variant: Variant24) -> Function {
    slice24_function(variant.name(), None, Some(variant))
}

// ---- machine edits and LIR surgery

/// `X86BlockMerge` on `machine`, as the O2 schedule runs it; the number of
/// merges.
pub(crate) fn block_merged(machine: &mut X86ISelFunction) -> usize {
    let mut pass = trust_cg_opt::X86BlockMerge::new();
    trust_cg_opt::X86MachinePass::run(&mut pass, machine);
    pass.last_run_merges()
}

/// `machine` with `X86BlockMerge` run, asserted to merge.
#[track_caller]
fn merged(what: &str, source: &Function, mut machine: X86ISelFunction) -> X86ISelFunction {
    let merges = block_merged(&mut machine);
    assert!(
        merges > 0,
        "{what}: the block merge merged nothing (is TCG_NO_X86_BLOCK_MERGE set?)\n{}{}",
        describe_lir(source),
        describe(&machine)
    );
    machine
}

/// Machine block `b` joined into `a` exactly as `X86BlockMerge::merge_once`
/// joins it (`a`'s final `jmp b` dropped, `b`'s rows appended, `b`'s
/// successors taken), without the renumbering.
fn merge_machine(machine: &mut X86ISelFunction, a: Block, b: Block) {
    let joined = machine.blocks.remove(&b).expect("a machine block");
    let into = machine.blocks.get_mut(&a).expect("a machine block");
    let jmp = into.insts.pop().expect("a terminator");
    assert_eq!(jmp.operands, vec![O::Block(b)], "{a:?} ends in jmp {b:?}");
    into.insts.extend(joined.insts);
    into.successors = joined.successors;
    machine.block_order.retain(|block| *block != b);
}

/// The stamp of a row: its LIR block and index.
fn stamp(inst: &X86ISelInst) -> Option<(Block, usize)> {
    inst.lowering_provenance
        .source_id()
        .map(|id| (Block(id.block), id.index as usize))
}

/// The walk ordinals of the rows stamped with LIR block `lir`.
fn stamped(machine: &X86ISelFunction, lir: Block) -> Vec<usize> {
    rows(machine)
        .into_iter()
        .filter(|(_, block, index)| {
            stamp(&machine.blocks[block].insts[*index]).is_some_and(|(b, _)| b == lir)
        })
        .map(|(ordinal, _, _)| ordinal)
        .collect()
}

/// Row `ordinal` restamped as instruction `index` of LIR block `block`, its
/// digest that instruction's when it has one.
fn restamp(
    machine: &mut X86ISelFunction,
    source: &Function,
    ordinal: usize,
    block: Block,
    index: usize,
) {
    let digest = source
        .blocks
        .get(&block)
        .and_then(|body| body.instructions.get(index))
        .map(Instruction::lowering_digest);
    match &mut inst_mut(machine, ordinal).lowering_provenance {
        LoweringProvenance::SourceInst {
            id, digest: old, ..
        } => {
            id.block = block.0;
            id.index = index as u32;
            if let Some(digest) = digest {
                *old = digest;
            }
        }
        other => panic!("row {ordinal} is {other:?}"),
    }
}

/// The two targets of `block`'s `Brif`.
fn brif_targets(source: &Function, block: Block) -> (Block, Block) {
    match source.blocks[&block]
        .instructions
        .last()
        .map(|inst| &inst.opcode)
    {
        Some(L::Brif {
            then_dest,
            else_dest,
            ..
        }) => (*then_dest, *else_dest),
        other => panic!("{block:?} ends in {other:?}"),
    }
}

/// The target of `block`'s `Jump`.
fn jump_dest(source: &Function, block: Block) -> Block {
    match source.blocks[&block]
        .instructions
        .last()
        .map(|inst| &inst.opcode)
    {
        Some(L::Jump { dest }) => *dest,
        other => panic!("{block:?} ends in {other:?}"),
    }
}

/// The smallest id above every LIR block of `source`.
fn fresh_block(source: &Function) -> Block {
    Block(source.blocks.keys().map(|block| block.0).max().unwrap_or(0) + 1)
}

/// LIR block `block` cut before its instruction `at` into itself (the
/// instructions before, then `Jump` to a new block) and a new block laid out
/// right after it (the rest, no parameter), every row stamped with an
/// instruction it moved restamped there: the exact inverse of contracting a
/// link, so the pair is what a block merge of the two would have produced.
pub(crate) fn split_lir(
    source: &mut Function,
    machine: &mut X86ISelFunction,
    block: Block,
    at: usize,
) -> Block {
    let fresh = fresh_block(source);
    let body = source.blocks.get_mut(&block).expect("a LIR block");
    let len = body.instructions.len();
    assert!(0 < at && at < len, "{block:?}: cut at {at} of {len}");
    let rest = body.instructions.split_off(at);
    body.instructions.push(Instruction {
        opcode: L::Jump { dest: fresh },
        args: vec![],
        results: vec![],
    });
    let rest_locs = if body.source_locs.is_empty() {
        Vec::new()
    } else {
        body.source_locs.resize(len, None);
        let rest = body.source_locs.split_off(at);
        body.source_locs.push(None);
        rest
    };
    if let Some(origins) = source.trust_ir_origins.get_mut(&block) {
        origins.resize(len, None);
        let rest = origins.split_off(at);
        origins.push(None);
        source.trust_ir_origins.insert(fresh, rest);
    }
    source.blocks.insert(
        fresh,
        trust_cg_lower::function::BasicBlock {
            params: Vec::new(),
            instructions: rest,
            source_locs: rest_locs,
        },
    );
    let position = source
        .block_order
        .iter()
        .position(|b| *b == block)
        .expect("a laid-out block");
    source.block_order.insert(position + 1, fresh);
    for body in machine.blocks.values_mut() {
        for inst in &mut body.insts {
            if let LoweringProvenance::SourceInst { id, .. } = &mut inst.lowering_provenance
                && id.block == block.0
                && id.index as usize >= at
            {
                id.block = fresh.0;
                id.index -= at as u32;
            }
        }
    }
    fresh
}

/// An unreachable LIR block `[Jump dest]` added to `source` (no machine
/// block lowers it).
fn add_dead_jump(source: &mut Function, dest: Block) -> Block {
    let fresh = fresh_block(source);
    source.blocks.insert(
        fresh,
        trust_cg_lower::function::BasicBlock {
            params: Vec::new(),
            instructions: vec![Instruction {
                opcode: L::Jump { dest },
                args: vec![],
                results: vec![],
            }],
            source_locs: Vec::new(),
        },
    );
    source.block_order.push(fresh);
    fresh
}

/// LIR blocks `a` and `b` renamed into each other's ids everywhere (the
/// blocks, the layout, the origins, the entry, every terminator's targets
/// and every machine stamp), each stamp's digest recomputed.
fn swap_lir_ids(source: &mut Function, machine: &mut X86ISelFunction, a: Block, b: Block) {
    let swap = |block: Block| {
        if block == a {
            b
        } else if block == b {
            a
        } else {
            block
        }
    };
    let blocks = std::mem::take(&mut source.blocks);
    for (block, mut body) in blocks {
        for inst in &mut body.instructions {
            match &mut inst.opcode {
                L::Jump { dest } => *dest = swap(*dest),
                L::Brif {
                    then_dest,
                    else_dest,
                    ..
                } => {
                    *then_dest = swap(*then_dest);
                    *else_dest = swap(*else_dest);
                }
                L::Switch { cases, default } => {
                    for (_, target) in cases.iter_mut() {
                        *target = swap(*target);
                    }
                    *default = swap(*default);
                }
                _ => {}
            }
        }
        source.blocks.insert(swap(block), body);
    }
    source.block_order = source
        .block_order
        .iter()
        .map(|block| swap(*block))
        .collect();
    let origins = std::mem::take(&mut source.trust_ir_origins);
    source.trust_ir_origins = origins
        .into_iter()
        .map(|(block, origins)| (swap(block), origins))
        .collect();
    source.entry_block = swap(source.entry_block);
    for body in machine.blocks.values_mut() {
        for inst in &mut body.insts {
            if let LoweringProvenance::SourceInst { id, digest, .. } = &mut inst.lowering_provenance
            {
                let block = swap(Block(id.block));
                id.block = block.0;
                if let Some(lir) = source.blocks[&block].instructions.get(id.index as usize) {
                    *digest = lir.lowering_digest();
                }
            }
        }
    }
}

/// The register copy row stamped with LIR block `lir` deleted, every later
/// read of its destination in its machine block renamed to its source (copy
/// propagation).
fn propagate_copy(machine: &mut X86ISelFunction, lir: Block) {
    let [ordinal] = stamped(machine, lir)[..] else {
        panic!("one row lowers {lir:?}\n{}", describe(machine));
    };
    let (_, block, index) = rows(machine)[ordinal];
    let row = remove_at(machine, ordinal);
    assert!(
        matches!(row.opcode, X86Opcode::MovRR | X86Opcode::MovRR32),
        "{lir:?} is a register copy: {row:?}"
    );
    let (dst, src) = (row.operands[0].clone(), row.operands[1].clone());
    for later in &mut machine.blocks.get_mut(&block).unwrap().insts[index..] {
        for operand in &mut later.operands {
            if *operand == dst {
                *operand = src.clone();
            }
        }
    }
}

/// A fixture's pair: the selector's stream, block-merged (or as the shape
/// names), with the shape's hand edit.
pub(crate) fn slice24_pair(shape: Shape24) -> (Function, X86ISelFunction) {
    use Shape24::*;
    let what = format!("{shape:?}");
    let mut source = slice24_lir(shape);
    let selected = select(&source, X86CallAbi::SystemV);
    let entry = source.entry_block;
    let mut machine = match shape {
        GuardThenDivide => {
            let mut machine = selected;
            let (x, _) = brif_targets(&source, entry);
            let guard = source.blocks[&x]
                .instructions
                .iter()
                .position(|inst| matches!(inst.opcode, L::GuardDivZero { .. }))
                .unwrap_or_else(|| panic!("{what}: a GuardDivZero\n{}", describe_lir(&source)));
            split_lir(&mut source, &mut machine, x, guard + 1);
            machine
        }
        PartialMerge => {
            let mut machine = selected;
            let (x, c1) = brif_targets(&source, entry);
            let y = jump_dest(&source, x);
            merge_machine(&mut machine, x, y);
            // `c1`'s `jmp c2` deleted: `c2` is laid out next (a fallthrough,
            // as branch layout leaves it), so no row names `c1`'s `Jump`.
            let c2 = jump_dest(&source, c1);
            let body = machine.blocks.get_mut(&c1).expect("c1's machine block");
            assert_eq!(
                body.insts
                    .last()
                    .map(|inst| (inst.opcode, inst.operands.clone())),
                Some((X86Opcode::Jmp, vec![O::Block(c2)])),
                "{what}: c1 ends in jmp c2"
            );
            body.insts.pop();
            let at = machine.block_order.iter().position(|b| *b == c1).unwrap();
            assert_eq!(
                machine.block_order.get(at + 1),
                Some(&c2),
                "{what}: c2 follows c1"
            );
            machine
        }
        _ => merged(&what, &source, selected),
    };
    match shape {
        SilentCopyMember => {
            let (x, _) = brif_targets(&source, entry);
            propagate_copy(&mut machine, jump_dest(&source, x));
        }
        SilentTail => {
            let (_, x) = brif_targets(&source, entry);
            let y = jump_dest(&source, x);
            let [ordinal] = stamped(&machine, y)[..] else {
                panic!("{what}: one row lowers {y:?}\n{}", describe(&machine));
            };
            let (_, block, index) = rows(&machine)[ordinal];
            let body = &machine.blocks[&block];
            assert_eq!(index + 1, body.insts.len(), "{what}: the final row");
            assert_eq!(body.insts[index].opcode, X86Opcode::Jmp, "{what}");
            let O::Block(target) = body.insts[index].operands[0] else {
                panic!("{what}: a jmp to a block");
            };
            let at = machine
                .block_order
                .iter()
                .position(|b| *b == block)
                .unwrap();
            assert_eq!(
                machine.block_order.get(at + 1),
                Some(&target),
                "{what}: the jmp's target is laid out next\n{}",
                describe(&machine)
            );
            remove_at(&mut machine, ordinal);
        }
        SeamFlags => {
            let n = jump_dest(&source, entry);
            let compare = stamped(&machine, n)
                .into_iter()
                .find(|ordinal| inst(&machine, *ordinal).opcode == X86Opcode::CmpRR)
                .unwrap_or_else(|| panic!("{what}: n's compare\n{}", describe(&machine)));
            remove_at(&mut machine, compare);
        }
        _ => {}
    }
    (source, machine)
}

/// A variant's pair: the selector's stream, block-merged.
pub(crate) fn variant24_pair(variant: Variant24) -> (Function, X86ISelFunction) {
    let source = slice24_variant_lir(variant);
    let machine = merged(
        &format!("{variant:?}"),
        &source,
        select(&source, X86CallAbi::SystemV),
    );
    (source, machine)
}

/// The laid-out machine block whose rows name LIR block `lir`.
#[track_caller]
fn machine_block_of(machine: &X86ISelFunction, lir: Block) -> Block {
    machine
        .block_order
        .iter()
        .copied()
        .find(|block| {
            machine.blocks[block]
                .insts
                .iter()
                .any(|inst| stamp(inst).is_some_and(|(b, _)| b == lir))
        })
        .unwrap_or_else(|| panic!("a machine block lowers {lir:?}\n{}", describe(machine)))
}

/// D2 over a folded branch, a hand edit (no x86-64 pass folds a `jcc` on a
/// known value: `X86ConstantFolding` keeps every branch row):
/// [`Shape24::JoinChain`] with every row stamped with the entry's `Brif`
/// deleted, `l`'s machine block joined into the entry's and `r`'s deleted
/// (dead code). No row names the `Brif`, so the removed-`Jump`
/// decline (D7) cannot fire: only the `Jump` clauses of the link rule (the
/// builder's and `Quotient::check`'s) refuse to contract `entry -> l`. A
/// WRONG lowering (the machine always takes `l`; the source takes `r` when
/// `a != 0`): contracted over its `Brif`, the quotient would drop the branch
/// and its theorem would hold.
pub(crate) fn folded_brif() -> (Function, X86ISelFunction) {
    let (source, mut machine) = slice24_pair(Shape24::JoinChain);
    let entry = source.entry_block;
    let (l, r) = brif_targets(&source, entry);
    let brif = source.blocks[&entry].instructions.len() - 1;
    let [head, left, right] = [entry, l, r].map(|lir| machine_block_of(&machine, lir));
    for body in machine.blocks.values_mut() {
        body.insts.retain(|inst| stamp(inst) != Some((entry, brif)));
    }
    assert!(
        machine.blocks[&head]
            .insts
            .iter()
            .all(|inst| !matches!(inst.opcode, X86Opcode::Jmp | X86Opcode::Jcc)),
        "D2 folded: the entry's transfers are the Brif's rows\n{}",
        describe(&machine)
    );
    let joined = machine.blocks.remove(&left).expect("l's machine block");
    machine.blocks.remove(&right).expect("r's machine block");
    let body = machine
        .blocks
        .get_mut(&head)
        .expect("the entry's machine block");
    body.insts.extend(joined.insts);
    body.successors = joined.successors;
    machine
        .block_order
        .retain(|block| *block != left && *block != right);
    (source, machine)
}

/// [`Variant24::NoParamEntry`] with a dead, stamp-silent `[Jump entry]`:
/// the entry is a LIR block one `Jump` enters, so only the not-the-entry
/// clauses of the link rule keep the dead block from heading the entry's
/// chain (no parameter to decline, no row to stamp).
pub(crate) fn entry_behind_a_dead_jump() -> (Function, X86ISelFunction) {
    let (mut source, machine) = variant24_pair(Variant24::NoParamEntry);
    let entry = source.entry_block;
    add_dead_jump(&mut source, entry);
    (source, machine)
}

/// The further pairs the controls name, by label.
#[track_caller]
pub(crate) fn extra24(label: &str) -> (Function, X86ISelFunction) {
    match label {
        "D2 folded" => folded_brif(),
        "entry behind a dead Jump" => entry_behind_a_dead_jump(),
        "long chain" => variant24_pair(Variant24::LongChain),
        "routine chain" => variant24_pair(Variant24::RoutineChain),
        other => panic!("no extra pair {other}"),
    }
}

/// The owner of a pair (the production route).
pub(crate) fn owner24<'a>(
    source: &'a Function,
    machine: &'a X86ISelFunction,
) -> Result<SourceBoundX86Body<'a>, X86BodyRefusal> {
    source_bound_x86_body(source, machine, SYSV)
}

/// The owner of a pair stated in parts at `points` (original coordinates).
pub(crate) fn parts24<'a>(
    source: &'a Function,
    machine: &'a X86ISelFunction,
    points: Vec<(Block, usize)>,
) -> Result<SourceBoundX86Body<'a>, X86BodyRefusal> {
    source_bound_x86_body_in_parts(source, machine, SYSV, &cut_at(points))
}

pub(crate) type PartsFixture24 = (&'static str, Function, X86ISelFunction, Vec<(Block, usize)>);

/// F14: the parts fixtures: label, pair, policy points (a head's start and
/// an absorbed member's start, a seam cut; [`Shape24::JoinChain`]'s
/// absorbed `n` is its largest LIR id).
pub(crate) fn parts_fixtures() -> Vec<PartsFixture24> {
    let mut fixtures = Vec::new();
    let (source, machine) = slice24_pair(Shape24::JoinChain);
    let (l, _) = brif_targets(&source, source.entry_block);
    let j = jump_dest(&source, l);
    let k = jump_dest(&source, j);
    fixtures.push((
        "JoinChain at j and k",
        source,
        machine,
        vec![(j, 0), (k, 0)],
    ));
    let (source, machine) = slice24_pair(Shape24::LoopBodyChain);
    let h = jump_dest(&source, source.entry_block);
    let (b1, _) = brif_targets(&source, h);
    let b2 = jump_dest(&source, b1);
    fixtures.push((
        "LoopBodyChain at h and b2",
        source,
        machine,
        vec![(h, 0), (b2, 0)],
    ));
    fixtures
}

/// The theorem's query as the replay renders it.
pub(crate) fn text(obligation: &ProofObligation) -> String {
    generate_smt2_query_raw(obligation, &replay_config())
}

/// Whether an owner's theorem (every part, for one stated in parts) holds on
/// slice 9's keyed samples.
pub(crate) fn owner_holds(owner: &SourceBoundX86Body<'_>) -> Result<(), String> {
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
pub(crate) fn owner_refuted(owner: &SourceBoundX86Body<'_>) -> bool {
    if owner.is_stated_in_parts() {
        some_part_refuted(owner)
    } else {
        dag_refuted_on_samples(owner.obligation())
    }
}

/// The text of a refusal.
fn refusal_text(result: &Result<SourceBoundX86Body<'_>, X86BodyRefusal>) -> String {
    match result {
        Ok(_) => "stated".into(),
        Err(refusal) => format!("{refusal}"),
    }
}

// ---- refusal controls and wrong lowerings (sources, pairs, edits)

/// Design §3's named refusals: label, pair, route (`Some(points)`: in parts
/// at `points`), the substring the refusal must hold.
pub(crate) type Refusal24 = (
    &'static str,
    Function,
    X86ISelFunction,
    Option<Vec<(Block, usize)>>,
    &'static str,
);

/// F2's blocks: `(l, r, j, k, n)`.
fn join_blocks(source: &Function) -> (Block, Block, Block, Block, Block) {
    let (l, r) = brif_targets(source, source.entry_block);
    let j = jump_dest(source, l);
    let k = jump_dest(source, j);
    let n = jump_dest(source, k);
    (l, r, j, k, n)
}

/// The walk ordinal of the first row stamped with `lir`.
#[track_caller]
fn first_stamped(machine: &X86ISelFunction, lir: Block) -> usize {
    *stamped(machine, lir)
        .first()
        .unwrap_or_else(|| panic!("a row lowers {lir:?}\n{}", describe(machine)))
}

pub(crate) fn refusal_controls() -> Vec<Refusal24> {
    let mut controls: Vec<Refusal24> = Vec::new();
    // D1, live: `l`'s machine block names `j` too, which `r` also enters.
    let (source, mut machine) = slice24_pair(Shape24::JoinChain);
    let (l, _, j, _, _) = join_blocks(&source);
    let row = first_stamped(&machine, l);
    restamp(&mut machine, &source, row, j, 0);
    controls.push(("D1 live", source, machine, None, "is entered from ["));
    // D1, unreachable: a dead `[Jump k]` enters the member `k` too.
    let (mut source, machine) = slice24_pair(Shape24::JoinChain);
    let (_, _, _, k, _) = join_blocks(&source);
    add_dead_jump(&mut source, k);
    controls.push((
        "D1 unreachable",
        source,
        machine,
        None,
        "(unreachable)], not from",
    ));
    // D2: `l`'s machine block names the entry, whose `Brif` enters `l`.
    let (source, mut machine) = slice24_pair(Shape24::JoinChain);
    let (l, _, _, _, _) = join_blocks(&source);
    let row = first_stamped(&machine, l);
    restamp(&mut machine, &source, row, source.entry_block, 0);
    controls.push((
        "D2",
        source,
        machine,
        None,
        "ends in a Brif, not a Jump to it",
    ));
    // D2 over a folded branch (no row names the `Brif`).
    let (source, machine) = folded_brif();
    controls.push((
        "D2 folded",
        source,
        machine,
        None,
        "ends in a Brif, not a Jump to it",
    ));
    // D3: a dead `[Jump entry]` with the smallest id, named by the entry's
    // machine block.
    let (mut source, mut machine) = slice24_pair(Shape24::JoinChain);
    let entry = source.entry_block;
    let dead = add_dead_jump(&mut source, entry);
    swap_lir_ids(&mut source, &mut machine, entry, dead);
    let row = first_stamped(&machine, source.entry_block);
    restamp(&mut machine, &source, row, entry, 0);
    controls.push(("D3", source, machine, None, "is the entry block"));
    // D4: the merged `x + y` block holds a row of `c2`, whose predecessor
    // `c1` another machine block lowers.
    let (source, mut machine) = slice24_pair(Shape24::PartialMerge);
    let (x, c1) = brif_targets(&source, source.entry_block);
    let c2 = jump_dest(&source, c1);
    let row = first_stamped(&machine, x);
    restamp(&mut machine, &source, row, c2, 0);
    controls.push((
        "D4",
        source,
        machine,
        None,
        "is not on the chain of single-entry Jumps through",
    ));
    // D5, both routes.
    for route in [None, Some(Vec::new())] {
        let (source, machine) = variant24_pair(Variant24::AbsorbedParams);
        controls.push((
            if route.is_none() { "D5" } else { "D5 parts" },
            source,
            machine,
            route,
            "would absorb, has 1 parameter(s)",
        ));
    }
    // D6.
    let (source, machine) = variant24_pair(Variant24::DoWhile);
    controls.push(("D6", source, machine, None, "returns to its head"));
    // D7: a row of `k` stamped with the `Jump` that ends `j`.
    let (source, mut machine) = slice24_pair(Shape24::JoinChain);
    let (_, _, j, k, _) = join_blocks(&source);
    let row = first_stamped(&machine, k);
    let jump = source.blocks[&j].instructions.len() - 1;
    restamp(&mut machine, &source, row, j, jump);
    controls.push((
        "D7",
        source,
        machine,
        None,
        "is stamped with the Jump that ends LIR block",
    ));
    // D8: a row of `k` stamped past its end.
    let (source, mut machine) = slice24_pair(Shape24::JoinChain);
    let (_, _, _, k, _) = join_blocks(&source);
    let row = first_stamped(&machine, k);
    restamp(&mut machine, &source, row, k, 99);
    controls.push((
        "D8",
        source,
        machine,
        None,
        "is stamped with instruction 99 of LIR block",
    ));
    // D9.
    let (source, machine) = variant24_pair(Variant24::DeadCycle);
    controls.push((
        "D9",
        source,
        machine,
        None,
        "form a cycle of single-entry Jumps",
    ));
    // D10.
    let (source, machine) = variant24_pair(Variant24::CopyAcrossSeam);
    controls.push(("D10", source, machine, None, "into loop header"));
    // Every row of `r` restamped as `k`: two machine blocks lower the
    // quotient's `j`.
    let (source, mut machine) = slice24_pair(Shape24::JoinChain);
    let (_, r, _, k, _) = join_blocks(&source);
    for row in stamped(&machine, r) {
        restamp(&mut machine, &source, row, k, 0);
    }
    controls.push(("both lower", source, machine, None, "both lower LIR block"));
    controls
}

/// Design §5.3's wrong lowerings: label, LIR, the wrong stream. Each must be
/// refuted on samples or make no claim, never stated and holding.
pub(crate) fn slice_twenty_four_refutations() -> Vec<(&'static str, Function, X86ISelFunction)> {
    let mut cases = Vec::new();
    // W4: `n`'s `sub` reads `b` for `a`, and every row of `n` is restamped
    // as `k`'s first instruction: stamps that name another member cannot
    // hide a wrong value (a restamp alone changes no machine semantics: the
    // correct machine restamped so is stated and holds, which is sound).
    let (source, mut machine) = slice24_pair(Shape24::JoinChain);
    let (_, _, _, k, n) = join_blocks(&source);
    let rows_of_n = stamped(&machine, n);
    let sub = rows_of_n
        .iter()
        .copied()
        .find(|row| inst(&machine, *row).opcode == X86Opcode::SubRR)
        .unwrap_or_else(|| panic!("W4: n's sub\n{}", describe(&machine)));
    // Rows 0 and 1 copy the arguments `a` (rdi) and `b` (rsi) into vregs.
    let (a, b) = (
        inst(&machine, 0).operands[0].clone(),
        inst(&machine, 1).operands[0].clone(),
    );
    assert_eq!(
        inst(&machine, sub).operands[2],
        a,
        "W4: n's sub subtracts `a`\n{}",
        describe(&machine)
    );
    inst_mut(&mut machine, sub).operands[2] = b;
    for row in rows_of_n {
        restamp(&mut machine, &source, row, k, 0);
    }
    cases.push(("W4 rows restamped", source, machine));
    // W6: `n`'s `sub` a `add`.
    let (source, mut machine) = slice24_pair(Shape24::JoinChain);
    let (_, _, _, _, n) = join_blocks(&source);
    let sub = stamped(&machine, n)
        .into_iter()
        .find(|row| inst(&machine, *row).opcode == X86Opcode::SubRR)
        .unwrap_or_else(|| panic!("W6: n's sub\n{}", describe(&machine)));
    inst_mut(&mut machine, sub).opcode = X86Opcode::AddRR;
    cases.push(("W6 op swapped", source, machine));
    // W7: `n`'s `setcc`, which reads the flags `entry`'s `cmp` set across the
    // seam, inverted.
    let (source, mut machine) = slice24_pair(Shape24::SeamFlags);
    let n = jump_dest(&source, source.entry_block);
    let setcc = stamped(&machine, n)
        .into_iter()
        .find(|row| inst(&machine, *row).opcode == X86Opcode::Setcc)
        .unwrap_or_else(|| panic!("W7: n's setcc\n{}", describe(&machine)));
    let at = inst(&machine, setcc)
        .operands
        .iter()
        .position(|operand| matches!(operand, O::CondCode(_)))
        .expect("W7: a setcc's condition");
    let inverted = match inst(&machine, setcc).operands[at] {
        O::CondCode(X86CondCode::B) => X86CondCode::AE,
        O::CondCode(X86CondCode::AE) => X86CondCode::B,
        ref other => panic!("W7: an unsigned compare's setcc, not {other:?}"),
    };
    inst_mut(&mut machine, setcc).operands[at] = O::CondCode(inverted);
    cases.push(("W7 seam jcc inverted", source, machine));
    // W8: the silent member's store row dropped.
    let (source, mut machine) = variant24_pair(Variant24::SilentStore);
    let (x, _) = brif_targets(&source, source.entry_block);
    let s = jump_dest(&source, x);
    let store = stamped(&machine, s)
        .into_iter()
        .find(|row| inst(&machine, *row).opcode != X86Opcode::Jmp)
        .unwrap_or_else(|| panic!("W8: s's store\n{}", describe(&machine)));
    remove_at(&mut machine, store);
    cases.push(("W8 store dropped", source, machine));
    // W5a: `k`'s product moved before `j`'s add, which defines its operand.
    let (source, mut machine) = slice24_pair(Shape24::JoinChain);
    let (_, _, j, k, _) = join_blocks(&source);
    let product = stamped(&machine, k)
        .into_iter()
        .find(|row| inst(&machine, *row).opcode == X86Opcode::ImulRR)
        .unwrap_or_else(|| panic!("W5a: k's imul\n{}", describe(&machine)));
    let first = first_stamped(&machine, j);
    let moved = remove_at(&mut machine, product);
    insert_at(&mut machine, first, moved);
    cases.push(("W5a definer reordered", source, machine));
    // W5b: `y`'s load moved before `x`'s store.
    let (source, mut machine) = slice24_pair(Shape24::CallsAndMemory);
    let (x, _) = brif_targets(&source, source.entry_block);
    let y = jump_dest(&source, x);
    let store = stamped(&machine, x)
        .into_iter()
        .find(|row| inst(&machine, *row).opcode == X86Opcode::MovMR)
        .unwrap_or_else(|| panic!("W5b: x's store\n{}", describe(&machine)));
    let load = stamped(&machine, y)
        .into_iter()
        .find(|row| inst(&machine, *row).opcode == X86Opcode::MovRM)
        .unwrap_or_else(|| panic!("W5b: y's load\n{}", describe(&machine)));
    let moved = remove_at(&mut machine, load);
    insert_at(&mut machine, store, moved);
    cases.push(("W5b access reordered", source, machine));
    cases.push(w13());
    cases
}

/// W13 (design §2.7, angle A): `[GuardDivZero d; Udiv; Jump b1]`, `b1 = [c
/// = q == 0; Brif c, b2, b3]`, honestly merged, then `cmp d, 0; je b2`
/// inserted before the guard's trap carrier: where the source traps, the
/// machine returns `b2`'s 1.
pub(crate) fn w13() -> (&'static str, Function, X86ISelFunction) {
    let (source, mut machine) = variant24_pair(Variant24::GuardBeforeBranch);
    let entry = source.entry_block;
    let b1 = jump_dest(&source, entry);
    let (b2, _) = brif_targets(&source, b1);
    let carrier = stamped(&machine, entry)
        .into_iter()
        .find(|row| inst(&machine, *row).opcode == X86Opcode::TrapDivZeroExact)
        .unwrap_or_else(|| panic!("W13: the guard's carrier\n{}", describe(&machine)));
    let divisor = inst(&machine, carrier).operands[0].clone();
    let target = machine
        .block_order
        .iter()
        .copied()
        .find(|block| {
            machine.blocks[block]
                .insts
                .iter()
                .any(|inst| stamp(inst).is_some_and(|(b, _)| b == b2))
        })
        .unwrap_or_else(|| panic!("W13: b2's machine block\n{}", describe(&machine)));
    let mut compare = X86ISelInst::new(X86Opcode::CmpRI, vec![divisor, O::Imm(0)]);
    compare.lowering_provenance = inst(&machine, carrier).lowering_provenance;
    let mut jcc = X86ISelInst::new(
        X86Opcode::Jcc,
        vec![O::CondCode(X86CondCode::E), O::Block(target)],
    );
    jcc.lowering_provenance = inst(&machine, carrier).lowering_provenance;
    insert_at(&mut machine, carrier, jcc);
    insert_at(&mut machine, carrier, compare);
    ("W13 jcc before the carrier", source, machine)
}

/// Every fixture of slices 16 to 23 that has a shape list: label, LIR, the
/// selector's stream.
pub(crate) fn later_fixtures() -> Vec<(String, Function, X86ISelFunction)> {
    let mut fixtures: Vec<(String, Function, X86ISelFunction)> = Vec::new();
    for shape in super::slice16::SLICE_SIXTEEN {
        let (source, machine) = super::slice16::slice16_pair(shape);
        fixtures.push((format!("s16 {shape:?}"), source, machine));
    }
    for shape in super::slice17::SLICE_SEVENTEEN {
        let (source, machine) = super::slice17::slice17_pair(shape);
        fixtures.push((format!("s17 {shape:?}"), source, machine));
    }
    for shape in super::slice20::SLICE_TWENTY {
        let (source, machine) = super::slice20::slice20_pair(shape);
        fixtures.push((format!("s20 {shape:?}"), source, machine));
    }
    for shape in super::slice21::slice_twenty_one() {
        let (source, machine) = super::slice21::slice21_pair(shape);
        fixtures.push((format!("s21 {shape:?}"), source, machine));
    }
    for shape in super::slice22::SLICE_TWENTY_TWO {
        let (source, machine) = super::slice22::slice22_pair(shape);
        fixtures.push((format!("s22 {shape:?}"), source, machine));
    }
    for shape in super::slice23::SLICE_TWENTY_THREE {
        let (source, machine) = super::slice23::slice23_pair(shape);
        fixtures.push((format!("s23 {shape:?}"), source, machine));
    }
    fixtures
}

/// The outcome of every O0 fixture of slices 1 to 23 with a shape list (the
/// selector's stream, one machine block per LIR block), one line each:
/// `label<TAB>stated<TAB>sha256` of its replayed units' text, or
/// `label<TAB>refused<TAB>sha256` of its refusal's text before any `; not
/// contracted:` note. The fails-before run on `7ee0def54` records these lines
/// (`slice24_o0_owners.txt`); `o0_is_untouched` compares.
pub(crate) fn o0_outcomes() -> Vec<String> {
    use sha2::{Digest, Sha256};
    let mut fixtures = super::slice16::earlier_fixtures();
    fixtures.extend(later_fixtures());
    fixtures
        .iter()
        .map(|(label, source, machine)| {
            let (kind, bytes) = match owner24(source, machine) {
                Ok(owner) => (
                    "stated",
                    owner
                        .replayed_units()
                        .into_iter()
                        .map(text)
                        .collect::<Vec<_>>()
                        .join("\n"),
                ),
                Err(refusal) => {
                    let said = format!("{refusal}");
                    let before = said
                        .split_once("; not contracted: ")
                        .map_or(said.clone(), |(before, _)| before.to_owned());
                    ("refused", before)
                }
            };
            format!("{label}\t{kind}\t{:x}", Sha256::digest(bytes.as_bytes()))
        })
        .collect()
}

// ---------------------------------------------------------------------------
// Controls (slice 24a)
// ---------------------------------------------------------------------------

/// A diagnostic, not a check: every slice-24a fixture's LIR, merged machine
/// rows and theorem (or refusal), every refusal control's and wrong
/// lowering's outcome.
#[test]
#[ignore]
fn print_slice_twenty_four_fixtures() {
    fn shown<T>(label: &str, build: impl FnOnce() -> T) -> Option<T> {
        match std::panic::catch_unwind(std::panic::AssertUnwindSafe(build)) {
            Ok(value) => Some(value),
            Err(_) => {
                println!("==== {label}: THE FIXTURE PANICKED (above)");
                None
            }
        }
    }
    for shape in SLICE_TWENTY_FOUR {
        let Some((source, machine)) = shown(&format!("{shape:?}"), || slice24_pair(shape)) else {
            continue;
        };
        println!(
            "==== {shape:?}\n{}{}",
            describe_lir(&source),
            describe_blocks(&machine)
        );
        match owner24(&source, &machine) {
            Ok(owner) => println!(
                "STATED merged={:?}\n{}",
                owner.merged_chains(),
                text(owner.obligation())
            ),
            Err(refusal) => println!("REFUSED {refusal}"),
        }
    }
    for variant in [
        Variant24::AbsorbedParams,
        Variant24::DoWhile,
        Variant24::DeadCycle,
        Variant24::CopyAcrossSeam,
        Variant24::SilentStore,
        Variant24::GuardBeforeBranch,
        Variant24::OnePathChain,
        Variant24::FloatConstChain,
        Variant24::NanConstChain,
    ] {
        let Some((source, machine)) = shown(&format!("{variant:?}"), || variant24_pair(variant))
        else {
            continue;
        };
        println!(
            "==== variant {variant:?}\n{}{}{}",
            describe_lir(&source),
            describe_blocks(&machine),
            refusal_text(&owner24(&source, &machine))
        );
    }
    for label in [
        "D2 folded",
        "entry behind a dead Jump",
        "routine chain",
        "long chain",
    ] {
        let Some((source, machine)) = shown(label, || extra24(label)) else {
            continue;
        };
        if label != "long chain" {
            println!(
                "==== extra {label}\n{}{}",
                describe_lir(&source),
                describe_blocks(&machine)
            );
        }
        match owner24(&source, &machine) {
            Ok(owner) => println!(
                "==== extra {label}: STATED merged={:?} parts={} regions={} holds={:?} refuted={}",
                owner.merged_chains(),
                owner.parts().len(),
                owner.shared_parts().region_claims().len(),
                owner_holds(&owner),
                owner_refuted(&owner)
            ),
            Err(refusal) => println!("==== extra {label}: REFUSED {refusal}"),
        }
    }
    let Some(parts) = shown("parts fixtures", parts_fixtures) else {
        return;
    };
    for (label, source, machine, points) in parts {
        println!("==== {label} (parts)\n{}", describe_blocks(&machine));
        println!("{}", refusal_text(&parts24(&source, &machine, points)));
    }
    if let Some(controls) = shown("refusal controls", refusal_controls) {
        for (label, source, machine, route, expected) in controls {
            let result = match route {
                None => owner24(&source, &machine),
                Some(points) => parts24(&source, &machine, points),
            };
            println!(
                "==== {label} (expects {expected:?})\n{}{}{}",
                describe_lir(&source),
                describe_blocks(&machine),
                refusal_text(&result)
            );
        }
    }
    if let Some(wrong) = shown("wrong lowerings", slice_twenty_four_refutations) {
        for (label, source, machine) in wrong {
            let result = owner24(&source, &machine);
            let verdict = match &result {
                Ok(owner) if owner_refuted(owner) => "stated, refuted on samples".to_string(),
                Ok(_) => "STATED AND HOLDS".to_string(),
                Err(refusal) => format!("{refusal}"),
            };
            println!(
                "==== {label} (wrong lowering)\n{}{verdict}",
                describe_blocks(&machine)
            );
        }
    }
}

/// The machine by block, in layout order: each block's successors, then its
/// rows with their walk ordinals and stamps.
fn describe_blocks(machine: &X86ISelFunction) -> String {
    let mut text = String::new();
    let mut ordinal = 0;
    for block in &machine.block_order {
        let body = &machine.blocks[block];
        text.push_str(&format!("  M{} succ={:?}\n", block.0, body.successors));
        for inst in &body.insts {
            text.push_str(&format!(
                "    [{ordinal}] {:?} {:?} @{:?}\n",
                inst.opcode,
                inst.operands,
                stamp(inst)
            ));
            ordinal += 1;
        }
    }
    text
}

use super::super::quotient::{Quotient, mutant, same_instruction};

/// The merged-chain quotient the stamps choose for a pair (its check run).
fn quotient_of<'a>(
    source: &'a Function,
    machine: &'a X86ISelFunction,
) -> Result<Quotient<'a>, X86BodyRefusal> {
    let cfg = source_cfg(source)?;
    Quotient::of(source, machine, &cfg)
}

// ---- the controls, each `Ok` on the correct code

/// The owner states `shape` over a merged-chain quotient, the routing
/// predicate admits it, and the theorem holds on samples.
fn owner_control(shape: Shape24) -> Result<(), String> {
    let (source, machine) = slice24_pair(shape);
    if !pair_admits_x86_body_owner(&source, &machine, SYSV) {
        return Err("the routing predicate refuses the pair".into());
    }
    let owner = owner24(&source, &machine).map_err(|refusal| format!("{refusal}"))?;
    if owner.merged_chains().is_none() {
        return Err("stated over the original pair, not a quotient".into());
    }
    owner_holds(&owner)
}

/// `Quotient::of` contracts a chain of `shape` and its check accepts it, and
/// the quotient is the exact contraction ([`contraction_holds`]).
fn quotient_control(source: &Function, machine: &X86ISelFunction) -> Result<(), String> {
    let quotient = quotient_of(source, machine).map_err(|refusal| format!("{refusal}"))?;
    if quotient.is_identity() {
        return Err("no chain contracted".into());
    }
    contraction_holds(source, machine, &quotient)
}

/// The quotient, read only through its maps, is the contraction design §2.3
/// states: every original location but a removed `Jump` maps to an equal
/// instruction of the quotient and back, one to one and onto; a removed
/// location is a `Jump` ending its block; the quotient machine is the
/// original's rows in order, each stamp the forward map of its original.
fn contraction_holds(
    source: &Function,
    machine: &X86ISelFunction,
    quotient: &Quotient<'_>,
) -> Result<(), String> {
    let (q, x) = (quotient.source(), quotient.machine());
    let mut image: HashSet<(Block, usize)> = HashSet::new();
    for (block, body) in &source.blocks {
        for (index, inst) in body.instructions.iter().enumerate() {
            match quotient.to_quotient(*block, index) {
                Some((head, at)) => {
                    let Some(stated) = q.blocks.get(&head).and_then(|b| b.instructions.get(at))
                    else {
                        return Err(format!("({block:?}, {index}) maps outside the quotient"));
                    };
                    if !same_instruction(stated, inst) {
                        return Err(format!("({block:?}, {index}) maps to another instruction"));
                    }
                    if quotient.original(head, at) != (*block, index) {
                        return Err(format!("({block:?}, {index}) does not map back"));
                    }
                    if !image.insert((head, at)) {
                        return Err(format!("({head:?}, {at}) is the image of two locations"));
                    }
                }
                None => {
                    if index + 1 != body.instructions.len()
                        || !matches!(inst.opcode, L::Jump { .. })
                    {
                        return Err(format!("({block:?}, {index}) is removed but no final Jump"));
                    }
                }
            }
        }
    }
    let locations: usize = q.blocks.values().map(|body| body.instructions.len()).sum();
    if locations != image.len() {
        return Err("a quotient location is no original's image".into());
    }
    if x.block_order != machine.block_order || x.blocks.len() != machine.blocks.len() {
        return Err("the quotient machine's blocks changed".into());
    }
    for (block, body) in &machine.blocks {
        let Some(stated) = x.blocks.get(block) else {
            return Err(format!("machine block {block:?} is missing"));
        };
        if stated.insts.len() != body.insts.len() || stated.successors != body.successors {
            return Err(format!("machine block {block:?} changed"));
        }
        for (new, old) in stated.insts.iter().zip(&body.insts) {
            if new.opcode != old.opcode || new.operands != old.operands || new.flags != old.flags {
                return Err(format!("a row of machine block {block:?} changed"));
            }
            let expected = stamp(old).map(|(b, i)| quotient.to_quotient(b, i));
            match (expected, stamp(new)) {
                (None, None) => {}
                (Some(Some(mapped)), Some(found)) if mapped == found => {}
                _ => return Err(format!("a stamp of machine block {block:?} is not forward")),
            }
        }
    }
    Ok(())
}

/// Every audit coordinate of `owner` names the ORIGINAL source: a call site
/// a `Call`, an access site a `Load`/`Store`, a definition an instruction
/// that is no `Jump` (or a join's parameters).
fn audit_holds(source: &Function, owner: &SourceBoundX86Body<'_>) -> Result<(), String> {
    let at = |block: Block, index: usize| {
        source
            .blocks
            .get(&block)
            .and_then(|body| body.instructions.get(index))
    };
    for &(block, index, _) in owner.call_sites() {
        if !at(block, index)
            .is_some_and(|inst| matches!(inst.opcode, L::Call { .. } | L::CallIndirect))
        {
            return Err(format!("call site ({block:?}, {index}) is no call"));
        }
    }
    for &(block, index, _) in owner.access_sites() {
        if !at(block, index)
            .is_some_and(|inst| matches!(inst.opcode, L::Load { .. } | L::Store { .. }))
        {
            return Err(format!("access site ({block:?}, {index}) is no access"));
        }
    }
    for (name, block, index) in owner.source_definitions() {
        let named = if *index == JOIN_ROW {
            source
                .blocks
                .get(block)
                .is_some_and(|body| !body.params.is_empty())
        } else {
            at(*block, *index).is_some_and(|inst| !matches!(inst.opcode, L::Jump { .. }))
        };
        if !named {
            return Err(format!(
                "definition {name} at ({block:?}, {index}) names no definer"
            ));
        }
    }
    Ok(())
}

fn audit_control(shape: Shape24) -> Result<(), String> {
    let (source, machine) = slice24_pair(shape);
    let owner = owner24(&source, &machine).map_err(|refusal| format!("{refusal}"))?;
    if owner.merged_chains().is_none() {
        return Err("stated over the original pair".into());
    }
    if owner.source_definitions().is_empty() {
        return Err("no definition to audit".into());
    }
    audit_holds(&source, &owner)
}

/// A named refusal control: `Unsupported`, naming `expected`, a decline (a
/// label `D..`) naming why the chain was not contracted.
fn refusal_control(label: &str) -> Result<(), String> {
    let (_, source, machine, route, expected) = refusal_controls()
        .into_iter()
        .find(|control| control.0 == label)
        .unwrap_or_else(|| panic!("no refusal control {label}"));
    let result = match route {
        None => owner24(&source, &machine),
        Some(points) => parts24(&source, &machine, points),
    };
    match result {
        Err(X86BodyRefusal::Unsupported(reason)) => {
            let text = format!("{reason}");
            if !text.contains(expected) {
                return Err(format!("expected {expected:?}, got {text}"));
            }
            if label.starts_with('D') && !text.contains("; not contracted: ") {
                return Err(format!("names no reason it was not contracted: {text}"));
            }
            Ok(())
        }
        Err(other) => Err(format!("not Unsupported: {other}")),
        Ok(_) => Err("stated".into()),
    }
}

/// A named refusal control judged at the quotient (slice 24c, design §5.8):
/// `Quotient::of` on the control's pair declines the chain (its first note
/// naming `expected`; the quotient may contract other chains) or its check
/// refuses (the refusal naming `expected`). The owner states some of these
/// pairs over segments since OD-228, so the builder and check rules they
/// guard are judged here, never through the owner.
fn quotient_refusal_control(label: &str) -> Result<(), String> {
    let (_, source, machine, _, expected) = refusal_controls()
        .into_iter()
        .find(|control| control.0 == label)
        .unwrap_or_else(|| panic!("no refusal control {label}"));
    match quotient_of(&source, &machine) {
        Ok(quotient) => {
            let note = quotient.annotate(String::new());
            if note.contains(expected) {
                Ok(())
            } else {
                Err(format!(
                    "expected {expected:?}, noted {note:?} (contracted: {})",
                    quotient.describe()
                ))
            }
        }
        Err(refusal) => {
            let text = format!("{refusal}");
            if text.contains(expected) {
                Ok(())
            } else {
                Err(format!("expected {expected:?}, got {text}"))
            }
        }
    }
}

/// Slice 24c (OD-228): the refusal controls whose owner is stated over
/// segments since then. Their builder and check rules are judged at the
/// quotient ([`quotient_refusal_control`]); the owner's outcome is the
/// measured verdict transition [`segment_transition`] pins.
const SEGMENT_TRANSITIONS: &[&str] = &["D2 folded", "D5", "D5 parts"];

/// The owner's outcome of a [`SEGMENT_TRANSITIONS`] control: `D5` and `D5
/// parts` (a chain the quotient declines) are stated over segments and
/// hold; `D2 folded` (a wrong lowering: the machine always takes `l`) is
/// stated over segments and refuted on samples.
fn segment_transition(label: &str) -> Result<(), String> {
    let (_, source, machine, route, _) = refusal_controls()
        .into_iter()
        .find(|control| control.0 == label)
        .unwrap_or_else(|| panic!("no refusal control {label}"));
    let owner = match route {
        None => owner24(&source, &machine),
        Some(points) => parts24(&source, &machine, points),
    }
    .map_err(|refusal| format!("not stated over segments: {refusal}"))?;
    if owner.segments().is_none() {
        return Err("stated over no segment".into());
    }
    match (label, owner_refuted(&owner)) {
        ("D2 folded", true) => Ok(()),
        ("D2 folded", false) => Err("the folded branch's theorem is not refuted".into()),
        (_, false) => owner_holds(&owner),
        (_, true) => Err("a correct chain's theorem is refuted".into()),
    }
}

/// F14: a parts fixture is stated in parts over its quotient and holds.
fn parts_control(index: usize) -> Result<(), String> {
    let (_, source, machine, points) = parts_fixtures().swap_remove(index);
    let cuts = points.len();
    let owner = parts24(&source, &machine, points).map_err(|refusal| format!("{refusal}"))?;
    if !owner.is_stated_in_parts() {
        return Err("not stated in parts".into());
    }
    // The entry's region and one per policy point (each a distinct cut).
    let regions = owner.shared_parts().region_claims().len();
    if regions != cuts + 1 {
        return Err(format!("{regions} regions for {cuts} cut points"));
    }
    if owner.merged_chains().is_none() {
        return Err("stated over the original pair".into());
    }
    audit_holds(&source, &owner)?;
    owner_holds(&owner)
}

/// The reviewed digest of [`Variant24::OnePathChain`]'s theorem, the same
/// before slice 24a (recorded by the fails-before run on `7ee0def54`).
const ONE_PATH_CHAIN_SHA256: &str =
    "8ee3e7976ed2569ffb99a1ef7770a6f859f3edea2a59b40203d732c62cf66279";

/// A one-path machine-chain body is stated over its original pair, its
/// theorem byte for byte today's.
fn one_path_control() -> Result<(), String> {
    use sha2::{Digest, Sha256};
    let (source, machine) = variant24_pair(Variant24::OnePathChain);
    let owner = owner24(&source, &machine).map_err(|refusal| format!("{refusal}"))?;
    if owner.merged_chains().is_some() {
        return Err("stated over a quotient".into());
    }
    let digest = format!("{:x}", Sha256::digest(text(owner.obligation()).as_bytes()));
    if digest != ONE_PATH_CHAIN_SHA256 {
        return Err(format!("its theorem moved: {digest}"));
    }
    Ok(())
}

/// The quotient is admitted with its original's encoding: F12's DAG (the
/// quotient alone would be stated path by path) and F12p's paths.
fn encoding_control() -> Result<(), String> {
    for (shape, dag) in [
        (Shape24::SeventeenBlocks, true),
        (Shape24::PerPathChain, false),
    ] {
        let (source, machine) = slice24_pair(shape);
        let original = admitted_body(&source).map_err(|refusal| format!("{refusal}"))?;
        if original.dag.is_some() != dag {
            return Err(format!(
                "{shape:?}: the original's encoding is not the fixture's"
            ));
        }
        let quotient = quotient_of(&source, &machine).map_err(|refusal| format!("{refusal}"))?;
        let stated = admitted_quotient(quotient.source(), &original)
            .map_err(|refusal| format!("{refusal}"))?;
        if stated.dag.is_some() != dag || stated.paths.is_empty() == !dag {
            return Err(format!(
                "{shape:?}: the quotient's encoding is not the original's"
            ));
        }
    }
    Ok(())
}

/// The reason of an `Unsupported` refusal, without its merged-chain
/// quotient suffix.
fn inner(reason: &X86BodyUnsupported) -> &X86BodyUnsupported {
    match reason {
        X86BodyUnsupported::OverQuotient { reason, .. } => inner(reason),
        other => other,
    }
}

/// The owner of an extra pair states it over a merged-chain quotient and
/// its theorem holds on samples.
fn credited_control(label: &str) -> Result<(), String> {
    let (source, machine) = extra24(label);
    let owner = owner24(&source, &machine).map_err(|refusal| format!("{refusal}"))?;
    if owner.merged_chains().is_none() {
        return Err("stated over the original pair".into());
    }
    owner_holds(&owner)
}

/// A wrong lowering is never credited: no claim (`Unsupported`), a named
/// mismatch, or a theorem refuted on samples.
fn never_credited_control(label: &str) -> Result<(), String> {
    let (source, machine) = extra24(label);
    match owner24(&source, &machine) {
        Ok(owner) if owner_refuted(&owner) => Ok(()),
        Ok(_) => Err("a wrong lowering's theorem is stated and holds".into()),
        Err(_) => Ok(()),
    }
}

/// With the builder mutant `builder` (and this thread's mutants), the pair
/// `label` is refused by `Quotient::check`'s link clause: a `Construction`
/// whose detail is `x -> y is not a link of the source`.
fn caught_control(label: &str, builder: &str) -> Result<(), String> {
    let _builder = mutant::set(&format!("{},{builder}", mutant::active()));
    let (source, machine) = extra24(label);
    match owner24(&source, &machine) {
        Err(X86BodyRefusal::Unsupported(reason)) => match inner(&reason) {
            X86BodyUnsupported::Construction(detail)
                if detail.contains("is not the exact contraction")
                    && detail.contains("is not a link of the source") =>
            {
                Ok(())
            }
            _ => Err(format!("not the check's link refusal: {reason}")),
        },
        Err(other) => Err(format!("not Unsupported: {other}")),
        Ok(_) => Err("stated".into()),
    }
}

/// The production route states [`Variant24::LongChain`] in parts over its
/// quotient: the planner cuts the one merged machine block (two regions at
/// least), every audit coordinate is the original's, and every part holds.
fn planned_parts_control() -> Result<(), String> {
    let (source, machine) = extra24("long chain");
    if split::fits_one_query(&source, &machine) {
        return Err("within the single-query bounds".into());
    }
    let owner = owner24(&source, &machine).map_err(|refusal| format!("{refusal}"))?;
    if !owner.is_stated_in_parts() {
        return Err("not stated in parts".into());
    }
    if owner.merged_chains().is_none() {
        return Err("stated over the original pair".into());
    }
    let regions = owner.shared_parts().region_claims().len();
    if regions < 2 {
        return Err(format!("{regions} region(s): the merged block was not cut"));
    }
    audit_holds(&source, &owner)?;
    owner_holds(&owner)
}

/// A region past a test policy's bound is named in ORIGINAL coordinates:
/// F1 cut at the start of its absorbed member `next` (a seam), at most two
/// blocks per region, refuses for the region from instruction 0 of `next`
/// (in the quotient, instruction 1 of the entry).
fn region_original_control() -> Result<(), String> {
    let (source, machine) = slice24_pair(Shape24::EntryChain);
    let next = jump_dest(&source, source.entry_block);
    let policy = split::SplitPolicy {
        region_blocks: 2,
        ..cut_at(vec![(next, 0)])
    };
    match source_bound_x86_body_in_parts(&source, &machine, SYSV, &policy) {
        Err(X86BodyRefusal::Unsupported(reason)) => {
            let text = format!("{reason}");
            let expected = format!("the region from instruction 0 of block {next:?} has");
            if matches!(inner(&reason), X86BodyUnsupported::SourceShape(_))
                && text.contains(&expected)
            {
                Ok(())
            } else {
                Err(format!("expected {expected:?}, got {text}"))
            }
        }
        Err(other) => Err(format!("not Unsupported: {other}")),
        Ok(_) => Err("stated".into()),
    }
}

/// A control of the mutant campaign.
#[derive(Debug, Clone, Copy)]
enum Control {
    Owner(Shape24),
    Quotient(Shape24),
    QuotientVariant(Variant24),
    Refusal(&'static str),
    /// [`quotient_refusal_control`] (slice 24c, design §5.8).
    QuotientRefusal(&'static str),
    Audit(Shape24),
    Parts(usize),
    OnePath,
    Encoding,
    Snapshot,
    /// The owner of `shape` contracts exactly these `(chains, absorbed)`.
    Chains(Shape24, (usize, usize)),
    /// [`credited_control`] of an extra pair.
    Credited(&'static str),
    /// [`never_credited_control`] of an extra pair.
    NeverCredited(&'static str),
    /// [`caught_control`]: an extra pair under a builder mutant.
    Caught(&'static str, &'static str),
    /// [`planned_parts_control`].
    PlannedParts,
    /// [`region_original_control`].
    RegionOriginal,
}

fn run_control(control: Control) -> Result<(), String> {
    match control {
        Control::Owner(shape) => owner_control(shape),
        Control::Quotient(shape) => {
            let (source, machine) = slice24_pair(shape);
            quotient_control(&source, &machine)
        }
        Control::QuotientVariant(variant) => {
            let (source, machine) = variant24_pair(variant);
            quotient_control(&source, &machine)
        }
        Control::Refusal(label) => refusal_control(label),
        Control::QuotientRefusal(label) => quotient_refusal_control(label),
        Control::Audit(shape) => audit_control(shape),
        Control::Parts(index) => parts_control(index),
        Control::OnePath => one_path_control(),
        Control::Encoding => encoding_control(),
        Control::Snapshot => snapshot_control(),
        Control::Chains(shape, expected) => {
            let (source, machine) = slice24_pair(shape);
            let owner = owner24(&source, &machine).map_err(|refusal| format!("{refusal}"))?;
            match owner.merged_chains() {
                Some(chains) if chains == expected => Ok(()),
                other => Err(format!("contracted {other:?}, not {expected:?}")),
            }
        }
        Control::Credited(label) => credited_control(label),
        Control::NeverCredited(label) => never_credited_control(label),
        Control::Caught(label, builder) => caught_control(label, builder),
        Control::PlannedParts => planned_parts_control(),
        Control::RegionOriginal => region_original_control(),
    }
}

/// `control` under the mutants `names` on this thread. A panic is a failed
/// control whose reason is the panic's message (`panicked: ..`), so the
/// campaign's log says why every mutant was killed.
fn under(names: &str, control: Control) -> Result<(), String> {
    let _mutant = mutant::set(names);
    std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| run_control(control))).unwrap_or_else(
        |payload| {
            let message = payload
                .downcast_ref::<String>()
                .cloned()
                .or_else(|| {
                    payload
                        .downcast_ref::<&str>()
                        .map(|text| (*text).to_owned())
                })
                .unwrap_or_else(|| "a panic with no message".into());
            Err(format!("panicked: {message}"))
        },
    )
}

/// Design §5.5: each mutant of a slice-24a rule (a thread's [`mutant::set`])
/// and the controls it must break. The `check-off` configurations reach
/// `Quotient::check`'s absence; `check-any-terminator-link` and
/// `check-entry-link` delete one clause of the check itself.
const MUTANTS: &[(&str, &[Control])] = &[
    // The builder's link rule over a `Brif`: on D2 the removed-`Jump`
    // decline (D7) declines first (the `Brif`'s rows are stamped); on the
    // folded branch, which no row names, the check refuses the contraction.
    (
        "link-any-terminator",
        &[
            Control::Refusal("D2"),
            Control::QuotientRefusal("D2"),
            Control::QuotientRefusal("D2 folded"),
        ],
    ),
    // With the check off, the folded branch is contracted over its `Brif`
    // and the wrong lowering's theorem is stated and holds: the check's
    // `Jump` clause is the only guard against it.
    (
        "link-any-terminator,check-off",
        &[Control::NeverCredited("D2 folded")],
    ),
    (
        "link-any-terminator,check-any-terminator-link",
        &[Control::NeverCredited("D2 folded")],
    ),
    (
        "check-any-terminator-link",
        &[Control::Caught("D2 folded", "link-any-terminator")],
    ),
    ("entering-live-only", &[Control::Refusal("D1 unreachable")]),
    // The builder's link rule into the entry: on D3 the absorbed-parameter
    // decline (D5) declines first (the entry declares the function's
    // parameters); a dead `[Jump entry]` before a parameterless entry is
    // contracted, and the check refuses it.
    (
        "allow-entry",
        &[
            Control::Refusal("D3"),
            Control::Credited("entry behind a dead Jump"),
        ],
    ),
    // With the check off, the quotient's entry block has no body: its own
    // admission refuses (no claim; `the_check_refuses_what_the_rules_decline`).
    (
        "allow-entry,check-off",
        &[Control::Credited("entry behind a dead Jump")],
    ),
    (
        "check-entry-link",
        &[Control::Caught("entry behind a dead Jump", "allow-entry")],
    ),
    ("allow-params", &[Control::QuotientRefusal("D5")]),
    ("allow-self-loop", &[Control::Refusal("D6")]),
    ("allow-jump-stamp", &[Control::Refusal("D7")]),
    ("copy-run-unchecked", &[Control::Refusal("D10")]),
    (
        "rewrite-merged-block-only",
        &[
            Control::Owner(Shape24::DenseSwitchTail),
            Control::Owner(Shape24::SparseSwitchTail),
        ],
    ),
    (
        "rewrite-merged-block-only,check-off",
        &[Control::Owner(Shape24::SparseSwitchTail)],
    ),
    ("no-forward-fill", &[Control::Owner(Shape24::SilentTail)]),
    ("no-backward-fill", &[Control::Owner(Shape24::SilentHead)]),
    (
        "single-first",
        &[Control::Owner(Shape24::SparseSwitchSilentMember)],
    ),
    // F12's final `* 3` is one claim over the DAG's join value and one per
    // path otherwise: the golden pins the original's encoding through the
    // owner, the encoding control through the admission.
    (
        "encoding-from-quotient",
        &[Control::Encoding, Control::Snapshot],
    ),
    (
        "audit-in-quotient-coords",
        &[
            Control::Audit(Shape24::CallsAndMemory),
            Control::RegionOriginal,
        ],
    ),
    // Planned over the original pair, the merged block is cut only within
    // its head's own instructions, and a region exceeds the row bound.
    ("plan-over-original", &[Control::PlannedParts]),
    ("route-gate-off", &[Control::OnePath]),
    // F17's second chain `c1 -> c2`, which the machine left apart (`c1`
    // falls through to `c2`), contracted although no machine block's
    // stamps name both: its two machine blocks then lower one quotient
    // block (`both lower`), and the owner refuses.
    (
        "contract-all-rule-chains",
        &[Control::Chains(Shape24::PartialMerge, (1, 1))],
    ),
    ("floor-off", &[Control::Parts(0)]),
    (
        "original-first-match",
        &[Control::Audit(Shape24::JumpOnlyMember)],
    ),
    (
        "builder-wrong-offset",
        &[Control::Quotient(Shape24::JoinChain)],
    ),
    // Stamps are not trusted: with the check off, wrong offsets make the
    // owner refuse the fixtures whose stamps they misplace (the golden
    // control panics naming the refusal).
    ("builder-wrong-offset,check-off", &[Control::Snapshot]),
    (
        "builder-drop-member-instructions",
        &[Control::Quotient(Shape24::JoinChain)],
    ),
    (
        "builder-drop-member-instructions,check-off",
        &[Control::Owner(Shape24::JoinChain)],
    ),
    (
        "builder-drop-value-types",
        &[Control::Quotient(Shape24::CallsAndMemory)],
    ),
    (
        "builder-drop-value-types,check-off",
        &[Control::Owner(Shape24::CallsAndMemory)],
    ),
    (
        "builder-const-pool",
        &[Control::QuotientVariant(Variant24::FloatConstChain)],
    ),
    // The check's instruction equality by `f64`'s `==`: an unchanged NaN
    // constant reads as changed (a correct quotient refused).
    (
        "check-float-eq",
        &[Control::QuotientVariant(Variant24::NanConstChain)],
    ),
    // A builder that turns the other arm's `-0.0` into `0.0`: the check's
    // bitwise comparison refuses it.
    (
        "builder-flip-zero",
        &[Control::QuotientVariant(Variant24::NanConstChain)],
    ),
];

// ---------------------------------------------------------------------------
// The gate
// ---------------------------------------------------------------------------

/// Every slice-24a shape is stated over its merged-chain quotient, admitted
/// by the routing predicate, and its theorem holds on samples.
#[test]
fn owner_states_every_merged_shape() {
    let failures: Vec<String> = SLICE_TWENTY_FOUR
        .into_iter()
        .filter_map(|shape| {
            owner_control(shape)
                .err()
                .map(|why| format!("{shape:?}: {why}"))
        })
        .collect();
    assert!(failures.is_empty(), "{}", failures.join("\n"));
}

/// Two builds of every merged shape state the same text.
#[test]
fn merged_shapes_are_deterministic() {
    for shape in SLICE_TWENTY_FOUR {
        let (source, machine) = slice24_pair(shape);
        let (again_source, again_machine) = slice24_pair(shape);
        let first = owner24(&source, &machine).map(|owner| text(owner.obligation()));
        let second = owner24(&again_source, &again_machine).map(|owner| text(owner.obligation()));
        assert_eq!(first.is_ok(), second.is_ok(), "{shape:?}");
        if let (Ok(first), Ok(second)) = (first, second) {
            assert_eq!(first, second, "{shape:?}: deterministic");
        }
    }
}

/// `Quotient::of` contracts a chain of every merged shape, and the result,
/// read through its maps alone, is the exact contraction.
#[test]
fn the_quotient_is_the_exact_contraction() {
    for shape in SLICE_TWENTY_FOUR {
        let (source, machine) = slice24_pair(shape);
        quotient_control(&source, &machine).unwrap_or_else(|why| {
            panic!(
                "{shape:?}: {why}\n{}{}",
                describe_lir(&source),
                describe(&machine)
            )
        });
    }
    for variant in [Variant24::FloatConstChain, Variant24::NanConstChain] {
        let (source, machine) = variant24_pair(variant);
        quotient_control(&source, &machine).unwrap_or_else(|why| panic!("{variant:?}: {why}"));
    }
}

/// Every audit coordinate of a merged owner, on both routes, names the
/// ORIGINAL source's instruction.
#[test]
fn audit_maps_are_in_original_coordinates() {
    for shape in SLICE_TWENTY_FOUR {
        let (source, machine) = slice24_pair(shape);
        let owner =
            owner24(&source, &machine).unwrap_or_else(|refusal| panic!("{shape:?}: {refusal}"));
        audit_holds(&source, &owner).unwrap_or_else(|why| panic!("{shape:?}: {why}"));
    }
    for (label, source, machine, points) in parts_fixtures() {
        let owner = parts24(&source, &machine, points)
            .unwrap_or_else(|refusal| panic!("{label}: {refusal}"));
        audit_holds(&source, &owner).unwrap_or_else(|why| panic!("{label}: {why}"));
    }
    // The members of F10 hold its calls and accesses: the maps name them.
    let (source, machine) = slice24_pair(Shape24::CallsAndMemory);
    let owner = owner24(&source, &machine).unwrap();
    let (x, _) = brif_targets(&source, source.entry_block);
    let y = jump_dest(&source, x);
    assert!(
        owner.call_sites().iter().any(|site| site.0 == y),
        "{:?}",
        owner.call_sites()
    );
    assert!(
        owner.access_sites().iter().any(|site| site.0 == y),
        "{:?}",
        owner.access_sites()
    );
}

/// The quotient is stated with its ORIGINAL source's encoding (OD-191): F12
/// over its DAG, F12p path by path, and a one-path chain past the path bound
/// keeps its long-chain trim, although the quotient's own shape would choose
/// otherwise.
#[test]
fn the_encoding_is_the_original_shapes() {
    encoding_control().unwrap();
    let (source, machine) = slice24_pair(Shape24::SeventeenBlocks);
    let quotient = quotient_of(&source, &machine).unwrap();
    let own = admitted_body(quotient.source()).unwrap();
    assert!(
        own.dag.is_none() && !own.paths.is_empty(),
        "F12's quotient alone is stated path by path"
    );
    // The long-chain variant: a one-path block cut in two crosses the path
    // bound only through the `Jump` the cut adds.
    let mut found = false;
    for adds in 240..270 {
        let mut builder = ModuleBuilder::new("x86_source_bound_body_slice24_long");
        let signature = builder.add_func_type(vec![Ty::U64, Ty::U64], vec![Ty::U64]);
        let name = format!("s24_long_{adds}");
        let mut f = builder.function(name.clone(), signature);
        let entry = f.create_block();
        let a = f.add_block_param(entry, Ty::U64);
        let b = f.add_block_param(entry, Ty::U64);
        f.switch_to_block(entry);
        let mut value = a;
        for _ in 0..adds {
            value = f.add(Ty::U64, value, b);
        }
        f.ret(vec![value]);
        f.build();
        let module = builder.build().unwrap();
        let mut source = trust_cg_lower::translate_module_for_arch_with_tls_with_license(
            &module,
            trust_cg_lower::GuardCarrierArch::X86_64,
            trust_cg_lower::TlsDialect::default(),
            &crate::license_test_support::permit_unlicensed(),
        )
        .unwrap()
        .into_iter()
        .map(|(function, _)| function)
        .find(|function| function.name == name)
        .unwrap();
        let whole = admitted_body(&source).unwrap();
        if whole.long_chain {
            break;
        }
        let mut machine = select(&source, X86CallAbi::SystemV);
        let entry = source.entry_block;
        split_lir(&mut source, &mut machine, entry, adds / 2);
        let original = admitted_body(&source).unwrap();
        if !original.long_chain {
            continue;
        }
        let quotient = quotient_of(&source, &machine).unwrap();
        assert!(!quotient.is_identity());
        assert!(!admitted_body(quotient.source()).unwrap().long_chain);
        assert!(
            admitted_quotient(quotient.source(), &original)
                .unwrap()
                .long_chain
        );
        found = true;
        break;
    }
    assert!(found, "no block length crosses the path bound by one Jump");
}

/// A one-path body whose machine has no `jcc` walks its machine chain, so it
/// is stated over its original pair even when blocks merged: its theorem is
/// pinned to the digest the code before slice 24a states.
#[test]
fn one_path_merged_bodies_keep_their_bytes() {
    one_path_control().unwrap();
}

/// No fixture of slices 1 to 23 at O0 (the selector's one machine block per
/// LIR block) changes: none is contracted (each has its block
/// correspondence, or the stamps choose no chain), every theorem its owner
/// states is byte for byte the one the code before slice 24a states, and
/// every refusal keeps that code's text, a `; not contracted:` note
/// appended at most: [`o0_outcomes`] equals the lines the fails-before run
/// recorded on `7ee0def54` (`slice24_o0_owners.txt`).
#[test]
fn o0_is_untouched() {
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tests/fixtures/x86_source_bound_body/slice24_o0_owners.txt");
    let recorded: Vec<String> = std::fs::read_to_string(&path)
        .unwrap_or_else(|error| panic!("{}: {error}", path.display()))
        .lines()
        .filter(|line| !line.starts_with('#'))
        .map(str::to_owned)
        .collect();
    let outcomes = o0_outcomes();
    let changed: Vec<String> = outcomes
        .iter()
        .zip(&recorded)
        .filter(|(now, before)| now != before)
        .map(|(now, before)| format!("now {now}\nbefore {before}"))
        .collect();
    assert!(
        changed.is_empty() && outcomes.len() == recorded.len(),
        "{} outcomes, {} recorded; changed:\n{}",
        outcomes.len(),
        recorded.len(),
        changed.join("\n")
    );
    let stated = outcomes
        .iter()
        .filter(|line| line.contains("\tstated\t"))
        .count();
    assert!(stated > 0, "no O0 fixture is stated");
    let mut fixtures = super::slice16::earlier_fixtures();
    fixtures.extend(later_fixtures());
    for (label, source, machine) in &fixtures {
        let Ok(cfg) = source_cfg(source) else {
            continue;
        };
        if block_correspondence(source, machine, &cfg.dead).is_ok() {
            continue;
        }
        match Quotient::of(source, machine, &cfg) {
            Ok(quotient) => assert!(
                quotient.is_identity(),
                "{label}: contracted at O0: {}",
                quotient.describe()
            ),
            Err(refusal) => panic!("{label}: {refusal}"),
        }
    }
}

/// F18: the full O2 schedule over every fixture of slices 1 to 24a: a
/// correct lowering is never named a mismatch, and every theorem the owner
/// builds (over a quotient or not) holds on samples.
#[test]
fn a_merged_body_never_names_a_correct_machine_a_mismatch() {
    use trust_cg_codegen::x86_64::pipeline::{X86Pipeline, X86PipelineConfig};
    let pipeline = X86Pipeline::new(X86PipelineConfig {
        opt_level: trust_cg_opt::OptLevel::O2,
        call_abi: X86CallAbi::SystemV,
        ..X86PipelineConfig::default()
    });
    let mut fixtures = super::slice16::earlier_fixtures();
    fixtures.extend(later_fixtures());
    for shape in SLICE_TWENTY_FOUR {
        let source = slice24_lir(shape);
        let machine = select(&source, X86CallAbi::SystemV);
        fixtures.push((format!("s24 {shape:?}"), source, machine));
    }
    let (mut built, mut merged) = (0, 0);
    for (label, source, mut machine) in fixtures {
        pipeline.run_x86_optimization_passes(&mut machine);
        match owner24(&source, &machine) {
            Ok(owner) => {
                built += 1;
                if let Some((chains, absorbed)) = owner.merged_chains() {
                    merged += 1;
                    eprintln!(
                        "SLICE24_O2 merged {label} chains={chains} absorbed={absorbed} parts={}",
                        owner.parts().len()
                    );
                }
                owner_holds(&owner)
                    .unwrap_or_else(|why| panic!("{label} at O2: {why}\n{}", describe(&machine)));
            }
            Err(X86BodyRefusal::Unsupported(_)) => {}
            Err(other) => panic!("{label} at O2: {other}\n{}", describe(&machine)),
        }
    }
    eprintln!("SLICE24_O2 built={built} merged={merged}");
    assert!(merged > 0, "no O2 body was stated over a quotient");
}

/// Design §3: every decline and refusal is `Unsupported`, by name, and a
/// decline names why its chain was not contracted.
#[test]
fn every_named_refusal_is_named() {
    let labels: Vec<&str> = refusal_controls().iter().map(|control| control.0).collect();
    let failures: Vec<String> = labels
        .into_iter()
        .filter_map(|label| {
            let control = if SEGMENT_TRANSITIONS.contains(&label) {
                quotient_refusal_control(label).and_then(|()| segment_transition(label))
            } else {
                refusal_control(label)
            };
            control.err().map(|why| format!("{label}: {why}"))
        })
        .collect();
    assert!(failures.is_empty(), "{}", failures.join("\n"));
    // A builder fault the check catches is a construction refusal, which
    // names the chains it was built for.
    let _mutant = mutant::set("builder-wrong-offset");
    let (source, machine) = slice24_pair(Shape24::JoinChain);
    match owner24(&source, &machine) {
        Err(X86BodyRefusal::Unsupported(reason @ X86BodyUnsupported::OverQuotient { .. })) => {
            assert!(
                matches!(inner(&reason), X86BodyUnsupported::Construction(detail)
                    if detail.contains("is not the exact contraction")),
                "{reason}"
            );
        }
        other => panic!("{}", refusal_text(&other)),
    }
}

/// F14: the parts route plans and cuts the quotient (at a head, and at an
/// absorbed member's start: a seam), every piece's id above the original
/// pair's; a test policy's point at a `Jump` the quotient removes refuses by
/// name.
#[test]
fn parts_state_merged_chains_at_heads_and_seams() {
    for index in 0..parts_fixtures().len() {
        parts_control(index).unwrap_or_else(|why| panic!("{}: {why}", parts_fixtures()[index].0));
    }
    let (source, machine) = slice24_pair(Shape24::JoinChain);
    let (_, _, j, _, _) = join_blocks(&source);
    let jump = source.blocks[&j].instructions.len() - 1;
    match parts24(&source, &machine, vec![(j, jump)]) {
        Err(X86BodyRefusal::Unsupported(reason)) => assert!(
            format!("{reason}").contains("which the merged-chain quotient removes"),
            "{reason}"
        ),
        other => panic!("{}", refusal_text(&other)),
    }
}

/// Design §5.3's wrong lowerings, and the folded branch of D2, are each
/// refuted on samples, a named mismatch or no claim, never a theorem that
/// holds. Each outcome is printed by kind.
#[test]
fn wrong_merged_lowerings_are_never_credited() {
    let mut cases = slice_twenty_four_refutations();
    let (source, machine) = folded_brif();
    cases.push(("W14 folded Brif", source, machine));
    for (label, source, machine) in cases {
        match owner24(&source, &machine) {
            Ok(owner) => {
                assert!(
                    owner_refuted(&owner),
                    "{label}: a wrong lowering's theorem holds\n{}{}",
                    describe(&machine),
                    text(owner.obligation())
                );
                eprintln!("S24_WRONG {label}: stated, refuted on samples");
            }
            Err(X86BodyRefusal::Mismatch(mismatch)) => {
                eprintln!("S24_WRONG {label}: named mismatch ({mismatch})")
            }
            Err(X86BodyRefusal::Unsupported(reason)) => {
                eprintln!("S24_WRONG {label}: no claim ({reason})")
            }
        }
    }
}

/// W13: a `jcc` before the guard's carrier inside the merged block (the
/// machine returns where the source traps) is never credited, and it is the
/// stop rule over the quotient that decides it: the walk over the quotient
/// pair refuses because the routes of the merged block to one successor
/// stop differently, or because the `jcc`'s fallthrough also reaches its
/// target (design §3), never a named mismatch; a statement must be refuted.
#[test]
fn a_jcc_before_a_trap_carrier_is_never_credited() {
    let (label, source, machine) = w13();
    match owner24(&source, &machine) {
        Ok(owner) => assert!(owner_refuted(&owner), "{label}: holds"),
        Err(X86BodyRefusal::Unsupported(X86BodyUnsupported::OverQuotient { reason, .. })) => {
            let reason = format!("{reason}");
            assert!(
                reason.contains("stop differently")
                    || reason.contains("whose fallthrough also reaches"),
                "{label}: not the stop rule over the quotient: {reason}"
            );
        }
        Err(other) => {
            panic!("{label}: neither the stop rule over the quotient nor refuted: {other}")
        }
    }
}

/// `Quotient::check` alone refuses the contractions the link rule declines
/// where no other decline can: a `Brif` no row names (the folded branch of
/// D2) and an entry with no parameter behind a dead `Jump`. With the
/// builder's rule broken, each is a `Construction` refusal of the check's
/// link clause; with the check off too, the entry's quotient has no entry
/// block and makes no claim. (With the check off, the folded branch is
/// credited: `every_mutant_fails_a_control` kills that configuration.)
#[test]
fn the_check_refuses_what_the_rules_decline() {
    for (label, builder) in [
        ("D2 folded", "link-any-terminator"),
        ("entry behind a dead Jump", "allow-entry"),
    ] {
        let _clean = mutant::set("");
        caught_control(label, builder).unwrap_or_else(|why| panic!("{label}: {why}"));
    }
    let _mutant = mutant::set("allow-entry,check-off");
    let (source, machine) = entry_behind_a_dead_jump();
    match owner24(&source, &machine) {
        Err(X86BodyRefusal::Unsupported(reason)) => {
            eprintln!("S24_CHECK entry behind a dead Jump, check off: no claim ({reason})")
        }
        other => panic!("with the check off: {}", refusal_text(&other)),
    }
}

/// OD-210 over the quotient: a merged chain whose theorem trusts
/// `__udivti3` is stated when its module is named and does not define the
/// routine, and refused when no module is named; that refusal names the
/// chains like every other refusal of the route (before, it was the bare
/// `TrustedRoutine`).
#[test]
fn a_trusted_routine_refusal_over_the_quotient_names_its_chains() {
    let (source, machine) = extra24("routine chain");
    let owner = super::slice22::fixture_owner(&source, &machine)
        .unwrap_or_else(|refusal| panic!("in its module: {refusal}"));
    assert!(owner.merged_chains().is_some(), "over a quotient");
    assert!(
        owner
            .trusted_routines()
            .any(|routine| routine == "__udivti3"),
        "{:?}",
        owner.trusted_routines().collect::<Vec<_>>()
    );
    match owner24(&source, &machine) {
        Err(X86BodyRefusal::Unsupported(reason @ X86BodyUnsupported::OverQuotient { .. })) => {
            assert!(
                matches!(
                    inner(&reason),
                    X86BodyUnsupported::TrustedRoutine {
                        definition: X86RoutineDefinition::Unnamed,
                        ..
                    }
                ),
                "{reason}"
            );
            assert!(format!("{reason}").contains("(over the merged-chain quotient: chains "));
        }
        other => panic!("{}", refusal_text(&other)),
    }
}

/// The parts route over a quotient on its production wiring: the planner
/// cuts [`Variant24::LongChain`]'s one merged machine block (past the
/// single-query bounds), and a region past a test policy's bound is named
/// in the ORIGINAL source's coordinates.
#[test]
fn the_parts_route_plans_and_bounds_a_merged_block() {
    planned_parts_control().unwrap();
    region_original_control().unwrap();
}

/// The verifier's trace (`TCG_X86_BODY_TRACE`) of a theorem over the
/// merged-chain quotient: its `merged chains=K absorbed=N` line, then (in
/// parts) its `stated in parts=` line, and its last line `bound rows=`, the
/// order the census parsers read (design §2.5). Run in a child process,
/// which writes the trace to its stderr; no replay (`TCG_REFINE_SOLVER=0`).
#[test]
fn the_merged_chains_trace_line_precedes_the_parts_and_bound_lines() {
    const CHILD: &str = "TCG_S24_TRACE_CHILD";
    const TEST: &str = "x86_source_bound_body::tests::slice24::\
                        the_merged_chains_trace_line_precedes_the_parts_and_bound_lines";
    if std::env::var_os(CHILD).is_some() {
        super::without_replay(|| {
            let verifier = promotion_verifier();
            let request = verifier.capture_request_with_mode(ProvenanceXCheckMode::Enforce);
            for (source, machine) in [slice24_pair(Shape24::JoinChain), extra24("long chain")] {
                let _ = verifier.verify_with_request_for_export(
                    &machine,
                    Some(&source),
                    SYSV,
                    &request,
                );
            }
        });
        return;
    }
    let output = std::process::Command::new(std::env::current_exe().expect("current libtest"))
        .args(["--exact", TEST, "--nocapture", "--test-threads=1"])
        .env(CHILD, "1")
        .env("TCG_X86_BODY_TRACE", "1")
        .stdin(std::process::Stdio::null())
        .output()
        .expect("run the child test");
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        output.status.success() && stdout.contains("test result: ok. 1 passed;"),
        "the child must pass exactly once: {}\n{stdout}\n{stderr}",
        output.status
    );
    for (function, parts) in [("s24_join_chain", false), ("s24_long_chain", true)] {
        let lines: Vec<&str> = stderr
            .lines()
            .filter(|line| line.starts_with(&format!("[TCG-X86-BODY-TRACE] fn={function} ")))
            .collect();
        let position = |needle: &str| lines.iter().position(|line| line.contains(needle));
        let merged = position(" merged chains=")
            .unwrap_or_else(|| panic!("{function}: no merged-chains line: {lines:?}"));
        let last = lines.last().expect("a trace line");
        assert!(
            last.contains(" bound rows="),
            "{function}: last line {last:?}"
        );
        assert!(merged + 1 < lines.len(), "{function}: {lines:?}");
        match position(" stated in parts=") {
            Some(stated) => {
                assert!(parts, "{function}: stated in parts: {lines:?}");
                assert!(merged < stated, "{function}: {lines:?}");
            }
            None => assert!(!parts, "{function}: no parts line: {lines:?}"),
        }
    }
}

/// Design §5.5: on the correct code every control holds; each mutant of a
/// slice-24a rule breaks the controls it names.
#[test]
fn every_mutant_fails_a_control() {
    let mut controls: Vec<Control> = MUTANTS
        .iter()
        .flat_map(|(_, controls)| controls.iter().copied())
        .collect();
    controls.extend(SLICE_TWENTY_FOUR.map(Control::Owner));
    for control in controls {
        under("", control).unwrap_or_else(|why| panic!("none: {control:?}: {why}"));
    }
    let mut survived = Vec::new();
    for (names, controls) in MUTANTS {
        for control in *controls {
            match under(names, *control) {
                Ok(()) => survived.push(format!("{names}: {control:?} still holds")),
                Err(why) => {
                    eprintln!("S24_MUTANT mutant={names} control={control:?} failed: {why}")
                }
            }
        }
    }
    assert!(survived.is_empty(), "{}", survived.join("\n"));
}

// ---------------------------------------------------------------------------
// The golden text
// ---------------------------------------------------------------------------

/// The golden text of every slice-24a fixture: its theorem (each part's, for
/// one stated in parts).
pub(crate) fn slice_twenty_four_snapshots() -> String {
    let mut rendered = String::new();
    for shape in SLICE_TWENTY_FOUR {
        let (source, machine) = slice24_pair(shape);
        let owner =
            owner24(&source, &machine).unwrap_or_else(|refusal| panic!("{shape:?}: {refusal}"));
        rendered.push_str(&format!(";;;; {shape:?}\n{}\n", text(owner.obligation())));
    }
    for (label, source, machine, points) in parts_fixtures() {
        let owner = parts24(&source, &machine, points)
            .unwrap_or_else(|refusal| panic!("{label}: {refusal}"));
        for (k, part) in owner.parts().iter().enumerate() {
            rendered.push_str(&format!(";;;; {label} | part {}\n{}\n", k + 1, text(part)));
        }
    }
    rendered
}

/// The reviewed digest of the slice-24a golden text.
const SLICE_TWENTY_FOUR_SNAPSHOT_SHA256: &str =
    "0e291cb367f9a57630410e08e4e223c359dc6fe8d731c43151b227b0ed06ab75";

fn snapshot_control() -> Result<(), String> {
    use sha2::{Digest, Sha256};
    let digest = format!(
        "{:x}",
        Sha256::digest(slice_twenty_four_snapshots().as_bytes())
    );
    if digest != SLICE_TWENTY_FOUR_SNAPSHOT_SHA256 {
        return Err(format!("the golden text moved: {digest}"));
    }
    Ok(())
}

/// The rendered theorems of every slice-24a fixture are the reviewed golden
/// text, pinned by digest.
#[test]
fn slice_twenty_four_smt2_is_canonical_per_shape() {
    use sha2::{Digest, Sha256};
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tests/fixtures/x86_source_bound_body/slice24_snapshots.smt2");
    let rendered = slice_twenty_four_snapshots();
    let digest = format!("{:x}", Sha256::digest(rendered.as_bytes()));
    if std::env::var_os("TCG_X86_BODY_SNAPSHOT_WRITE").is_some() {
        std::fs::write(&path, &rendered).unwrap();
        panic!(
            "rewrote {}; review its diff, set SLICE_TWENTY_FOUR_SNAPSHOT_SHA256 to {digest} and \
             re-run without TCG_X86_BODY_SNAPSHOT_WRITE",
            path.display()
        );
    }
    let golden = std::fs::read_to_string(&path).unwrap_or_default();
    assert_eq!(rendered, golden, "slice24_snapshots.smt2 drifted");
    assert_eq!(digest, SLICE_TWENTY_FOUR_SNAPSHOT_SHA256);
}
