// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! Slice 24c of the x86-64 source-bound body theorem: segments, the
//! if-converted regions (ruling OD-228). `X86IfConvert` keeps a diamond's
//! header rows, hoists the arms' flag-free computes (stamped clones), adds an
//! unattributed `mov` and `cmov` and deletes both arms; an arm that only
//! copied a value leaves no row (stamp-silent). The machine block then lowers
//! rows of several LIR blocks, or names one whose arms have no machine block,
//! and the owner states the theorem over the segment the stamps choose: one
//! machine block paired with every source path through a single-entry
//! acyclic region of LIR blocks.
//!
//! Fixtures take their LIR from the trust-ir adapter (translated with an
//! explicit `Permit`) and their machine stream from the real x86-64
//! instruction selector (`super::select`), then from the real x86 pass
//! pipeline (`super::slice25::optimized`: O2, and O3 for
//! [`Shape24c::JoinContinues`]); [`pair24c`] asserts the pipeline
//! if-converted (a `cmov` row), so an inherited opt-out knob cannot hollow a
//! fixture. [`Shape24c::AbsorbedParams`] is slice 24a's D5 pair (the
//! block-merged selector stream). The wrong lowerings and refusal controls
//! ([`case24c`]) are those pairs with the labelled hand edits each names.
//! Every test here runs without a solver (the
//! `x86_source_bound_body::tests::slice24c::` library gate); the replay on
//! AY and Clean is in `slice24c_qualification`.
//!
//! Everything above the "Controls" section uses only the slice 1-25 API, so
//! the same fixtures are judged by the code before slice 24c (the
//! fails-before record of the 2026-11-05 report).

use super::slice5::describe;
use super::slice6::describe_lir;
use super::slice16::cut_at;
use super::slice24::{owner_holds, owner_refuted, text};
use super::*;
use trust_cg_ir::X86CondCode;
use trust_cg_ir::regs::RegClass;
use trust_ir::{Constant, ICmpOp, SwitchCase};

// ---------------------------------------------------------------------------
// Fixtures
// ---------------------------------------------------------------------------

/// Slice-24c fixture shapes (design §5.2), each a correct lowering the owner
/// states over its segments.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Shape24c {
    /// P1 (`align_offset`): `if c < 8 { a + 5 } else { 9 }` into `j(v)`:
    /// both arms computed (named).
    AlignOffset,
    /// P2 (`wrapping_abs`'s shape): `if x < y { y - x } else { x }`: one
    /// computed arm, one copy (stamp-silent). (`wrapping_abs`'s own `x < 0`
    /// is a `test` the selector leaves unstamped: a silent head, which stays
    /// refused, [`Variant24c::ZeroTestAbs`].)
    WrappingAbs,
    /// P3 (`select_unpredictable`'s shape): `if c < a { a } else { b }`:
    /// both arms copies, the machine block naming its head alone. (A
    /// `c != 0` test is an unstamped `test`: [`Variant24c::ZeroTestSelect`].)
    SelectUnpredictable,
    /// P4 (`match force_sign`): a two-way `Switch` of an `u8`, its arms the
    /// constants 10 and 20.
    ForceSign,
    /// P5 (`integer_decode`): `y = a + b; br n; n: if y < c { y + 1 } else
    /// { 7 }`: the chain `entry -> n` and the diamond in one machine block
    /// (the block merge, then the if-conversion).
    IntegerDecode,
    /// P6: a bottom-tested counting loop from `h(0, 1)` whose header `h(i,
    /// acc)` computes `s = acc + i` and is a diamond `if s < n { s + 3 } else
    /// { acc }` into the latch `latch(v)` (a non-header join), the segment's
    /// head a loop header. The header's `s` is live into the arm, so the
    /// loop rotation does not copy the header into the latch's edge (a
    /// pure-test header is copied, its arms then entered twice and never
    /// if-converted; a top-tested loop is rotated and refused before any
    /// segment, [`Variant24c::RotatedLoop`]). The two initial values differ:
    /// from `h(0, 0)` the entry edge's second copy reads the first's register
    /// and carries no stamp (refused at the loop's entry edge, as without
    /// segments).
    LoopDiamond,
    /// P9 (O3): P1 whose join `j(v)` continues (`if v < b { v } else { v + 1
    /// }`), merged into the if-converted block: an internal join.
    JoinContinues,
    /// P11: slice 24a's D5 (`x: br y(t); y(p): ..`, the member `y` declares
    /// a parameter, so the merged-chain quotient declines it): a chain-only
    /// segment.
    AbsorbedParams,
}

/// Every slice-24c fixture shape (P7 and P8 are routes of P1:
/// [`encodings_of_p1`], [`Variant24c::LongDiamond`]).
pub(crate) const SLICE_TWENTY_FOUR_C: [Shape24c; 8] = [
    Shape24c::AlignOffset,
    Shape24c::WrappingAbs,
    Shape24c::SelectUnpredictable,
    Shape24c::ForceSign,
    Shape24c::IntegerDecode,
    Shape24c::LoopDiamond,
    Shape24c::JoinContinues,
    Shape24c::AbsorbedParams,
];

/// Further sources: the bases of the wrong lowerings and refusal controls.
/// Each `edited` source differs from its base only where it names; the
/// pair's machine is the base's.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Variant24c {
    /// W3's base: `entry: if d < 100 { br h } else { br w }; w: br h; h:` P1.
    /// Edited: `w: br t` (a live block entering a member).
    PrefixedDiamond,
    /// W4: P1, edited with `sink(a)` in the then arm.
    ArmCall,
    /// N11's base: P1 after `sink(a)` in the head. Edited: `sink(a)` in the
    /// then arm too (two members with calls).
    TwoCalls,
    /// W5: P1 over an incoming `p: *mut u64`, edited with `*p = x` in the then
    /// arm.
    ArmStore,
    /// W6: P1 with a private slot `s = 9` before the branch and `s` read at
    /// the join, edited with `s = x` in the then arm.
    ArmPrivateStore,
    /// W8: P1, edited so that the then arm returns `x`.
    ArmReturns,
    /// W9: P1, edited with `q = x / c` in the then arm (an undefined
    /// division: a stop), the arm passing `q`.
    ArmDivides,
    /// W17: P1, edited so that the else arm traps.
    ArmTraps,
    /// N7: P1, edited so that the else arm also exits to a new returning
    /// block `r` (`if c >= 100 { return 0 }`), which a synthetic machine
    /// block lowers: the segment's machine block reaches `j` only.
    ElseExits,
    /// W10: a counting loop `while i < n { acc += i; i += 1 }` (the O2
    /// rotation copies the header's test into the latch).
    RotatedLoop,
    /// P8: P1 whose join `j(v)` computes `v + 7` and heads a chain of
    /// [`LONG_DIAMOND`] blocks: past the single-query bounds (the parts
    /// route).
    LongDiamond,
    /// SH2: `wrapping_abs` itself, `if x < 0 { 0 - x } else { x }`: the
    /// zero test is an unstamped `test`, so the if-converted block names no
    /// head (a silent head): refused, no segment.
    ZeroTestAbs,
    /// SH3: `select_unpredictable` over `c != 0`: no row of the if-converted
    /// block is stamped (a silent head): refused, no segment.
    ZeroTestSelect,
    /// P8s: P1 whose join `j(v)` computes `v + 7` and heads a chain of
    /// [`SHORT_TAIL`] blocks: within the single-query bounds, stated over
    /// OD-226's quotient (the chain contracted) and P1's segment.
    ShortTail,
    /// P12: P1 whose join `j(v)` tests `w = v + 7 < 100` into two chains:
    /// `A` ([`FORKED_LIVE`] blocks) adds constants to `a` and returns that
    /// plus `v`, so the join's parameter stays live through it; `B`
    /// ([`FORKED_DEAD`] blocks) adds constants to `a` into `y`, then
    /// branches on `y < b` to return `y` or `b` (a branch, so that a region
    /// of `B`'s keeps a claim once its identities drop). Past the
    /// single-query block bound and, over OD-226's quotient, past one part's
    /// 256 rows: the production planner cuts, and no cut may be at a point of
    /// `A`, where `v` (defined only by the diamond's members) is live.
    ForkedTail,
    /// N3: a bottom-tested counting loop `h(i, acc)` from `h(0, 1)` whose
    /// header computes the invariant `k = a * b` and `acc + k`:
    /// X86LoopInvariantCodeMotion hoists the header's rows for `k` into the
    /// preheader's machine block, which then names the entry and the loop
    /// header.
    LicmHeader,
    /// N8: the entry computes `x = a + 5` and jumps to `p(w)`, which
    /// computes `y = w * b` and enters the bottom-tested loop `h(v, i)`
    /// (`v + i`, `i + 1 < n`): `X86BlockMerge` joins the entry and `p` (one
    /// machine block naming both; OD-226's quotient declines the chain, since
    /// `p` declares a parameter), whose segment would exit into a loop
    /// header. A diamond whose join is a loop header never reaches the
    /// chooser: the header is entered from both arms, and the lane admits one
    /// entering edge.
    ChainIntoLoop,
}

/// The blocks after [`Variant24c::LongDiamond`]'s join.
pub(crate) const LONG_DIAMOND: usize = 140;

/// The blocks after [`Variant24c::ShortTail`]'s join.
pub(crate) const SHORT_TAIL: usize = 3;

/// The blocks of [`Variant24c::ForkedTail`]'s chain `A` (the join's
/// parameter live) and `B` (dead): one row each at O2, so a cut inside `A`
/// after its first 64-row piece would leave the larger first region (the
/// planner's preference), and only a cut inside `B` is admissible.
pub(crate) const FORKED_LIVE: usize = 122;
pub(crate) const FORKED_DEAD: usize = 162;

type Builder24c<'a> = trust_ir_build::FunctionBuilder<'a>;
type V24c = trust_ir::value::ValueId;

/// Translate one function of `builder`'s module under the explicit Permit
/// the workspace's fixtures use.
fn translate24c(builder: ModuleBuilder, name: &str) -> Function {
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

/// `x + k` (`u64`).
fn plus(f: &mut Builder24c<'_>, x: V24c, k: i128) -> V24c {
    let k = f.iconst(Ty::U64, k);
    f.add(Ty::U64, x, k)
}

/// What the then arm of [`diamond`] runs after `x = a + 5`, before its
/// transfer.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum ThenArm {
    Plain,
    Call(trust_ir::FuncId),
    Store(V24c),
    Return,
    Divide,
}

/// P1's diamond from the current block: `if c < 8 { x = a + 5 } else { 9 }`
/// into a new join `j(v)`, which becomes current; `then` adds to the then
/// arm, `trap_else` makes the else arm trap. Returns `j`'s parameter and
/// the then arm.
fn diamond(
    f: &mut Builder24c<'_>,
    a: V24c,
    c: V24c,
    then: ThenArm,
    trap_else: bool,
) -> (V24c, trust_ir::value::BlockId) {
    let (t, e, j) = (f.create_block(), f.create_block(), f.create_block());
    let jv = f.add_block_param(j, Ty::U64);
    let eight = f.iconst(Ty::U64, 8);
    let test = f.icmp(ICmpOp::Ult, Ty::U64, c, eight);
    f.condbr(test, t, vec![], e, vec![]);
    f.switch_to_block(t);
    let x = plus(f, a, 5);
    match then {
        ThenArm::Plain => f.br(j, vec![x]),
        ThenArm::Call(sink) => {
            f.call_void(sink, vec![a]);
            f.br(j, vec![x]);
        }
        ThenArm::Store(p) => {
            f.store(Ty::U64, p, x);
            f.br(j, vec![x]);
        }
        ThenArm::Return => f.ret(vec![x]),
        ThenArm::Divide => {
            let q = f.udiv(Ty::U64, x, c);
            f.br(j, vec![q]);
        }
    }
    f.switch_to_block(e);
    if trap_else {
        f.unreachable();
    } else {
        let nine = f.iconst(Ty::U64, 9);
        f.br(j, vec![nine]);
    }
    f.switch_to_block(j);
    (jv, t)
}

/// The LIR the trust-ir adapter produces for a shape or a variant (`edited`:
/// the variant's edited source, else its base).
fn lir24c(name: &str, shape: Option<Shape24c>, variant: Option<(Variant24c, bool)>) -> Function {
    use Shape24c::*;
    use Variant24c::*;
    let mut builder = ModuleBuilder::new("x86_source_bound_body_slice24c");
    let ptr_u64 = Ty::PtrMut(Box::new(Ty::U64));
    let sink_ty = builder.add_func_type(vec![Ty::U64], vec![]);
    let sink = builder.declare_function("sink", sink_ty);
    let (params, results): (Vec<Ty>, Vec<Ty>) = match (shape, variant) {
        (Some(WrappingAbs), _) => (vec![Ty::I64, Ty::I64], vec![Ty::I64]),
        (_, Some((ZeroTestAbs, _))) => (vec![Ty::I64], vec![Ty::I64]),
        (_, Some((ZeroTestSelect, _))) => (vec![Ty::U64, Ty::U64, Ty::U64], vec![Ty::U64]),
        (Some(SelectUnpredictable | JoinContinues | IntegerDecode), _) => {
            (vec![Ty::U64, Ty::U64, Ty::U64], vec![Ty::U64])
        }
        (Some(ForceSign), _) => (vec![Ty::U8], vec![Ty::U64]),
        (Some(LoopDiamond), _) | (_, Some((RotatedLoop, _))) => (vec![Ty::U64], vec![Ty::U64]),
        (_, Some((LicmHeader | ChainIntoLoop, _))) => {
            (vec![Ty::U64, Ty::U64, Ty::U64], vec![Ty::U64])
        }
        (_, Some((PrefixedDiamond, _))) => (vec![Ty::U64, Ty::U64, Ty::U64], vec![Ty::U64]),
        (_, Some((ArmStore, _))) => (vec![ptr_u64, Ty::U64, Ty::U64], vec![Ty::U64]),
        _ => (vec![Ty::U64, Ty::U64], vec![Ty::U64]),
    };
    let signature = builder.add_func_type(params.clone(), results);
    let mut f = builder.function(name.to_owned(), signature);
    let entry = f.create_block();
    let args: Vec<V24c> = params
        .iter()
        .map(|ty| f.add_block_param(entry, ty.clone()))
        .collect();
    f.switch_to_block(entry);
    match (shape, variant) {
        (Some(AlignOffset), _) => {
            let (jv, _) = diamond(&mut f, args[0], args[1], ThenArm::Plain, false);
            f.ret(vec![jv]);
        }
        (Some(WrappingAbs), _) => {
            let (t, e, j) = (f.create_block(), f.create_block(), f.create_block());
            let jv = f.add_block_param(j, Ty::I64);
            let below = f.icmp(ICmpOp::Slt, Ty::I64, args[0], args[1]);
            f.condbr(below, t, vec![], e, vec![]);
            f.switch_to_block(t);
            let negated = f.sub(Ty::I64, args[1], args[0]);
            f.br(j, vec![negated]);
            f.switch_to_block(e);
            f.br(j, vec![args[0]]);
            f.switch_to_block(j);
            f.ret(vec![jv]);
        }
        (Some(SelectUnpredictable), _) => {
            let (t, e, j) = (f.create_block(), f.create_block(), f.create_block());
            let jv = f.add_block_param(j, Ty::U64);
            let test = f.icmp(ICmpOp::Ult, Ty::U64, args[0], args[1]);
            f.condbr(test, t, vec![], e, vec![]);
            f.switch_to_block(t);
            f.br(j, vec![args[1]]);
            f.switch_to_block(e);
            f.br(j, vec![args[2]]);
            f.switch_to_block(j);
            f.ret(vec![jv]);
        }
        (None, Some((ZeroTestAbs, _))) => {
            let (t, e, j) = (f.create_block(), f.create_block(), f.create_block());
            let jv = f.add_block_param(j, Ty::I64);
            let zero = f.iconst(Ty::I64, 0);
            let negative = f.icmp(ICmpOp::Slt, Ty::I64, args[0], zero);
            f.condbr(negative, t, vec![], e, vec![]);
            f.switch_to_block(t);
            let negated = f.sub(Ty::I64, zero, args[0]);
            f.br(j, vec![negated]);
            f.switch_to_block(e);
            f.br(j, vec![args[0]]);
            f.switch_to_block(j);
            f.ret(vec![jv]);
        }
        (None, Some((ZeroTestSelect, _))) => {
            let (t, e, j) = (f.create_block(), f.create_block(), f.create_block());
            let jv = f.add_block_param(j, Ty::U64);
            let zero = f.iconst(Ty::U64, 0);
            let test = f.icmp(ICmpOp::Ne, Ty::U64, args[0], zero);
            f.condbr(test, t, vec![], e, vec![]);
            f.switch_to_block(t);
            f.br(j, vec![args[1]]);
            f.switch_to_block(e);
            f.br(j, vec![args[2]]);
            f.switch_to_block(j);
            f.ret(vec![jv]);
        }
        (Some(ForceSign), _) => {
            let (t, e, j) = (f.create_block(), f.create_block(), f.create_block());
            let jv = f.add_block_param(j, Ty::U64);
            f.switch(
                args[0],
                vec![SwitchCase {
                    value: Constant::Int(0),
                    target: t,
                    args: vec![],
                }],
                e,
                vec![],
            );
            f.switch_to_block(t);
            let ten = f.iconst(Ty::U64, 10);
            f.br(j, vec![ten]);
            f.switch_to_block(e);
            let twenty = f.iconst(Ty::U64, 20);
            f.br(j, vec![twenty]);
            f.switch_to_block(j);
            f.ret(vec![jv]);
        }
        (Some(IntegerDecode), _) => {
            let (n, t, e, j) = (
                f.create_block(),
                f.create_block(),
                f.create_block(),
                f.create_block(),
            );
            let jv = f.add_block_param(j, Ty::U64);
            let y = f.add(Ty::U64, args[0], args[1]);
            f.br(n, vec![]);
            f.switch_to_block(n);
            let test = f.icmp(ICmpOp::Ult, Ty::U64, y, args[2]);
            f.condbr(test, t, vec![], e, vec![]);
            f.switch_to_block(t);
            let z = plus(&mut f, y, 1);
            f.br(j, vec![z]);
            f.switch_to_block(e);
            let seven = f.iconst(Ty::U64, 7);
            f.br(j, vec![seven]);
            f.switch_to_block(j);
            f.ret(vec![jv]);
        }
        (Some(LoopDiamond), _) => {
            let (h, t, e, latch, exit) = (
                f.create_block(),
                f.create_block(),
                f.create_block(),
                f.create_block(),
                f.create_block(),
            );
            let i = f.add_block_param(h, Ty::U64);
            let acc = f.add_block_param(h, Ty::U64);
            let v = f.add_block_param(latch, Ty::U64);
            let zero = f.iconst(Ty::U64, 0);
            let one = f.iconst(Ty::U64, 1);
            f.br(h, vec![zero, one]);
            f.switch_to_block(h);
            let s = f.add(Ty::U64, acc, i);
            let below = f.icmp(ICmpOp::Ult, Ty::U64, s, args[0]);
            f.condbr(below, t, vec![], e, vec![]);
            f.switch_to_block(t);
            let x = plus(&mut f, s, 3);
            f.br(latch, vec![x]);
            f.switch_to_block(e);
            f.br(latch, vec![acc]);
            f.switch_to_block(latch);
            let next = plus(&mut f, i, 1);
            let more = f.icmp(ICmpOp::Ult, Ty::U64, next, args[0]);
            f.condbr(more, h, vec![next, v], exit, vec![]);
            f.switch_to_block(exit);
            f.ret(vec![v]);
        }
        (Some(JoinContinues), _) => {
            let (jv, _) = diamond(&mut f, args[0], args[1], ThenArm::Plain, false);
            let (low, high) = (f.create_block(), f.create_block());
            let test = f.icmp(ICmpOp::Ult, Ty::U64, jv, args[2]);
            f.condbr(test, low, vec![], high, vec![]);
            f.switch_to_block(low);
            f.ret(vec![jv]);
            f.switch_to_block(high);
            let bumped = plus(&mut f, jv, 1);
            f.ret(vec![bumped]);
        }
        (Some(AbsorbedParams), _) => unreachable!("slice 24a's D5 pair"),
        (None, Some((PrefixedDiamond, edited))) => {
            let (h, w) = (f.create_block(), f.create_block());
            let hundred = f.iconst(Ty::U64, 100);
            let small = f.icmp(ICmpOp::Ult, Ty::U64, args[2], hundred);
            f.condbr(small, h, vec![], w, vec![]);
            f.switch_to_block(h);
            let (jv, t) = diamond(&mut f, args[0], args[1], ThenArm::Plain, false);
            f.ret(vec![jv]);
            // `w` enters the head (the base) or, edited, the then arm `t`.
            f.switch_to_block(w);
            f.br(if edited { t } else { h }, vec![]);
        }
        (None, Some((ArmCall, edited))) => {
            let then = if edited {
                ThenArm::Call(sink)
            } else {
                ThenArm::Plain
            };
            let (jv, _) = diamond(&mut f, args[0], args[1], then, false);
            f.ret(vec![jv]);
        }
        (None, Some((TwoCalls, edited))) => {
            f.call_void(sink, vec![args[0]]);
            let then = if edited {
                ThenArm::Call(sink)
            } else {
                ThenArm::Plain
            };
            let (jv, _) = diamond(&mut f, args[0], args[1], then, false);
            f.ret(vec![jv]);
        }
        (None, Some((ArmStore, edited))) => {
            let then = if edited {
                ThenArm::Store(args[0])
            } else {
                ThenArm::Plain
            };
            let (jv, _) = diamond(&mut f, args[1], args[2], then, false);
            f.ret(vec![jv]);
        }
        (None, Some((ArmPrivateStore, edited))) => {
            let slot = f.alloca(Ty::U64);
            let nine = f.iconst(Ty::U64, 9);
            f.store(Ty::U64, slot, nine);
            let then = if edited {
                ThenArm::Store(slot)
            } else {
                ThenArm::Plain
            };
            let (jv, _) = diamond(&mut f, args[0], args[1], then, false);
            let held = f.load(Ty::U64, slot);
            let sum = f.add(Ty::U64, held, jv);
            f.ret(vec![sum]);
        }
        (None, Some((ArmReturns, edited))) => {
            let then = if edited {
                ThenArm::Return
            } else {
                ThenArm::Plain
            };
            let (jv, _) = diamond(&mut f, args[0], args[1], then, false);
            f.ret(vec![jv]);
        }
        (None, Some((ArmDivides, edited))) => {
            let then = if edited {
                ThenArm::Divide
            } else {
                ThenArm::Plain
            };
            let (jv, _) = diamond(&mut f, args[0], args[1], then, false);
            f.ret(vec![jv]);
        }
        (None, Some((ElseExits, false))) => {
            let (jv, _) = diamond(&mut f, args[0], args[1], ThenArm::Plain, false);
            f.ret(vec![jv]);
        }
        (None, Some((ElseExits, true))) => {
            let (t, e, j, r) = (
                f.create_block(),
                f.create_block(),
                f.create_block(),
                f.create_block(),
            );
            let jv = f.add_block_param(j, Ty::U64);
            let eight = f.iconst(Ty::U64, 8);
            let test = f.icmp(ICmpOp::Ult, Ty::U64, args[1], eight);
            f.condbr(test, t, vec![], e, vec![]);
            f.switch_to_block(t);
            let x = plus(&mut f, args[0], 5);
            f.br(j, vec![x]);
            f.switch_to_block(e);
            let nine = f.iconst(Ty::U64, 9);
            let hundred = f.iconst(Ty::U64, 100);
            let big = f.icmp(ICmpOp::Uge, Ty::U64, args[1], hundred);
            f.condbr(big, r, vec![], j, vec![nine]);
            f.switch_to_block(j);
            f.ret(vec![jv]);
            f.switch_to_block(r);
            let zero = f.iconst(Ty::U64, 0);
            f.ret(vec![zero]);
        }
        (None, Some((ArmTraps, edited))) => {
            let (jv, _) = diamond(&mut f, args[0], args[1], ThenArm::Plain, edited);
            f.ret(vec![jv]);
        }
        (None, Some((RotatedLoop, _))) => {
            let (h, body, exit) = (f.create_block(), f.create_block(), f.create_block());
            let i = f.add_block_param(h, Ty::U64);
            let acc = f.add_block_param(h, Ty::U64);
            let zero = f.iconst(Ty::U64, 0);
            f.br(h, vec![zero, zero]);
            f.switch_to_block(h);
            let more = f.icmp(ICmpOp::Ult, Ty::U64, i, args[0]);
            f.condbr(more, body, vec![], exit, vec![]);
            f.switch_to_block(body);
            let sum = f.add(Ty::U64, acc, i);
            let next = plus(&mut f, i, 1);
            f.br(h, vec![next, sum]);
            f.switch_to_block(exit);
            f.ret(vec![acc]);
        }
        (None, Some((LongDiamond, _))) => {
            let (jv, _) = diamond(&mut f, args[0], args[1], ThenArm::Plain, false);
            let chain: Vec<_> = (0..LONG_DIAMOND).map(|_| f.create_block()).collect();
            let mut value = plus(&mut f, jv, 7);
            f.br(chain[0], vec![]);
            for (i, block) in chain.iter().enumerate() {
                f.switch_to_block(*block);
                value = plus(&mut f, value, i as i128 + 1);
                if i + 1 < LONG_DIAMOND {
                    f.br(chain[i + 1], vec![]);
                } else {
                    f.ret(vec![value]);
                }
            }
        }
        (None, Some((ShortTail, _))) => {
            let (jv, _) = diamond(&mut f, args[0], args[1], ThenArm::Plain, false);
            let chain: Vec<_> = (0..SHORT_TAIL).map(|_| f.create_block()).collect();
            let mut value = plus(&mut f, jv, 7);
            f.br(chain[0], vec![]);
            for (i, block) in chain.iter().enumerate() {
                f.switch_to_block(*block);
                value = plus(&mut f, value, i as i128 + 1);
                if i + 1 < SHORT_TAIL {
                    f.br(chain[i + 1], vec![]);
                } else {
                    f.ret(vec![value]);
                }
            }
        }
        (None, Some((ForkedTail, _))) => {
            let (jv, _) = diamond(&mut f, args[0], args[1], ThenArm::Plain, false);
            let w = plus(&mut f, jv, 7);
            let hundred = f.iconst(Ty::U64, 100);
            let low = f.icmp(ICmpOp::Ult, Ty::U64, w, hundred);
            let live: Vec<_> = (0..FORKED_LIVE).map(|_| f.create_block()).collect();
            let dead: Vec<_> = (0..FORKED_DEAD).map(|_| f.create_block()).collect();
            f.condbr(low, live[0], vec![], dead[0], vec![]);
            let mut x = args[0];
            for (i, block) in live.iter().enumerate() {
                f.switch_to_block(*block);
                x = plus(&mut f, x, i as i128 + 1);
                if i + 1 < FORKED_LIVE {
                    f.br(live[i + 1], vec![]);
                } else {
                    let result = f.add(Ty::U64, x, jv);
                    f.ret(vec![result]);
                }
            }
            let (below, above) = (f.create_block(), f.create_block());
            let mut y = args[0];
            for (i, block) in dead.iter().enumerate() {
                f.switch_to_block(*block);
                y = plus(&mut f, y, i as i128 + 2);
                if i + 1 < FORKED_DEAD {
                    f.br(dead[i + 1], vec![]);
                } else {
                    let under = f.icmp(ICmpOp::Ult, Ty::U64, y, args[1]);
                    f.condbr(under, below, vec![], above, vec![]);
                }
            }
            f.switch_to_block(below);
            f.ret(vec![y]);
            f.switch_to_block(above);
            f.ret(vec![args[1]]);
        }
        (None, Some((LicmHeader, _))) => {
            let (h, exit) = (f.create_block(), f.create_block());
            let i = f.add_block_param(h, Ty::U64);
            let acc = f.add_block_param(h, Ty::U64);
            let zero = f.iconst(Ty::U64, 0);
            let one = f.iconst(Ty::U64, 1);
            f.br(h, vec![zero, one]);
            f.switch_to_block(h);
            let k = f.mul(Ty::U64, args[0], args[1]);
            let s = f.add(Ty::U64, acc, k);
            let next = plus(&mut f, i, 1);
            let more = f.icmp(ICmpOp::Ult, Ty::U64, next, args[2]);
            f.condbr(more, h, vec![next, s], exit, vec![]);
            f.switch_to_block(exit);
            f.ret(vec![s]);
        }
        (None, Some((ChainIntoLoop, _))) => {
            let (p, h, exit) = (f.create_block(), f.create_block(), f.create_block());
            let w = f.add_block_param(p, Ty::U64);
            let v = f.add_block_param(h, Ty::U64);
            let i = f.add_block_param(h, Ty::U64);
            let x = plus(&mut f, args[0], 5);
            f.br(p, vec![x]);
            f.switch_to_block(p);
            let y = f.mul(Ty::U64, w, args[1]);
            let one = f.iconst(Ty::U64, 1);
            f.br(h, vec![y, one]);
            f.switch_to_block(h);
            let sum = f.add(Ty::U64, v, i);
            let next = plus(&mut f, i, 1);
            let more = f.icmp(ICmpOp::Ult, Ty::U64, next, args[2]);
            f.condbr(more, h, vec![sum, next], exit, vec![]);
            f.switch_to_block(exit);
            f.ret(vec![sum]);
        }
        other => unreachable!("{other:?}"),
    }
    f.build();
    translate24c(builder, name)
}

/// The snake-case name of a fixture or variant (`s24c_align_offset`).
fn name24c(what: &dyn std::fmt::Debug) -> String {
    let name = format!("{what:?}");
    let mut snake = String::from("s24c_");
    for (i, c) in name.chars().enumerate() {
        if c.is_ascii_uppercase() && i > 0 {
            snake.push('_');
        }
        snake.push(c.to_ascii_lowercase());
    }
    snake
}

/// The LIR of a slice-24c fixture.
pub(crate) fn shape24c_lir(shape: Shape24c) -> Function {
    lir24c(&name24c(&shape), Some(shape), None)
}

/// The LIR of a variant (`edited`: its edited source, else its base).
pub(crate) fn variant24c_lir(variant: Variant24c, edited: bool) -> Function {
    lir24c(&name24c(&variant), None, Some((variant, edited)))
}

/// The walk ordinals of the `cmov` rows of `machine`.
pub(crate) fn cmov_rows(machine: &X86ISelFunction) -> Vec<usize> {
    super::slice25::rows_with(machine, &[X86Opcode::Cmovcc, X86Opcode::Cmovcc32])
}

/// `source`'s real pipeline stream at `opt_level`, asserted to if-convert.
#[track_caller]
fn if_converted(
    what: &str,
    source: &Function,
    opt_level: trust_cg_opt::OptLevel,
) -> X86ISelFunction {
    let machine = super::slice25::optimized(source, opt_level);
    assert!(
        !cmov_rows(&machine).is_empty(),
        "{what}: the pipeline if-converted nothing (is TCG_NO_IFCONVERT set?)\n{}{}",
        describe_lir(source),
        describe(&machine)
    );
    machine
}

/// A slice-24c fixture pair: the adapter's LIR and the real O2 stream (O3
/// for [`Shape24c::JoinContinues`]; slice 24a's D5 pair for
/// [`Shape24c::AbsorbedParams`]).
pub(crate) fn pair24c(shape: Shape24c) -> (Function, X86ISelFunction) {
    let what = format!("{shape:?}");
    match shape {
        Shape24c::AbsorbedParams => {
            super::slice24::variant24_pair(super::slice24::Variant24::AbsorbedParams)
        }
        Shape24c::JoinContinues => {
            let source = shape24c_lir(shape);
            let machine = if_converted(&what, &source, trust_cg_opt::OptLevel::O3);
            (source, machine)
        }
        _ => {
            let source = shape24c_lir(shape);
            let machine = if_converted(&what, &source, trust_cg_opt::OptLevel::O2);
            (source, machine)
        }
    }
}

/// A variant's pair: its edited source and its base's O2 stream (the base
/// asserted to if-convert, but for [`Variant24c::RotatedLoop`],
/// [`Variant24c::LicmHeader`] and [`Variant24c::ChainIntoLoop`], whose
/// controls do not need a `cmov`).
pub(crate) fn variant24c_pair(variant: Variant24c) -> (Function, X86ISelFunction) {
    let what = format!("{variant:?}");
    let base = variant24c_lir(variant, false);
    let machine = if matches!(
        variant,
        Variant24c::RotatedLoop | Variant24c::LicmHeader | Variant24c::ChainIntoLoop
    ) {
        super::slice25::optimized(&base, trust_cg_opt::OptLevel::O2)
    } else {
        if_converted(&what, &base, trust_cg_opt::OptLevel::O2)
    };
    (variant24c_lir(variant, true), machine)
}

/// The composition subjects: the O2 pipeline over earlier slices' fixtures
/// that the owner states over several segments (five, and 34 in one query),
/// a segment with an indexed access, segments with private slot bytes and
/// a segment over OD-226's quotient, then [`Variant24c::ShortTail`] (one
/// segment over the quotient) and [`Variant24c::ForkedTail`] (in parts),
/// each with its label.
pub(crate) fn composition24c() -> Vec<(String, Function, X86ISelFunction)> {
    use trust_cg_codegen::x86_64::pipeline::{X86Pipeline, X86PipelineConfig};
    const WANTED: [&str; 5] = [
        "s9 Diamonds5",
        "s9 SlotJoin",
        "s17 IndexedAcrossJoin",
        "s16 DiamondChain",
        "s24 PartialMerge",
    ];
    let pipeline = X86Pipeline::new(X86PipelineConfig {
        opt_level: trust_cg_opt::OptLevel::O2,
        call_abi: X86CallAbi::SystemV,
        ..X86PipelineConfig::default()
    });
    let mut fixtures = o0_fixtures24c();
    let mut subjects = Vec::new();
    for wanted in WANTED {
        let at = fixtures
            .iter()
            .position(|(label, _, _)| label == wanted)
            .unwrap_or_else(|| panic!("no fixture {wanted}"));
        let (label, source, mut machine) = fixtures.swap_remove(at);
        pipeline.run_x86_optimization_passes(&mut machine);
        subjects.push((format!("{label} O2"), source, machine));
    }
    let (source, machine) = case24c("P8s");
    subjects.push(("ShortTail".into(), source, machine));
    let (source, machine) = case24c("P12");
    subjects.push(("ForkedTail in parts".into(), source, machine));
    subjects
}

/// The owner of a pair (the production route).
pub(crate) fn owner24c<'a>(
    source: &'a Function,
    machine: &'a X86ISelFunction,
) -> Result<SourceBoundX86Body<'a>, X86BodyRefusal> {
    source_bound_x86_body(source, machine, SYSV)
}

/// The owner of a pair stated in parts at `points`.
pub(crate) fn parts24c<'a>(
    source: &'a Function,
    machine: &'a X86ISelFunction,
    points: Vec<(Block, usize)>,
) -> Result<SourceBoundX86Body<'a>, X86BodyRefusal> {
    source_bound_x86_body_in_parts(source, machine, SYSV, &cut_at(points))
}

/// A refusal's text, or `stated`.
pub(crate) fn outcome24c(result: &Result<SourceBoundX86Body<'_>, X86BodyRefusal>) -> String {
    match result {
        Ok(_) => "stated".into(),
        Err(refusal) => format!("{refusal}"),
    }
}

/// The DAG encoding and the slice-6 path encoding (P7).
pub(crate) const DAG24C: PathEncoding = PathEncoding {
    dag: Some(true),
    ..PathEncoding::CANONICAL
};
pub(crate) const PATHS24C: PathEncoding = PathEncoding {
    dag: Some(false),
    ..PathEncoding::CANONICAL
};

/// P7: P1's theorem under the path encoding and the DAG encoding (each
/// without the affine refusal, as slice 9's encodings are compared).
pub(crate) fn encodings_of_p1() -> Vec<(&'static str, Result<ProofObligation, X86BodyRefusal>)> {
    let (source, machine) = pair24c(Shape24c::AlignOffset);
    vec![
        (
            "paths",
            theorem_with_path_encoding(&source, &machine, SYSV, PATHS24C),
        ),
        (
            "DAG",
            theorem_with_path_encoding(&source, &machine, SYSV, DAG24C),
        ),
    ]
}

// ---- edits

/// The first LIR block a `Brif` of `block` names: `(then, else)`.
fn brif24c(source: &Function, block: Block) -> (Block, Block) {
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

/// The diamond's head (the block whose `Brif` tests `c < 8`) of a
/// P1-shaped source: the entry, or the entry's then target for
/// [`Variant24c::PrefixedDiamond`].
fn head24c(source: &Function) -> Block {
    let entry = source.entry_block;
    match source.blocks[&entry]
        .instructions
        .last()
        .map(|inst| &inst.opcode)
    {
        Some(L::Brif { then_dest, .. })
            if matches!(
                source.blocks[then_dest]
                    .instructions
                    .last()
                    .map(|inst| &inst.opcode),
                Some(L::Brif { .. })
            ) =>
        {
            *then_dest
        }
        _ => entry,
    }
}

/// The diamond's `(head, then, else, join)` of a P1-shaped source.
pub(crate) fn diamond_blocks(source: &Function) -> (Block, Block, Block, Block) {
    let head = head24c(source);
    let (t, e) = brif24c(source, head);
    let join = match source.blocks[&e]
        .instructions
        .last()
        .map(|inst| &inst.opcode)
    {
        Some(L::Jump { dest }) => *dest,
        _ => match source.blocks[&t]
            .instructions
            .last()
            .map(|inst| &inst.opcode)
        {
            Some(L::Jump { dest }) => *dest,
            other => panic!("no join: {other:?}"),
        },
    };
    (head, t, e, join)
}

/// The P8 policy points: `(J, 0)` (the exit target, which declares the
/// join's parameter) and the then arm's start, each named by N13.
pub(crate) fn p8_points(source: &Function) -> [(Block, usize); 2] {
    let (_, t, _, j) = diamond_blocks(source);
    [(j, 0), (t, 0)]
}

/// The P12 policy point: the start of the 60th block of chain `A`, where the
/// join's parameter is live (named by N13).
pub(crate) fn p12_point(source: &Function) -> (Block, usize) {
    let (_, _, _, j) = diamond_blocks(source);
    let (mut block, _) = brif24c(source, j);
    for _ in 0..60 {
        block = match source.blocks[&block]
            .instructions
            .last()
            .map(|inst| &inst.opcode)
        {
            Some(L::Jump { dest }) => *dest,
            other => panic!("P12: chain A's {block:?} ends in {other:?}"),
        };
    }
    (block, 0)
}

/// A 64-bit virtual register the hand edits add (ids far above the
/// selector's).
fn vreg24c(id: u32) -> O {
    O::VReg(trust_cg_ir::regs::VReg::new(id, RegClass::Gpr64))
}

/// The walk ordinal of the first row of `machine` stamped `(block, index)`.
fn stamped_row(machine: &X86ISelFunction, block: Block, index: usize) -> usize {
    machine
        .block_order
        .iter()
        .flat_map(|b| &machine.blocks[b].insts)
        .position(|inst| {
            inst.lowering_provenance
                .source_id()
                .is_some_and(|id| id.block == block.0 && id.index as usize == index)
        })
        .unwrap_or_else(|| panic!("no row stamped ({block:?}, {index})\n{}", describe(machine)))
}

/// Restamp every row of `machine` stamped in `block` at an index of at least
/// `from` by `shift` (an instruction inserted or removed before it).
fn shift_stamps(machine: &mut X86ISelFunction, block: Block, from: usize, shift: isize) {
    for body in machine.blocks.values_mut() {
        for inst in &mut body.insts {
            if let LoweringProvenance::SourceInst { id, .. } = &mut inst.lowering_provenance
                && id.block == block.0
                && id.index as usize >= from
            {
                id.index = (id.index as isize + shift) as u32;
            }
        }
    }
}

/// The selector's unsigned 64-bit `udiv` rows (`select_div`): `rax =
/// dividend; rdx = 0; div divisor`, each with `provenance`.
fn udiv_rows(dividend: O, divisor: O, provenance: LoweringProvenance) -> Vec<X86ISelInst> {
    let rax = O::PReg(trust_cg_ir::x86_64_regs::RAX);
    let rdx = O::PReg(trust_cg_ir::x86_64_regs::RDX);
    let mut rows = vec![
        X86ISelInst::new(X86Opcode::MovRR, vec![rax, dividend]),
        X86ISelInst::new(X86Opcode::XorRR, vec![rdx.clone(), rdx.clone(), rdx]),
        X86ISelInst::new(X86Opcode::Div, vec![divisor]),
    ];
    for row in &mut rows {
        row.lowering_provenance = provenance;
    }
    rows
}

/// A copy of the machine block that lowers `lir` (the first laid out), every
/// row stamped `(stamp, 0)`, laid out last: the copy's id.
fn restamped_copy(machine: &mut X86ISelFunction, lir: Block, stamp: Block) -> Block {
    let original = *machine
        .block_order
        .iter()
        .find(|block| {
            machine.blocks[*block].insts.iter().any(|inst| {
                inst.lowering_provenance
                    .source_id()
                    .is_some_and(|id| id.block == lir.0)
            })
        })
        .unwrap_or_else(|| panic!("no machine block lowers {lir:?}\n{}", describe(machine)));
    let mut copy = machine.blocks[&original].clone();
    for inst in &mut copy.insts {
        if let LoweringProvenance::SourceInst { id, .. } = &mut inst.lowering_provenance {
            id.block = stamp.0;
            id.index = 0;
        }
    }
    let fresh = Block(
        machine
            .blocks
            .keys()
            .map(|block| block.0)
            .max()
            .unwrap_or(0)
            + 1,
    );
    machine.blocks.insert(fresh, copy);
    machine.block_order.push(fresh);
    fresh
}

/// The pairs the wrong lowerings and refusal controls name, by label (design
/// §5.3; each a labelled hand edit of a real stream).
#[track_caller]
pub(crate) fn case24c(label: &str) -> (Function, X86ISelFunction) {
    match label {
        // The `cmov`'s condition inverted.
        "W1" => {
            let (source, mut machine) = pair24c(Shape24c::AlignOffset);
            let row = cmov_rows(&machine)[0];
            for operand in &mut inst_mut(&mut machine, row).operands {
                if let O::CondCode(cc) = operand {
                    *cc = cc.invert();
                }
            }
            (source, machine)
        }
        // The `cmov` deleted.
        "W2" => {
            let (source, mut machine) = pair24c(Shape24c::AlignOffset);
            let row = cmov_rows(&machine)[0];
            remove_at(&mut machine, row);
            (source, machine)
        }
        // `w`'s `Jump` retargeted from the head to the then arm (the LIR
        // only): a live block enters a member; `w`'s machine block jumps
        // into the segment's.
        "W3" => variant24c_pair(Variant24c::PrefixedDiamond),
        // The then arm's call, which no machine row runs.
        "W4" => variant24c_pair(Variant24c::ArmCall),
        // Design W4, the speculated call: the then arm's call moved into the
        // segment's machine block, which runs it on every path. The machine
        // is TwoCalls' base stream (its head calls `sink(a)` before the
        // diamond), its call rows restamped to the then arm's call and every
        // later stamp moved to the edited source's indices.
        "W4s" => {
            let source = variant24c_lir(Variant24c::ArmCall, true);
            let two = variant24c_lir(Variant24c::TwoCalls, false);
            let mut machine = if_converted("TwoCalls", &two, trust_cg_opt::OptLevel::O2);
            machine.name = source.name.clone();
            let call_at = |function: &Function, block: Block| -> usize {
                function.blocks[&block]
                    .instructions
                    .iter()
                    .position(|inst| matches!(inst.opcode, L::Call { .. }))
                    .unwrap_or_else(|| panic!("W4s: no call in {block:?}"))
            };
            let (head, t, _, _) = diamond_blocks(&source);
            let head_call = call_at(&two, two.entry_block);
            let arm_call = call_at(&source, t);
            assert_eq!(head, two.entry_block, "W4s: the head is the entry");
            // The arm's own stamps from the call on move up by one.
            shift_stamps(&mut machine, t, arm_call, 1);
            for body in machine.blocks.values_mut() {
                for inst in &mut body.insts {
                    if let LoweringProvenance::SourceInst { id, .. } = &mut inst.lowering_provenance
                        && id.block == head.0
                    {
                        let index = id.index as usize;
                        if index == head_call {
                            id.block = t.0;
                            id.index = arm_call as u32;
                        } else if index > head_call {
                            id.index -= 1;
                        }
                    }
                }
            }
            (source, machine)
        }
        // A call in the head and, edited in, one in the then arm.
        "N11" => variant24c_pair(Variant24c::TwoCalls),
        // N6: P1 with a dead copy of its if-converted block laid out after
        // it, so two machine blocks name the segment's members (synthetic).
        "N6" => {
            let (source, mut machine) = pair24c(Shape24c::AlignOffset);
            let first = machine.block_order[0];
            let copy = machine.blocks[&first].clone();
            let fresh = Block(
                machine
                    .blocks
                    .keys()
                    .map(|block| block.0)
                    .max()
                    .unwrap_or(0)
                    + 1,
            );
            machine.blocks.insert(fresh, copy);
            machine.block_order.push(fresh);
            (source, machine)
        }
        // The then arm's incoming store, which no machine row runs.
        "W5" => variant24c_pair(Variant24c::ArmStore),
        // A machine-only incoming load: W5's base (no store) whose segment
        // machine block loads `[p]`, unstamped.
        "W5l" => {
            let source = variant24c_lir(Variant24c::ArmStore, false);
            let mut machine = if_converted("ArmStore", &source, trust_cg_opt::OptLevel::O2);
            let rdi = O::PReg(trust_cg_ir::x86_64_regs::RDI);
            let arrives = machine
                .block_order
                .iter()
                .flat_map(|block| &machine.blocks[block].insts)
                .position(|inst| {
                    inst.opcode == X86Opcode::MovRR && inst.operands.get(1) == Some(&rdi)
                })
                .unwrap_or_else(|| panic!("W5l: no copy of rdi\n{}", describe(&machine)));
            let pointer = inst(&machine, arrives).operands[0].clone();
            insert_at(
                &mut machine,
                arrives + 1,
                X86ISelInst::new(
                    X86Opcode::MovRM,
                    vec![
                        vreg24c(9_911),
                        O::MemAddr {
                            base: Box::new(pointer),
                            disp: 0,
                        },
                    ],
                ),
            );
            (source, machine)
        }
        // "Both lower": P1 with a copy of the join's machine block, every row
        // stamped with the then arm, laid out last.
        "BL" => {
            let (source, mut machine) = pair24c(Shape24c::AlignOffset);
            let (_, t, _, j) = diamond_blocks(&source);
            restamped_copy(&mut machine, j, t);
            (source, machine)
        }
        // N3 and N8 (real O2 output, no edit).
        "N3" => variant24c_pair(Variant24c::LicmHeader),
        "N8" => variant24c_pair(Variant24c::ChainIntoLoop),
        // P8s and P12 (real O2 output, no edit).
        "P8s" => variant24c_pair(Variant24c::ShortTail),
        "P12" => variant24c_pair(Variant24c::ForkedTail),
        // The then arm's private store, which no machine row runs; the slot
        // is read at the join.
        "W6" => variant24c_pair(Variant24c::ArmPrivateStore),
        // The two-way `Switch`'s constants swapped.
        "W7" => {
            let (source, mut machine) = pair24c(Shape24c::ForceSign);
            let rows: Vec<usize> = super::slice25::rows_with(&machine, &[X86Opcode::MovRI])
                .into_iter()
                .filter(|row| {
                    matches!(
                        inst(&machine, *row).operands.as_slice(),
                        [_, O::Imm(10 | 20)]
                    )
                })
                .collect();
            assert_eq!(
                rows.len(),
                2,
                "W7: two constant rows\n{}",
                describe(&machine)
            );
            for row in rows {
                if let [_, O::Imm(value)] = inst_mut(&mut machine, row).operands.as_mut_slice() {
                    *value = 30 - *value;
                }
            }
            (source, machine)
        }
        // The then arm returns; the machine never returns there.
        "W8" => variant24c_pair(Variant24c::ArmReturns),
        // The then arm divides; the machine does not.
        "W9" => variant24c_pair(Variant24c::ArmDivides),
        // Design W9, the speculated division: the then arm's `udiv` rows (the
        // selector's) moved into the segment's machine block after the arm's
        // `add`, and the arm's copy reading their quotient. A CORRECT
        // speculation (the divisor `c` is zero only where `c < 8`, on the arm
        // that divides), refused all the same (N10: the effects rule).
        "W9s" => {
            let (source, mut machine) = variant24c_pair(Variant24c::ArmDivides);
            let (_, t, _, _) = diamond_blocks(&source);
            let add = stamped_row(&machine, t, 1);
            let compare = super::slice25::rows_with(&machine, &[X86Opcode::CmpRI])[0];
            let dividend = inst(&machine, add).operands[0].clone();
            let divisor = inst(&machine, compare).operands[0].clone();
            let copy = stamped_row(&machine, t, 2);
            let mut provenance = inst(&machine, add).lowering_provenance;
            if let LoweringProvenance::SourceInst { id, .. } = &mut provenance {
                id.index = 2;
            }
            let quotient = vreg24c(9_903);
            let mut rows = udiv_rows(dividend, divisor, provenance);
            let mut read = X86ISelInst::new(
                X86Opcode::MovRR,
                vec![quotient.clone(), O::PReg(trust_cg_ir::x86_64_regs::RAX)],
            );
            read.lowering_provenance = provenance;
            rows.push(read);
            // The copy, now the edited source's instruction 3, reads the
            // quotient.
            let copied = inst_mut(&mut machine, copy);
            copied.operands[1] = quotient;
            if let LoweringProvenance::SourceInst { id, .. } = &mut copied.lowering_provenance {
                id.index = 3;
            }
            for (offset, row) in rows.into_iter().enumerate() {
                insert_at(&mut machine, add + 1 + offset, row);
            }
            (source, machine)
        }
        // The machine-only speculated `#DE`: P1's machine block divides,
        // unstamped, by `k = (c < 8) ? 1 : 0`, which is zero exactly on the
        // else arm's path; the source never stops. Refuted by the effect
        // member's (the head's) stop claims.
        "W9m" => {
            let (source, mut machine) = pair24c(Shape24c::AlignOffset);
            let compare = super::slice25::rows_with(&machine, &[X86Opcode::CmpRI])[0];
            let c = inst(&machine, compare).operands[0].clone();
            let (k, one) = (vreg24c(9_901), vreg24c(9_902));
            let mut rows = vec![
                X86ISelInst::new(X86Opcode::MovRI, vec![k.clone(), O::Imm(0)]),
                X86ISelInst::new(X86Opcode::MovRI, vec![one.clone(), O::Imm(1)]),
                X86ISelInst::new(X86Opcode::CmpRI, vec![c, O::Imm(8)]),
                X86ISelInst::new(
                    X86Opcode::Cmovcc,
                    vec![k.clone(), one.clone(), O::CondCode(X86CondCode::B)],
                ),
            ];
            rows.extend(udiv_rows(one, k, LoweringProvenance::UNATTRIBUTED));
            // Before the head's compare, which then sets the flags its
            // `cmov` reads as before.
            for (offset, row) in rows.into_iter().enumerate() {
                insert_at(&mut machine, compare + offset, row);
            }
            (source, machine)
        }
        // The O2 rotation of a counting loop.
        "W10" => variant24c_pair(Variant24c::RotatedLoop),
        // Slice 24a's folded branch (D2 folded).
        "W14" => super::slice24::folded_brif(),
        // P8 cut at the join (`(J, 0)`) by a test policy.
        "W15" | "P8" => variant24c_pair(Variant24c::LongDiamond),
        // The else arm traps; the machine computes 9 there.
        "W17" => variant24c_pair(Variant24c::ArmTraps),
        // Silent heads: the if-converted block names no head.
        "SH2" => variant24c_pair(Variant24c::ZeroTestAbs),
        "SH3" => variant24c_pair(Variant24c::ZeroTestSelect),
        // The else arm also exits to a returning block `r`; a synthetic
        // machine block (a copy of the join's, every row stamped with `r`)
        // lowers it, and the segment's machine block never reaches it.
        "N7" => {
            let (source, mut machine) = variant24c_pair(Variant24c::ElseExits);
            let (_, _, e, j) = diamond_blocks(&source);
            let r = match source.blocks[&e]
                .instructions
                .last()
                .map(|inst| &inst.opcode)
            {
                Some(L::Brif { then_dest, .. }) => *then_dest,
                other => panic!("N7: the else arm ends in {other:?}"),
            };
            restamped_copy(&mut machine, j, r);
            (source, machine)
        }
        other => panic!("no slice-24c case {other}"),
    }
}

/// The wrong lowerings the solver must refute (design §5.3, and the
/// machine-only speculated `#DE`, W9m).
pub(crate) const REFUTED24C: &[&str] = &["W1", "W2", "W6", "W7", "W9m", "W14"];

/// Every case label [`case24c`] builds but the parts route's and the
/// positive P8s and P12: the wrong lowerings and the refusal controls.
pub(crate) const CASES24C: &[&str] = &[
    "W1", "W2", "W3", "W4", "W4s", "W5", "W5l", "W6", "W7", "W8", "W9", "W9s", "W9m", "W10", "W14",
    "W17", "SH2", "SH3", "BL", "N3", "N8",
];

/// Every O0 fixture of slices 1 to 25 with a shape list and every slice-24c
/// source: label, LIR, the selector's stream (one machine block per LIR
/// block; slice 25's through the O0 pipeline, which is the selector's).
pub(crate) fn o0_fixtures24c() -> Vec<(String, Function, X86ISelFunction)> {
    let mut fixtures = super::slice16::earlier_fixtures();
    fixtures.extend(super::slice24::later_fixtures());
    for shape in super::slice24::SLICE_TWENTY_FOUR {
        let source = super::slice24::slice24_lir(shape);
        let machine = select(&source, X86CallAbi::SystemV);
        fixtures.push((format!("s24 {shape:?}"), source, machine));
    }
    for shape in super::slice25::SLICE_TWENTY_FIVE {
        let source = super::slice25::slice25_lir(shape);
        let machine = super::slice25::optimized(&source, trust_cg_opt::OptLevel::O0);
        fixtures.push((format!("s25 {shape:?}"), source, machine));
    }
    for shape in SLICE_TWENTY_FOUR_C {
        if shape == Shape24c::AbsorbedParams {
            continue;
        }
        let source = shape24c_lir(shape);
        let machine = select(&source, X86CallAbi::SystemV);
        fixtures.push((format!("s24c {shape:?}"), source, machine));
    }
    fixtures
}

/// The outcome of every [`o0_fixtures24c`] pair, one line each:
/// `label<TAB>stated<TAB>sha256` of its replayed units' text, or
/// `label<TAB>refused<TAB>sha256` of its whole refusal text. The
/// fails-before run on `a617488aa` records these lines
/// (`slice24c_o0_owners.txt`); `o0_is_untouched_by_segments` compares.
pub(crate) fn o0_outcomes24c() -> Vec<String> {
    use sha2::{Digest, Sha256};
    o0_fixtures24c()
        .iter()
        .map(|(label, source, machine)| {
            let (kind, bytes) = match owner24c(source, machine) {
                Ok(owner) => (
                    "stated",
                    owner
                        .replayed_units()
                        .into_iter()
                        .map(text)
                        .collect::<Vec<_>>()
                        .join("\n"),
                ),
                Err(refusal) => ("refused", format!("{refusal}")),
            };
            format!("{label}\t{kind}\t{:x}", Sha256::digest(bytes.as_bytes()))
        })
        .collect()
}

/// `machine` block by block: each laid-out block, its successors, and each
/// row with its TV-1 stamp (`@(block, index)`, `@-` for none).
pub(crate) fn describe24c(machine: &X86ISelFunction) -> String {
    let mut text = String::new();
    let mut ordinal = 0;
    for block in &machine.block_order {
        let body = &machine.blocks[block];
        text.push_str(&format!("  M{} succ={:?}\n", block.0, body.successors));
        for inst in &body.insts {
            let stamp = inst.lowering_provenance.source_id().map_or_else(
                || "-".to_owned(),
                |id| format!("({}, {})", id.block, id.index),
            );
            text.push_str(&format!(
                "    [{ordinal}] {:?} {:?} @{stamp}\n",
                inst.opcode, inst.operands
            ));
            ordinal += 1;
        }
    }
    text
}

/// A diagnostic, not a check: every slice-24c fixture's and case's LIR,
/// machine rows and owner outcome.
#[test]
#[ignore]
fn print_slice_twenty_four_c_fixtures() {
    for shape in SLICE_TWENTY_FOUR_C {
        let (source, machine) = pair24c(shape);
        println!(
            "==== {shape:?}\n{}{}{}",
            describe_lir(&source),
            describe24c(&machine),
            outcome24c(&owner24c(&source, &machine))
        );
    }
    for label in CASES24C
        .iter()
        .chain(&["P8", "P8s", "P12", "N6", "N7", "N11"])
    {
        if ["P8", "P8s", "P12"].contains(label) {
            let (source, machine) = case24c(label);
            println!("==== {label}\n{}", outcome24c(&owner24c(&source, &machine)));
            continue;
        }
        let (source, machine) = case24c(label);
        println!(
            "==== {label}\n{}{}{}",
            describe_lir(&source),
            describe24c(&machine),
            outcome24c(&owner24c(&source, &machine))
        );
    }
    for (encoding, theorem) in encodings_of_p1() {
        println!(
            "==== P7 {encoding}: {}",
            theorem.map_or_else(|refusal| format!("{refusal}"), |_| "stated".into())
        );
    }
}

// ---------------------------------------------------------------------------
// Controls (slice 24c)
// ---------------------------------------------------------------------------

use super::super::quotient::mutant;
use super::super::segment::{self, Segment, SegmentKind};

/// The checked segments `choose` proposes for a pair (none: the error).
fn segments_of(source: &Function, machine: &X86ISelFunction) -> Result<segment::Segments, String> {
    let cfg = source_cfg(source).map_err(|refusal| format!("{refusal}"))?;
    let chosen = segment::choose(source, machine, &cfg);
    segment::check(source, machine, &cfg, &chosen.segments)
        .map_err(|(head, detail)| format!("{head:?}: {detail}"))
}

/// The reason of an `Unsupported` refusal without its segment and
/// merged-chain suffixes.
fn inner24c(reason: &X86BodyUnsupported) -> &X86BodyUnsupported {
    match reason {
        X86BodyUnsupported::OverQuotient { reason, .. }
        | X86BodyUnsupported::OverSegments { reason, .. } => inner24c(reason),
        other => other,
    }
}

// ---- the controls, each `Ok` on the correct code

/// A fixture is stated over segments (`kind` among them), and its theorem
/// holds on samples.
fn owner_control(shape: Shape24c) -> Result<(), String> {
    let (source, machine) = pair24c(shape);
    let owner = owner24c(&source, &machine).map_err(|refusal| format!("{refusal}"))?;
    if owner.segments().is_none() {
        return Err("stated over no segment".into());
    }
    owner_holds(&owner)
}

/// The segments of a fixture, checked, are those its shape names.
fn segment_control(shape: Shape24c) -> Result<(), String> {
    let (source, machine) = pair24c(shape);
    let segments = segments_of(&source, &machine)?;
    let kinds: Vec<SegmentKind> = segments.iter().map(|segment| segment.kind).collect();
    // P2's machine block names its head and its computing arm (a diamond);
    // P3's names its head alone (silent).
    let expected = match shape {
        Shape24c::SelectUnpredictable => SegmentKind::Silent,
        Shape24c::AbsorbedParams => SegmentKind::Chain,
        _ => SegmentKind::Diamond,
    };
    if kinds != [expected] {
        return Err(format!("{kinds:?}, not one {expected:?}"));
    }
    Ok(())
}

/// A refusal control: `Unsupported`, naming every text of `expected` and
/// none of `absent`.
fn refused_control(
    result: Result<SourceBoundX86Body<'_>, X86BodyRefusal>,
    expected: &[String],
    absent: &[String],
) -> Result<(), String> {
    match result {
        Err(X86BodyRefusal::Unsupported(reason)) => {
            let text = format!("{reason}");
            if let Some(missing) = expected
                .iter()
                .find(|needle| !text.contains(needle.as_str()))
            {
                Err(format!("expected {missing:?}, got {text}"))
            } else if let Some(present) =
                absent.iter().find(|needle| text.contains(needle.as_str()))
            {
                Err(format!("{present:?} must not appear: {text}"))
            } else {
                Ok(())
            }
        }
        Err(other) => Err(format!("not Unsupported: {other}")),
        Ok(owner) => Err(format!(
            "stated ({})",
            if owner_holds(&owner).is_ok() {
                "holds"
            } else {
                "refuted"
            }
        )),
    }
}

/// A named refusal of design §3: its label, the pair, how it is stated
/// (`Some(points)`: in parts at those points), the texts the refusal must
/// hold and the texts it must not.
pub(crate) struct NamedRefusal {
    pub(crate) label: &'static str,
    pub(crate) source: Function,
    pub(crate) machine: X86ISelFunction,
    pub(crate) route: Option<Vec<(Block, usize)>>,
    pub(crate) expected: Vec<String>,
    pub(crate) absent: Vec<String>,
}

/// The named refusals of design §3, by label.
pub(crate) fn named_refusals() -> Vec<NamedRefusal> {
    let mut controls = Vec::new();
    let mut push = |label: &'static str,
                    (source, machine): (Function, X86ISelFunction),
                    route: Option<Vec<(Block, usize)>>,
                    expected: Vec<String>,
                    absent: Vec<String>| {
        controls.push(NamedRefusal {
            label,
            source,
            machine,
            route,
            expected,
            absent,
        });
    };
    // N1: `w` enters the then arm from outside the segment.
    let (source, machine) = case24c("W3");
    let (head, t, _, _) = diamond_blocks(&source);
    push(
        "N1",
        (source, machine),
        None,
        vec![
            format!("; no segment: LIR block {t:?}, which machine block"),
            "is entered from [".into(),
            format!("is not in the segment of {head:?}"),
        ],
        Vec::new(),
    );
    // N3: X86LoopInvariantCodeMotion's rows of a loop header in the
    // preheader's machine block.
    let (source, machine) = case24c("N3");
    let header = source.blocks[&source.entry_block]
        .instructions
        .last()
        .and_then(|inst| match &inst.opcode {
            L::Jump { dest } => Some(*dest),
            _ => None,
        })
        .expect("N3: the entry jumps to the loop header");
    push(
        "N3",
        (source, machine),
        None,
        vec![
            "lowers rows of several LIR blocks".into(),
            format!("; no segment: LIR block {header:?} is a loop header"),
        ],
        Vec::new(),
    );
    // N5: the then arm returns.
    let (source, machine) = case24c("W8");
    let (head, t, _, _) = diamond_blocks(&source);
    push(
        "N5",
        (source, machine),
        None,
        vec![format!(
            "; no segment: LIR block {t:?} of the segment of {head:?} ends in a Return"
        )],
        Vec::new(),
    );
    // N5, a trapping member.
    let (source, machine) = case24c("W17");
    let (head, _, e, _) = diamond_blocks(&source);
    push(
        "N5 trap",
        (source, machine),
        None,
        vec![format!(
            "; no segment: LIR block {e:?} of the segment of {head:?} ends in a Trap"
        )],
        Vec::new(),
    );
    // N8: the merged entry and `p` exit into a loop header.
    let (source, machine) = case24c("N8");
    let header = source_cfg(&source).expect("N8's control flow").loops[0].header;
    let entry = source.entry_block;
    push(
        "N8",
        (source, machine),
        None,
        vec![format!(
            "; no segment: the segment of {entry:?} exits into loop header {header:?}"
        )],
        Vec::new(),
    );
    // N10: an effect in an arm (a call, an incoming store, a division), and
    // the arm's call and division speculated into the segment's machine
    // block.
    for (label, case) in [
        ("N10 call", "W4"),
        ("N10 store", "W5"),
        ("N10 division", "W9"),
        ("N10 speculated call", "W4s"),
        ("N10 speculated division", "W9s"),
    ] {
        let (source, machine) = case24c(case);
        let (head, t, _, _) = diamond_blocks(&source);
        push(
            label,
            (source, machine),
            None,
            vec![format!(
                "LIR block {t:?} in the segment of {head:?} has a call, incoming access, rounding \
                 operation, stop or indexed access, and a run through the segment need not pass it"
            )],
            Vec::new(),
        );
    }
    // N7: the segment exits to `r`, which its machine block never reaches;
    // the refusal is at the machine block OD-226's note is about, so the
    // note is appended.
    let (source, machine) = case24c("N7");
    let (head, _, _, _) = diamond_blocks(&source);
    push(
        "N7",
        (source, machine),
        None,
        vec![
            format!("(the segment of {head:?}: "),
            "; not contracted: ".into(),
        ],
        Vec::new(),
    );
    // N11: calls in the head and in the then arm.
    let (source, machine) = case24c("N11");
    let (head, t, _, _) = diamond_blocks(&source);
    push(
        "N11",
        (source, machine),
        None,
        vec![format!(
            "LIR blocks {head:?} and {t:?} in the segment of {head:?} both have calls"
        )],
        Vec::new(),
    );
    // Another machine block names a member ("both lower"): the refusal is at
    // the copy, not at the block OD-226's note is about, so no note.
    let (source, machine) = case24c("BL");
    let (_, t, _, _) = diamond_blocks(&source);
    let (first, copy) = (
        machine.block_order[0],
        *machine.block_order.last().expect("a laid-out block"),
    );
    push(
        "both lower",
        (source, machine),
        None,
        vec![format!(
            "machine blocks {first:?} and {copy:?} both lower LIR block {t:?}"
        )],
        vec!["; not contracted: ".into()],
    );
    // N13: a policy point at the join (it declares the merge's parameter),
    // one inside the then arm, and one inside P12's chain `A`, where the
    // join's parameter is live.
    let (source, machine) = case24c("P8");
    let (head, _, _, _) = diamond_blocks(&source);
    let [join, member] = p8_points(&source);
    push(
        "N13 join",
        (source.clone(), machine.clone()),
        Some(vec![join]),
        vec![format!(
            "a cut point at the start of LIR block {:?}, an exit target of the segment of \
             {head:?} whose parameters machine block",
            join.0
        )],
        Vec::new(),
    );
    push(
        "N13 member",
        (source, machine),
        Some(vec![member]),
        vec![format!(
            "a cut point in LIR block {:?}, which the segment of {head:?} states inside machine \
             block",
            member.0
        )],
        Vec::new(),
    );
    let (source, machine) = case24c("P12");
    let (head, _, _, _) = diamond_blocks(&source);
    let point = p12_point(&source);
    push(
        "N13 live",
        (source, machine),
        Some(vec![point]),
        vec![format!(
            "is live, which only members of the segment of {head:?} define (inside machine block"
        )],
        Vec::new(),
    );
    controls
}

/// Every named refusal of [`named_refusals`] holds its texts.
fn named_control(label: &str) -> Result<(), String> {
    let control = named_refusals()
        .into_iter()
        .find(|control| control.label == label)
        .unwrap_or_else(|| panic!("no named refusal {label}"));
    let result = match control.route {
        None => owner24c(&control.source, &control.machine),
        Some(points) => parts24c(&control.source, &control.machine, points),
    };
    refused_control(result, &control.expected, &control.absent)
}

/// A wrong lowering is never credited: no claim, a named mismatch, or a
/// theorem refuted on samples.
fn never_credited_control(label: &str) -> Result<(), String> {
    let (source, machine) = case24c(label);
    match owner24c(&source, &machine) {
        Ok(owner) if owner_refuted(&owner) => Ok(()),
        Ok(_) => Err("a wrong lowering's theorem is stated and holds".into()),
        Err(_) => Ok(()),
    }
}

/// A wrong lowering is never credited in the DAG encoding (where each
/// unit's claims are stated under its own guard): no claim, a named
/// mismatch, or a theorem refuted on samples.
fn never_credited_dag_control(label: &str) -> Result<(), String> {
    let (source, machine) = case24c(label);
    match theorem_with_path_encoding(&source, &machine, SYSV, DAG24C) {
        Ok(theorem) if super::slice9::dag_refuted_on_samples(&theorem) => Ok(()),
        Ok(_) => Err("a wrong lowering's DAG theorem is stated and holds".into()),
        Err(_) => Ok(()),
    }
}

/// A wrong lowering is stated over segments and refuted on samples.
fn refuted_control(label: &str) -> Result<(), String> {
    let (source, machine) = case24c(label);
    let owner = owner24c(&source, &machine).map_err(|refusal| format!("{refusal}"))?;
    if owner.segments().is_none() {
        return Err("stated over no segment".into());
    }
    if owner_refuted(&owner) {
        Ok(())
    } else {
        Err("the theorem is not refuted on samples".into())
    }
}

/// W17 in the DAG encoding: the else arm traps, the machine computes 9
/// there. The chooser declines a member that traps (N5); with `C5` off the
/// member guard refuses (`Construction`, C11).
fn trap_member_control() -> Result<(), String> {
    let (source, machine) = case24c("W17");
    match theorem_with_path_encoding(&source, &machine, SYSV, DAG24C) {
        Err(X86BodyRefusal::Unsupported(reason)) => {
            let text = format!("{reason}");
            let (head, _, e, _) = diamond_blocks(&source);
            let chooser = format!("LIR block {e:?} of the segment of {head:?} ends in a Trap");
            let guard = format!("segment member {e:?} carries a return or a trap");
            if text.contains(&chooser) || text.contains(&guard) {
                Ok(())
            } else {
                Err(format!("neither N5 nor C11: {text}"))
            }
        }
        Err(other) => Err(format!("not Unsupported: {other}")),
        Ok(theorem) => {
            if super::slice9::dag_refuted_on_samples(&theorem) {
                Err("stated (refuted on samples)".into())
            } else {
                Err("stated and holds: the trap arm is dropped".into())
            }
        }
    }
}

/// W17 in the DAG encoding is refused by the member guard (C11) when the
/// chooser's C5 is off.
fn member_guard_control() -> Result<(), String> {
    let (source, machine) = case24c("W17");
    let (_, _, e, _) = diamond_blocks(&source);
    match theorem_with_path_encoding(&source, &machine, SYSV, DAG24C) {
        Err(X86BodyRefusal::Unsupported(reason)) => match inner24c(&reason) {
            X86BodyUnsupported::Construction(detail)
                if detail.contains(&format!("segment member {e:?} carries")) =>
            {
                Ok(())
            }
            _ => Err(format!("not C11: {reason}")),
        },
        Err(other) => Err(format!("not Unsupported: {other}")),
        Ok(_) => Err("stated".into()),
    }
}

/// A forged chooser output (W16): what [`segment::check`] is given (with
/// the control flow of `source`), and the text of the one clause that must
/// refuse it.
pub(crate) struct ForgedCase {
    pub(crate) label: &'static str,
    source: Function,
    machine: X86ISelFunction,
    segments: Vec<Segment>,
    needle: String,
}

/// A segment of `source` over `machine` block `m` with `members` (the head
/// first), its exits and internal edges derived as the chooser derives them.
fn forge(source: &Function, m: Block, members: Vec<Block>) -> Segment {
    let (exits, internal) = segment::edges_of(source, &members);
    Segment {
        head: members[0],
        machine: m,
        members,
        exits,
        internal,
        kind: SegmentKind::Diamond,
    }
}

/// The LIR blocks a machine block's rows name.
fn names24c(machine: &X86ISelFunction, block: Block) -> std::collections::BTreeSet<Block> {
    machine.blocks[&block]
        .insts
        .iter()
        .filter_map(|inst| inst.lowering_provenance.source_id())
        .map(|id| Block(id.block))
        .collect()
}

/// The first laid-out machine block whose rows name exactly `lir`
/// (`alone`), or name it among others.
fn naming24c(machine: &X86ISelFunction, lir: Block, alone: bool) -> Block {
    *machine
        .block_order
        .iter()
        .find(|block| {
            let named = names24c(machine, **block);
            if alone {
                named == std::collections::BTreeSet::from([lir])
            } else {
                named.contains(&lir)
            }
        })
        .unwrap_or_else(|| panic!("no machine block names {lir:?}\n{}", describe24c(machine)))
}

/// One forged output per clause of [`segment::check`] that a forged output
/// can reach first, each built so that only that clause refuses it (so the
/// clause's own mutant, `s24c-check-…`, either accepts it or names another
/// clause). The clauses an earlier one implies (the entry as a member, a
/// member not reached from the head, a member branching to the head, a
/// member with no live predecessor) are refused by the clause that implies
/// them, which the case names.
pub(crate) fn forged_cases() -> Vec<ForgedCase> {
    let mut cases = Vec::new();
    let p1 = pair24c(Shape24c::AlignOffset);
    let cfg = source_cfg(&p1.0).expect("P1's control flow");
    let chosen = segment::choose(&p1.0, &p1.1, &cfg).segments;
    let real = chosen[0].clone();
    let (_, _, _, join) = diamond_blocks(&p1.0);
    let join_block = naming24c(&p1.1, join, true);
    let mut case = |label: &'static str,
                    (source, machine): (&Function, &X86ISelFunction),
                    segments: Vec<Segment>,
                    needle: String| {
        cases.push(ForgedCase {
            label,
            source: source.clone(),
            machine: machine.clone(),
            segments,
            needle,
        });
    };
    let on_p1 = (&p1.0, &p1.1);
    // C1: a head with no body; a machine block that is not laid out.
    let mut dead_head = real.clone();
    dead_head.head = Block(9_999);
    case(
        "dead head",
        on_p1,
        vec![dead_head],
        "its head Block(9999) is not a live LIR block".into(),
    );
    let mut not_laid_out = real.clone();
    not_laid_out.machine = Block(9_999);
    case(
        "not laid out",
        on_p1,
        vec![not_laid_out],
        "machine block Block(9999) is not a laid-out block of its own".into(),
    );
    // C0: a head the machine block does not name (the join), the members
    // kept; a member list missing a named block; a named block with no body.
    let mut unnamed_head = real.clone();
    unnamed_head.head = join;
    case(
        "unnamed head",
        on_p1,
        vec![unnamed_head],
        "does not name its head".into(),
    );
    let mut fewer = real.clone();
    fewer.members.truncate(2);
    case(
        "named outside",
        on_p1,
        vec![fewer],
        "which is not a member".into(),
    );
    let mut bodiless_machine = p1.1.clone();
    if let LoweringProvenance::SourceInst { id, .. } = &mut bodiless_machine
        .blocks
        .get_mut(&real.machine)
        .expect("the segment's machine block")
        .insts
        .iter_mut()
        .find(|inst| {
            inst.lowering_provenance
                .source_id()
                .is_some_and(|id| id.block != real.head.0)
        })
        .expect("a row stamped with an arm")
        .lowering_provenance
    {
        id.block = 9_998;
    }
    let mut with_bodiless = real.clone();
    with_bodiless.members.push(Block(9_998));
    case(
        "bodiless",
        (&p1.0, &bodiless_machine),
        vec![with_bodiless],
        "LIR block Block(9998) has no body".into(),
    );
    // C0: two segments of one machine block; a second segment (the join's
    // machine block) holding a member of the first.
    case(
        "shared machine block",
        on_p1,
        vec![real.clone(), real.clone()],
        "lowers two segments".into(),
    );
    case(
        "overlap",
        on_p1,
        vec![
            real.clone(),
            forge(&p1.0, join_block, vec![join, real.members[1]]),
        ],
        format!(
            "LIR block {:?} is also in the segment of {:?}",
            real.members[1], real.head
        ),
    );
    // C0: a named arm as the head, the members kept: the real head, a member,
    // enters it.
    let mut arm_head = real.clone();
    arm_head.head = real.members[1];
    case(
        "arm head",
        on_p1,
        vec![arm_head],
        "its head is entered from member".into(),
    );
    // The members: not starting at the head; out of topological order.
    let mut unstarted = real.clone();
    unstarted.members.swap(0, 1);
    case(
        "members start",
        on_p1,
        vec![unstarted],
        "its members do not start at its head".into(),
    );
    let mut swapped = real.members.clone();
    swapped.swap(1, 2);
    case(
        "out of order",
        on_p1,
        vec![forge(&p1.0, real.machine, swapped)],
        format!(
            "its members {:?} and {:?} are not live and in topological order",
            real.members[2], real.members[1]
        ),
    );
    // C2, implied: the entry as a member after the head (the join's machine
    // block, the join first): the entry is first in the topological order.
    case(
        "entry as member",
        on_p1,
        vec![forge(&p1.0, join_block, vec![join, p1.0.entry_block])],
        format!(
            "its members {join:?} and {:?} are not live and in topological order",
            p1.0.entry_block
        ),
    );
    // C2: the chooser's segment of W3's base (`w` enters the head) checked
    // against W3's edited source (`w` enters the then arm).
    let base = variant24c_lir(Variant24c::PrefixedDiamond, false);
    let (edited, w3_machine) = case24c("W3");
    let base_cfg = source_cfg(&base).expect("W3's base control flow");
    let w3_chosen = segment::choose(&base, &w3_machine, &base_cfg).segments;
    let (_, w3_t, _, _) = diamond_blocks(&edited);
    case(
        "entered from outside",
        (&edited, &w3_machine),
        w3_chosen,
        format!("member {w3_t:?} is entered from"),
    );
    // C5: a member past the join, which returns.
    let mut past = real.members.clone();
    past.push(join);
    case(
        "past the join",
        on_p1,
        vec![forge(&p1.0, real.machine, past)],
        format!("member {join:?} ends in a Return"),
    );
    // C3: a loop inside the segment: P6's entry with its loop header, the
    // header's arms and the latch, under the entry's machine block.
    let p6 = pair24c(Shape24c::LoopDiamond);
    let p6_cfg = source_cfg(&p6.0).expect("P6's control flow");
    let lp = &p6_cfg.loops[0];
    let (header, latch) = (lp.header, lp.latches[0]);
    let looped: Vec<Block> = p6_cfg
        .order
        .iter()
        .copied()
        .filter(|block| *block == p6.0.entry_block || lp.blocks.contains(block))
        .collect();
    case(
        "loop inside",
        (&p6.0, &p6.1),
        vec![forge(
            &p6.0,
            naming24c(&p6.1, p6.0.entry_block, false),
            looped,
        )],
        format!("the edge {latch:?} -> {header:?} runs backward"),
    );
    // The exits: not the members' edges out of the segment.
    let mut reversed = real.clone();
    reversed.exits.reverse();
    case(
        "exits differ",
        on_p1,
        vec![reversed],
        "its exits are not its members' edges out of it".into(),
    );
    // C6: N8's merged entry and `p`, which exit into a loop header.
    let n8 = case24c("N8");
    let n8_cfg = source_cfg(&n8.0).expect("N8's control flow");
    let n8_entry = n8.0.entry_block;
    let n8_members = vec![n8_entry, n8_cfg.successors[&n8_entry][0]];
    let n8_header = n8_cfg.loops[0].header;
    let n8_machine = naming24c(&n8.1, n8_entry, false);
    case(
        "exit into a loop header",
        (&n8.0, &n8.1),
        vec![forge(&n8.0, n8_machine, n8_members)],
        format!("it exits into loop header {n8_header:?}"),
    );
    // C7: P1's machine block with a row naming a jump table.
    let mut dispatching = p1.1.clone();
    dispatching
        .blocks
        .get_mut(&real.machine)
        .expect("the segment's machine block")
        .insts
        .insert(
            0,
            X86ISelInst::new(
                X86Opcode::LeaRip,
                vec![vreg24c(9_921), O::JumpTableIndex(0)],
            ),
        );
    case(
        "dispatch",
        (&p1.0, &dispatching),
        vec![real.clone()],
        format!(
            "machine block {:?} reaches a jump-table dispatch or binary-search block",
            real.machine
        ),
    );
    cases
}

/// A forged output is refused by [`segment::check`] with its clause's text.
fn check_forged(case: &ForgedCase) -> Result<(), String> {
    let cfg = source_cfg(&case.source).map_err(|refusal| format!("{refusal}"))?;
    match segment::check(&case.source, &case.machine, &cfg, &case.segments) {
        Err((_, detail)) if detail.contains(&case.needle) => Ok(()),
        Err((_, detail)) => Err(format!("expected {:?}, got {detail}", case.needle)),
        Ok(_) => Err("accepted".into()),
    }
}

/// The forged output `label` is refused by its clause's text.
fn forged_case_control(label: &str) -> Result<(), String> {
    let case = forged_cases()
        .into_iter()
        .find(|case| case.label == label)
        .unwrap_or_else(|| panic!("no forged case {label}"));
    check_forged(&case)
}

/// W16: every forged chooser output is refused by the check, each by its
/// clause's text.
fn forged_control() -> Result<(), String> {
    let failures: Vec<String> = forged_cases()
        .iter()
        .filter_map(|case| {
            check_forged(case)
                .err()
                .map(|why| format!("{}: {why}", case.label))
        })
        .collect();
    if failures.is_empty() {
        Ok(())
    } else {
        Err(failures.join("; "))
    }
}

/// C11 re-derives the effect member: with the walk kept by the segment's
/// last member (`s24c-walk-on-member`, active on this thread), P1's DAG
/// theorem is refused by the member guard (`Construction`, naming the
/// member and the effect member the rule picks).
fn misplaced_walk_control() -> Result<(), String> {
    let (source, machine) = pair24c(Shape24c::AlignOffset);
    let segments = segments_of(&source, &machine)?;
    let segment = segments.iter().next().ok_or("no segment")?;
    let last = *segment.members.last().expect("a member");
    let expected = format!(
        "segment member {last:?} carries a walk, and the effects rule picks member {:?}",
        segment.head
    );
    match theorem_with_path_encoding(&source, &machine, SYSV, DAG24C) {
        Err(X86BodyRefusal::Unsupported(reason)) => match inner24c(&reason) {
            X86BodyUnsupported::Construction(detail) if detail.contains(&expected) => Ok(()),
            _ => Err(format!("expected {expected:?}, got {reason}")),
        },
        Err(other) => Err(format!("not Unsupported: {other}")),
        Ok(_) => Err("stated".into()),
    }
}

/// P12: the production route states the forked tail in at least two parts
/// over P1's segment (the cut avoids every banned point: chain `A`, where
/// the join's parameter is live, and the diamond), every part holding.
fn forked_parts_control() -> Result<(), String> {
    let (source, machine) = case24c("P12");
    if split::fits_one_query(&source, &machine) {
        return Err("within the single-query bounds".into());
    }
    let owner = owner24c(&source, &machine).map_err(|refusal| format!("{refusal}"))?;
    if owner.segments().is_none() {
        return Err("stated over no segment".into());
    }
    if owner.parts().len() < 2 {
        return Err(format!("stated in {} part(s)", owner.parts().len()));
    }
    owner_holds(&owner)
}

/// P8: the production route states the long diamond (past the single-query
/// block bound) through the parts route, over its segment and OD-226's
/// quotient of its chain, in ONE part (over the quotient its one region
/// fits a part), holding on samples.
fn planned_parts_control() -> Result<(), String> {
    let (source, machine) = case24c("P8");
    if split::fits_one_query(&source, &machine) {
        return Err("within the single-query bounds".into());
    }
    let owner = owner24c(&source, &machine).map_err(|refusal| format!("{refusal}"))?;
    if !owner.is_stated_in_parts() {
        return Err("not stated in parts".into());
    }
    if owner.segments().is_none() {
        return Err("stated over no segment".into());
    }
    if owner.parts().len() != 1 {
        return Err(format!("stated in {} parts", owner.parts().len()));
    }
    owner_holds(&owner)
}

/// N6: the chooser declines the dead copy of P1's if-converted block, whose
/// named blocks the first block's segment claimed (`is in the segment of`),
/// and the pair makes no claim.
fn overlap_control() -> Result<(), String> {
    let (source, machine) = case24c("N6");
    let cfg = source_cfg(&source).map_err(|refusal| format!("{refusal}"))?;
    let chosen = segment::choose(&source, &machine, &cfg);
    let [segment] = chosen.segments.as_slice() else {
        return Err(format!("{} segments chosen", chosen.segments.len()));
    };
    let copy = *machine.block_order.last().expect("a laid-out block");
    let expected = format!(
        "is in the segment of {:?} (machine block {:?})",
        segment.head, segment.machine
    );
    match chosen.declined.get(&copy) {
        Some(note) if note.contains(&expected) => {}
        other => {
            return Err(format!(
                "{copy:?}: expected {expected:?}, declined {other:?}"
            ));
        }
    }
    // The refusal is at the copy, not at the machine block OD-226's note is
    // about: no stale note.
    match owner24c(&source, &machine) {
        Err(X86BodyRefusal::Unsupported(reason)) => {
            let text = format!("{reason}");
            if text.contains("; not contracted: ") {
                Err(format!("a stale OD-226 note: {text}"))
            } else {
                Ok(())
            }
        }
        Err(other) => Err(format!("not Unsupported: {other}")),
        Ok(_) => Err("stated".into()),
    }
}

/// N6 with the chooser's overlap decline off (`s24c-chooser-overlap` added
/// on this thread): the two overlapping segments reach the check, which
/// refuses them by name (`Construction`).
fn overlap_checked_control() -> Result<(), String> {
    let active = mutant::active();
    let names = if active.is_empty() {
        "s24c-chooser-overlap".to_owned()
    } else {
        format!("{active},s24c-chooser-overlap")
    };
    let _overlap = mutant::set(&names);
    let (source, machine) = case24c("N6");
    match owner24c(&source, &machine) {
        Err(X86BodyRefusal::Unsupported(reason)) => {
            let text = format!("{reason}");
            if text.contains("is not single-entry") && text.contains("is also in the segment of") {
                Ok(())
            } else {
                Err(format!("not the check's refusal: {text}"))
            }
        }
        Err(other) => Err(format!("not Unsupported: {other}")),
        Ok(_) => Err("stated".into()),
    }
}

/// W15 with the parts bans off (`s24c-parts-no-ban` added on this thread):
/// a cut at the join `(j, 0)`, a parameterized exit target, finds no machine
/// row writing the value live across it, since the cut pairing reads
/// `lowering` (never the segment's machine block), so the pair is refused
/// there, never stated (stated, it is refuted: the bans are the first
/// guard, the pairing the second).
fn unbanned_cut_control() -> Result<(), String> {
    let active = mutant::active();
    let names = if active.is_empty() {
        "s24c-parts-no-ban".to_owned()
    } else {
        format!("{active},s24c-parts-no-ban")
    };
    let _bans_off = mutant::set(&names);
    let (source, machine) = case24c("P8");
    let [join, _] = p8_points(&source);
    match parts24c(&source, &machine, vec![join]) {
        Err(X86BodyRefusal::Unsupported(reason)) => {
            let text = format!("{reason}");
            let expected = format!("live across cut point {:?}", join.0);
            if text.contains("no machine row writes a register as the definition of")
                && text.contains(&expected)
            {
                Ok(())
            } else {
                Err(format!("expected the cut pairing's refusal, got {text}"))
            }
        }
        Err(other) => Err(format!("not Unsupported: {other}")),
        Ok(owner) if owner_refuted(&owner) => Err("stated and refuted".into()),
        Ok(_) => Err("stated".into()),
    }
}

/// P7: P1's theorem under the path and the DAG encodings both holds on
/// samples.
fn encodings_control() -> Result<(), String> {
    for (encoding, theorem) in encodings_of_p1() {
        let theorem = theorem.map_err(|refusal| format!("{encoding}: {refusal}"))?;
        if !super::slice9::dag_holds_on_samples(&theorem) {
            return Err(format!("{encoding}: refuted on samples"));
        }
    }
    Ok(())
}

/// N12: an internal join with a private byte OD-192 leaves dead is refused
/// (P9's internal join, given a dead byte by hand in its DAG admission).
fn dead_join_control() -> Result<(), String> {
    let (source, machine) = pair24c(Shape24c::JoinContinues);
    let segments = segments_of(&source, &machine)?;
    let segment = segments
        .iter()
        .next()
        .ok_or_else(|| "no segment".to_owned())?;
    let mut body = admitted_body_as(&source, Some(true)).map_err(|refusal| format!("{refusal}"))?;
    let dag = body.dag.as_mut().ok_or_else(|| "no DAG".to_owned())?;
    let join = *segment
        .members
        .iter()
        .find(|member| {
            dag.predecessors
                .get(member)
                .is_some_and(|from| from.len() > 1)
        })
        .ok_or_else(|| "no internal join".to_owned())?;
    dag.join_dead
        .insert(join, std::collections::BTreeSet::from([(0, 0)]));
    match segment::internal_joins(segment, dag) {
        Err(refusal) => {
            let text = format!("{refusal}");
            let expected = format!(
                "the segment of {:?} has an internal join {join:?} whose private bytes OD-192 \
                 leaves dead",
                segment.head
            );
            if text.contains(&expected) {
                Ok(())
            } else {
                Err(format!("expected {expected:?}, got {text}"))
            }
        }
        Ok(()) => Err("accepted".into()),
    }
}

/// A control of the mutant campaign.
#[derive(Debug, Clone, Copy)]
enum Control24c {
    Owner(Shape24c),
    Segment(Shape24c),
    Named(&'static str),
    NeverCredited(&'static str),
    NeverCreditedDag(&'static str),
    Refuted(&'static str),
    TrapMember,
    Forged,
    ForgedCase(&'static str),
    PlannedParts,
    ForkedParts,
    UnbannedCut,
    Overlap,
    OverlapChecked,
    Encodings,
    DeadJoin,
    Snapshot,
}

fn run_control24c(control: Control24c) -> Result<(), String> {
    match control {
        Control24c::Owner(shape) => owner_control(shape),
        Control24c::Segment(shape) => segment_control(shape),
        Control24c::Named(label) => named_control(label),
        Control24c::NeverCredited(label) => never_credited_control(label),
        Control24c::NeverCreditedDag(label) => never_credited_dag_control(label),
        Control24c::Refuted(label) => refuted_control(label),
        Control24c::TrapMember => trap_member_control(),
        Control24c::Forged => forged_control(),
        Control24c::ForgedCase(label) => forged_case_control(label),
        Control24c::PlannedParts => planned_parts_control(),
        Control24c::ForkedParts => forked_parts_control(),
        Control24c::UnbannedCut => unbanned_cut_control(),
        Control24c::Overlap => overlap_control(),
        Control24c::OverlapChecked => overlap_checked_control(),
        Control24c::Encodings => encodings_control(),
        Control24c::DeadJoin => dead_join_control(),
        Control24c::Snapshot => snapshot_control(),
    }
}

/// `control` under the mutants `names` on this thread; a panic is a failed
/// control naming the panic's message.
fn under24c(names: &str, control: Control24c) -> Result<(), String> {
    let _mutant = mutant::set(names);
    std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| run_control24c(control)))
        .unwrap_or_else(|payload| {
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
        })
}

/// Controls every mutant campaign runs on the correct code besides those the
/// mutants name (each must hold there).
const CLEAN24C: &[Control24c] = &[
    Control24c::Segment(Shape24c::AlignOffset),
    Control24c::Segment(Shape24c::SelectUnpredictable),
    Control24c::Segment(Shape24c::AbsorbedParams),
    Control24c::Refuted("W1"),
    Control24c::Refuted("W14"),
    Control24c::NeverCredited("W3"),
    Control24c::NeverCredited("W10"),
    Control24c::Forged,
    Control24c::PlannedParts,
    Control24c::ForkedParts,
    Control24c::Encodings,
    Control24c::DeadJoin,
    Control24c::Snapshot,
];

/// Design §5.6: each mutant of a slice-24c rule and the controls it must
/// break.
const MUTANTS24C: &[(&str, &[Control24c])] = &[
    ("s24c-entering-any", &[Control24c::Named("N1")]),
    ("s24c-effects-off", &[Control24c::Named("N10 store")]),
    ("s24c-effect-off-spine", &[Control24c::Named("N10 call")]),
    ("s24c-two-effect-members", &[Control24c::Named("N11")]),
    (
        "s24c-member-any-terminator",
        &[Control24c::Named("N5 trap")],
    ),
    (
        "s24c-member-any-terminator,s24c-theorem-guard-off",
        &[Control24c::TrapMember],
    ),
    (
        "s24c-member-rewalk",
        &[
            Control24c::Owner(Shape24c::AlignOffset),
            Control24c::Owner(Shape24c::WrappingAbs),
            Control24c::Owner(Shape24c::SelectUnpredictable),
            Control24c::Owner(Shape24c::ForceSign),
        ],
    ),
    // ForceSign's `cmov` reads the flags of the head's `test`, ahead of
    // both arms' rows (X86IfConvert re-emits a compare before the `cmov`
    // in P1, P2, P5 and P9, so the flags those read never cross a member).
    (
        "s24c-flags-reset-at-members",
        &[Control24c::Owner(Shape24c::ForceSign)],
    ),
    ("s24c-parts-no-ban", &[Control24c::Named("N13 join")]),
    // With the bans off (inside the control), a cut at the join pairs the
    // segment's machine block's row: W15 is stated and refuted.
    ("s24c-cut-pairing-machine-of", &[Control24c::UnbannedCut]),
    // A machine block that reaches only some exit targets passes the
    // correspondence; the walk's missing route then refuses it (no claim),
    // under another name than N7's.
    ("s24c-equality-to-subset", &[Control24c::Named("N7")]),
    (
        "s24c-chooser-wrong-head",
        &[Control24c::Owner(Shape24c::SelectUnpredictable)],
    ),
    ("s24c-chooser-overlap", &[Control24c::Overlap]),
    // With the overlap decline off (inside the control), the check is the
    // guard that refuses the overlapping segments.
    ("s24c-check-off", &[Control24c::OverlapChecked]),
    // Each clause of the check, off: the forged output only it refuses
    // first is accepted or refused by a later clause, under another text.
    ("s24c-check-c1", &[Control24c::ForgedCase("dead head")]),
    (
        "s24c-check-named",
        &[Control24c::ForgedCase("named outside")],
    ),
    (
        "s24c-check-shared",
        &[Control24c::ForgedCase("shared machine block")],
    ),
    ("s24c-check-overlap", &[Control24c::ForgedCase("overlap")]),
    (
        "s24c-check-head-entry",
        &[Control24c::ForgedCase("arm head")],
    ),
    (
        "s24c-check-order",
        &[
            Control24c::ForgedCase("out of order"),
            Control24c::ForgedCase("entry as member"),
        ],
    ),
    (
        "s24c-check-entering-any",
        &[Control24c::ForgedCase("entered from outside")],
    ),
    (
        "s24c-check-terminator",
        &[Control24c::ForgedCase("past the join")],
    ),
    (
        "s24c-check-backward",
        &[Control24c::ForgedCase("loop inside")],
    ),
    (
        "s24c-check-exits",
        &[Control24c::ForgedCase("exits differ")],
    ),
    (
        "s24c-check-loop-exit",
        &[Control24c::ForgedCase("exit into a loop header")],
    ),
    ("s24c-check-dispatch", &[Control24c::ForgedCase("dispatch")]),
    // The walk kept by another member than `E`: the member guard, which
    // re-derives `E`, refuses P1's DAG theorem.
    ("s24c-walk-on-member", &[Control24c::Encodings]),
    // The bans' liveness clause off: P12's plan cuts in chain `A`, where the
    // join's parameter is live, and the cut pairing refuses it.
    ("s24c-parts-defined-no-ban", &[Control24c::ForkedParts]),
    // The effects rule is the guard of a speculated call or store: with it
    // off (and the member guard, which re-runs it, off), the DAG theorem of
    // the wrong lowering is stated and holds.
    (
        "s24c-effect-off-spine,s24c-theorem-guard-off",
        &[Control24c::NeverCreditedDag("W4s")],
    ),
    (
        "s24c-effects-off,s24c-theorem-guard-off",
        &[Control24c::NeverCreditedDag("W5")],
    ),
    (
        "s24c-two-effect-members,s24c-theorem-guard-off",
        &[Control24c::NeverCreditedDag("N11")],
    ),
];

// ---- the solver-free gate

/// Every slice-24c shape is stated over its segments, which are its
/// shape's, and its theorem holds on samples.
#[test]
fn owner_states_every_segment_shape() {
    let failures: Vec<String> = SLICE_TWENTY_FOUR_C
        .iter()
        .flat_map(|shape| {
            [owner_control(*shape), segment_control(*shape)]
                .into_iter()
                .filter_map(move |result| result.err().map(|why| format!("{shape:?}: {why}")))
        })
        .collect();
    assert!(failures.is_empty(), "{}", failures.join("\n"));
}

/// Stating a fixture twice gives the same bytes.
#[test]
fn segment_theorems_are_deterministic() {
    for shape in SLICE_TWENTY_FOUR_C {
        let (source, machine) = pair24c(shape);
        let once = owner24c(&source, &machine).map(|owner| text(owner.obligation()));
        let again = owner24c(&source, &machine).map(|owner| text(owner.obligation()));
        assert_eq!(
            once.map_err(|refusal| format!("{refusal}")),
            again.map_err(|refusal| format!("{refusal}")),
            "{shape:?}"
        );
    }
}

/// P7: the path and DAG encodings of P1 both hold.
#[test]
fn both_encodings_state_a_segment() {
    encodings_control().unwrap();
}

/// Every refusal of design §3 this slice builds is named (N12 at its rule,
/// over a forged dead byte), and the check refuses forged chooser outputs
/// (W16) by name.
#[test]
fn every_named_segment_refusal_is_named() {
    let labels: Vec<&str> = named_refusals()
        .iter()
        .map(|control| control.label)
        .collect();
    let failures: Vec<String> = labels
        .into_iter()
        .filter_map(|label| {
            named_control(label)
                .err()
                .map(|why| format!("{label}: {why}"))
        })
        .collect();
    assert!(failures.is_empty(), "{}", failures.join("\n"));
    dead_join_control().unwrap();
    forged_control().unwrap();
    trap_member_control().unwrap();
}

/// C11: with the chooser's C5 off (`s24c-member-any-terminator`), the
/// trapping member of W17 reaches the DAG theorem, and the member guard
/// refuses it (`Construction`).
#[test]
fn the_member_guard_refuses_a_trapping_member() {
    let _mutant = mutant::set("s24c-member-any-terminator");
    member_guard_control().unwrap();
}

/// The wrong lowerings of design §5.3 are never credited, and those the
/// solver must refute are stated over segments and refuted on samples.
#[test]
fn wrong_segment_lowerings_are_never_credited() {
    let failures: Vec<String> = CASES24C
        .iter()
        .filter_map(|label| {
            never_credited_control(label)
                .err()
                .map(|why| format!("{label}: {why}"))
        })
        .chain(REFUTED24C.iter().filter_map(|label| {
            refuted_control(label)
                .err()
                .map(|why| format!("{label}: {why}"))
        }))
        .collect();
    assert!(failures.is_empty(), "{}", failures.join("\n"));
}

/// P8: the production route states the long diamond through the parts
/// route over its segment (one part); P12: the forked tail in at least two
/// parts.
#[test]
fn the_parts_route_states_a_segment() {
    planned_parts_control().unwrap();
    forked_parts_control().unwrap();
}

/// The composition the qualification lanes replay: each subject is stated
/// over segments and holds on samples; P7's path theorem is P1's own (so the
/// replay lane replays P1's DAG theorem alone).
#[test]
fn the_composition_is_stated_over_segments() {
    let mut failures = Vec::new();
    for (label, source, machine) in composition24c() {
        match owner24c(&source, &machine) {
            Ok(owner) if owner.segments().is_none() => {
                failures.push(format!("{label}: stated over no segment"));
            }
            Ok(owner) => {
                if let Err(why) = owner_holds(&owner) {
                    failures.push(format!("{label}: {why}"));
                }
                eprintln!(
                    "S24C_COMPOSITION {label} segments={:?} parts={} in_parts={}",
                    owner.segments(),
                    owner.parts().len(),
                    owner.is_stated_in_parts()
                );
            }
            Err(refusal) => failures.push(format!("{label}: {refusal}")),
        }
    }
    assert!(failures.is_empty(), "{}", failures.join("\n"));
    let (source, machine) = pair24c(Shape24c::AlignOffset);
    let p1 = owner24c(&source, &machine).expect("P1 is stated");
    let paths = theorem_with_path_encoding(&source, &machine, SYSV, PATHS24C).expect("P7 paths");
    assert_eq!(
        text(&paths),
        text(p1.obligation()),
        "P7: the path theorem is P1's own"
    );
}

/// C11 re-derives the effect member: a walk kept by another member
/// (`s24c-walk-on-member`) is refused by name; under the rule as slice 24c
/// first stated it (`s24c-guard-one-walker`: at most one walk, on any
/// member) the same misplaced walk is stated (the fails-before record).
#[test]
fn the_member_guard_re_derives_the_effect_member() {
    {
        let _mutant = mutant::set("s24c-walk-on-member");
        misplaced_walk_control().unwrap();
    }
    let _mutant = mutant::set("s24c-walk-on-member,s24c-guard-one-walker");
    let (source, machine) = pair24c(Shape24c::AlignOffset);
    assert!(
        theorem_with_path_encoding(&source, &machine, SYSV, DAG24C).is_ok(),
        "the first rule refuses the misplaced walk"
    );
}

/// Every forged chooser output is refused by its clause, by name (one
/// per clause a forged output reaches first).
#[test]
fn every_forged_segment_is_refused_by_its_clause() {
    let cases = forged_cases();
    eprintln!("S24C_FORGED {} cases", cases.len());
    forged_control().unwrap();
}

/// The stamps are the chooser's only input from the machine: every one-row
/// restamp of a wrong lowering (to unattributed, or to each LIR block at the
/// row's index, clamped to the block) is never stated and holding, and no
/// restamp of a correct fixture panics. Each outcome is tallied
/// (`S24C_PERTURB`).
#[test]
fn a_restamped_row_never_credits_a_wrong_lowering() {
    let wrong: Vec<&str> = REFUTED24C
        .iter()
        .copied()
        .chain(["W4s", "W5l", "W9s"])
        .collect();
    let mut credited = Vec::new();
    let mut tally: std::collections::BTreeMap<String, usize> = Default::default();
    let subjects: Vec<(String, bool, Function, X86ISelFunction)> = wrong
        .iter()
        .map(|label| {
            let (source, machine) = case24c(label);
            ((*label).to_owned(), true, source, machine)
        })
        .chain(SLICE_TWENTY_FOUR_C.iter().map(|shape| {
            let (source, machine) = pair24c(*shape);
            (format!("{shape:?}"), false, source, machine)
        }))
        .collect();
    for (label, is_wrong, source, machine) in &subjects {
        let mut blocks: Vec<Block> = source.blocks.keys().copied().collect();
        blocks.sort_unstable();
        for block in machine.block_order.clone() {
            for row in 0..machine.blocks[&block].insts.len() {
                let original = machine.blocks[&block].insts[row].lowering_provenance;
                let mut stamps = vec![LoweringProvenance::UNATTRIBUTED];
                let index = original.source_id().map_or(0, |id| id.index as usize);
                for lir in &blocks {
                    let last = source.blocks[lir].instructions.len().saturating_sub(1);
                    let mut stamp = match original {
                        LoweringProvenance::SourceInst { .. } => original,
                        _ => machine
                            .block_order
                            .iter()
                            .flat_map(|b| &machine.blocks[b].insts)
                            .map(|inst| inst.lowering_provenance)
                            .find(|p| matches!(p, LoweringProvenance::SourceInst { .. }))
                            .expect("a stamped row"),
                    };
                    if let LoweringProvenance::SourceInst { id, .. } = &mut stamp {
                        id.block = lir.0;
                        id.index = index.min(last) as u32;
                    }
                    stamps.push(stamp);
                }
                for stamp in stamps {
                    if stamp == original {
                        continue;
                    }
                    let mut perturbed = machine.clone();
                    perturbed
                        .blocks
                        .get_mut(&block)
                        .expect("the row's block")
                        .insts[row]
                        .lowering_provenance = stamp;
                    let outcome = match owner24c(source, &perturbed) {
                        Ok(owner) if owner_holds(&owner).is_ok() => "holds",
                        Ok(_) => "refuted",
                        Err(X86BodyRefusal::Unsupported(_)) => "unsupported",
                        Err(_) => "other refusal",
                    };
                    *tally
                        .entry(format!(
                            "{} {outcome}",
                            if *is_wrong { "wrong" } else { "correct" }
                        ))
                        .or_default() += 1;
                    if *is_wrong && outcome == "holds" {
                        credited.push(format!("{label}: {block:?} row {row} -> {stamp:?}"));
                    }
                }
            }
        }
    }
    eprintln!("S24C_PERTURB {tally:?}");
    assert!(credited.is_empty(), "{}", credited.join("\n"));
}

/// Design §5.6: on the correct code every control holds; each mutant of a
/// slice-24c rule breaks the controls it names.
#[test]
fn every_slice24c_mutant_fails_a_control() {
    let mut controls: Vec<Control24c> = MUTANTS24C
        .iter()
        .flat_map(|(_, controls)| controls.iter().copied())
        .collect();
    controls.extend(SLICE_TWENTY_FOUR_C.map(Control24c::Owner));
    controls.extend(CLEAN24C.iter().copied());
    // Every control that fails unmutated (each mutant is still run, so one
    // run reports every outcome; the test fails on either list).
    let unmutated: Vec<String> = controls
        .into_iter()
        .filter_map(|control| {
            under24c("", control)
                .err()
                .map(|why| format!("none: {control:?}: {why}"))
        })
        .collect();
    let mut survived = Vec::new();
    for (names, controls) in MUTANTS24C {
        for control in *controls {
            match under24c(names, *control) {
                Ok(()) => survived.push(format!("{names}: {control:?} still holds")),
                Err(why) => {
                    eprintln!("S24C_MUTANT mutant={names} control={control:?} failed: {why}")
                }
            }
        }
    }
    assert!(unmutated.is_empty(), "{}", unmutated.join("\n"));
    assert!(survived.is_empty(), "{}", survived.join("\n"));
}

// ---- the golden text

/// The golden text of every slice-24c fixture: its theorem.
pub(crate) fn slice_twenty_four_c_snapshots() -> String {
    let mut rendered = String::new();
    for shape in SLICE_TWENTY_FOUR_C {
        let (source, machine) = pair24c(shape);
        let owner =
            owner24c(&source, &machine).unwrap_or_else(|refusal| panic!("{shape:?}: {refusal}"));
        rendered.push_str(&format!(";;;; {shape:?}\n{}\n", text(owner.obligation())));
    }
    rendered
}

/// The reviewed digest of the slice-24c golden text.
const SLICE_TWENTY_FOUR_C_SNAPSHOT_SHA256: &str =
    "2fecb9486eb6c21e98098413cf02428b3430ebc1e8098e6d7b9dd1d56032470b";

fn snapshot_control() -> Result<(), String> {
    use sha2::{Digest, Sha256};
    let digest = format!(
        "{:x}",
        Sha256::digest(slice_twenty_four_c_snapshots().as_bytes())
    );
    if digest != SLICE_TWENTY_FOUR_C_SNAPSHOT_SHA256 {
        return Err(format!("the golden text moved: {digest}"));
    }
    Ok(())
}

/// The rendered theorems of every slice-24c fixture are the reviewed golden
/// text, pinned by digest.
#[test]
fn slice_twenty_four_c_smt2_is_canonical_per_shape() {
    use sha2::{Digest, Sha256};
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tests/fixtures/x86_source_bound_body/slice24c_snapshots.smt2");
    let rendered = slice_twenty_four_c_snapshots();
    let digest = format!("{:x}", Sha256::digest(rendered.as_bytes()));
    if std::env::var_os("TCG_X86_BODY_SNAPSHOT_WRITE").is_some() {
        std::fs::write(&path, &rendered).unwrap();
        panic!(
            "rewrote {}; review its diff, set SLICE_TWENTY_FOUR_C_SNAPSHOT_SHA256 to {digest} and \
             re-run without TCG_X86_BODY_SNAPSHOT_WRITE",
            path.display()
        );
    }
    let golden = std::fs::read_to_string(&path).unwrap_or_default();
    assert_eq!(rendered, golden, "slice24c_snapshots.smt2 drifted");
    assert_eq!(digest, SLICE_TWENTY_FOUR_C_SNAPSHOT_SHA256);
}

// ---- O0, O2 and the trace

/// No fixture of slices 1 to 25 at O0, and no slice-24c source at O0 (the
/// selector's one machine block per LIR block), changes: every theorem its
/// owner states and every refusal text is byte for byte what the code before
/// slice 24c gives ([`o0_outcomes24c`] equals the lines the fails-before run
/// recorded on `a617488aa`, `slice24c_o0_owners.txt`), and the chooser picks
/// no segment for any of them.
#[test]
fn o0_is_untouched_by_segments() {
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tests/fixtures/x86_source_bound_body/slice24c_o0_owners.txt");
    let recorded: Vec<String> = std::fs::read_to_string(&path)
        .unwrap_or_else(|error| panic!("{}: {error}", path.display()))
        .lines()
        .filter(|line| !line.starts_with('#'))
        .map(str::to_owned)
        .collect();
    let outcomes = o0_outcomes24c();
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
    for (label, source, machine) in o0_fixtures24c() {
        let Ok(cfg) = source_cfg(&source) else {
            continue;
        };
        let chosen = segment::choose(&source, &machine, &cfg);
        assert!(
            chosen.segments.is_empty(),
            "{label}: a segment at O0: {:?}",
            chosen.segments
        );
    }
}

/// The F18 analog: the full O2 schedule over every fixture of slices 1 to
/// 25 (and slice 6's O1/O2/O3 control set through `earlier_fixtures`): a
/// correct lowering is never named a mismatch, every theorem the owner
/// builds (over segments or not) holds on samples, and some are stated over
/// segments.
#[test]
fn a_segment_never_names_a_correct_machine_a_mismatch() {
    use trust_cg_codegen::x86_64::pipeline::{X86Pipeline, X86PipelineConfig};
    let mut over_segments = 0;
    let mut built = 0;
    for opt_level in [
        trust_cg_opt::OptLevel::O1,
        trust_cg_opt::OptLevel::O2,
        trust_cg_opt::OptLevel::O3,
    ] {
        let pipeline = X86Pipeline::new(X86PipelineConfig {
            opt_level,
            call_abi: X86CallAbi::SystemV,
            ..X86PipelineConfig::default()
        });
        let fixtures = o0_fixtures24c();
        for (label, source, mut machine) in fixtures {
            pipeline.run_x86_optimization_passes(&mut machine);
            match owner24c(&source, &machine) {
                Ok(owner) => {
                    built += 1;
                    if let Some((segments, members, kinds)) = owner.segments() {
                        over_segments += 1;
                        eprintln!(
                            "SLICE24C_OPT {opt_level:?} {label} segments={segments} \
                             members={members} kinds={kinds}"
                        );
                    }
                    owner_holds(&owner).unwrap_or_else(|why| {
                        panic!("{label} at {opt_level:?}: {why}\n{}", describe(&machine))
                    });
                }
                Err(X86BodyRefusal::Unsupported(_)) => {}
                Err(other) => panic!("{label} at {opt_level:?}: {other}\n{}", describe(&machine)),
            }
        }
    }
    eprintln!("SLICE24C_OPT built={built} over_segments={over_segments}");
    assert!(
        over_segments > 0,
        "no optimized body was stated over segments"
    );
}

/// The verifier's trace (`TCG_X86_BODY_TRACE`) of a theorem over segments:
/// its `segments=` line after any `merged chains=` line and before the
/// `stated in parts=` line, and its last line `bound rows=`, the order the
/// census parsers read. Run in a child process, which writes the trace to
/// its stderr; no replay.
#[test]
fn the_segments_trace_line_precedes_the_parts_and_bound_lines() {
    const CHILD: &str = "TCG_S24C_TRACE_CHILD";
    const TEST: &str = "x86_source_bound_body::tests::slice24c::\
                        the_segments_trace_line_precedes_the_parts_and_bound_lines";
    if std::env::var_os(CHILD).is_some() {
        super::without_replay(|| {
            let verifier = promotion_verifier();
            let request = verifier.capture_request_with_mode(ProvenanceXCheckMode::Enforce);
            for (source, machine) in [
                pair24c(Shape24c::AlignOffset),
                pair24c(Shape24c::IntegerDecode),
                case24c("P8"),
            ] {
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
    for (function, parts) in [
        ("s24c_align_offset", false),
        ("s24c_integer_decode", false),
        ("s24c_long_diamond", true),
    ] {
        let lines: Vec<&str> = stderr
            .lines()
            .filter(|line| line.starts_with(&format!("[TCG-X86-BODY-TRACE] fn={function} ")))
            .collect();
        let position = |needle: &str| lines.iter().position(|line| line.contains(needle));
        let segments = position(" segments=")
            .unwrap_or_else(|| panic!("{function}: no segments line: {lines:?}"));
        if let Some(merged) = position(" merged chains=") {
            assert!(merged < segments, "{function}: {lines:?}");
        }
        let last = lines.last().expect("a trace line");
        assert!(
            last.contains(" bound rows="),
            "{function}: last line {last:?}"
        );
        assert!(segments + 1 < lines.len(), "{function}: {lines:?}");
        match position(" stated in parts=") {
            Some(stated) => {
                assert!(parts, "{function}: stated in parts: {lines:?}");
                assert!(segments < stated, "{function}: {lines:?}");
            }
            None => assert!(!parts, "{function}: no parts line: {lines:?}"),
        }
    }
}

/// The neutral mutant `s24c-kind-diamond` (every segment labelled a
/// diamond) changes no verdict and no theorem byte, and the switch is wired:
/// P3's segment, which is silent, reads as a diamond under it.
#[test]
fn the_kind_label_mutant_is_neutral() {
    let outcome = |shape: Shape24c| {
        let (source, machine) = pair24c(shape);
        match owner24c(&source, &machine) {
            Ok(owner) => (owner.segments(), text(owner.obligation())),
            Err(refusal) => panic!("{shape:?}: {refusal}"),
        }
    };
    let before: Vec<_> = SLICE_TWENTY_FOUR_C
        .iter()
        .map(|shape| outcome(*shape))
        .collect();
    let refusals: Vec<String> = CASES24C
        .iter()
        .map(|label| {
            let (source, machine) = case24c(label);
            outcome24c(&owner24c(&source, &machine))
        })
        .collect();
    let _mutant = mutant::set("s24c-kind-diamond");
    for (shape, (segments, theorem)) in SLICE_TWENTY_FOUR_C.iter().zip(before) {
        let (relabelled, again) = outcome(*shape);
        assert_eq!(again, theorem, "{shape:?}: the theorem changed");
        let (count, members, kinds) = segments.expect("stated over segments");
        let (count_again, members_again, kinds_again) = relabelled.expect("stated over segments");
        assert_eq!((count, members), (count_again, members_again), "{shape:?}");
        if *shape == Shape24c::SelectUnpredictable {
            assert_eq!(kinds, "[silent]", "{shape:?}");
            assert_eq!(
                kinds_again, "[diamond]",
                "s24c-kind-diamond changes nothing"
            );
        }
    }
    for (label, before) in CASES24C.iter().zip(refusals) {
        let (source, machine) = case24c(label);
        assert_eq!(outcome24c(&owner24c(&source, &machine)), before, "{label}");
    }
}
