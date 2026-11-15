// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! Ruling OD-233 on the x86-64 body theorem in parts (OD-182): a cut input
//! the source brings as one term over the run's fixed inputs on every edge
//! into its cut is DEFINED as that term in the cut's region, and CLAIMED
//! equal to it on every edge (`split::cut_definitions`, `build_theorem`).
//!
//! Fixtures take their LIR from the trust-ir adapter (translated with an
//! explicit `Permit`) and their machine stream from the real x86-64
//! instruction selector (`super::select`), then from the real x86 pass
//! pipeline at O2 (`X86Pipeline::run_x86_optimization_passes`, which
//! includes `x86_slot_forward`'s single-predecessor forwarding), or at O1
//! for the loops ([`level233`]); the only hand edits are the labelled
//! wrong lowerings ([`Wrong233`]). Each fixture
//! asserts its own shape (`every_fixture_has_its_shape`), so a pass change
//! that removes the shape fails by name. P6 is slice 25's three slot
//! fixtures (`super::slice25`).
//!
//! Every test here runs without a solver (the
//! `x86_source_bound_body::tests::od233::` library gate); the replay on AY
//! and Clean is in `od233_qualification`.
//!
//! Everything above the "Controls" section uses only the API of the code
//! before OD-233 (and none of slice 25's), so the same fixtures are judged
//! by the code at the slice-25 base and at the commit before slice 25 (the
//! fails-before record of the 2026-11-05 report).

use super::slice5::describe;
use super::slice6::describe_lir;
use super::slice16::{every_block, every_point, in_parts};
use super::slice24::{owner_holds, owner_refuted};
use super::*;
use trust_ir::value::GlobalId;
use trust_ir::{Constant, ICmpOp, Linkage};

// ---------------------------------------------------------------------------
// Fixtures
// ---------------------------------------------------------------------------

/// The OD-233 fixture shapes (design §5.2 and §5.4), each a correct
/// lowering.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Shape233 {
    // ---- P: positive fixtures
    /// P1, the `core::wtf8::slice_error_fail` reduction: `fn(ptr, len,
    /// begin, end)`. Block 0 stores `ptr` and `len` into two slots, copies
    /// the length to slot B through a load and a store, reloads B as `v`
    /// and stores it once into the address-taken local L (and `begin`,
    /// `end` into Bg, En); `begin > v` panics with `&Bg, &L`. Block 2 (only
    /// predecessor Block 0) reloads En and L and tests `end > L` (the
    /// machine compares the forwarded registers); Block 4 tests `begin >
    /// end`.
    Wtf8LenLocal,
    /// P1b: P1 with `len` stored into L directly (a leaf: L's bytes are
    /// closed, so nothing is defined).
    Wtf8LenDirect,
    /// P2: P1 storing `len + 1` (the machine forwards the `add`'s result).
    ComputedLenLocal,
    /// P3: `fn(begin, end)`: a symbol's address stored into L; `begin >
    /// end` panics with `&L`, else Block 2 reloads it, passes it to a call
    /// and returns (a stored symbol address is never a closed byte).
    SymbolLocal,
    /// P4: `fn(x, y) -> u64`: `m = x * 3` in Block 0, each arm of a branch
    /// calls out and passes `m` to Block 3's parameter, which returns
    /// `param + y` (cut at Block 3).
    CommonCutParam,
    /// P5: `fn(x, n) -> u64`: L stored `x + 1` before a counted loop whose
    /// body reloads L every iteration and never writes it; after the loop
    /// `&L` escapes to a call (cut at the loop header).
    InvariantLocalAcrossHeader,
    /// P7: `fn(c, x) -> u32`: L stored the u64 `x + 1`; past the branch on
    /// `c` (Block 1, one predecessor) the low u32 of L is reloaded and
    /// returned; the other arm lets `&L` escape.
    NarrowReadBack,
    /// P8: `fn(x, y)`: L stored `x + 1` in Block 0; each arm of a branch on
    /// `y` calls out and jumps to the join J, which branches on `x > y` to C
    /// (C passes `&L` to a call) or returns. Cut at the first arm and at C
    /// ([`points233`]): J is in Block 0's region and in the arm's, so its
    /// edge into C is stated in both, with two source terms (Block 0's
    /// store, the arm's defined input) that resolve to one.
    SharedJoinLocal,
    /// Q1: P1 with a jump-only block before Block 2, which the O2 pipeline
    /// merges into it: stated over slice 24a's merged-chain quotient.
    MergedLenLocal,
    /// P1L: Q1 whose last block makes 300 calls, then passes `&L` to a call
    /// (past the single-query machine bounds: the production planner states
    /// it in parts; the trace test only).
    LongLenLocal,
    // ---- V and N: inputs that stay free, and a body with no observable
    /// V1: the two arms store different terms into L, which the join
    /// reloads.
    PathsDiffer,
    /// V2: L stored `x + 1`, then `&L` escapes to a call before the cut
    /// (L's bytes are the call's).
    CallAfterStore,
    /// V2b: `&L` escapes, L is stored `x + 1`, then a store through an
    /// incoming pointer (which may point into L) precedes the cut (L's
    /// bytes are that access's).
    MayAliasStore,
    /// V3: L stored `x + 1` before a loop whose body increments it.
    LoopCarried,
    /// V4: the stored value reads an earlier cut's free item (a load of
    /// incoming memory live across Block 1); L is reloaded at a join.
    EarlierFreeItem,
    /// V5: the stored value is computed from a call result after a slot
    /// escaped (tainted, slice 7).
    TaintedStore,
    /// V6: the stored value's term has more than 64 nodes.
    OverSixtyFour,
    /// V7: an `I128` value computed from a parameter, live across a cut.
    WideItem,
    /// V8: a call result before a loop, live across its header.
    CallInLoop,
    /// V9: P8 whose first arm re-stores L with `y`, and whose C reloads L
    /// and passes the value to a call before `&L`: J's two stated edges into
    /// C bring different terms, and L's bytes, which C reads, stay free at C.
    SharedJoinDiffers,
    /// N1: one block storing a symbol's address into L, then passing `&L`
    /// to a call, cut between the two: every claim of the statement is an
    /// identity (OD-115), though L's bytes are definable at the cut.
    SymbolNoObservable,
    /// W3's source: P1 with a second predecessor of Block 2 that re-stores L
    /// with `end`.
    TwoPredecessors,
}

/// The positive fixtures (P1-P5, P7, P8, Q1; P6 is slice 25's).
pub(crate) const POSITIVE: [Shape233; 9] = [
    Shape233::Wtf8LenLocal,
    Shape233::Wtf8LenDirect,
    Shape233::ComputedLenLocal,
    Shape233::SymbolLocal,
    Shape233::CommonCutParam,
    Shape233::InvariantLocalAcrossHeader,
    Shape233::NarrowReadBack,
    Shape233::SharedJoinLocal,
    Shape233::MergedLenLocal,
];

/// The free-input and refusal controls (V1-V9, V2b, N1) and W3's source.
pub(crate) const CONTROLS: [Shape233; 12] = [
    Shape233::PathsDiffer,
    Shape233::CallAfterStore,
    Shape233::MayAliasStore,
    Shape233::LoopCarried,
    Shape233::EarlierFreeItem,
    Shape233::TaintedStore,
    Shape233::OverSixtyFour,
    Shape233::WideItem,
    Shape233::CallInLoop,
    Shape233::SharedJoinDiffers,
    Shape233::SymbolNoObservable,
    Shape233::TwoPredecessors,
];

impl Shape233 {
    /// The design's label of the fixture.
    pub(crate) fn label(self) -> &'static str {
        use Shape233::*;
        match self {
            Wtf8LenLocal => "P1",
            Wtf8LenDirect => "P1b",
            ComputedLenLocal => "P2",
            SymbolLocal => "P3",
            CommonCutParam => "P4",
            InvariantLocalAcrossHeader => "P5",
            NarrowReadBack => "P7",
            SharedJoinLocal => "P8",
            MergedLenLocal => "Q1",
            LongLenLocal => "P1L",
            PathsDiffer => "V1",
            CallAfterStore => "V2",
            MayAliasStore => "V2b",
            LoopCarried => "V3",
            EarlierFreeItem => "V4",
            TaintedStore => "V5",
            OverSixtyFour => "V6",
            WideItem => "V7",
            CallInLoop => "V8",
            SharedJoinDiffers => "V9",
            SymbolNoObservable => "N1",
            TwoPredecessors => "W3-source",
        }
    }

    fn name(self) -> String {
        let name = format!("{self:?}");
        let mut snake = String::from("od233_");
        for (i, c) in name.chars().enumerate() {
            if c.is_ascii_uppercase() && i > 0 {
                snake.push('_');
            }
            snake.push(c.to_ascii_lowercase());
        }
        snake
    }
}

/// Translate one function of `builder`'s module under the explicit Permit
/// the workspace's fixtures use.
fn translate233(builder: ModuleBuilder, name: &str) -> Function {
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

type V233 = trust_ir::value::ValueId;

/// What P1's family stores into L.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Stored {
    /// The read-back `v` of the copied length (P1).
    Copied,
    /// The parameter `len` itself (P1b).
    Direct,
    /// `v + 1` (P2).
    PlusOne,
}

/// The LIR the trust-ir adapter produces for an OD-233 shape.
pub(crate) fn od233_lir(shape: Shape233) -> Function {
    use Shape233::*;
    let mut builder = ModuleBuilder::new("x86_source_bound_body_od233");
    builder.add_global(trust_ir::Global {
        name: "od233_g".into(),
        ty: Ty::U64,
        mutable: true,
        initializer: Some(Constant::Int(0)),
        linkage: Linkage::External,
        tls: None,
        align: None,
        section: None,
        visibility: Default::default(),
        retained: false,
    });
    let ptr = |ty: Ty| Ty::PtrMut(Box::new(ty));
    let panic2_ty = builder.add_func_type(vec![ptr(Ty::U64), ptr(Ty::U64)], vec![]);
    let panic2 = builder.declare_function("od233_panic2", panic2_ty);
    let panic1_ty = builder.add_func_type(vec![ptr(Ty::U64)], vec![]);
    let panic1 = builder.declare_function("od233_panic1", panic1_ty);
    let sink_ty = builder.add_func_type(vec![ptr(Ty::U64)], vec![]);
    let sink = builder.declare_function("od233_sink", sink_ty);
    let note_ty = builder.add_func_type(vec![Ty::U64], vec![]);
    let note = builder.declare_function("od233_note", note_ty);
    let other = builder.declare_function("od233_other", note_ty);
    let get_ty = builder.add_func_type(vec![ptr(Ty::U64)], vec![Ty::U64]);
    let get = builder.declare_function("od233_get", get_ty);
    let fresh_ty = builder.add_func_type(vec![], vec![Ty::U64]);
    let fresh = builder.declare_function("od233_fresh", fresh_ty);
    let (params, results): (Vec<Ty>, Vec<Ty>) = match shape {
        Wtf8LenLocal | Wtf8LenDirect | ComputedLenLocal | TwoPredecessors | MergedLenLocal
        | LongLenLocal => (vec![Ty::U64; 4], vec![]),
        SymbolLocal | SharedJoinLocal | SharedJoinDiffers => (vec![Ty::U64; 2], vec![]),
        SymbolNoObservable => (vec![], vec![]),
        CommonCutParam
        | InvariantLocalAcrossHeader
        | PathsDiffer
        | CallAfterStore
        | LoopCarried
        | OverSixtyFour
        | WideItem
        | CallInLoop => (vec![Ty::U64; 2], vec![Ty::U64]),
        NarrowReadBack => (vec![Ty::U64; 2], vec![Ty::U32]),
        MayAliasStore => (vec![ptr(ptr(Ty::U64)), Ty::U64], vec![Ty::U64]),
        EarlierFreeItem => (vec![ptr(Ty::U64), Ty::U64], vec![Ty::U64]),
        TaintedStore => (vec![Ty::U64], vec![Ty::U64]),
    };
    let signature = builder.add_func_type(params.clone(), results);
    let name = shape.name();
    let mut f = builder.function(name.clone(), signature);
    let entry = f.create_block();
    let args: Vec<V233> = params
        .iter()
        .map(|ty| f.add_block_param(entry, ty.clone()))
        .collect();
    f.switch_to_block(entry);
    match shape {
        Wtf8LenLocal | Wtf8LenDirect | ComputedLenLocal | TwoPredecessors | MergedLenLocal
        | LongLenLocal => {
            let stored = match shape {
                Wtf8LenDirect => Stored::Direct,
                ComputedLenLocal => Stored::PlusOne,
                _ => Stored::Copied,
            };
            let (ptr_arg, len, begin, end) = (args[0], args[1], args[2], args[3]);
            // L is the first slot ([`local_slot`]); the slice's two words and
            // the copy are 8-byte slots of their own (an offset into one
            // slot is a scaled-index row at O2, which only slice 25 states).
            let l = f.alloca(Ty::U64);
            let a_ptr = f.alloca(Ty::U64);
            f.store(Ty::U64, a_ptr, ptr_arg);
            let a_len = f.alloca(Ty::U64);
            f.store(Ty::U64, a_len, len);
            let b = f.alloca(Ty::U64);
            let t = f.load(Ty::U64, a_len);
            f.store(Ty::U64, b, t);
            let v = f.load(Ty::U64, b);
            let v = match stored {
                Stored::Copied => v,
                Stored::Direct => len,
                Stored::PlusOne => {
                    let one = f.iconst(Ty::U64, 1);
                    f.add(Ty::U64, v, one)
                }
            };
            f.store(Ty::U64, l, v);
            let bg = f.alloca(Ty::U64);
            f.store(Ty::U64, bg, begin);
            let en = f.alloca(Ty::U64);
            f.store(Ty::U64, en, end);
            let blocks: Vec<_> = (0..6).map(|_| f.create_block()).collect();
            let (b1, b2, b3, b4, b5, b6) = (
                blocks[0], blocks[1], blocks[2], blocks[3], blocks[4], blocks[5],
            );
            let test = f.icmp(ICmpOp::Ugt, Ty::U64, begin, v);
            if shape == TwoPredecessors {
                // Block 1 re-stores L with `end` and joins Block 2.
                let restore = f.create_block();
                let zero = f.iconst(Ty::U64, 0);
                let odd = f.icmp(ICmpOp::Ne, Ty::U64, end, zero);
                let split = f.create_block();
                f.condbr(test, b1, vec![], split, vec![]);
                f.switch_to_block(split);
                f.condbr(odd, restore, vec![], b2, vec![]);
                f.switch_to_block(restore);
                f.store(Ty::U64, l, end);
                f.br(b2, vec![]);
            } else if matches!(shape, MergedLenLocal | LongLenLocal) {
                // A jump-only block before Block 2 (merged into it at O2).
                let via = f.create_block();
                f.condbr(test, b1, vec![], via, vec![]);
                f.switch_to_block(via);
                f.br(b2, vec![]);
            } else {
                f.condbr(test, b1, vec![], b2, vec![]);
            }
            f.switch_to_block(b1);
            f.call_void(panic2, vec![bg, l]);
            f.unreachable();
            f.switch_to_block(b2);
            let e = f.load(Ty::U64, en);
            let x = f.load(Ty::U64, l);
            let past = f.icmp(ICmpOp::Ugt, Ty::U64, e, x);
            f.condbr(past, b3, vec![], b4, vec![]);
            f.switch_to_block(b3);
            f.call_void(panic2, vec![en, l]);
            f.unreachable();
            f.switch_to_block(b4);
            let reversed = f.icmp(ICmpOp::Ugt, Ty::U64, begin, end);
            f.condbr(reversed, b5, vec![], b6, vec![]);
            f.switch_to_block(b5);
            f.call_void(panic2, vec![bg, en]);
            f.unreachable();
            f.switch_to_block(b6);
            if shape == LongLenLocal {
                for _ in 0..300 {
                    f.call_void(note, vec![begin]);
                }
                f.call_void(sink, vec![l]);
            }
            f.ret(vec![]);
        }
        SharedJoinLocal | SharedJoinDiffers => {
            let (x, y) = (args[0], args[1]);
            let l = f.alloca(Ty::U64);
            let one = f.iconst(Ty::U64, 1);
            let v = f.add(Ty::U64, x, one);
            f.store(Ty::U64, l, v);
            let zero = f.iconst(Ty::U64, 0);
            let test = f.icmp(ICmpOp::Ne, Ty::U64, y, zero);
            let blocks: Vec<_> = (0..5).map(|_| f.create_block()).collect();
            let (arm, other_arm, join, sunk, done) =
                (blocks[0], blocks[1], blocks[2], blocks[3], blocks[4]);
            f.condbr(test, arm, vec![], other_arm, vec![]);
            f.switch_to_block(arm);
            if shape == SharedJoinDiffers {
                f.store(Ty::U64, l, y);
            }
            f.call_void(note, vec![y]);
            f.br(join, vec![]);
            f.switch_to_block(other_arm);
            f.call_void(other, vec![x]);
            f.br(join, vec![]);
            f.switch_to_block(join);
            let past = f.icmp(ICmpOp::Ugt, Ty::U64, x, y);
            f.condbr(past, sunk, vec![], done, vec![]);
            f.switch_to_block(sunk);
            if shape == SharedJoinDiffers {
                let reloaded = f.load(Ty::U64, l);
                f.call_void(note, vec![reloaded]);
            }
            f.call_void(sink, vec![l]);
            f.ret(vec![]);
            f.switch_to_block(done);
            f.ret(vec![]);
        }
        SymbolLocal | SymbolNoObservable => {
            let l = f.alloca(ptr(Ty::U64));
            let g = f.global_addr(GlobalId::new(0));
            f.store(ptr(Ty::U64), l, g);
            if shape == SymbolLocal {
                let (b1, b2) = (f.create_block(), f.create_block());
                let test = f.icmp(ICmpOp::Ugt, Ty::U64, args[0], args[1]);
                f.condbr(test, b1, vec![], b2, vec![]);
                f.switch_to_block(b1);
                f.call_void(panic1, vec![l]);
                f.unreachable();
                f.switch_to_block(b2);
                let x = f.load(ptr(Ty::U64), l);
                f.call_void(sink, vec![x]);
                f.ret(vec![]);
            } else {
                // Cut before the call ([`points233`]).
                f.call_void(sink, vec![l]);
                f.ret(vec![]);
            }
        }
        CommonCutParam => {
            let three = f.iconst(Ty::U64, 3);
            let m = f.mul(Ty::U64, args[0], three);
            let zero = f.iconst(Ty::U64, 0);
            let test = f.icmp(ICmpOp::Ne, Ty::U64, args[1], zero);
            let (b1, b2, b3) = (f.create_block(), f.create_block(), f.create_block());
            let z = f.add_block_param(b3, Ty::U64);
            f.condbr(test, b1, vec![], b2, vec![]);
            f.switch_to_block(b1);
            f.call_void(note, vec![args[1]]);
            f.br(b3, vec![m]);
            f.switch_to_block(b2);
            f.call_void(other, vec![args[0]]);
            f.br(b3, vec![m]);
            f.switch_to_block(b3);
            let sum = f.add(Ty::U64, z, args[1]);
            f.ret(vec![sum]);
        }
        InvariantLocalAcrossHeader | LoopCarried => {
            let l = f.alloca(Ty::U64);
            let one = f.iconst(Ty::U64, 1);
            let v = f.add(Ty::U64, args[0], one);
            f.store(Ty::U64, l, v);
            let zero = f.iconst(Ty::U64, 0);
            let (header, body, exit) = (f.create_block(), f.create_block(), f.create_block());
            let i = f.add_block_param(header, Ty::U64);
            let acc = f.add_block_param(header, Ty::U64);
            f.br(header, vec![zero, zero]);
            f.switch_to_block(header);
            let more = f.icmp(ICmpOp::Ult, Ty::U64, i, args[1]);
            f.condbr(more, body, vec![], exit, vec![]);
            f.switch_to_block(body);
            let x = f.load(Ty::U64, l);
            let acc2 = f.add(Ty::U64, acc, x);
            if shape == LoopCarried {
                let bumped = f.add(Ty::U64, x, one);
                f.store(Ty::U64, l, bumped);
            }
            let i2 = f.add(Ty::U64, i, one);
            f.br(header, vec![i2, acc2]);
            f.switch_to_block(exit);
            f.call_void(sink, vec![l]);
            f.ret(vec![acc]);
        }
        NarrowReadBack => {
            let l = f.alloca(Ty::U64);
            let one = f.iconst(Ty::U64, 1);
            let v = f.add(Ty::U64, args[1], one);
            f.store(Ty::U64, l, v);
            let zero = f.iconst(Ty::U64, 0);
            let test = f.icmp(ICmpOp::Ne, Ty::U64, args[0], zero);
            let (b1, b2) = (f.create_block(), f.create_block());
            f.condbr(test, b1, vec![], b2, vec![]);
            f.switch_to_block(b1);
            let low = f.load(Ty::U32, l);
            f.ret(vec![low]);
            f.switch_to_block(b2);
            f.call_void(sink, vec![l]);
            let none = f.iconst(Ty::U32, 0);
            f.ret(vec![none]);
        }
        PathsDiffer => {
            let l = f.alloca(Ty::U64);
            let one = f.iconst(Ty::U64, 1);
            let zero = f.iconst(Ty::U64, 0);
            let test = f.icmp(ICmpOp::Ne, Ty::U64, args[0], zero);
            let (b1, b2, b3) = (f.create_block(), f.create_block(), f.create_block());
            f.condbr(test, b1, vec![], b2, vec![]);
            f.switch_to_block(b1);
            let x = f.add(Ty::U64, args[1], one);
            f.store(Ty::U64, l, x);
            f.br(b3, vec![]);
            f.switch_to_block(b2);
            let y = f.add(Ty::U64, args[0], one);
            f.store(Ty::U64, l, y);
            f.br(b3, vec![]);
            f.switch_to_block(b3);
            let z = f.load(Ty::U64, l);
            f.call_void(sink, vec![l]);
            f.ret(vec![z]);
        }
        CallAfterStore | MayAliasStore | TaintedStore | OverSixtyFour => {
            let l = f.alloca(Ty::U64);
            let one = f.iconst(Ty::U64, 1);
            let zero = f.iconst(Ty::U64, 0);
            let key = *args.last().expect("a parameter");
            let stored = match shape {
                CallAfterStore => {
                    let v = f.add(Ty::U64, args[1], one);
                    f.store(Ty::U64, l, v);
                    f.call_void(sink, vec![l]);
                    None
                }
                MayAliasStore => {
                    f.call_void(sink, vec![l]);
                    let v = f.add(Ty::U64, args[1], one);
                    f.store(Ty::U64, l, v);
                    let q = f.load(ptr(Ty::U64), args[0]);
                    let seven = f.iconst(Ty::U64, 7);
                    f.store(Ty::U64, q, seven);
                    None
                }
                TaintedStore => {
                    let m = f.alloca(Ty::U64);
                    f.store(Ty::U64, m, args[0]);
                    let r = f.call(get, vec![m]);
                    let masked = f.binop(BinOp::And, Ty::U64, r, zero);
                    Some(masked)
                }
                _ => {
                    let mut x = args[0];
                    for _ in 0..6 {
                        let square = f.mul(Ty::U64, x, x);
                        x = f.add(Ty::U64, square, args[1]);
                    }
                    Some(x)
                }
            };
            if let Some(stored) = stored {
                f.store(Ty::U64, l, stored);
            }
            let test = f.icmp(ICmpOp::Ne, Ty::U64, key, zero);
            let (b1, b2) = (f.create_block(), f.create_block());
            if matches!(shape, TaintedStore | OverSixtyFour) {
                // Block 2 has two predecessors: the machine reloads L there.
                f.condbr(test, b1, vec![], b2, vec![]);
                f.switch_to_block(b1);
                f.call_void(note, vec![key]);
                f.br(b2, vec![]);
                f.switch_to_block(b2);
                let x = f.load(Ty::U64, l);
                f.call_void(sink, vec![l]);
                f.ret(vec![x]);
            } else {
                f.condbr(test, b1, vec![], b2, vec![]);
                f.switch_to_block(b1);
                let x = f.load(Ty::U64, l);
                f.ret(vec![x]);
                f.switch_to_block(b2);
                f.ret(vec![zero]);
            }
        }
        EarlierFreeItem => {
            let l = f.alloca(Ty::U64);
            let w = f.load(Ty::U64, args[0]);
            let one = f.iconst(Ty::U64, 1);
            let zero = f.iconst(Ty::U64, 0);
            let test = f.icmp(ICmpOp::Ne, Ty::U64, args[1], zero);
            let blocks: Vec<_> = (0..4).map(|_| f.create_block()).collect();
            let (b1, b2, b3, b4) = (blocks[0], blocks[1], blocks[2], blocks[3]);
            f.condbr(test, b1, vec![], b4, vec![]);
            f.switch_to_block(b1);
            let s = f.add(Ty::U64, w, one);
            f.store(Ty::U64, l, s);
            let big = f.icmp(ICmpOp::Ugt, Ty::U64, args[1], s);
            f.condbr(big, b2, vec![], b3, vec![]);
            // Block 3 has two predecessors: the machine reloads L there.
            f.switch_to_block(b2);
            f.call_void(note, vec![args[1]]);
            f.br(b3, vec![]);
            f.switch_to_block(b3);
            let x = f.load(Ty::U64, l);
            f.call_void(sink, vec![l]);
            f.ret(vec![x]);
            f.switch_to_block(b4);
            f.ret(vec![one]);
        }
        WideItem => {
            let wide = f.zext(Ty::U64, Ty::U128, args[0]);
            let doubled = f.add(Ty::U128, wide, wide);
            let zero = f.iconst(Ty::U64, 0);
            let test = f.icmp(ICmpOp::Ne, Ty::U64, args[1], zero);
            let (b1, b2) = (f.create_block(), f.create_block());
            f.condbr(test, b1, vec![], b2, vec![]);
            f.switch_to_block(b1);
            let sixty_four = f.iconst(Ty::U128, 64);
            let high = f.binop(BinOp::LShr, Ty::U128, doubled, sixty_four);
            let high = f.trunc(Ty::U128, Ty::U64, high);
            let low = f.trunc(Ty::U128, Ty::U64, doubled);
            let sum = f.add(Ty::U64, low, high);
            f.ret(vec![sum]);
            f.switch_to_block(b2);
            f.ret(vec![zero]);
        }
        CallInLoop => {
            let r = f.call(fresh, vec![]);
            let zero = f.iconst(Ty::U64, 0);
            let one = f.iconst(Ty::U64, 1);
            let (header, body, exit) = (f.create_block(), f.create_block(), f.create_block());
            let i = f.add_block_param(header, Ty::U64);
            let acc = f.add_block_param(header, Ty::U64);
            f.br(header, vec![zero, zero]);
            f.switch_to_block(header);
            let more = f.icmp(ICmpOp::Ult, Ty::U64, i, args[1]);
            f.condbr(more, body, vec![], exit, vec![]);
            f.switch_to_block(body);
            let acc2 = f.add(Ty::U64, acc, r);
            let i2 = f.add(Ty::U64, i, one);
            f.br(header, vec![i2, acc2]);
            f.switch_to_block(exit);
            let sum = f.add(Ty::U64, acc, args[0]);
            f.ret(vec![sum]);
        }
    }
    f.build();
    translate233(builder, &name)
}

/// The pipeline level of a fixture's machine stream: O2, but O1 for the
/// loops (P5, V3, V8). O2 rotates every loop (`x86-loop-rotate`), and a
/// rotated loop's machine blocks do not correspond to its LIR blocks, which
/// the body route refuses (slice 26's scope); O1 runs LICM without
/// rotation.
pub(crate) fn level233(shape: Shape233) -> trust_cg_opt::OptLevel {
    use Shape233::*;
    match shape {
        InvariantLocalAcrossHeader | LoopCarried | CallInLoop => trust_cg_opt::OptLevel::O1,
        _ => trust_cg_opt::OptLevel::O2,
    }
}

/// The machine stream of `source`: the real selector, then the real x86
/// pass pipeline at `level`.
pub(crate) fn optimized233(source: &Function, level: trust_cg_opt::OptLevel) -> X86ISelFunction {
    use trust_cg_codegen::x86_64::pipeline::{X86Pipeline, X86PipelineConfig};
    let mut machine = select(source, X86CallAbi::SystemV);
    X86Pipeline::new(X86PipelineConfig {
        opt_level: level,
        call_abi: X86CallAbi::SystemV,
        ..X86PipelineConfig::default()
    })
    .run_x86_optimization_passes(&mut machine);
    machine
}

/// An OD-233 fixture pair: the adapter's LIR and the real stream at the
/// fixture's level ([`level233`]).
pub(crate) fn od233_pair(shape: Shape233) -> (Function, X86ISelFunction) {
    let source = od233_lir(shape);
    let machine = optimized233(&source, level233(shape));
    (source, machine)
}

/// The fixture's cut points: the start of every block but the entry (as
/// the census planner cuts wtf8), or for P4 Block 3 alone, for a loop the
/// loop header alone (the split route always cuts there), for N1 its one
/// block before the call (its instruction 3), for P8 and V9 the first arm
/// and C (not the join, which both regions then hold), for Q1 every block
/// start but the jump-only block's (its one instruction is the `Jump` the
/// merged-chain quotient removes, so no cut point can fall there).
pub(crate) fn points233(shape: Shape233, source: &Function) -> Vec<(Block, usize)> {
    use Shape233::*;
    match shape {
        MergedLenLocal => {
            let (_, via) = brif233(source, source.entry_block);
            every_block(source)
                .into_iter()
                .filter(|(block, _)| *block != via)
                .collect()
        }
        CommonCutParam => vec![(Block(3), 0)],
        InvariantLocalAcrossHeader | LoopCarried | CallInLoop => vec![],
        SymbolNoObservable => vec![(source.entry_block, 3)],
        SharedJoinLocal | SharedJoinDiffers => {
            let (arm, _) = brif233(source, source.entry_block);
            let (sunk, _) = brif233(source, jump233(source, arm));
            let mut points = vec![(arm, 0), (sunk, 0)];
            points.sort();
            points
        }
        _ => every_block(source),
    }
}

/// The two destinations of the `Brif` that ends LIR block `block`.
fn brif233(source: &Function, block: Block) -> (Block, Block) {
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

/// The destination of the `Jump` that ends LIR block `block`.
fn jump233(source: &Function, block: Block) -> Block {
    match source.blocks[&block]
        .instructions
        .last()
        .map(|inst| &inst.opcode)
    {
        Some(L::Jump { dest }) => *dest,
        other => panic!("{block:?} ends in {other:?}"),
    }
}

/// The owner of a fixture pair stated in parts at its points.
pub(crate) fn owner233<'a>(
    shape: Shape233,
    source: &'a Function,
    machine: &'a X86ISelFunction,
) -> Result<SourceBoundX86Body<'a>, X86BodyRefusal> {
    in_parts(source, machine, points233(shape, source))
}

/// A refusal's text, or `stated`.
pub(crate) fn refusal_text233(result: &Result<SourceBoundX86Body<'_>, X86BodyRefusal>) -> String {
    match result {
        Ok(_) => "stated".into(),
        Err(refusal) => format!("{refusal}"),
    }
}

/// The verdict of an owner on samples: `holds`, or why not.
pub(crate) fn verdict233(result: &Result<SourceBoundX86Body<'_>, X86BodyRefusal>) -> String {
    match result {
        Ok(owner) => match owner_holds(owner) {
            Ok(()) => "holds".into(),
            Err(why) => why,
        },
        Err(refusal) => format!("refused: {refusal}"),
    }
}

/// The SHA-256 of an owner's statement and of every part, as the replay
/// renders them.
pub(crate) fn statement_digest233(owner: &SourceBoundX86Body<'_>) -> String {
    use sha2::{Digest, Sha256};
    let mut hasher = Sha256::new();
    hasher.update(super::slice24::text(owner.obligation()).as_bytes());
    for part in owner.parts() {
        hasher.update(b";;;; part\n");
        hasher.update(super::slice24::text(part).as_bytes());
    }
    format!("{:x}", hasher.finalize())
}

/// The stack slot memory operand `operand` addresses: `[slot + disp]`, or
/// `[v + disp]` for a `v` some `lea v, [slot + disp]` of `machine` defines.
fn slot_of(machine: &X86ISelFunction, operand: &O) -> Option<u32> {
    let O::MemAddr { base, .. } = operand else {
        return None;
    };
    match base.as_ref() {
        O::StackSlot(slot) => Some(*slot),
        base @ O::VReg(_) => machine.blocks.values().find_map(|block| {
            block
                .insts
                .iter()
                .find_map(|inst| match inst.operands.as_slice() {
                    [dst, O::MemAddr { base: slot, .. }]
                        if inst.opcode == X86Opcode::Lea && dst == base =>
                    {
                        match slot.as_ref() {
                            O::StackSlot(slot) => Some(*slot),
                            _ => None,
                        }
                    }
                    _ => None,
                })
        }),
        _ => None,
    }
}

/// The machine rows of `block` (its index in `block_order`) as `(opcode,
/// operands)`.
fn block_rows(machine: &X86ISelFunction, block: usize) -> &[X86ISelInst] {
    &machine.blocks[&machine.block_order[block]].insts
}

/// The rows of `machine` that store into stack slot `slot` (`MovMR*` with a
/// `[slot + disp]` destination), as `(block index, row index)`.
fn stores_into(machine: &X86ISelFunction, slot: u32) -> Vec<(usize, usize)> {
    let mut found = Vec::new();
    for (b, block) in machine.block_order.iter().enumerate() {
        for (i, inst) in machine.blocks[block].insts.iter().enumerate() {
            if matches!(
                inst.opcode,
                X86Opcode::MovMR | X86Opcode::MovMR32 | X86Opcode::MovMR8
            ) && inst.operands.first().and_then(|at| slot_of(machine, at)) == Some(slot)
            {
                found.push((b, i));
            }
        }
    }
    found
}

/// The rows of `machine` that load from stack slot `slot`.
fn loads_from(machine: &X86ISelFunction, slot: u32) -> Vec<(usize, usize)> {
    let mut found = Vec::new();
    for (b, block) in machine.block_order.iter().enumerate() {
        for (i, inst) in machine.blocks[block].insts.iter().enumerate() {
            if matches!(
                inst.opcode,
                X86Opcode::MovRM
                    | X86Opcode::MovRM32
                    | X86Opcode::MovRM8
                    | X86Opcode::MovzxRM8
                    | X86Opcode::MovzxRM16
            ) && inst.operands.get(1).and_then(|at| slot_of(machine, at)) == Some(slot)
            {
                found.push((b, i));
            }
        }
    }
    found
}

/// Whether `machine` has a scaled-index (SIB) load or store row (slice 25's;
/// `LeaSib`, an address computation, is stated before slice 25).
fn has_sib_row(machine: &X86ISelFunction) -> bool {
    machine.blocks.values().any(|block| {
        block.insts.iter().any(|inst| {
            inst.opcode != X86Opcode::LeaSib
                && inst
                    .operands
                    .iter()
                    .any(|operand| matches!(operand, O::SibMemAddr { .. }))
        })
    })
}

/// The label and pair of a fixture's wrong lowerings (design §5.3, W1-W4,
/// and W6 of P8; W5 is an edit of slice 25's SlotConstU64, in the controls).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Wrong233 {
    /// W1: P1 with Block 2 comparing the forwarded length plus one.
    ComparesLenPlusOne,
    /// W2: P1 with Block 0 storing `begin` into L (the forwarded copy still
    /// the length).
    StoresBegin,
    /// W3: [`Shape233::TwoPredecessors`] with Block 2's reload of L replaced
    /// by the length register (wrong where Block 1 re-stored L with `end`).
    ForwardsAcrossJoin,
    /// W4: P5 with the machine incrementing L in the loop.
    IncrementsInLoop,
    /// W6: P8 with the first arm's machine block storing `y` into L before
    /// its jump to the join (the source does not): wrong on the arm's path
    /// only, which reaches C through the join that two regions hold.
    StoresInArm,
}

pub(crate) const WRONG: [Wrong233; 5] = [
    Wrong233::ComparesLenPlusOne,
    Wrong233::StoresBegin,
    Wrong233::ForwardsAcrossJoin,
    Wrong233::IncrementsInLoop,
    Wrong233::StoresInArm,
];

impl Wrong233 {
    pub(crate) fn label(self) -> &'static str {
        match self {
            Wrong233::ComparesLenPlusOne => "W1",
            Wrong233::StoresBegin => "W2",
            Wrong233::ForwardsAcrossJoin => "W3",
            Wrong233::IncrementsInLoop => "W4",
            Wrong233::StoresInArm => "W6",
        }
    }

    /// The shape whose pair the edit starts from.
    pub(crate) fn shape(self) -> Shape233 {
        match self {
            Wrong233::ComparesLenPlusOne | Wrong233::StoresBegin => Shape233::Wtf8LenLocal,
            Wrong233::ForwardsAcrossJoin => Shape233::TwoPredecessors,
            Wrong233::IncrementsInLoop => Shape233::InvariantLocalAcrossHeader,
            Wrong233::StoresInArm => Shape233::SharedJoinLocal,
        }
    }
}

/// A wrong lowering's pair: the fixture's real O2 stream with the labelled
/// hand edit.
pub(crate) fn wrong233(wrong: Wrong233) -> (Function, X86ISelFunction) {
    let (source, mut machine) = od233_pair(wrong.shape());
    let fresh = 30_000u32;
    match wrong {
        Wrong233::ComparesLenPlusOne => {
            // Block 2's compare of the forwarded length: compare `len + 1`.
            let (block, row, operand) = forwarded_compare(&machine);
            let block_id = machine.block_order[block];
            let body = machine.blocks.get_mut(&block_id).unwrap();
            let held = body.insts[row].operands[operand].clone();
            let bumped = vreg(fresh);
            body.insts.insert(
                row,
                X86ISelInst::new(X86Opcode::AddRI, vec![bumped.clone(), held, O::Imm(1)]),
            );
            body.insts[row + 1].operands[operand] = bumped;
        }
        Wrong233::StoresBegin => {
            // Block 0's store into L: store the third argument's register.
            let slot = local_slot(&machine);
            let (block, row) = stores_into(&machine, slot)[0];
            let begin = entry_copy_of(&machine, preg(trust_cg_ir::x86_64_regs::RDX.encoding()));
            let block_id = machine.block_order[block];
            machine.blocks.get_mut(&block_id).unwrap().insts[row].operands[1] = begin;
        }
        Wrong233::ForwardsAcrossJoin => {
            // Block 2's reload of L: the length register instead.
            let slot = local_slot(&machine);
            let reload = loads_from(&machine, slot)
                .into_iter()
                .find(|(block, _)| *block > 0)
                .unwrap_or_else(|| panic!("W3: no reload of L\n{}", describe(&machine)));
            let len = entry_copy_of(&machine, preg(trust_cg_ir::x86_64_regs::RSI.encoding()));
            let block_id = machine.block_order[reload.0];
            let row = &mut machine.blocks.get_mut(&block_id).unwrap().insts[reload.1];
            let dst = row.operands[0].clone();
            *row = X86ISelInst::new(X86Opcode::MovRR, vec![dst, len]);
        }
        Wrong233::IncrementsInLoop => {
            // The loop body: `add [L], 1` through its address, a load, an
            // add and a store.
            let slot = local_slot(&machine);
            let body_block = loop_body_block(&machine);
            let block_id = machine.block_order[body_block];
            let body = machine.blocks.get_mut(&block_id).unwrap();
            let (address, loaded, bumped) = (vreg(fresh), vreg(fresh + 1), vreg(fresh + 2));
            let at = O::MemAddr {
                base: Box::new(address.clone()),
                disp: 0,
            };
            let rows = vec![
                X86ISelInst::new(
                    X86Opcode::Lea,
                    vec![
                        address,
                        O::MemAddr {
                            base: Box::new(O::StackSlot(slot)),
                            disp: 0,
                        },
                    ],
                ),
                X86ISelInst::new(X86Opcode::MovRM, vec![loaded.clone(), at.clone()]),
                X86ISelInst::new(X86Opcode::AddRI, vec![bumped.clone(), loaded, O::Imm(1)]),
                X86ISelInst::new(X86Opcode::MovMR, vec![at, bumped]),
            ];
            for (k, row) in rows.into_iter().enumerate() {
                body.insts.insert(k, row);
            }
        }
        Wrong233::StoresInArm => {
            // Block 0's store into L, repeated with `y`'s register before
            // the first arm's jump.
            let slot = local_slot(&machine);
            let (block, row) = stores_into(&machine, slot)[0];
            let store = block_rows(&machine, block)[row].clone();
            let y = entry_copy_of(&machine, preg(trust_cg_ir::x86_64_regs::RSI.encoding()));
            let (arm, _) = brif233(&source, source.entry_block);
            let at = machine
                .block_order
                .iter()
                .copied()
                .find(|block| {
                    machine.blocks[block].insts.iter().any(|inst| {
                        inst.lowering_provenance
                            .source_id()
                            .is_some_and(|id| Block(id.block) == arm)
                    })
                })
                .unwrap_or_else(|| {
                    panic!("W6: no machine block of {arm:?}\n{}", describe(&machine))
                });
            let body = machine.blocks.get_mut(&at).unwrap();
            let end = body.insts.len() - 1;
            body.insts.insert(
                end,
                X86ISelInst::new(store.opcode, vec![store.operands[0].clone(), y]),
            );
        }
    }
    (source, machine)
}

/// The virtual register the entry block copies physical register `reg`
/// into (`MovRR v, reg`).
fn entry_copy_of(machine: &X86ISelFunction, reg: O) -> O {
    block_rows(machine, 0)
        .iter()
        .find(|inst| inst.opcode == X86Opcode::MovRR && inst.operands.get(1) == Some(&reg))
        .map(|inst| inst.operands[0].clone())
        .unwrap_or_else(|| panic!("no entry copy of {reg:?}\n{}", describe(machine)))
}

/// The address-taken local L of P1's family, P3, P5 and the controls:
/// every such fixture allocates it first, an 8-byte slot.
fn local_slot(machine: &X86ISelFunction) -> u32 {
    let size = machine.stack_slots.first().map(|slot| slot.size);
    assert_eq!(
        size,
        Some(8),
        "L is the first, 8-byte slot\n{}",
        describe(machine)
    );
    0
}

/// P1's compare of the forwarded L after Block 0 (block index, row, the
/// operand): the first `cmp` past Block 0 that reads the register Block 0
/// stores into L, or a register Block 0 copies it into (`mov d, s`).
fn forwarded_compare(machine: &X86ISelFunction) -> (usize, usize, usize) {
    let slot = local_slot(machine);
    let mut stored: Vec<O> = stores_into(machine, slot)
        .into_iter()
        .filter(|(block, _)| *block == 0)
        .map(|(block, row)| block_rows(machine, block)[row].operands[1].clone())
        .collect();
    loop {
        let copies: Vec<O> = block_rows(machine, 0)
            .iter()
            .filter(|inst| inst.opcode == X86Opcode::MovRR)
            .filter_map(|inst| match inst.operands.as_slice() {
                [dst @ O::VReg(_), src] if stored.contains(src) && !stored.contains(dst) => {
                    Some(dst.clone())
                }
                _ => None,
            })
            .collect();
        if copies.is_empty() {
            break;
        }
        stored.extend(copies);
    }
    for b in 1..machine.block_order.len() {
        for (i, inst) in block_rows(machine, b).iter().enumerate() {
            if inst.opcode == X86Opcode::CmpRR
                && let Some(k) = inst
                    .operands
                    .iter()
                    .position(|operand| stored.contains(operand))
            {
                return (b, i, k);
            }
        }
    }
    panic!("no compare of a forwarded register\n{}", describe(machine))
}

/// The machine block that loops back to an earlier block (the loop body).
fn loop_body_block(machine: &X86ISelFunction) -> usize {
    for (b, block) in machine.block_order.iter().enumerate() {
        for inst in &machine.blocks[block].insts {
            for operand in &inst.operands {
                if let O::Block(target) = operand
                    && let Some(t) = machine.block_order.iter().position(|x| x == target)
                    && t <= b
                    && b > 0
                {
                    return b;
                }
            }
        }
    }
    panic!("no back edge\n{}", describe(machine))
}

// ---- the shape of every fixture

/// Each fixture's machine stream has the shape it is for: P1's family one
/// store into L, in Block 0, and a later block comparing the register
/// stored there without reloading L; P3 no reload of L past Block 0 (the
/// call passes the forwarded address); V4 a reload past Block 0 (at the
/// join); the loops L written in the loop body only for V3; N1's cut at a
/// clean point. No fixture has a scaled-index load or store row.
#[test]
fn every_fixture_has_its_shape() {
    use Shape233::*;
    for shape in POSITIVE.into_iter().chain(CONTROLS) {
        let (source, machine) = od233_pair(shape);
        let context = || {
            format!(
                "{shape:?}\n{}\n{}",
                describe_lir(&source),
                describe(&machine)
            )
        };
        assert!(!has_sib_row(&machine), "{}", context());
        match shape {
            SymbolLocal | EarlierFreeItem => {
                let slot = local_slot(&machine);
                let reloaded = loads_from(&machine, slot)
                    .iter()
                    .any(|(block, _)| *block > 0);
                assert_eq!(
                    reloaded,
                    shape == EarlierFreeItem,
                    "L reloaded past Block 0: {}",
                    context()
                );
            }
            SymbolNoObservable => {
                let points = every_point(&source, &machine);
                for point in points233(shape, &source) {
                    assert!(
                        points.contains(&point),
                        "{point:?} is no clean point: {}",
                        context()
                    );
                }
            }
            Wtf8LenLocal | ComputedLenLocal | Wtf8LenDirect | MergedLenLocal => {
                if shape == MergedLenLocal {
                    assert!(
                        machine.block_order.len() < source.blocks.len(),
                        "a merged machine block: {}",
                        context()
                    );
                }
                let slot = local_slot(&machine);
                let stores = stores_into(&machine, slot);
                assert!(
                    stores.len() == 1 && stores[0].0 == 0,
                    "one store into L, in Block 0 ({stores:?}): {}",
                    context()
                );
                let (block, _, _) = forwarded_compare(&machine);
                assert!(
                    !loads_from(&machine, slot)
                        .iter()
                        .any(|(at, _)| *at == block),
                    "the compared block reloads L: {}",
                    context()
                );
            }
            SharedJoinLocal | SharedJoinDiffers => {
                // Block 0 stores L (and V9's arm again); only V9's C reloads
                // it (P8's C passes its address alone); every LIR block is a
                // machine block.
                let slot = local_slot(&machine);
                let stores: Vec<usize> = stores_into(&machine, slot)
                    .into_iter()
                    .map(|(block, _)| block)
                    .collect();
                assert_eq!(
                    stores.len(),
                    if shape == SharedJoinDiffers { 2 } else { 1 },
                    "the stores into L ({stores:?}): {}",
                    context()
                );
                assert_eq!(stores[0], 0, "{}", context());
                let loads = loads_from(&machine, slot);
                assert_eq!(
                    loads.len(),
                    usize::from(shape == SharedJoinDiffers),
                    "the loads of L ({loads:?}): {}",
                    context()
                );
                assert_eq!(
                    machine.block_order.len(),
                    source.blocks.len(),
                    "{}",
                    context()
                );
            }
            InvariantLocalAcrossHeader | LoopCarried => {
                let slot = local_slot(&machine);
                let body = loop_body_block(&machine);
                let writes_in_loop = stores_into(&machine, slot)
                    .iter()
                    .any(|(block, _)| *block == body);
                assert_eq!(
                    writes_in_loop,
                    shape == LoopCarried,
                    "L written in the loop: {}",
                    context()
                );
            }
            _ => {}
        }
    }
}

// ---- printers

fn print233(
    label: &str,
    source: &Function,
    machine: &X86ISelFunction,
    points: Vec<(Block, usize)>,
) {
    println!(
        "==== {label}\n{}\n{}",
        describe_lir(source),
        describe(machine)
    );
    let result = in_parts(source, machine, points.clone());
    println!(
        "points={points:?} parts={} result={} verdict={} digest={}",
        result
            .as_ref()
            .map(|owner| owner.parts().len())
            .unwrap_or(0),
        refusal_text233(&result),
        verdict233(&result),
        result.as_ref().map(statement_digest233).unwrap_or_default()
    );
    if let Ok(owner) = &result {
        for part in owner.parts() {
            println!(
                "  {} holds={}",
                part.name,
                super::slice9::dag_holds_on_samples(part)
            );
        }
        if std::env::var_os("TCG_OD233_PRINT_TEXT").is_some() {
            for part in owner.parts() {
                println!(";;;; {}\n{}", part.name, super::slice24::text(part));
            }
        }
    }
}

/// Print every fixture's LIR, machine stream and parts verdict.
#[test]
#[ignore = "printer"]
fn print_od233_fixtures() {
    for shape in POSITIVE.into_iter().chain(CONTROLS) {
        let (source, machine) = od233_pair(shape);
        print233(
            &format!("{} {shape:?}", shape.label()),
            &source,
            &machine,
            points233(shape, &source),
        );
    }
    for wrong in WRONG {
        let (source, machine) = wrong233(wrong);
        print233(
            &format!("{} {wrong:?}", wrong.label()),
            &source,
            &machine,
            points233(wrong.shape(), &source),
        );
        let result = owner233(wrong.shape(), &source, &machine);
        println!(
            "refuted={}",
            result
                .as_ref()
                .map(|owner| owner_refuted(owner))
                .unwrap_or(false)
        );
    }
}

// ---------------------------------------------------------------------------
// Controls (OD-233)
// ---------------------------------------------------------------------------

use super::super::quotient::mutant;
use super::slice16::{parts_hold_on_every_sampler, some_part_refuted};
use super::slice25::{Shape25, slice25_pair};

/// P6: slice 25's three slot fixtures, stated in parts at every point (an
/// `imul` of two constants is an item of a cut there, its term fixed for the
/// run).
pub(crate) const SLOT_FIXTURES: [Shape25; 3] = [
    Shape25::SlotConstU64,
    Shape25::SlotConstAcrossBlocks,
    Shape25::SlotStoreReloadU32,
];

/// A P6 fixture's owner, stated in parts at every point.
pub(crate) fn slot_owner<'a>(
    source: &'a Function,
    machine: &'a X86ISelFunction,
) -> Result<SourceBoundX86Body<'a>, X86BodyRefusal> {
    in_parts(source, machine, every_point(source, machine))
}

/// W5: SlotConstU64 with its `imul` by 8 made one by 16 (a labelled hand
/// edit of the real stream).
pub(crate) fn slot_wrong() -> (Function, X86ISelFunction) {
    let (source, mut machine) = slice25_pair(Shape25::SlotConstU64);
    let mut edited = 0;
    for block in machine.block_order.clone() {
        for inst in &mut machine.blocks.get_mut(&block).unwrap().insts {
            if inst.opcode == X86Opcode::ImulRRI && inst.operands.get(2) == Some(&O::Imm(8)) {
                inst.operands[2] = O::Imm(16);
                edited += 1;
            }
        }
    }
    assert!(edited > 0, "W5: no imul by 8\n{}", describe(&machine));
    (source, machine)
}

/// The eleven decompositions slice 25's fails-before record (on 6c036f1de,
/// `fails-before5.log`) found refuted in parts: each fixture's scaled-index
/// rows split into the earlier slices' `lea; mov [t]` rows
/// (`slice25::decompose`), cut at the fused stream's every point.
pub(crate) const REFUTED_DECOMPOSITIONS: [Shape25; 11] = [
    Shape25::U64Index,
    Shape25::U32Index,
    Shape25::FieldDispU32,
    Shape25::StoreU32,
    Shape25::StoreU64,
    Shape25::F64Index,
    Shape25::F32Index,
    Shape25::ByteMerge,
    Shape25::SlotConstU64,
    Shape25::SlotConstAcrossBlocks,
    Shape25::SlotStoreReloadU32,
];

/// One statement in parts at `points` under the mutants `names` (`""`:
/// none): each part's verdict on slice 9's keyed samples, the defined
/// inputs and the statement's digest; or the refusal's text.
type Judged = Result<(Vec<bool>, (usize, usize), String), String>;

fn judged(
    names: &str,
    source: &Function,
    machine: &X86ISelFunction,
    points: &[(Block, usize)],
) -> Judged {
    let _mutant = mutant::set(names);
    match in_parts(source, machine, points.to_vec()) {
        Ok(owner) => Ok((
            owner
                .parts()
                .iter()
                .map(super::slice9::dag_holds_on_samples)
                .collect(),
            owner.defined_cut_inputs(),
            statement_digest233(&owner),
        )),
        Err(refusal) => Err(refusal.to_string()),
    }
}

/// Every subject of this module: label, pair and points (P1-P5, P7 and the
/// controls at their points, the wrong lowerings at their fixture's, P6 and
/// W5 at every point).
/// A named source/machine fixture and the source points where it is cut.
type CutSubject233 = (String, Function, X86ISelFunction, Vec<(Block, usize)>);

fn subjects233() -> Vec<CutSubject233> {
    let mut subjects = Vec::new();
    for shape in POSITIVE.into_iter().chain(CONTROLS) {
        let (source, machine) = od233_pair(shape);
        let points = points233(shape, &source);
        subjects.push((
            format!("{} {shape:?}", shape.label()),
            source,
            machine,
            points,
        ));
    }
    for wrong in WRONG {
        let (source, machine) = wrong233(wrong);
        let points = points233(wrong.shape(), &source);
        subjects.push((
            format!("{} {wrong:?}", wrong.label()),
            source,
            machine,
            points,
        ));
    }
    for shape in SLOT_FIXTURES {
        let (source, machine) = slice25_pair(shape);
        let points = every_point(&source, &machine);
        subjects.push((format!("P6 {shape:?}"), source, machine, points));
    }
    let (source, machine) = slot_wrong();
    let points = every_point(&source, &machine);
    subjects.push(("W5 SlotConstU64 imul by 16".into(), source, machine, points));
    subjects
}

/// Print every subject with the rule and without it (`od233-off`), the
/// eleven decompositions, and the parts of two statements the rule re-cuts
/// (P7 and slice 25's FieldU32 at every point; their claims, cut at 600
/// characters).
#[test]
#[ignore = "printer"]
fn print_od233_with_and_without_the_rule() {
    let recut = [
        (
            "P7 NarrowReadBack".to_string(),
            od233_pair(Shape233::NarrowReadBack),
        ),
        (
            "s25 FieldU32".to_string(),
            slice25_pair(super::slice25::Shape25::FieldU32),
        ),
    ];
    for (label, (source, machine)) in &recut {
        let points = every_point(source, machine);
        for names in ["od233-off", ""] {
            let _mutant = mutant::set(names);
            let Ok(owner) = in_parts(source, machine, points.clone()) else {
                println!("OD233_RECUT {label} mutants={names:?} refused");
                continue;
            };
            println!(
                "OD233_RECUT {label} mutants={names:?} parts={} regions={:?} defined={:?} defined_names={:?}",
                owner.parts().len(),
                owner.shared_parts().region_claims(),
                owner.defined_cut_inputs(),
                defined_in(owner.obligation())
                    .into_iter()
                    .map(|(name, _)| name)
                    .collect::<Vec<_>>()
            );
            for part in owner.parts() {
                let claims = format!("{}", part.aarch64_expr);
                println!(
                    "  {} holds={} premises={} claims={}",
                    part.name,
                    super::slice9::dag_holds_on_samples(part),
                    part.preconditions.len(),
                    &claims[..claims.len().min(600)]
                );
                println!(";;;; {}\n{}", part.name, super::slice24::text(part));
            }
            println!(
                ";;;; statement\n{}",
                super::slice24::text(owner.obligation())
            );
        }
    }
    for (label, source, machine, points) in subjects233() {
        let off = judged("od233-off", &source, &machine, &points);
        let on = judged("", &source, &machine, &points);
        println!("OD233_COMPARE subject={label} points={points:?}\n  off={off:?}\n  on={on:?}");
        if let Ok(owner) = in_parts(&source, &machine, points.clone())
            && std::env::var_os("TCG_OD233_PRINT_TEXT").is_some()
        {
            println!(
                ";;;; statement\n{}",
                super::slice24::text(owner.obligation())
            );
        }
    }
    for shape in REFUTED_DECOMPOSITIONS {
        let (source, machine) = slice25_pair(shape);
        let decomposed = super::slice25::decompose(&machine, false);
        let points = every_point(&source, &machine);
        let off = judged("od233-off", &source, &decomposed, &points);
        let on = judged("", &source, &decomposed, &points);
        println!("OD233_DECOMPOSED shape={shape:?} points={points:?}\n  off={off:?}\n  on={on:?}");
        if std::env::var_os("TCG_OD233_PRINT_TEXT").is_some()
            && let Ok(owner) = in_parts(&source, &decomposed, points.clone())
        {
            println!("{}", describe(&decomposed));
            for part in owner.parts() {
                println!(";;;; {}\n{}", part.name, super::slice24::text(part));
            }
        }
    }
}

/// Every positive fixture (P1-P5, P7) is stated in parts at its points,
/// every part holding on every sampler and its inventory checking, with
/// the inputs it is for defined: bytes of L for P1, P2, P3, P5 and P7, a
/// value item for P4, nothing for P1b (L's bytes are closed there, and its
/// statement is the one without the rule); and P6.
#[test]
fn every_positive_fixture_holds_in_parts() {
    use Shape233::*;
    for shape in POSITIVE {
        let (source, machine) = od233_pair(shape);
        let owner = owner233(shape, &source, &machine)
            .unwrap_or_else(|refusal| panic!("{shape:?}: {refusal}\n{}", describe(&machine)));
        assert!(owner.is_stated_in_parts(), "{shape:?}");
        owner
            .check_parts()
            .unwrap_or_else(|why| panic!("{shape:?}: the inventory: {why}"));
        parts_hold_on_every_sampler(&owner)
            .unwrap_or_else(|why| panic!("{shape:?}: {why}\n{}", describe(&machine)));
        let (bytes, items) = owner.defined_cut_inputs();
        let names: Vec<String> = defined_in(owner.obligation())
            .into_iter()
            .map(|(name, _)| name)
            .collect();
        eprintln!(
            "OD233_HOLDS {shape:?} defined={:?} names={names:?}",
            (bytes, items)
        );
        match shape {
            Wtf8LenDirect => {
                assert_eq!((bytes, items), (0, 0), "{shape:?}");
                // L's bytes are closed: no cut-input byte is declared at all.
                let declared: Vec<&String> = owner
                    .obligation()
                    .inputs
                    .iter()
                    .map(|(name, _)| name)
                    .filter(|name| is_header_input(name))
                    .collect();
                assert!(declared.is_empty(), "{shape:?}: cut inputs {declared:?}");
                let points = points233(shape, &source);
                assert_eq!(
                    judged("", &source, &machine, &points).map(|(_, _, digest)| digest),
                    judged("od233-off", &source, &machine, &points).map(|(_, _, digest)| digest),
                    "{shape:?}: the statement moved"
                );
            }
            CommonCutParam => assert!(items > 0, "{shape:?}: no item defined"),
            MergedLenLocal | SharedJoinLocal => {
                let l = format!("b{}o", local_slot(&machine));
                assert!(
                    names.iter().any(|name| name.contains(&l)),
                    "{shape:?}: no byte of L defined: {names:?}"
                );
                if shape == MergedLenLocal {
                    // Stated over the merged-chain quotient.
                    assert!(
                        owner.merged_chains().is_some(),
                        "{shape:?}: stated over the original pair"
                    );
                } else {
                    // Two regions state one block's edge into C, each claiming
                    // L's defined bytes there.
                    let record = owner.definition_record();
                    assert!(
                        shared_edges(record) > 0,
                        "{shape:?}: no edge stated in two regions: {:?}",
                        record.stated_edges
                    );
                }
            }
            _ => {
                let l = format!("b{}o", local_slot(&machine));
                assert!(
                    names.iter().any(|name| name.contains(&l)),
                    "{shape:?}: no byte of L defined: {names:?}"
                );
            }
        }
    }
    for shape in SLOT_FIXTURES {
        let (source, machine) = slice25_pair(shape);
        let owner =
            slot_owner(&source, &machine).unwrap_or_else(|refusal| panic!("{shape:?}: {refusal}"));
        owner
            .check_parts()
            .unwrap_or_else(|why| panic!("{shape:?}: the inventory: {why}"));
        parts_hold_on_every_sampler(&owner).unwrap_or_else(|why| panic!("P6 {shape:?}: {why}"));
        eprintln!(
            "OD233_HOLDS P6 {shape:?} defined={:?}",
            owner.defined_cut_inputs()
        );
    }
}

/// Every wrong lowering (W1-W6) stated in parts is refuted on the samples
/// (or named a mismatch), never holding.
#[test]
fn every_wrong_lowering_is_refuted_in_parts() {
    let mut cases: Vec<CutSubject233> = WRONG
        .into_iter()
        .map(|wrong| {
            let (source, machine) = wrong233(wrong);
            let points = points233(wrong.shape(), &source);
            (
                format!("{} {wrong:?}", wrong.label()),
                source,
                machine,
                points,
            )
        })
        .collect();
    let (source, machine) = slot_wrong();
    let points = every_point(&source, &machine);
    cases.push(("W5".into(), source, machine, points));
    for (label, source, machine, points) in cases {
        match in_parts(&source, &machine, points) {
            Ok(owner) => {
                let refuted: Vec<usize> = owner
                    .parts()
                    .iter()
                    .enumerate()
                    .filter(|(_, part)| super::slice9::dag_refuted_on_samples(part))
                    .map(|(k, _)| k + 1)
                    .collect();
                eprintln!(
                    "OD233_WRONG {label} refuted_parts={refuted:?} defined={:?}",
                    owner.defined_cut_inputs()
                );
                assert!(
                    some_part_refuted(&owner),
                    "{label}: a wrong lowering holds in parts"
                );
            }
            Err(X86BodyRefusal::Mismatch(mismatch)) => {
                eprintln!("OD233_WRONG {label} mismatch={mismatch}")
            }
            Err(refusal) => panic!("{label}: refused ({refusal})"),
        }
    }
}

/// The free-input and refusal controls (V1-V9, V2b, N1; design §5.4) state
/// exactly what they state without the rule (`od233-off`): no input
/// defined, the same statement digest and verdict, or the same refusal (N1:
/// NoObservable); and each control's candidate inputs ([`candidates233`])
/// are still inputs of its cut, declared and not defined, so a pass change
/// that removes a candidate fails by name.
#[test]
fn every_free_input_control_keeps_its_statement() {
    for shape in CONTROLS {
        if shape == Shape233::TwoPredecessors {
            // W3's source, not a control: L is defined at its panic block.
            continue;
        }
        let (source, machine) = od233_pair(shape);
        let points = points233(shape, &source);
        let off = judged("od233-off", &source, &machine, &points);
        let on = judged("", &source, &machine, &points);
        eprintln!("OD233_CONTROL {} {shape:?} on={on:?}", shape.label());
        assert_eq!(on, off, "{shape:?}: the statement moved");
        match &on {
            Ok((_, defined, _)) => assert_eq!(*defined, (0, 0), "{shape:?}"),
            Err(refusal) if shape == Shape233::SymbolNoObservable => {
                assert!(refusal.contains(NO_OBSERVABLE), "{shape:?}: {refusal}")
            }
            Err(refusal) => panic!("{shape:?} is refused: {refusal}"),
        }
        // The input the control is for is still a cut input, declared free.
        let owner = owner233(shape, &source, &machine);
        if let Ok(owner) = &owner {
            let declared: HashSet<&str> = owner
                .obligation()
                .inputs
                .iter()
                .map(|(name, _)| name.as_str())
                .collect();
            let defined: HashSet<String> = defined_in(owner.obligation())
                .into_iter()
                .map(|(name, _)| name)
                .collect();
            for name in candidates233(shape, &source) {
                assert!(
                    declared.contains(name.as_str()) && !defined.contains(&name),
                    "{shape:?}: {name} is no free cut input: {declared:?}"
                );
            }
            if shape == Shape233::SharedJoinDiffers {
                assert!(
                    shared_edges(owner.definition_record()) > 0,
                    "{shape:?}: no edge stated in two regions"
                );
            }
        }
    }
}

/// The cut inputs each free-input control is for (V1-V9, V2b), which must
/// stay free: L's eight bytes at the cut its stores reach, V4's earlier free
/// item too, V7's two `I128` halves, V8's call result.
fn candidates233(shape: Shape233, source: &Function) -> Vec<String> {
    use Shape233::*;
    let bytes = |cut: u32| (0..8).map(move |offset| format!("x{cut}b0o{offset}"));
    let c = || {
        let (arm, _) = brif233(source, source.entry_block);
        brif233(source, jump233(source, arm)).0.0
    };
    match shape {
        PathsDiffer => bytes(3).collect(),
        CallAfterStore | MayAliasStore | LoopCarried => bytes(1).collect(),
        EarlierFreeItem => bytes(4).chain(["x1v0".to_string()]).collect(),
        TaintedStore | OverSixtyFour => bytes(2).collect(),
        WideItem => vec!["x1v0h".into(), "x1v0l".into()],
        CallInLoop => vec!["x1v2".into()],
        SharedJoinDiffers => bytes(c()).collect(),
        _ => Vec::new(),
    }
}

/// How many `(from, cut)` pairs a statement's record states in more than one
/// region (a block two regions hold, entering a later cut).
fn shared_edges(record: &super::super::split::DefinitionRecord) -> usize {
    let mut regions: HashMap<(Block, Block), HashSet<usize>> = HashMap::new();
    for (region, from, cut) in &record.stated_edges {
        regions.entry((*from, *cut)).or_default().insert(*region);
    }
    regions.values().filter(|regions| regions.len() > 1).count()
}

// ---- the statement's shape

/// The cut inputs a statement defines: each premise that defines a cut
/// interface's name (`x{C}v{i}`, `x{C}b{s}o{o}`), in definition order.
fn defined_in(obligation: &ProofObligation) -> Vec<(String, E)> {
    obligation
        .preconditions
        .iter()
        .rev()
        .filter_map(|premise| match premise {
            E::Eq { lhs, rhs } => match lhs.as_ref() {
                E::Var { name, .. } if is_header_input(name) => {
                    Some((name.clone(), rhs.as_ref().clone()))
                }
                _ => None,
            },
            _ => None,
        })
        .collect()
}

/// How many equations of `expr` claim `name` equal to a term: `(= t name)`,
/// OD-233's claim on a cut edge.
fn claims_of(expr: &E, name: &str) -> usize {
    let mut count = 0;
    let mut stack = vec![expr];
    while let Some(node) = stack.pop() {
        if let E::Eq { rhs, .. } = node
            && matches!(rhs.as_ref(), E::Var { name: var, .. } if var == name)
        {
            count += 1;
        }
        node.for_each_child(&mut |child| stack.push(child));
    }
    count
}

/// Design §5.5's statement audit, over every subject that defines a cut
/// input: each definition is a premise naming only the run's fixed inputs
/// (no slot address) and is declared once; each defined name is considered
/// exactly once on EVERY stated edge into its cut (`(region, from, cut)`:
/// a block two regions hold is two stated edges, so a cut may have more
/// stated edges than predecessors), claimed on at least one, and each claim
/// the record makes is a subterm of the statement; and every premise
/// defines a fresh name from earlier ones only (the statement's own check,
/// re-run on every part).
#[test]
fn every_definition_is_fixed_for_the_run_and_claimed_on_its_edges() {
    let mut audited = 0;
    for (label, source, machine, points) in subjects233() {
        let Ok(owner) = in_parts(&source, &machine, points) else {
            continue;
        };
        let (bytes, items) = owner.defined_cut_inputs();
        let obligation = owner.obligation();
        let defined = defined_in(obligation);
        if bytes + items == 0 {
            assert!(
                defined.is_empty(),
                "{label}: a definition with no defined input: {defined:?}"
            );
            continue;
        }
        audited += 1;
        owner
            .check_parts()
            .unwrap_or_else(|why| panic!("{label}: the inventory: {why}"));
        eprintln!(
            "OD233_AUDIT {label} defined={:?} premises={}",
            (bytes, items),
            defined.len()
        );
        for (name, term) in &defined {
            for used in term.free_vars() {
                assert!(
                    super::super::split::fixed_for_the_run(&used)
                        && parse_slot_address_name(&used).is_none(),
                    "{label}: {name} names {used}"
                );
            }
            assert_eq!(
                obligation
                    .inputs
                    .iter()
                    .filter(|(input, _)| input == name)
                    .count(),
                1,
                "{label}: {name} is declared once"
            );
            let claims = claims_of(&obligation.aarch64_expr, name)
                + claims_of(&obligation.trust_ir_expr, name);
            // The record: every stated edge into the cut considers the name
            // once; each claim it makes is in the statement.
            let record = owner.definition_record();
            let cut = Block(
                name[1..]
                    .chars()
                    .take_while(char::is_ascii_digit)
                    .collect::<String>()
                    .parse()
                    .expect("a cut input name"),
            );
            let edges: Vec<&(usize, Block, Block)> = record
                .stated_edges
                .iter()
                .filter(|(_, _, into)| *into == cut)
                .collect();
            assert!(!edges.is_empty(), "{label}: no stated edge into {cut:?}");
            let mut stated = 0;
            for (region, from, into) in &edges {
                let considered: Vec<&Option<E>> = record
                    .claims
                    .iter()
                    .filter(|(r, f, c, n, _)| r == region && f == from && c == into && n == name)
                    .map(|(_, _, _, _, claim)| claim)
                    .collect();
                assert_eq!(
                    considered.len(),
                    1,
                    "{label}: {name} on the edge from {from:?} in region {region}"
                );
                if let Some(claim) = considered[0] {
                    stated += 1;
                    assert!(
                        contains_term(&obligation.aarch64_expr, claim),
                        "{label}: {name}'s claim {claim} is not in the statement"
                    );
                }
            }
            eprintln!(
                "OD233_AUDIT {label} {name} claims={claims} stated_edges={} stated_claims={stated}",
                edges.len()
            );
            assert!(stated > 0, "{label}: {name} is claimed on no edge");
            assert!(stated <= edges.len(), "{label}: {name}");
        }
    }
    assert!(audited > 0, "no subject defines a cut input");
}

/// Whether `term` is a subterm of `expr`.
fn contains_term(expr: &E, term: &E) -> bool {
    let mut stack = vec![expr];
    while let Some(node) = stack.pop() {
        if node == term {
            return true;
        }
        node.for_each_child(&mut |child| stack.push(child));
    }
    false
}

// ---- mutants (design §5.7)

/// A control of the mutant campaign.
#[derive(Debug, Clone, Copy)]
enum Control233 {
    /// The fixture is stated in parts at its points, every part holding.
    Holds(Shape233),
    /// The P6 fixture is stated in parts at every point, every part holding.
    HoldsSlot(Shape25),
    /// The fixture is refused with this text (a part of its refusal).
    Refused(Shape233, &'static str),
    /// Control F: with every positive fixture's first defined byte forged
    /// (`od233-forge`), none that defines a byte holds.
    ForgeNeverHolds,
    /// Control F for items: with the first defined item forged in the choice
    /// (`od233-forge-item`), no positive or P6 fixture that defines an item
    /// holds.
    ForgeItemNeverHolds,
}

fn run_control233(control: Control233) -> Result<(), String> {
    match control {
        Control233::Holds(shape) => {
            let (source, machine) = od233_pair(shape);
            let owner =
                owner233(shape, &source, &machine).map_err(|refusal| refusal.to_string())?;
            owner_holds(&owner)
        }
        Control233::HoldsSlot(shape) => {
            let (source, machine) = slice25_pair(shape);
            let owner = slot_owner(&source, &machine).map_err(|refusal| refusal.to_string())?;
            owner_holds(&owner)
        }
        Control233::ForgeItemNeverHolds => {
            let active = mutant::active();
            let _forge = mutant::set(&format!("{active},od233-forge-item"));
            let mut forged = 0;
            let mut pairs: Vec<CutSubject233> = Vec::new();
            for shape in POSITIVE {
                let (source, machine) = od233_pair(shape);
                let points = points233(shape, &source);
                pairs.push((format!("{shape:?}"), source, machine, points));
            }
            for shape in SLOT_FIXTURES {
                let (source, machine) = slice25_pair(shape);
                let points = every_point(&source, &machine);
                pairs.push((format!("P6 {shape:?}"), source, machine, points));
            }
            for (label, source, machine, points) in pairs {
                let Ok(owner) = in_parts(&source, &machine, points) else {
                    continue;
                };
                if owner.defined_cut_inputs().1 == 0 {
                    continue;
                }
                forged += 1;
                if owner_holds(&owner).is_ok() {
                    return Err(format!("{label} holds with a forged item"));
                }
            }
            if forged == 0 {
                return Err("no positive fixture defines an item".into());
            }
            Ok(())
        }
        Control233::Refused(shape, needle) => {
            let (source, machine) = od233_pair(shape);
            match owner233(shape, &source, &machine) {
                Ok(_) => Err(format!("{shape:?} is stated")),
                Err(refusal) if refusal.to_string().contains(needle) => Ok(()),
                Err(refusal) => Err(format!("{shape:?} refused otherwise: {refusal}")),
            }
        }
        Control233::ForgeNeverHolds => {
            let active = mutant::active();
            let _forge = mutant::set(&format!("{active},od233-forge"));
            let mut forged = 0;
            for shape in POSITIVE {
                let (source, machine) = od233_pair(shape);
                let Ok(owner) = owner233(shape, &source, &machine) else {
                    continue;
                };
                if owner.defined_cut_inputs().0 == 0 {
                    continue;
                }
                forged += 1;
                if owner_holds(&owner).is_ok() {
                    return Err(format!("{shape:?} holds with a forged definition"));
                }
            }
            if forged == 0 {
                return Err("no positive fixture defines a byte".into());
            }
            Ok(())
        }
    }
}

/// `control` under the mutants `names` on this thread; a panic is a failed
/// control.
fn under233(names: &str, control: Control233) -> Result<(), String> {
    let _mutant = mutant::set(names);
    std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| run_control233(control)))
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

/// The NoObservable refusal's text.
const NO_OBSERVABLE: &str = "the body has no value observable";

/// A part refuted on samples (the text of [`owner_holds`]'s failure).
const REFUTED: &str = "is refuted on samples";

/// K1's refusal text.
const K1: &str = "is defined by a term that is not fixed for the run (OD-233)";

/// K2's refusal text.
const K2: &str = "is not claimed on the edge from";

/// Design §5.7: each OD-233 mutant and the controls it must break, each
/// with the text its failure must hold (so a kill from another cause, or a
/// reworded refusal, fails the campaign by name).
const MUTANTS233: &[(&str, &[(Control233, &str)])] = &[
    (
        "od233-off",
        &[(Control233::Holds(Shape233::Wtf8LenLocal), REFUTED)],
    ),
    (
        "od233-forge",
        &[(Control233::Holds(Shape233::Wtf8LenLocal), REFUTED)],
    ),
    (
        "od233-forge-byte",
        &[(Control233::Holds(Shape233::Wtf8LenLocal), REFUTED)],
    ),
    (
        "od233-forge-item",
        &[
            (Control233::Holds(Shape233::CommonCutParam), REFUTED),
            (Control233::HoldsSlot(Shape25::SlotConstU64), REFUTED),
        ],
    ),
    (
        "od233-no-claim",
        &[(Control233::Holds(Shape233::Wtf8LenLocal), K2)],
    ),
    (
        "od233-drop-repeat-claim",
        &[(Control233::Holds(Shape233::SharedJoinLocal), K2)],
    ),
    (
        "od233-no-claim-no-k2",
        &[
            (
                Control233::ForgeNeverHolds,
                "holds with a forged definition",
            ),
            (Control233::ForgeItemNeverHolds, "holds with a forged item"),
        ],
    ),
    (
        "od233-first-edge",
        &[(Control233::Holds(Shape233::PathsDiffer), REFUTED)],
    ),
    (
        "od233-no-shrink",
        &[(Control233::Holds(Shape233::LoopCarried), REFUTED)],
    ),
    (
        "od233-any-name",
        &[(Control233::Holds(Shape233::CallInLoop), K1)],
    ),
    (
        "od233-observable",
        &[(
            Control233::Refused(Shape233::SymbolNoObservable, NO_OBSERVABLE),
            "SymbolNoObservable is stated",
        )],
    ),
    (
        "od233-free",
        &[(
            Control233::Holds(Shape233::Wtf8LenLocal),
            "premise constrains the free input",
        )],
    ),
    (
        "od233-late",
        &[(
            Control233::Holds(Shape233::Wtf8LenLocal),
            "before its definition",
        )],
    ),
];

/// Every control passes without a mutant, and each mutant makes EVERY one
/// of its controls fail, each failure holding its text.
#[test]
fn every_od233_mutant_fails_a_control() {
    let mut survived = Vec::new();
    for (names, controls) in MUTANTS233 {
        for (control, needle) in *controls {
            under233("", *control)
                .unwrap_or_else(|why| panic!("control {control:?} fails unmutated: {why}"));
            match under233(names, *control) {
                Ok(()) => survived.push(format!("{names} survived {control:?}")),
                Err(why) => {
                    eprintln!("OD233_MUTANT mutant={names} control={control:?} failed: {why}");
                    if !why.contains(needle) {
                        survived.push(format!(
                            "{names} failed {control:?} without {needle:?}: {why}"
                        ));
                    }
                }
            }
        }
    }
    assert!(survived.is_empty(), "{}", survived.join("\n"));
}

/// K2 is checked per stated edge `(region, from, cut)`: P8's join is in two
/// regions, so its edge into C is stated twice. Dropping the claims on the
/// second (`od233-drop-repeat-claim`) is refused by K2 by name; checked by
/// block and cut alone (`od233-k2-by-pair`, the keying before review), the
/// same drop passes K2 and the statement holds, the claim on that edge
/// missing: the region keying is what refuses it.
#[test]
fn k2_is_checked_for_each_region_s_stated_edge() {
    let shape = Shape233::SharedJoinLocal;
    let refused = under233("od233-drop-repeat-claim", Control233::Holds(shape));
    eprintln!("OD233_K2 region keying: {refused:?}");
    assert!(
        refused
            .as_ref()
            .is_err_and(|why| why.contains(K2) && why.contains(" in region ")),
        "{refused:?}"
    );
    let by_pair = under233(
        "od233-k2-by-pair,od233-drop-repeat-claim",
        Control233::Holds(shape),
    );
    eprintln!("OD233_K2 by block and cut alone: {by_pair:?}");
    assert!(by_pair.is_ok(), "{by_pair:?}");
}

// ---- OD-182's sweeps and the goldens (design §5.5)

/// Every fixture of slices 1 to 25 (slice 24a's and 25's included) and of
/// this module: label and pair.
fn every_fixture() -> Vec<(String, Function, X86ISelFunction)> {
    let mut fixtures = super::slice16::earlier_fixtures();
    fixtures.extend(super::slice24::later_fixtures());
    for shape in super::slice24::SLICE_TWENTY_FOUR {
        let (source, machine) = super::slice24::slice24_pair(shape);
        fixtures.push((format!("s24 {shape:?}"), source, machine));
    }
    for shape in super::slice25::SLICE_TWENTY_FIVE {
        let (source, machine) = slice25_pair(shape);
        fixtures.push((format!("s25 {shape:?}"), source, machine));
    }
    for shape in POSITIVE.into_iter().chain(CONTROLS) {
        let (source, machine) = od233_pair(shape);
        fixtures.push((
            format!("od233 {} {shape:?}", shape.label()),
            source,
            machine,
        ));
    }
    fixtures
}

/// OD-182's sweeps with the rule and without it (`od233-off`): every
/// fixture of slices 1 to 25 and of this module, cut at every block start
/// and at every clean point. A statement that defines nothing is the one
/// without the rule (its digest); one that defines an input is judged
/// region by region ([`region_verdicts`]), and no region that holds without
/// the rule stops holding with it. No statement is refused with the rule
/// that is stated without it, or refused otherwise. Every region that holds
/// only with the rule is listed with its fixture's defined inputs, and so
/// is every statement whose parts the spelling cuts otherwise, with how it
/// is spelled ([`Spelling233`]) both ways. Printed, not asserted: every
/// statement's digests both ways (`OD233_SWEEP_DIGEST`, which the report
/// compares with the same fixtures' digests at slice 25's base), every
/// statement that defines an input with whether it is stated over the
/// merged-chain quotient, the most distinct claims a part has against the
/// claim split's bound, and how many statements a candidate tainted input
/// would change (`od233-taint`, a measurement of whether the taint
/// exclusion is reached).
#[test]
fn defined_cut_inputs_never_stop_a_part_holding() {
    let mut defects = Vec::new();
    let mut newly = Vec::new();
    let mut recut = Vec::new();
    let (mut compared, mut defining) = (0usize, 0usize);
    let (mut quotient, mut quotient_defining) = (0usize, 0usize);
    let (mut most_with, mut most_without) = (0usize, 0usize);
    let mut tainted = Vec::new();
    for (label, source, machine) in every_fixture() {
        for (cut, points) in [
            ("every block", super::slice16::every_block(&source)),
            ("every point", every_point(&source, &machine)),
        ] {
            let off = stated233("od233-off", &source, &machine, &points, true);
            let on = stated233("", &source, &machine, &points, true);
            let taint = stated233("od233-taint", &source, &machine, &points, false);
            compared += 1;
            let text = |stated: &Result<Stated233, String>| match stated {
                Ok(stated) => stated.digest.clone(),
                Err(refusal) => format!("refused: {refusal}"),
            };
            eprintln!(
                "OD233_SWEEP_DIGEST\t{label}\t{cut}\toff={}\ton={}\tdefined={:?}\tmerged={:?}",
                text(&off),
                text(&on),
                on.as_ref().map(|on| on.defined).unwrap_or_default(),
                on.as_ref().ok().and_then(|on| on.merged)
            );
            if text(&taint) != text(&on) {
                tainted.push(format!("{label} at {cut}"));
            }
            if let Ok(stated) = &off {
                most_without = most_without.max(stated.spelling.most_claims);
            }
            if let Ok(stated) = &on {
                most_with = most_with.max(stated.spelling.most_claims);
                if stated.merged.is_some() {
                    quotient += 1;
                }
            }
            match (&off, &on) {
                (Ok(off), Ok(on)) => {
                    let (before, after, defined) = (&off.holds, &on.holds, on.defined);
                    // With nothing defined the statement is the one without
                    // the rule, and so is every verdict.
                    if defined == (0, 0) {
                        if off.digest != on.digest {
                            defects.push(format!(
                                "{label} at {cut}: the statement moved with nothing defined"
                            ));
                        }
                        continue;
                    }
                    defining += 1;
                    if on.merged.is_some() {
                        quotient_defining += 1;
                    }
                    eprintln!(
                        "OD233_SWEEP defining: {label} at {cut}: defined bytes={} items={} \
                         merged={:?} parts={} (without {}) {}",
                        defined.0,
                        defined.1,
                        on.merged,
                        after.len(),
                        before.len(),
                        on.spelling
                    );
                    // Judged region by region: the spelling may cut the parts
                    // otherwise (a region whose claims all became identities
                    // is no part; one whose definition claim the spelling
                    // keeps is one).
                    let off_regions = regions233("od233-off", &source, &machine, &points);
                    let on_regions = regions233("", &source, &machine, &points);
                    if off_regions.len() != on_regions.len() {
                        defects.push(format!(
                            "{label} at {cut}: {} regions became {}",
                            off_regions.len(),
                            on_regions.len()
                        ));
                        continue;
                    }
                    for (r, (held, holds)) in off_regions.iter().zip(&on_regions).enumerate() {
                        if *held && !holds {
                            defects
                                .push(format!("{label} at {cut}: region {} stops holding", r + 1));
                        }
                        if !held && *holds {
                            newly.push(format!(
                                "{label} at {cut}: region {} of {} (defined bytes={} items={})",
                                r + 1,
                                on_regions.len(),
                                defined.0,
                                defined.1
                            ));
                        }
                    }
                    if before.len() != after.len() {
                        recut.push(format!(
                            "{label} at {cut}: {} parts became {} (defined bytes={} items={}; refuted parts {} became {}); without the rule {}; with it {}",
                            before.len(),
                            after.len(),
                            defined.0,
                            defined.1,
                            before.iter().filter(|held| !**held).count(),
                            after.iter().filter(|holds| !**holds).count(),
                            off.spelling,
                            on.spelling
                        ));
                    }
                }
                (Ok(_), Err(refusal)) => {
                    defects.push(format!(
                        "{label} at {cut}: refused with the rule: {refusal}"
                    ));
                }
                (Err(_), Ok(on)) => {
                    for (k, holds) in on.holds.iter().enumerate() {
                        if *holds {
                            newly.push(format!(
                                "{label} at {cut}: part {} of {} of a statement refused without the rule (defined bytes={} items={})",
                                k + 1,
                                on.holds.len(),
                                on.defined.0,
                                on.defined.1
                            ));
                        }
                    }
                }
                (Err(before), Err(after)) => {
                    if before != after {
                        defects.push(format!(
                            "{label} at {cut}: refused otherwise: {before} became {after}"
                        ));
                    }
                }
            }
        }
    }
    eprintln!(
        "OD233_SWEEP compared={compared} defining={defining} newly_holding={} recut={}",
        newly.len(),
        recut.len()
    );
    eprintln!(
        "OD233_SWEEP quotient stated={quotient} defining={quotient_defining}; most distinct \
         claims in one part: {most_with} with the rule, {most_without} without (a claim split \
         states at most {}); a tainted candidate changes {} statements",
        super::super::split::MAX_CLAIM_PARTS,
        tainted.len()
    );
    for line in &newly {
        eprintln!("OD233_SWEEP newly holding: {line}");
    }
    for line in &recut {
        eprintln!("OD233_SWEEP re-cut: {line}");
    }
    for line in &tainted {
        eprintln!("OD233_SWEEP tainted candidate changes: {line}");
    }
    assert!(defects.is_empty(), "{}", defects.join("\n"));
}

/// How a statement in parts is spelled: its parts; whether every region
/// with a claim is stated plainly (each part its region's claims as the
/// statement has them: slice 9's rule when every region's spelled claims
/// drop); the most distinct claims one part has (a claim split states at
/// most `split::MAX_CLAIM_PARTS`) and how many parts have more; and how many
/// parts still hold an OD-233 definition claim, an equation whose right
/// side is a defined cut input's name.
struct Spelling233 {
    parts: usize,
    plain: bool,
    most_claims: usize,
    over_bound: usize,
    with_definition_claims: usize,
}

impl std::fmt::Display for Spelling233 {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "[parts={} plain={} most_claims={} over_bound={} with_definition_claims={}]",
            self.parts, self.plain, self.most_claims, self.over_bound, self.with_definition_claims
        )
    }
}

fn spelling233(owner: &SourceBoundX86Body<'_>) -> Spelling233 {
    let statement = owner.obligation();
    let regions = owner.shared_parts().region_claims().to_vec();
    let total: usize = regions.iter().sum();
    let mut claims: Vec<E> = Vec::with_capacity(total);
    let mut rest = &statement.aarch64_expr;
    for _ in 1..total {
        let E::And { lhs, rhs } = rest else {
            break;
        };
        claims.push(lhs.as_ref().clone());
        rest = rhs.as_ref();
    }
    claims.push(rest.clone());
    let mut raw: Vec<E> = Vec::new();
    let mut at = 0;
    for count in &regions {
        let mine = claims[at.min(claims.len())..(at + count).min(claims.len())].to_vec();
        at += count;
        if let Some(claim) = mine
            .into_iter()
            .rev()
            .reduce(|tail, term| term.and_expr(tail))
        {
            raw.push(claim);
        }
    }
    let parts = owner.parts();
    let plain = parts.len() == raw.len()
        && parts
            .iter()
            .zip(&raw)
            .all(|(part, claim)| part.aarch64_expr == *claim);
    let distinct = |part: &ProofObligation| {
        let mut seen: Vec<&E> = Vec::new();
        let mut rest = &part.aarch64_expr;
        while let E::And { lhs, rhs } = rest {
            if !seen.contains(&lhs.as_ref()) {
                seen.push(lhs.as_ref());
            }
            rest = rhs.as_ref();
        }
        if !seen.contains(&rest) {
            seen.push(rest);
        }
        seen.len()
    };
    let bound = super::super::split::MAX_CLAIM_PARTS;
    let defined: Vec<String> = defined_in(statement)
        .into_iter()
        .map(|(name, _)| name)
        .collect();
    Spelling233 {
        parts: parts.len(),
        plain,
        most_claims: parts.iter().map(distinct).max().unwrap_or(0),
        over_bound: parts.iter().filter(|part| distinct(part) > bound).count(),
        with_definition_claims: parts
            .iter()
            .filter(|part| {
                defined
                    .iter()
                    .any(|name| claims_of(&part.aarch64_expr, name) > 0)
            })
            .count(),
    }
}

/// One statement in parts at `points` under the mutants `names`, built
/// once: each part's verdict on slice 9's keyed samples (none unless
/// `sample`), the defined inputs, the digest, the merged chains and the
/// spelling; or the refusal's text.
struct Stated233 {
    holds: Vec<bool>,
    defined: (usize, usize),
    digest: String,
    merged: Option<(usize, usize)>,
    spelling: Spelling233,
}

fn stated233(
    names: &str,
    source: &Function,
    machine: &X86ISelFunction,
    points: &[(Block, usize)],
    sample: bool,
) -> Result<Stated233, String> {
    let _mutant = mutant::set(names);
    let owner =
        in_parts(source, machine, points.to_vec()).map_err(|refusal| refusal.to_string())?;
    Ok(Stated233 {
        holds: if sample {
            owner
                .parts()
                .iter()
                .map(super::slice9::dag_holds_on_samples)
                .collect()
        } else {
            Vec::new()
        },
        defined: owner.defined_cut_inputs(),
        digest: statement_digest233(&owner),
        merged: owner.merged_chains(),
        spelling: spelling233(&owner),
    })
}

/// Each region's claims of an owner's statement in parts, judged on slice
/// 9's keyed samples under the cone of the statement's definitions they
/// reach (a region with no claim holds): the verdict of the region's part
/// however the spelling cuts the parts (its spelled part is equivalent to
/// it, [`split::split_parts`]).
fn region_verdicts(owner: &SourceBoundX86Body<'_>) -> Vec<bool> {
    let statement = owner.obligation();
    let regions = owner.shared_parts().region_claims().to_vec();
    let definitions: Vec<(String, E)> = statement
        .preconditions
        .iter()
        .rev()
        .map(|premise| match premise {
            E::Eq { lhs, rhs } => match lhs.as_ref() {
                E::Var { name, .. } => (name.clone(), rhs.as_ref().clone()),
                _ => panic!("premise {premise} defines no name"),
            },
            _ => panic!("premise {premise} is no equation"),
        })
        .collect();
    let by_name: HashMap<&str, &E> = definitions
        .iter()
        .map(|(name, expr)| (name.as_str(), expr))
        .collect();
    let free: Vec<(String, u32)> = statement
        .inputs
        .iter()
        .filter(|(name, _)| !by_name.contains_key(name.as_str()))
        .cloned()
        .collect();
    let total: usize = regions.iter().sum();
    let mut claims: Vec<E> = Vec::with_capacity(total);
    let mut rest = &statement.aarch64_expr;
    for _ in 1..total {
        let E::And { lhs, rhs } = rest else {
            panic!("the statement has fewer claims than its regions account for");
        };
        claims.push(lhs.as_ref().clone());
        rest = rhs.as_ref();
    }
    claims.push(rest.clone());
    let mut at = 0;
    regions
        .iter()
        .map(|count| {
            let mine = claims[at..at + count].to_vec();
            at += count;
            let Some(claim) = mine
                .into_iter()
                .rev()
                .reduce(|tail, term| term.and_expr(tail))
            else {
                return true;
            };
            let mut reached: HashSet<String> = HashSet::new();
            let mut pending = claim.free_vars();
            while let Some(name) = pending.pop() {
                if reached.insert(name.clone())
                    && let Some(expr) = by_name.get(name.as_str())
                {
                    pending.extend(expr.free_vars());
                }
            }
            let cone: Vec<(String, E)> = definitions
                .iter()
                .filter(|(name, _)| reached.contains(name))
                .cloned()
                .collect();
            super::slice9::dag_holds_on_samples(&super::super::split::part_obligation(
                statement, &free, cone, claim,
            ))
        })
        .collect()
}

/// [`region_verdicts`] of a statement in parts at `points` under the
/// mutants `names` (empty when refused).
fn regions233(
    names: &str,
    source: &Function,
    machine: &X86ISelFunction,
    points: &[(Block, usize)],
) -> Vec<bool> {
    let _mutant = mutant::set(names);
    in_parts(source, machine, points.to_vec())
        .map(|owner| region_verdicts(&owner))
        .unwrap_or_default()
}

/// The in-parts golden (slice 16's size shapes, stated in parts by the
/// production planner: `slice16_parts_snapshots.smt2`) moves only where a
/// definition appears: each size shape whose parts read otherwise with the
/// rule than without it (`od233-off`) defines a cut input, and is listed.
#[test]
fn the_in_parts_golden_moves_only_where_an_input_is_defined() {
    for shape in super::slice16::SLICE_SIXTEEN {
        let (source, machine) = super::slice16::slice16_pair(shape);
        let render = |names: &str| {
            let _mutant = mutant::set(names);
            let owner = super::slice22::fixture_owner(&source, &machine)
                .unwrap_or_else(|refusal| panic!("{shape:?}: {refusal}"));
            let parts: Vec<String> = owner
                .parts()
                .iter()
                .map(|part| generate_smt2_query_raw(part, &replay_config()))
                .collect();
            (owner.defined_cut_inputs(), parts)
        };
        let (_, without) = render("od233-off");
        let (defined, with) = render("");
        eprintln!(
            "OD233_GOLDEN {shape:?} moved={} defined={defined:?}",
            with != without
        );
        if with != without {
            assert!(
                defined.0 + defined.1 > 0,
                "{shape:?}: its parts moved, and nothing is defined"
            );
        } else {
            assert_eq!(
                defined,
                (0, 0),
                "{shape:?}: defines inputs and its parts do not move"
            );
        }
    }
}

/// The verifier's trace (`TCG_X86_BODY_TRACE`) of a statement the
/// production planner states in parts and that defines cut inputs (P1L:
/// past the single-query machine bounds, over the merged-chain quotient):
/// one `defined cut inputs bytes=B items=I` line, with the counts its owner
/// defines, after its `merged chains=` line and before its `stated in parts=`
/// line, and its last line `bound rows=`, the order the census parsers read;
/// slice 16's `LongChain`, stated in parts and defining nothing, prints no
/// such line. Run in a child process, which writes the trace to its stderr;
/// no replay (`TCG_REFINE_SOLVER=0`).
#[test]
fn the_defined_cut_inputs_trace_line_precedes_the_parts_and_bound_lines() {
    const CHILD: &str = "TCG_OD233_TRACE_CHILD";
    const TEST: &str = "x86_source_bound_body::tests::od233::\
                        the_defined_cut_inputs_trace_line_precedes_the_parts_and_bound_lines";
    let long = || od233_pair(Shape233::LongLenLocal);
    let chain = || super::slice16::slice16_pair(super::slice16::SizeShape::LongChain);
    if std::env::var_os(CHILD).is_some() {
        super::without_replay(|| {
            let verifier = super::promotion_verifier();
            let request = verifier.capture_request_with_mode(ProvenanceXCheckMode::Enforce);
            for (source, machine) in [long(), chain()] {
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
    let (source, machine) = long();
    assert!(
        !super::super::split::fits_one_query(&source, &machine),
        "P1L fits one query"
    );
    let owner = super::slice22::fixture_owner(&source, &machine)
        .unwrap_or_else(|refusal| panic!("P1L: {refusal}\n{}", describe(&machine)));
    assert!(
        owner.is_stated_in_parts() && owner.merged_chains().is_some(),
        "P1L: in parts over the quotient"
    );
    let (bytes, items) = owner.defined_cut_inputs();
    assert!(bytes + items > 0, "P1L defines nothing");
    eprintln!(
        "OD233_TRACE P1L parts={} defined={:?} merged={:?}",
        owner.parts().len(),
        (bytes, items),
        owner.merged_chains()
    );
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
    for (function, defines) in [
        (Shape233::LongLenLocal.name(), Some((bytes, items))),
        ("s16_long_chain".to_string(), None),
    ] {
        let prefix = format!("[TCG-X86-BODY-TRACE] fn={function} ");
        let lines: Vec<&str> = stderr
            .lines()
            .filter(|line| line.starts_with(&prefix))
            .collect();
        eprintln!("OD233_TRACE {function}: {lines:?}");
        let position = |needle: &str| lines.iter().position(|line| line.contains(needle));
        let last = lines.last().expect("a trace line");
        assert!(
            last.contains(" bound rows="),
            "{function}: last line {last:?}"
        );
        let stated = position(" stated in parts=")
            .unwrap_or_else(|| panic!("{function}: no parts line: {lines:?}"));
        let defined_lines = lines
            .iter()
            .filter(|line| line.contains(" defined cut inputs "))
            .count();
        match defines {
            Some((bytes, items)) => {
                let expected = format!("{prefix}defined cut inputs bytes={bytes} items={items}");
                let defined = lines
                    .iter()
                    .position(|line| *line == expected)
                    .unwrap_or_else(|| panic!("{function}: no {expected:?}: {lines:?}"));
                let merged = position(" merged chains=")
                    .unwrap_or_else(|| panic!("{function}: no merged-chains line: {lines:?}"));
                assert!(
                    merged < defined && defined < stated,
                    "{function}: {lines:?}"
                );
                assert_eq!(defined_lines, 1, "{function}: {lines:?}");
            }
            None => assert_eq!(defined_lines, 0, "{function}: {lines:?}"),
        }
    }
}

/// N1: a statement whose every claim but the definition claims is an
/// identity (OD-115) still refuses NoObservable, with the rule and without
/// it, though it defines a cut input (stated when the definition claims
/// count as observables, `od233-observable`).
#[test]
fn an_observable_free_statement_still_refuses() {
    let shape = Shape233::SymbolNoObservable;
    let (source, machine) = od233_pair(shape);
    for names in ["", "od233-off"] {
        let _mutant = mutant::set(names);
        let result = owner233(shape, &source, &machine);
        assert!(
            matches!(
                &result,
                Err(X86BodyRefusal::Unsupported(
                    X86BodyUnsupported::NoObservable
                ))
            ),
            "N1 under [{names}]: {}",
            refusal_text233(&result)
        );
    }
    let _mutant = mutant::set("od233-observable");
    let result = owner233(shape, &source, &machine);
    eprintln!(
        "OD233_N1 observable: {} defined={:?}",
        refusal_text233(&result),
        result.as_ref().map(|owner| owner.defined_cut_inputs()).ok()
    );
}
