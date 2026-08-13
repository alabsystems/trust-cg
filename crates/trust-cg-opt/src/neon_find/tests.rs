// Unit tests for the neon-find early-exit search vectorizer.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

use super::*;
use trust_cg_ir::Signature;

fn v(id: u32) -> MachOperand {
    MachOperand::VReg(VReg::new(id, RegClass::Gpr32))
}
fn v64(id: u32) -> MachOperand {
    MachOperand::VReg(VReg::new(id, RegClass::Gpr64))
}
fn i(x: i64) -> MachOperand {
    MachOperand::Imm(x)
}
fn b(x: BlockId) -> MachOperand {
    MachOperand::Block(x)
}
fn count(func: &MachFunction, op: AArch64Opcode) -> usize {
    func.blocks
        .iter()
        .flat_map(|blk| blk.insts.iter().copied())
        .filter(|&id| func.inst(id).opcode == op)
        .count()
}

/// A structural corruption to inject, to pin the bail conditions.
#[derive(Clone, Copy, PartialEq)]
enum Corrupt {
    None,
    /// Insert a store into the body (a side effect).
    StoreInBody,
    /// Replace the body load with an atomic load-acquire.
    AtomicLoad,
    /// Make the body compare a `<` (ordered) instead of `==` (LT branch).
    NonEqCompare,
    /// Make the early-exit branch target stay inside the loop (no real exit).
    ExitInsideLoop,
    /// Increment iv by 2 (not a unit-stride find).
    StrideTwo,
    /// Carry a live-out reduction (`sum += a[iv]`) alongside the search: a body
    /// `AddRR` accumulate plus its latch back-edge copy `sum = MovR(sum_next)`.
    /// `iv` is then NOT the only loop-carried value, so the block-skipping
    /// vector filter (which advances only `iv`) would silently drop the
    /// reduction -> must BAIL.
    LiveOutReduction,
}

/// Build `for i in 0..n: if a[i] == key { return i } ; return -1` in the exact
/// shape the pipeline hands to neon-find (header / body / latch), optionally
/// corrupted.
///
/// Registers: v64(0)=base, v(1)=n, v(2)=key, v(6)=iv, v64(10)=elem-size(4).
fn build_find(corrupt: Corrupt) -> MachFunction {
    let mut func = MachFunction::new("findkey".to_string(), Signature::new(vec![], vec![]));
    let bb0 = func.entry;
    let header = func.create_block();
    let body = func.create_block();
    let latch = func.create_block();
    let match_exit = func.create_block();
    let nomatch_exit = func.create_block();

    let push = |func: &mut MachFunction, blk: BlockId, op, ops| {
        let id = func.push_inst(MachInst::new(op, ops));
        func.append_inst(blk, id);
    };
    use AArch64Opcode::*;

    // Preheader.
    push(&mut func, bb0, Copy, vec![v64(0), v64(0)]); // base
    push(&mut func, bb0, Copy, vec![v(1), v(1)]); // n
    push(&mut func, bb0, Copy, vec![v(2), v(2)]); // key
    push(&mut func, bb0, Movz, vec![v(3), i(0)]);
    push(&mut func, bb0, Movz, vec![v(4), i(1)]);
    push(&mut func, bb0, Movz, vec![v64(10), i(4)]); // element size
    push(&mut func, bb0, MovR, vec![v(6), v(3)]); // iv = 0
    if corrupt == Corrupt::LiveOutReduction {
        push(&mut func, bb0, Movz, vec![v(20), i(0)]); // sum = 0 (loop-carried)
    }
    push(&mut func, bb0, B, vec![b(header)]);

    // Header: iv < n ? body : no-match exit.
    push(&mut func, header, CmpRR, vec![v(6), v(1)]);
    push(&mut func, header, BCond, vec![i(CC_LT), b(body)]);
    push(&mut func, header, B, vec![b(nomatch_exit)]);

    // Body: v = a[iv]; v == key ? match : latch.
    push(&mut func, body, MovR, vec![v(8), v(6)]);
    push(&mut func, body, Sxtw, vec![v64(9), v(8)]);
    push(
        &mut func,
        body,
        Madd,
        vec![v64(11), v64(9), v64(10), v64(0)],
    );
    if corrupt == Corrupt::AtomicLoad {
        push(&mut func, body, Ldar, vec![v(12), v64(11)]);
    } else {
        push(&mut func, body, LdrRI, vec![v(12), v64(11), i(0)]);
    }
    if corrupt == Corrupt::StoreInBody {
        push(&mut func, body, StrRI, vec![v(2), v64(11), i(0)]);
    }
    if corrupt == Corrupt::LiveOutReduction {
        // sum_next = sum + a[iv]  (the accumulate the vector filter would drop)
        push(&mut func, body, AddRR, vec![v(21), v(20), v(12)]);
    }
    push(&mut func, body, CmpRR, vec![v(12), v(2)]);
    let eq_cc = if corrupt == Corrupt::NonEqCompare {
        CC_LT
    } else {
        CC_EQ
    };
    let eq_target = if corrupt == Corrupt::ExitInsideLoop {
        latch
    } else {
        match_exit
    };
    push(&mut func, body, BCond, vec![i(eq_cc), b(eq_target)]);
    push(&mut func, body, B, vec![b(latch)]);

    // Latch: iv += stride ; -> header.
    let stride = if corrupt == Corrupt::StrideTwo { 2 } else { 1 };
    push(&mut func, latch, Movz, vec![v(15), i(stride)]);
    push(&mut func, latch, AddRR, vec![v(16), v(6), v(15)]);
    push(&mut func, latch, MovR, vec![v(6), v(16)]);
    if corrupt == Corrupt::LiveOutReduction {
        // sum = sum_next: the second loop-carried value's back-edge copy.
        push(&mut func, latch, MovR, vec![v(20), v(21)]);
    }
    push(&mut func, latch, B, vec![b(header)]);

    // Exits.
    push(&mut func, match_exit, Ret, vec![]);
    push(&mut func, nomatch_exit, Ret, vec![]);

    func.add_edge(bb0, header);
    func.add_edge(header, body);
    func.add_edge(header, nomatch_exit);
    func.add_edge(body, eq_target);
    func.add_edge(body, latch);
    func.add_edge(latch, header);
    func.next_vreg = 256;
    func
}

fn fires(corrupt: Corrupt) -> (bool, MachFunction) {
    let mut func = build_find(corrupt);
    let mut pass = NeonFindPass::new();
    let changed = pass.run(&mut func);
    (changed, func)
}

#[test]
fn fires_on_find_i32() {
    let (changed, func) = fires(Corrupt::None);
    assert!(changed, "find(a, n, key) should vectorize");
    // One CMEQ.4S per vector, 4 vectors per 16-element block.
    assert_eq!(
        count(&func, AArch64Opcode::NeonCmeqV),
        UNROLL,
        "4 CMEQ.4S masks"
    );
    assert_eq!(
        count(&func, AArch64Opcode::NeonLdpQPost),
        UNROLL / 2,
        "2 LDP q,q"
    );
    // key splat.
    assert_eq!(
        count(&func, AArch64Opcode::NeonDupGen),
        1,
        "one DUP key splat"
    );
    // any-hit test: two D-lane UMOV extracts (no horizontal-reduce op).
    assert_eq!(
        count(&func, AArch64Opcode::NeonUmovGen),
        2,
        "2 UMOV.D halves"
    );
    assert_eq!(
        count(&func, AArch64Opcode::NeonUmaxv),
        0,
        "no horizontal reduce"
    );
    // 3 masks OR-tree + never touches the scalar loop's ops.
    assert_eq!(
        count(&func, AArch64Opcode::NeonOrrV),
        UNROLL - 1,
        "3-way OR tree"
    );
}

#[test]
fn scalar_loop_preserved() {
    // The transform is purely additive: the original scalar load + equality
    // compare are still present untouched (delegated first-match).
    let (changed, func) = fires(Corrupt::None);
    assert!(changed);
    assert!(
        count(&func, AArch64Opcode::LdrRI) >= 1,
        "scalar load intact"
    );
    // the scalar body's CmpRR(load,key) plus the vector any-hit CmpRI.
    assert!(
        count(&func, AArch64Opcode::CmpRR) >= 2,
        "scalar compare intact"
    );
}

#[test]
fn bails_on_store_in_body() {
    let (changed, _) = fires(Corrupt::StoreInBody);
    assert!(!changed, "a store in the body is a side effect -> BAIL");
}

#[test]
fn bails_on_atomic_load() {
    let (changed, _) = fires(Corrupt::AtomicLoad);
    assert!(!changed, "an atomic load-acquire in the body -> BAIL");
}

#[test]
fn bails_on_non_eq_compare() {
    let (changed, _) = fires(Corrupt::NonEqCompare);
    assert!(
        !changed,
        "an ordered `<` search is not first-match-equal -> BAIL"
    );
}

#[test]
fn bails_on_exit_inside_loop() {
    let (changed, _) = fires(Corrupt::ExitInsideLoop);
    assert!(
        !changed,
        "the early-exit branch must LEAVE the loop -> BAIL"
    );
}

#[test]
fn bails_on_non_unit_stride() {
    let (changed, _) = fires(Corrupt::StrideTwo);
    assert!(!changed, "iv must advance by 1 -> BAIL");
}

#[test]
fn bails_on_live_out_reduction() {
    // A first-match search that ALSO carries a reduction (`sum += a[iv]`, a
    // second loop-carried value with a latch back-edge copy) must NOT be
    // vectorized: the block-skipping filter advances only `iv` and would drop
    // the accumulate for every skipped element. Without the R4b guard this
    // fires and miscompiles.
    let (changed, _) = fires(Corrupt::LiveOutReduction);
    assert!(
        !changed,
        "iv is not the only loop-carried value (live-out reduction) -> BAIL"
    );
}

// ---------------------------------------------------------------------------
// Byte (`memchr`, `.16B`) width mirror
// ---------------------------------------------------------------------------

/// All `Imm` operands of every instance of `op`, in program order.
fn imms_of(func: &MachFunction, op: AArch64Opcode) -> Vec<Vec<i64>> {
    func.blocks
        .iter()
        .flat_map(|blk| blk.insts.iter().copied())
        .filter(|&id| func.inst(id).opcode == op)
        .map(|id| {
            func.inst(id)
                .operands
                .iter()
                .filter_map(|o| match o {
                    MachOperand::Imm(x) => Some(*x),
                    _ => None,
                })
                .collect()
        })
        .collect()
}

/// Address shapes for the byte kernel's `a[i]` (the `*1` gep folds to a plain
/// add; the `Madd(idx, 1, base)` form is the un-folded equivalent).
#[derive(Clone, Copy, PartialEq)]
enum ByteAddr {
    AddRR,
    Madd,
}

/// Build `for i in 0..n: if ext(a_u8[i]) == key { return i } ; return -1` in
/// the byte-load shape the pipeline hands to neon-find: the term is
/// `Uxtb/Sxtb(LdrbRI(base + sxtw(iv)))`.
///
/// Registers: v64(0)=base, v(1)=n, v(2)=key, v(6)=iv.
fn build_find_byte(addr: ByteAddr, sext: bool, corrupt: Corrupt) -> MachFunction {
    let mut func = MachFunction::new("findbyte".to_string(), Signature::new(vec![], vec![]));
    let bb0 = func.entry;
    let header = func.create_block();
    let body = func.create_block();
    let latch = func.create_block();
    let match_exit = func.create_block();
    let nomatch_exit = func.create_block();

    let push = |func: &mut MachFunction, blk: BlockId, op, ops| {
        let id = func.push_inst(MachInst::new(op, ops));
        func.append_inst(blk, id);
    };
    use AArch64Opcode::*;

    // Preheader.
    push(&mut func, bb0, Copy, vec![v64(0), v64(0)]); // base
    push(&mut func, bb0, Copy, vec![v(1), v(1)]); // n
    push(&mut func, bb0, Copy, vec![v(2), v(2)]); // key
    push(&mut func, bb0, Movz, vec![v(3), i(0)]);
    push(&mut func, bb0, Movz, vec![v(4), i(1)]);
    push(&mut func, bb0, Movz, vec![v64(10), i(1)]); // element size (Madd form)
    push(&mut func, bb0, MovR, vec![v(6), v(3)]); // iv = 0
    push(&mut func, bb0, B, vec![b(header)]);

    // Header: iv < n ? body : no-match exit.
    push(&mut func, header, CmpRR, vec![v(6), v(1)]);
    push(&mut func, header, BCond, vec![i(CC_LT), b(body)]);
    push(&mut func, header, B, vec![b(nomatch_exit)]);

    // Body: v = ext(a_u8[iv]); v == key ? match : latch.
    push(&mut func, body, MovR, vec![v(8), v(6)]);
    push(&mut func, body, Sxtw, vec![v64(9), v(8)]);
    match addr {
        ByteAddr::AddRR => push(&mut func, body, AddRR, vec![v64(11), v64(0), v64(9)]),
        ByteAddr::Madd => push(
            &mut func,
            body,
            Madd,
            vec![v64(11), v64(9), v64(10), v64(0)],
        ),
    }
    if corrupt == Corrupt::AtomicLoad {
        push(&mut func, body, Ldar, vec![v(12), v64(11)]);
    } else {
        push(&mut func, body, LdrbRI, vec![v(12), v64(11), i(0)]);
    }
    push(
        &mut func,
        body,
        if sext { Sxtb } else { Uxtb },
        vec![v(13), v(12)],
    );
    if corrupt == Corrupt::StoreInBody {
        push(&mut func, body, StrRI, vec![v(2), v64(11), i(0)]);
    }
    push(&mut func, body, CmpRR, vec![v(13), v(2)]);
    let eq_cc = if corrupt == Corrupt::NonEqCompare {
        CC_LT
    } else {
        CC_EQ
    };
    push(&mut func, body, BCond, vec![i(eq_cc), b(match_exit)]);
    push(&mut func, body, B, vec![b(latch)]);

    // Latch: iv += stride ; -> header.
    let stride = if corrupt == Corrupt::StrideTwo { 2 } else { 1 };
    push(&mut func, latch, Movz, vec![v(15), i(stride)]);
    push(&mut func, latch, AddRR, vec![v(16), v(6), v(15)]);
    push(&mut func, latch, MovR, vec![v(6), v(16)]);
    push(&mut func, latch, B, vec![b(header)]);

    // Exits.
    push(&mut func, match_exit, Ret, vec![]);
    push(&mut func, nomatch_exit, Ret, vec![]);

    func.add_edge(bb0, header);
    func.add_edge(header, body);
    func.add_edge(header, nomatch_exit);
    func.add_edge(body, match_exit);
    func.add_edge(body, latch);
    func.add_edge(latch, header);
    func.next_vreg = 256;
    func
}

fn fires_byte(addr: ByteAddr, sext: bool, corrupt: Corrupt) -> (bool, MachFunction) {
    let mut func = build_find_byte(addr, sext, corrupt);
    let mut pass = NeonFindPass::new();
    let changed = pass.run(&mut func);
    (changed, func)
}

#[test]
fn fires_on_find_byte_u8() {
    let (changed, func) = fires_byte(ByteAddr::AddRR, false, Corrupt::None);
    assert!(changed, "memchr(a, n, key) over u8 should vectorize");
    // Same block-filter structure as i32: 4 masks, 2 LDP pairs, 1 splat,
    // 2 UMOV.D halves, 3-way OR tree — but at the `.16B` arrangement.
    assert_eq!(
        count(&func, AArch64Opcode::NeonCmeqV),
        UNROLL,
        "4 CMEQ.16B masks"
    );
    assert_eq!(
        count(&func, AArch64Opcode::NeonLdpQPost),
        UNROLL / 2,
        "2 LDP q,q"
    );
    assert_eq!(
        count(&func, AArch64Opcode::NeonDupGen),
        1,
        "one DUP key splat"
    );
    assert_eq!(
        count(&func, AArch64Opcode::NeonUmovGen),
        2,
        "2 UMOV.D halves"
    );
    assert_eq!(
        count(&func, AArch64Opcode::NeonOrrV),
        UNROLL - 1,
        "3-way OR tree"
    );
    // Every CMEQ carries the `.16B` arrangement; the splat is a byte DUP.
    for imms in imms_of(&func, AArch64Opcode::NeonCmeqV) {
        assert_eq!(imms, vec![ARR_B16], "CMEQ at .16B");
    }
    for imms in imms_of(&func, AArch64Opcode::NeonDupGen) {
        assert_eq!(imms, vec![ELEM_B], "DUP.16B key splat");
    }
    // The vector latch advances iv by the 64-byte block width.
    assert!(
        imms_of(&func, AArch64Opcode::AddRI)
            .iter()
            .any(|imms| imms == &vec![UNROLL as i64 * VF_B]),
        "iv += 64 vector latch"
    );
}

#[test]
fn fires_on_find_byte_s8() {
    // Sxtb is the same superset filter (see the module docs) — fires.
    let (changed, func) = fires_byte(ByteAddr::AddRR, true, Corrupt::None);
    assert!(changed, "signed-byte find should vectorize too");
    assert_eq!(count(&func, AArch64Opcode::NeonCmeqV), UNROLL);
}

#[test]
fn fires_on_find_byte_madd_addr() {
    // The un-folded `Madd(sxtw(iv), 1, base)` address form fires as well.
    let (changed, func) = fires_byte(ByteAddr::Madd, false, Corrupt::None);
    assert!(changed, "Madd *1 address form should vectorize");
    assert_eq!(count(&func, AArch64Opcode::NeonCmeqV), UNROLL);
}

#[test]
fn byte_scalar_loop_preserved() {
    // Purely additive at the byte width too: the scalar Ldrb/Uxtb survive.
    let (changed, func) = fires_byte(ByteAddr::AddRR, false, Corrupt::None);
    assert!(changed);
    assert!(
        count(&func, AArch64Opcode::LdrbRI) >= 1,
        "scalar byte load intact"
    );
    assert!(
        count(&func, AArch64Opcode::Uxtb) >= 1,
        "scalar extend intact"
    );
}

#[test]
fn byte_bails_on_store_in_body() {
    let (changed, _) = fires_byte(ByteAddr::AddRR, false, Corrupt::StoreInBody);
    assert!(!changed, "a store in the byte body -> BAIL");
}

#[test]
fn byte_bails_on_non_eq_compare() {
    let (changed, _) = fires_byte(ByteAddr::AddRR, false, Corrupt::NonEqCompare);
    assert!(!changed, "an ordered `<` byte search -> BAIL");
}

#[test]
fn byte_bails_on_non_unit_stride() {
    let (changed, _) = fires_byte(ByteAddr::AddRR, false, Corrupt::StrideTwo);
    assert!(!changed, "byte iv must advance by 1 -> BAIL");
}

#[test]
fn i32_width_untouched_by_byte_mirror() {
    // Shape pin: the existing i32 kernel still lowers at the `.4S` arrangement
    // with the S-element splat and the 16-element block advance — the byte
    // mirror must not perturb the shipped width (the fuzzer additionally diffs
    // object bytes against the pre-mirror goldens).
    let (changed, func) = fires(Corrupt::None);
    assert!(changed);
    for imms in imms_of(&func, AArch64Opcode::NeonCmeqV) {
        assert_eq!(imms, vec![ARR_S4], "i32 CMEQ stays at .4S");
    }
    for imms in imms_of(&func, AArch64Opcode::NeonDupGen) {
        assert_eq!(imms, vec![ELEM_S], "i32 DUP stays at S elements");
    }
    assert!(
        imms_of(&func, AArch64Opcode::AddRI)
            .iter()
            .any(|imms| imms == &vec![WIDTH]),
        "i32 vector latch stays iv += 16"
    );
}

// ---------------------------------------------------------------------------
// Forward-chain (const-bound, Gpr64-direct) recognizer — the bridge's
// fixed-size-local-array `while i<N { if a[i]==key break }` search shape.
// ---------------------------------------------------------------------------

/// Corruptions specific to the chain shape.
#[derive(Clone, Copy, PartialEq)]
enum ChainCorrupt {
    None,
    /// Ordered `<` (CC_LT) match compare instead of `==` — not a first-match
    /// equality search.
    NonEqCompare,
    /// The equality edge stays inside the loop (no real early exit).
    ExitInsideLoop,
    /// `iv += 2` in the latch (not a unit-stride search).
    StrideTwo,
    /// A bounds-check-elim-DETACHED `TrapBoundsCheckExact` left in `func.insts`
    /// whose operand0 is a READ of the pass-block iv-copy: with the flat
    /// `build_def_map` it would shadow the real in-block def and break the
    /// address walk. `build_live_def_map` must ignore it (the pass still fires).
    DetachedTrapShadow,
    /// A `Gpr32` induction — the chain path is `Gpr64`-only (strict path's
    /// domain), so this must BAIL (and the 4-block shape is not strict either).
    Gpr32Iv,
    /// The guard compares against a REGISTER holding a materialized constant
    /// (`Movz r, #N` in the entry block; `CmpRR(iv, r)` + `LO`) — the shape the
    /// bridge actually emits for `while i < N` over a fixed-size local array
    /// (e06_find). NOT a corruption: this must FIRE with the recovered `N`.
    RegConstBound,
    /// The guard compares against a truly RUNTIME register bound (an opaque
    /// `Copy`-defined value, no `const_value`) — must BAIL (fail-closed: the
    /// chain path only fires on provably-constant trip bounds).
    RegRuntimeBound,
}

/// Build the const-bound forward-chain search `for i in 0..N { if a[i]==key {
/// break } }` (mixed `Gpr64` index / `Gpr32` element) in the CFG the bridge
/// hands neon-find: a `CmpRI(iv,N)+LO` header guard, an elided-bounds
/// pass-through, an early-exit equality MATCH block, and an `iv+1` latch.
///
/// Registers: v64(0)=base, v(2)=key, v64(10)=elem-size(4), v64(30)=iv.
fn build_find_chain(corrupt: ChainCorrupt) -> MachFunction {
    const N: i64 = 2048;
    let mut func = MachFunction::new("findchain".to_string(), Signature::new(vec![], vec![]));
    let bb0 = func.entry;
    let header = func.create_block();
    let pass = func.create_block();
    let mblk = func.create_block();
    let latch = func.create_block();
    let match_exit = func.create_block();
    let nomatch_exit = func.create_block();

    let push = |func: &mut MachFunction, blk: BlockId, op, ops| {
        let id = func.push_inst(MachInst::new(op, ops));
        func.append_inst(blk, id);
        id
    };
    use AArch64Opcode::*;

    let gp = corrupt == ChainCorrupt::Gpr32Iv;
    // The induction: `Gpr64` usize on the real shape, `Gpr32` for the bail probe.
    let iv = |id: u32| {
        MachOperand::VReg(VReg::new(
            id,
            if gp { RegClass::Gpr32 } else { RegClass::Gpr64 },
        ))
    };

    // Preheader.
    push(&mut func, bb0, Copy, vec![v64(0), v64(0)]); // base
    push(&mut func, bb0, Copy, vec![v(2), v(2)]); // key
    push(&mut func, bb0, Movz, vec![v64(10), i(4)]); // element size
    push(&mut func, bb0, Movz, vec![iv(29), i(0)]);
    push(&mut func, bb0, MovR, vec![iv(30), iv(29)]); // iv = 0
    match corrupt {
        // The bridge's e06 shape: the fixed array length lives in a REGISTER
        // materialized once in the entry block (`Movz r, #N`).
        ChainCorrupt::RegConstBound => {
            push(&mut func, bb0, Movz, vec![v64(50), i(N)]);
        }
        // A runtime bound: an opaque Copy-defined register (no const_value).
        ChainCorrupt::RegRuntimeBound => {
            push(&mut func, bb0, Copy, vec![v64(50), v64(50)]);
        }
        _ => {}
    }
    push(&mut func, bb0, B, vec![b(header)]);

    // Header guard: `MovR t=iv; Cmp(t, N); b.lo pass; b nomatch` — the bound is
    // a `CmpRI` immediate by default, or a `CmpRR` register on the Reg*Bound
    // variants (the shape real lowering emits for a fixed-size local array).
    push(&mut func, header, MovR, vec![iv(31), iv(30)]);
    if matches!(
        corrupt,
        ChainCorrupt::RegConstBound | ChainCorrupt::RegRuntimeBound
    ) {
        push(&mut func, header, CmpRR, vec![iv(31), v64(50)]);
    } else {
        push(&mut func, header, CmpRI, vec![iv(31), i(N)]);
    }
    push(&mut func, header, BCond, vec![i(CC_LO), b(pass)]);
    push(&mut func, header, B, vec![b(nomatch_exit)]);

    // Pass-through (its per-iteration bounds check was elided).
    let ivcopy = push(&mut func, pass, MovR, vec![iv(32), iv(30)]);
    let _ = ivcopy;
    push(&mut func, pass, B, vec![b(mblk)]);

    // Match block: `v = a[iv]; v == key ? match_exit(out) : latch(in)`. The index
    // is the `Gpr64` iv used DIRECTLY (no Sxtw) — the mixed-width addressing.
    if gp {
        // A Gpr32 iv still needs a 64-bit index; sxtw it (so the address is
        // well-formed) — the class check, not the address, is what must BAIL.
        push(&mut func, mblk, Sxtw, vec![v64(37), iv(32)]);
        push(
            &mut func,
            mblk,
            Madd,
            vec![v64(33), v64(37), v64(10), v64(0)],
        );
    } else {
        push(
            &mut func,
            mblk,
            Madd,
            vec![v64(33), iv(32), v64(10), v64(0)],
        );
    }
    push(&mut func, mblk, LdrRI, vec![v(34), v64(33), i(0)]);
    push(&mut func, mblk, CmpRR, vec![v(34), v(2)]);
    let eq_cc = if corrupt == ChainCorrupt::NonEqCompare {
        CC_LT
    } else {
        CC_EQ
    };
    let eq_target = if corrupt == ChainCorrupt::ExitInsideLoop {
        latch
    } else {
        match_exit
    };
    push(&mut func, mblk, BCond, vec![i(eq_cc), b(eq_target)]);
    push(&mut func, mblk, B, vec![b(latch)]);

    // Latch: `iv += stride ; -> header`.
    let stride = if corrupt == ChainCorrupt::StrideTwo {
        2
    } else {
        1
    };
    push(&mut func, latch, AddRI, vec![iv(35), iv(30), i(stride)]);
    push(&mut func, latch, MovR, vec![iv(30), iv(35)]);
    push(&mut func, latch, B, vec![b(header)]);

    push(&mut func, match_exit, Ret, vec![]);
    push(&mut func, nomatch_exit, Ret, vec![]);

    // A DETACHED `TrapBoundsCheckExact [ivcopy, ivcopy, N]` left in `func.insts`
    // but appended to NO block — the bounds-check-elim carrier that shadows the
    // real in-block def of the pass-block iv-copy under the flat def map.
    if corrupt == ChainCorrupt::DetachedTrapShadow {
        let _detached = func.push_inst(MachInst::new(
            AArch64Opcode::TrapBoundsCheckExact,
            vec![iv(32), iv(32), i(N)],
        ));
        // intentionally NOT appended to any block
    }

    func.add_edge(bb0, header);
    func.add_edge(header, pass);
    func.add_edge(header, nomatch_exit);
    func.add_edge(pass, mblk);
    func.add_edge(mblk, eq_target);
    func.add_edge(mblk, latch);
    func.add_edge(latch, header);
    func.next_vreg = 256;
    func
}

fn fires_chain(corrupt: ChainCorrupt) -> (bool, MachFunction) {
    let mut func = build_find_chain(corrupt);
    let mut pass = NeonFindPass::new();
    let changed = pass.run(&mut func);
    (changed, func)
}

#[test]
fn fires_on_forward_chain_const_bound() {
    let (changed, func) = fires_chain(ChainCorrupt::None);
    assert!(
        changed,
        "const-bound Gpr64 forward-chain search should vectorize"
    );
    assert_eq!(
        count(&func, AArch64Opcode::NeonCmeqV),
        UNROLL,
        "4 CMEQ.4S masks"
    );
    assert_eq!(
        count(&func, AArch64Opcode::NeonLdpQPost),
        UNROLL / 2,
        "2 LDP q,q"
    );
    assert_eq!(
        count(&func, AArch64Opcode::NeonDupGen),
        1,
        "one DUP key splat"
    );
    assert_eq!(
        count(&func, AArch64Opcode::NeonUmovGen),
        2,
        "2 UMOV.D halves"
    );
    assert_eq!(
        count(&func, AArch64Opcode::NeonOrrV),
        UNROLL - 1,
        "3-way OR tree"
    );
    // The vector guard is UNSIGNED (LO) with a materialized const `N-(WIDTH-1)`
    // = 2048-15 = 2033, and the scalar loop is untouched (its load survives).
    assert!(
        imms_of(&func, AArch64Opcode::Movz)
            .iter()
            .any(|imms| imms == &vec![2033]),
        "materialized main_bound = N-(WIDTH-1) = 2033"
    );
    assert!(
        imms_of(&func, AArch64Opcode::BCond)
            .iter()
            .any(|imms| imms == &vec![CC_LO]),
        "unsigned LO vector guard"
    );
    assert!(
        count(&func, AArch64Opcode::LdrRI) >= 1,
        "scalar load intact"
    );
    // The vector latch advances iv by the 16-element block width.
    assert!(
        imms_of(&func, AArch64Opcode::AddRI)
            .iter()
            .any(|imms| imms == &vec![WIDTH]),
        "iv += 16 vector latch"
    );
}

#[test]
fn chain_fires_through_detached_trap_shadow() {
    // The REQUIRED build_live_def_map fix: a detached TrapBoundsCheckExact whose
    // operand0 re-reads the pass-block iv-copy must NOT shadow the real def.
    let (changed, func) = fires_chain(ChainCorrupt::DetachedTrapShadow);
    assert!(
        changed,
        "recognition must survive the detached-trap def shadow"
    );
    assert_eq!(count(&func, AArch64Opcode::NeonCmeqV), UNROLL);
}

#[test]
fn chain_bails_on_non_eq_compare() {
    let (changed, _) = fires_chain(ChainCorrupt::NonEqCompare);
    assert!(
        !changed,
        "an ordered `<` chain search is not first-match-equal -> BAIL"
    );
}

#[test]
fn chain_bails_on_exit_inside_loop() {
    let (changed, _) = fires_chain(ChainCorrupt::ExitInsideLoop);
    assert!(!changed, "the equality edge must LEAVE the loop -> BAIL");
}

#[test]
fn chain_bails_on_non_unit_stride() {
    let (changed, _) = fires_chain(ChainCorrupt::StrideTwo);
    assert!(!changed, "iv must advance by 1 -> BAIL");
}

#[test]
fn chain_bails_on_gpr32_induction() {
    let (changed, _) = fires_chain(ChainCorrupt::Gpr32Iv);
    assert!(
        !changed,
        "the chain path is Gpr64-only -> BAIL on a Gpr32 induction"
    );
}

#[test]
fn chain_fires_on_register_materialized_const_bound() {
    // The e06_find shape: the guard is `CmpRR(iv, r)` where `r` is `Movz #N` in
    // the entry block (the bridge CSEs the fixed array length into one register
    // reused by the loop guard and the bounds checks). The constant must be
    // recovered through the register and the pass must FIRE with the same
    // vector-guard bound `N-(WIDTH-1)` as the immediate form.
    let (changed, func) = fires_chain(ChainCorrupt::RegConstBound);
    assert!(
        changed,
        "register-materialized const bound (CmpRR against Movz #N) should vectorize"
    );
    assert_eq!(
        count(&func, AArch64Opcode::NeonCmeqV),
        UNROLL,
        "4 CMEQ.4S masks"
    );
    // Same materialized main_bound as the CmpRI form: N-(WIDTH-1) = 2048-15.
    assert!(
        imms_of(&func, AArch64Opcode::Movz)
            .iter()
            .any(|imms| imms == &vec![2033]),
        "materialized main_bound = N-(WIDTH-1) = 2033"
    );
}

#[test]
fn chain_bails_on_runtime_register_bound() {
    // A truly runtime bound register (opaque Copy def, no const_value) must
    // stay fail-closed: no compile-time N means no provable vector guard.
    let (changed, _) = fires_chain(ChainCorrupt::RegRuntimeBound);
    assert!(
        !changed,
        "a runtime (non-constant) register bound must BAIL on the chain path"
    );
}
