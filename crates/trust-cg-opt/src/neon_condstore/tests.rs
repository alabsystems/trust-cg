// Unit tests for the `neon-condstore` conditional-store vectorizer.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// Structural shape pins (cfg(test) only): the private structural harness FIRES
// with noalias, BAILS when the two-pointer form cannot prove disjointness
// (overlap), and BAILS on a non-diamond (plain map) loop. The public pass is
// separately pinned inert because no typed ownership capability exists yet.

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

/// Build `for i<n: if (a[i] > 0) b[i] = a[i]*2` in the EXACT un-rotated diamond
/// the aarch64 pipeline hands the neon passes (verified via `TRUST_CG_DUMP_MIR`):
/// header(counted test) / cond(load+predicate) / then(store) / skip / latch.
///
/// * `in_place`: the store base is the SAME pointer as the load base (single
///   array `if(a[i]>0) a[i]=a[i]*2`).
/// * Register map: v0=base_b(store,Gpr64,noalias id0), v1=base_a(load,Gpr64,
///   noalias id1), v2=n, v3=0, v4=1, v5=2, v10=4(es). iv=v6.
fn build_condstore_loop(in_place: bool) -> MachFunction {
    let mut func = MachFunction::new("k".to_string(), Signature::new(vec![], vec![]));
    let bb0 = func.entry;
    let header = func.create_block();
    let cond = func.create_block();
    let then_b = func.create_block();
    let skip = func.create_block();
    let latch = func.create_block();
    let exit = func.create_block();

    let push = |func: &mut MachFunction, blk: BlockId, op, ops| {
        let id = func.push_inst(MachInst::new(op, ops));
        func.append_inst(blk, id);
    };
    use AArch64Opcode::*;
    // The base the store writes: `b` normally, or `a` (== load base) in place.
    let store_base = if in_place { 1 } else { 0 };

    // Preheader: pointers + constants; iv = 0.
    push(&mut func, bb0, Copy, vec![v64(0), v64(0)]); // base_b
    push(&mut func, bb0, Copy, vec![v64(1), v64(1)]); // base_a
    push(&mut func, bb0, Copy, vec![v(2), v(2)]); // n
    push(&mut func, bb0, Movz, vec![v(3), i(0)]);
    push(&mut func, bb0, Movz, vec![v(4), i(1)]);
    push(&mut func, bb0, Movz, vec![v(5), i(2)]);
    push(&mut func, bb0, Movz, vec![v64(10), i(4)]); // element size
    push(&mut func, bb0, MovR, vec![v(6), v(3)]); // iv = 0
    push(&mut func, bb0, B, vec![b(header)]);

    // Header: counted test `iv < n`.
    push(&mut func, header, CmpRR, vec![v(6), v(2)]);
    push(&mut func, header, BCond, vec![i(CC_LT), b(cond)]);
    push(&mut func, header, B, vec![b(exit)]);

    // Cond: load a[i]; predicate a[i] > 0; branch to then (store) / skip.
    push(&mut func, cond, MovR, vec![v(8), v(6)]); // iv copy
    push(&mut func, cond, Sxtw, vec![v64(9), v(8)]);
    push(
        &mut func,
        cond,
        Madd,
        vec![v64(11), v64(9), v64(10), v64(1)],
    ); // a + iv*4
    push(&mut func, cond, LdrRI, vec![v(12), v64(11), i(0)]); // a[i]
    push(&mut func, cond, CmpRR, vec![v(12), v(3)]); // a[i] : 0
    push(&mut func, cond, BCond, vec![i(CC_GT), b(then_b)]); // store when a[i] > 0
    push(&mut func, cond, B, vec![b(skip)]);

    // Then: f = a[i]*2; store b[i] = f.
    push(&mut func, then_b, MulRR, vec![v(15), v(12), v(5)]);
    push(
        &mut func,
        then_b,
        Madd,
        vec![v64(18), v64(9), v64(10), v64(store_base)],
    ); // b + iv*4
    push(&mut func, then_b, StrRI, vec![v(15), v64(18), i(0)]);
    push(&mut func, then_b, MovR, vec![v(19), v(8)]); // carry iv
    push(&mut func, then_b, B, vec![b(latch)]);

    // Skip: carry iv, no store.
    push(&mut func, skip, MovR, vec![v(19), v(8)]);
    push(&mut func, skip, B, vec![b(latch)]);

    // Latch: iv + 1; writeback; back-edge.
    push(&mut func, latch, AddRR, vec![v(20), v(19), v(4)]);
    push(&mut func, latch, MovR, vec![v(6), v(20)]);
    push(&mut func, latch, B, vec![b(header)]);

    // Exit.
    push(&mut func, exit, Ret, vec![]);

    func.add_edge(bb0, header);
    func.add_edge(header, cond);
    func.add_edge(header, exit);
    func.add_edge(cond, then_b);
    func.add_edge(cond, skip);
    func.add_edge(then_b, latch);
    func.add_edge(skip, latch);
    func.add_edge(latch, header);
    func.next_vreg = 128;
    func
}

/// A plain 2-block map loop `for i<n: b[i] = a[i]*2` in the ROTATED guard/header/
/// latch shape neon-map fires on — condstore must NOT steal it.
fn build_plain_map_loop() -> MachFunction {
    let mut func = MachFunction::new("k".to_string(), Signature::new(vec![], vec![]));
    let bb0 = func.entry;
    let guard = func.create_block();
    let hdr = func.create_block();
    let latch = func.create_block();
    let exit = func.create_block();
    let push = |func: &mut MachFunction, blk: BlockId, op, ops| {
        let id = func.push_inst(MachInst::new(op, ops));
        func.append_inst(blk, id);
    };
    use AArch64Opcode::*;
    push(&mut func, bb0, Copy, vec![v64(0), v64(0)]);
    push(&mut func, bb0, Copy, vec![v64(1), v64(1)]);
    push(&mut func, bb0, Copy, vec![v(2), v(2)]);
    push(&mut func, bb0, Movz, vec![v(3), i(0)]);
    push(&mut func, bb0, Movz, vec![v(4), i(1)]);
    push(&mut func, bb0, Movz, vec![v(5), i(2)]);
    push(&mut func, bb0, Movz, vec![v64(10), i(4)]);
    push(&mut func, bb0, MovR, vec![v(6), v(3)]);
    push(&mut func, bb0, B, vec![b(guard)]);
    push(&mut func, guard, CmpRR, vec![v(6), v(2)]);
    push(&mut func, guard, BCond, vec![i(CC_LT), b(hdr)]);
    push(&mut func, guard, B, vec![b(exit)]);
    push(&mut func, hdr, Sxtw, vec![v64(9), v(6)]);
    push(&mut func, hdr, Madd, vec![v64(11), v64(9), v64(10), v64(1)]);
    push(&mut func, hdr, LdrRI, vec![v(12), v64(11), i(0)]);
    push(&mut func, hdr, MulRR, vec![v(15), v(12), v(5)]);
    push(&mut func, hdr, Madd, vec![v64(18), v64(9), v64(10), v64(0)]);
    push(&mut func, hdr, StrRI, vec![v(15), v64(18), i(0)]);
    push(&mut func, hdr, AddRR, vec![v(20), v(6), v(4)]);
    push(&mut func, hdr, B, vec![b(latch)]);
    push(&mut func, latch, AddRI, vec![v(6), v(20), i(0)]);
    push(&mut func, latch, CmpRR, vec![v(6), v(2)]);
    push(&mut func, latch, BCond, vec![i(CC_LT), b(hdr)]);
    push(&mut func, exit, Ret, vec![]);
    func.add_edge(bb0, guard);
    func.add_edge(guard, hdr);
    func.add_edge(guard, exit);
    func.add_edge(hdr, latch);
    func.add_edge(latch, hdr);
    func.add_edge(latch, exit);
    func.next_vreg = 128;
    func
}

#[test]
fn structural_runner_fires_with_noalias() {
    let mut func = build_condstore_loop(false);
    func.noalias_params = vec![0, 1]; // store base b (id0) + load base a (id1)
    let mut pass = NeonCondStorePass::new();
    let fired = (
        pass.run_with_structural_test_authority(&mut func),
        pass.fired(),
    );
    assert!(
        fired.0,
        "structural runner must recognize `if(a[i]>0) b[i]=a[i]*2`"
    );
    assert_eq!(fired.1, 1);
    // mask per sub-block: 4 CMGT.4S (a[i] > 0). value: 4 MUL.4S (a[i]*2).
    assert_eq!(
        count(&func, AArch64Opcode::NeonCmgtV),
        UNROLL,
        "4 CMGT masks"
    );
    assert_eq!(count(&func, AArch64Opcode::NeonMulV), UNROLL, "4 MUL value");
    // merge: 4 BIT (mask ? value : old_b). No fail-closed EOR/AND bitselect.
    assert_eq!(
        count(&func, AArch64Opcode::NeonBitV),
        UNROLL,
        "4 BIT merges"
    );
    // loads: base_a + base_b, each 2 LDP q-pairs = 4. stores: 2 STP q-pairs.
    assert_eq!(
        count(&func, AArch64Opcode::NeonLdpQPost),
        2 * (UNROLL / 2),
        "4 LDP q,q"
    );
    assert_eq!(
        count(&func, AArch64Opcode::NeonStpQPost),
        UNROLL / 2,
        "2 STP q,q"
    );
    assert_eq!(
        count(&func, AArch64Opcode::NeonSt1Post),
        0,
        "all stores paired"
    );
    // The scalar store is UNTOUCHED (purely additive): the original StrRI stays.
    assert_eq!(
        count(&func, AArch64Opcode::StrRI),
        1,
        "scalar store preserved"
    );
}

#[test]
fn structural_runner_accepts_in_place_without_noalias() {
    // Single-array in-place `if(a[i]>0) a[i]=a[i]*2`: the only pointer touched is
    // the store base, so no noalias is needed (aliasing is not load-bearing) —
    // Production still requires a validator-issued writable/ownership capability.
    let mut func = build_condstore_loop(true);
    assert!(func.noalias_params.is_empty());
    let mut pass = NeonCondStorePass::new();
    let fired = (
        pass.run_with_structural_test_authority(&mut func),
        pass.fired(),
    );
    assert!(
        fired.0,
        "structural runner must recognize single-array in-place shape"
    );
    assert_eq!(count(&func, AArch64Opcode::NeonBitV), UNROLL);
    // Only ONE array streamed (a == b): 1 base × 2 LDP q-pairs.
    assert_eq!(
        count(&func, AArch64Opcode::NeonLdpQPost),
        UNROLL / 2,
        "2 LDP q,q (one array)"
    );
    assert_eq!(count(&func, AArch64Opcode::NeonStpQPost), UNROLL / 2);
}

#[test]
fn public_pass_is_inert_without_typed_authority() {
    // The public pass has no typed ownership capability and is always inert.
    let mut func = build_condstore_loop(false);
    func.noalias_params = vec![0, 1];
    let mut pass = NeonCondStorePass::new();
    let changed = pass.run(&mut func);
    assert!(
        !changed,
        "public pass must BAIL without typed ownership evidence"
    );
    assert_eq!(count(&func, AArch64Opcode::NeonBitV), 0, "no NEON emitted");
    assert_eq!(
        count(&func, AArch64Opcode::NeonStpQPost),
        0,
        "no NEON store"
    );
}

#[test]
fn bails_on_overlap_without_noalias() {
    // Two distinct pointers `a`, `b` with NO noalias (they might overlap, e.g. the
    // differential's aliasing seed a==b): disjointness is unprovable → BAIL.
    let mut func = build_condstore_loop(false);
    assert!(func.noalias_params.is_empty());
    let mut pass = NeonCondStorePass::new();
    let changed = pass.run_with_structural_test_authority(&mut func);
    assert!(
        !changed,
        "two-pointer form without noalias must BAIL (possible overlap)"
    );
    assert_eq!(count(&func, AArch64Opcode::NeonBitV), 0);
    assert_eq!(count(&func, AArch64Opcode::NeonStpQPost), 0);
}

#[test]
fn bails_on_non_diamond_plain_map() {
    // A plain unconditional map loop (neon-map's shape) is NOT a conditional-store
    // diamond — condstore must leave it for neon-map.
    let mut func = build_plain_map_loop();
    func.noalias_params = vec![0, 1];
    let mut pass = NeonCondStorePass::new();
    let changed = pass.run_with_structural_test_authority(&mut func);
    assert!(!changed, "plain map loop must BAIL (no predicate diamond)");
    assert_eq!(count(&func, AArch64Opcode::NeonBitV), 0);
    assert_eq!(count(&func, AArch64Opcode::NeonStpQPost), 0);
}

// ---------------------------------------------------------------------------
// i64 (`.2D`) width mirror
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

/// The i64 mirror of [`build_condstore_loop`]: `for i<n: if (a[i] > 0)
/// b[i] = a[i]+7` with all-`Gpr64` carried values, `base + iv*8` addresses
/// (no sxtw — the index is already 64-bit). `MUL.2D` does not exist, so the
/// value is an ADD.
fn build_condstore_loop_i64(in_place: bool) -> MachFunction {
    let mut func = MachFunction::new("k".to_string(), Signature::new(vec![], vec![]));
    let bb0 = func.entry;
    let header = func.create_block();
    let cond = func.create_block();
    let then_b = func.create_block();
    let skip = func.create_block();
    let latch = func.create_block();
    let exit = func.create_block();

    let push = |func: &mut MachFunction, blk: BlockId, op, ops| {
        let id = func.push_inst(MachInst::new(op, ops));
        func.append_inst(blk, id);
    };
    use AArch64Opcode::*;
    let store_base = if in_place { 1 } else { 0 };

    // Preheader: pointers + constants; iv = 0.
    push(&mut func, bb0, Copy, vec![v64(0), v64(0)]); // base_b
    push(&mut func, bb0, Copy, vec![v64(1), v64(1)]); // base_a
    push(&mut func, bb0, Copy, vec![v64(2), v64(2)]); // n
    push(&mut func, bb0, Movz, vec![v64(3), i(0)]);
    push(&mut func, bb0, Movz, vec![v64(4), i(1)]);
    push(&mut func, bb0, Movz, vec![v64(5), i(7)]);
    push(&mut func, bb0, Movz, vec![v64(10), i(8)]); // element size
    push(&mut func, bb0, MovR, vec![v64(6), v64(3)]); // iv = 0
    push(&mut func, bb0, B, vec![b(header)]);

    // Header: counted test `iv < n`.
    push(&mut func, header, CmpRR, vec![v64(6), v64(2)]);
    push(&mut func, header, BCond, vec![i(CC_LT), b(cond)]);
    push(&mut func, header, B, vec![b(exit)]);

    // Cond: load a[i]; predicate a[i] > 0; branch to then (store) / skip.
    push(&mut func, cond, MovR, vec![v64(8), v64(6)]); // iv copy
    push(
        &mut func,
        cond,
        Madd,
        vec![v64(11), v64(8), v64(10), v64(1)],
    ); // a + iv*8
    push(&mut func, cond, LdrRI, vec![v64(12), v64(11), i(0)]); // a[i]
    push(&mut func, cond, CmpRR, vec![v64(12), v64(3)]); // a[i] : 0
    push(&mut func, cond, BCond, vec![i(CC_GT), b(then_b)]); // store when a[i] > 0
    push(&mut func, cond, B, vec![b(skip)]);

    // Then: f = a[i]+7; store b[i] = f.
    push(&mut func, then_b, AddRR, vec![v64(15), v64(12), v64(5)]);
    push(
        &mut func,
        then_b,
        Madd,
        vec![v64(18), v64(8), v64(10), v64(store_base)],
    ); // b + iv*8
    push(&mut func, then_b, StrRI, vec![v64(15), v64(18), i(0)]);
    push(&mut func, then_b, MovR, vec![v64(19), v64(8)]); // carry iv
    push(&mut func, then_b, B, vec![b(latch)]);

    // Skip: carry iv, no store.
    push(&mut func, skip, MovR, vec![v64(19), v64(8)]);
    push(&mut func, skip, B, vec![b(latch)]);

    // Latch: iv + 1; writeback; back-edge.
    push(&mut func, latch, AddRR, vec![v64(20), v64(19), v64(4)]);
    push(&mut func, latch, MovR, vec![v64(6), v64(20)]);
    push(&mut func, latch, B, vec![b(header)]);

    // Exit.
    push(&mut func, exit, Ret, vec![]);

    func.add_edge(bb0, header);
    func.add_edge(header, cond);
    func.add_edge(header, exit);
    func.add_edge(cond, then_b);
    func.add_edge(cond, skip);
    func.add_edge(then_b, latch);
    func.add_edge(skip, latch);
    func.add_edge(latch, header);
    func.next_vreg = 128;
    func
}

#[test]
fn i64_structural_runner_fires_with_noalias() {
    let mut func = build_condstore_loop_i64(false);
    func.noalias_params = vec![0, 1];
    let mut pass = NeonCondStorePass::new();
    let fired = (
        pass.run_with_structural_test_authority(&mut func),
        pass.fired(),
    );
    assert!(
        fired.0,
        "structural runner must recognize the valid i64 shape"
    );
    assert_eq!(fired.1, 1);
    // Same structure as i32: 4 masks / 4 values / 4 BIT merges / paired LDP+STP.
    assert_eq!(
        count(&func, AArch64Opcode::NeonCmgtV),
        UNROLL,
        "4 CMGT.2D masks"
    );
    assert_eq!(
        count(&func, AArch64Opcode::NeonAddV),
        UNROLL,
        "4 ADD.2D value"
    );
    assert_eq!(
        count(&func, AArch64Opcode::NeonBitV),
        UNROLL,
        "4 BIT merges"
    );
    assert_eq!(
        count(&func, AArch64Opcode::NeonLdpQPost),
        2 * (UNROLL / 2),
        "4 LDP q,q"
    );
    assert_eq!(
        count(&func, AArch64Opcode::NeonStpQPost),
        UNROLL / 2,
        "2 STP q,q"
    );
    assert_eq!(
        count(&func, AArch64Opcode::StrRI),
        1,
        "scalar store preserved"
    );
    // Every arrangement-carrying compare/arith is `.2D`; broadcasts are D-elem.
    for imms in imms_of(&func, AArch64Opcode::NeonCmgtV) {
        assert_eq!(imms, vec![ARR_D2], "mask compare at .2D");
    }
    for imms in imms_of(&func, AArch64Opcode::NeonAddV) {
        assert_eq!(imms, vec![ARR_D2], "value add at .2D");
    }
    for imms in imms_of(&func, AArch64Opcode::NeonDupGen) {
        assert_eq!(imms.last(), Some(&ELEM_D), "DUP broadcasts D elements");
    }
    // The i64 precheck (`n < 8 -> all-scalar`) exists.
    assert!(
        imms_of(&func, AArch64Opcode::CmpRI)
            .iter()
            .any(|imms| imms == &vec![UNROLL as i64 * VF_I64]),
        "i64 precheck compares the bound against width 8"
    );
}

#[test]
fn i64_structural_runner_accepts_in_place_without_noalias() {
    let mut func = build_condstore_loop_i64(true);
    assert!(func.noalias_params.is_empty());
    let mut pass = NeonCondStorePass::new();
    let fired = (
        pass.run_with_structural_test_authority(&mut func),
        pass.fired(),
    );
    assert!(
        fired.0,
        "structural runner must recognize i64 in-place shape"
    );
    assert_eq!(count(&func, AArch64Opcode::NeonBitV), UNROLL);
    assert_eq!(
        count(&func, AArch64Opcode::NeonLdpQPost),
        UNROLL / 2,
        "2 LDP q,q (one array)"
    );
    assert_eq!(count(&func, AArch64Opcode::NeonStpQPost), UNROLL / 2);
}

#[test]
fn i64_public_pass_is_inert_without_typed_authority() {
    let mut func = build_condstore_loop_i64(false);
    func.noalias_params = vec![0, 1];
    let mut pass = NeonCondStorePass::new();
    let changed = pass.run(&mut func);
    assert!(
        !changed,
        "i64 public pass must BAIL without typed ownership authority"
    );
    assert_eq!(count(&func, AArch64Opcode::NeonBitV), 0, "no NEON emitted");
    assert_eq!(
        count(&func, AArch64Opcode::NeonStpQPost),
        0,
        "no NEON store"
    );
}

#[test]
fn i64_bails_on_overlap_without_noalias() {
    // The aliasing gate is width-independent too.
    let mut func = build_condstore_loop_i64(false);
    assert!(func.noalias_params.is_empty());
    let mut pass = NeonCondStorePass::new();
    let changed = pass.run_with_structural_test_authority(&mut func);
    assert!(!changed, "i64 two-pointer form without noalias must BAIL");
    assert_eq!(count(&func, AArch64Opcode::NeonBitV), 0);
}

#[test]
fn i32_structural_shape_untouched_by_i64_mirror() {
    // Shape pin: the shipped i32 kernel still lowers at `.4S`/S-element codes
    // with the sxtw guard (no precheck) — the i64 mirror must not perturb it
    // (the fuzzer additionally diffs object bytes against pre-mirror goldens).
    let mut func = build_condstore_loop(false);
    func.noalias_params = vec![0, 1];
    let mut pass = NeonCondStorePass::new();
    let fired = pass.run_with_structural_test_authority(&mut func);
    assert!(fired);
    for imms in imms_of(&func, AArch64Opcode::NeonCmgtV) {
        assert_eq!(imms, vec![ARR_S4], "i32 mask compare stays at .4S");
    }
    for imms in imms_of(&func, AArch64Opcode::NeonMulV) {
        assert_eq!(imms, vec![ARR_S4], "i32 value mul stays at .4S");
    }
    for imms in imms_of(&func, AArch64Opcode::NeonDupGen) {
        assert_eq!(imms.last(), Some(&ELEM_S), "i32 DUP stays at S elements");
    }
    // No i64 precheck on the i32 path (no CmpRI against width 16 — the i32
    // guard is the sxtw compare, and the loop itself has no CmpRI at all).
    assert!(
        !imms_of(&func, AArch64Opcode::CmpRI)
            .iter()
            .any(|imms| imms == &vec![UNROLL as i64 * VF]),
        "no precheck on the i32 path"
    );
}
