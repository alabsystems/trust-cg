use super::*;
use trust_cg_ir::{MachInst, MachOperand, Signature, VReg};

fn vfp(id: u32) -> MachOperand {
    MachOperand::VReg(VReg::new(id, RegClass::Fpr64))
}
fn vg(id: u32) -> MachOperand {
    MachOperand::VReg(VReg::new(id, RegClass::Gpr64))
}
fn imm(x: i64) -> MachOperand {
    MachOperand::Imm(x)
}

fn func_with(insts: Vec<(AArch64Opcode, Vec<MachOperand>)>) -> MachFunction {
    let mut f = MachFunction::new("t".to_string(), Signature::new(vec![], vec![]));
    let b = f.entry;
    for (op, ops) in insts {
        let id = f.push_inst(MachInst::new(op, ops));
        f.append_inst(b, id);
    }
    f
}

fn opcodes(f: &MachFunction) -> Vec<AArch64Opcode> {
    f.blocks[0]
        .insts
        .iter()
        .map(|&id| f.inst(id).opcode)
        .collect()
}

fn count_op(f: &MachFunction, op: AArch64Opcode) -> usize {
    f.blocks[0]
        .insts
        .iter()
        .filter(|&&id| f.inst(id).opcode == op)
        .count()
}

#[test]
fn pairs_two_adjacent_fpr64_loads() {
    // ldr d0,[x10,#0]; ldr d1,[x10,#8]  ->  ldp d0,d1,[x10,#0]
    let mut f = func_with(vec![
        (AArch64Opcode::LdrRI, vec![vfp(0), vg(10), imm(0)]),
        (AArch64Opcode::LdrRI, vec![vfp(1), vg(10), imm(8)]),
    ]);
    assert!(MemPairFormation.run(&mut f));
    assert_eq!(opcodes(&f), vec![AArch64Opcode::LdpRI]);
    let p = f.inst(f.blocks[0].insts[0]);
    assert_eq!(p.operands[0], vfp(0)); // lower-offset data first
    assert_eq!(p.operands[1], vfp(1));
    assert_eq!(p.operands[2], vg(10)); // base
    assert_eq!(p.operands[3], imm(0)); // lower offset
}

#[test]
fn pairs_two_adjacent_fpr64_stores_and_orders_by_offset() {
    // str d1,[x10,#8]; str d0,[x10,#0]  (reversed) -> stp d0,d1,[x10,#0]
    let mut f = func_with(vec![
        (AArch64Opcode::StrRI, vec![vfp(1), vg(10), imm(8)]),
        (AArch64Opcode::StrRI, vec![vfp(0), vg(10), imm(0)]),
    ]);
    assert!(MemPairFormation.run(&mut f));
    assert_eq!(opcodes(&f), vec![AArch64Opcode::StpRI]);
    let p = f.inst(f.blocks[0].insts[0]);
    assert_eq!(p.operands[0], vfp(0)); // lower offset's source first
    assert_eq!(p.operands[1], vfp(1));
    assert_eq!(p.operands[3], imm(0));
}

#[test]
fn does_not_pair_nonconsecutive_offsets() {
    let mut f = func_with(vec![
        (AArch64Opcode::LdrRI, vec![vfp(0), vg(10), imm(0)]),
        (AArch64Opcode::LdrRI, vec![vfp(1), vg(10), imm(16)]), // gap
    ]);
    assert!(!MemPairFormation.run(&mut f));
    assert_eq!(
        opcodes(&f),
        vec![AArch64Opcode::LdrRI, AArch64Opcode::LdrRI]
    );
}

#[test]
fn does_not_pair_different_base() {
    let mut f = func_with(vec![
        (AArch64Opcode::LdrRI, vec![vfp(0), vg(10), imm(0)]),
        (AArch64Opcode::LdrRI, vec![vfp(1), vg(11), imm(8)]),
    ]);
    assert!(!MemPairFormation.run(&mut f));
}

#[test]
fn does_not_pair_loads_into_same_register_or_base() {
    // same dest reg (unpredictable LDP)
    let mut f = func_with(vec![
        (AArch64Opcode::LdrRI, vec![vfp(0), vg(10), imm(0)]),
        (AArch64Opcode::LdrRI, vec![vfp(0), vg(10), imm(8)]),
    ]);
    assert!(!MemPairFormation.run(&mut f));
    // dest equals base (Gpr load into its own address reg)
    let mut g = func_with(vec![
        (AArch64Opcode::LdrRI, vec![vg(10), vg(10), imm(0)]),
        (AArch64Opcode::LdrRI, vec![vg(1), vg(10), imm(8)]),
    ]);
    assert!(!MemPairFormation.run(&mut g));
}

#[test]
fn does_not_pair_mismatched_class() {
    let mut f = func_with(vec![
        (AArch64Opcode::LdrRI, vec![vfp(0), vg(10), imm(0)]),
        (AArch64Opcode::LdrRI, vec![vg(1), vg(10), imm(8)]),
    ]);
    assert!(!MemPairFormation.run(&mut f));
}

#[test]
fn rejects_out_of_range_pair_offset() {
    // byte offset 8*64 = 512 -> /8 = 64, just past the [-64,63] imm7 range.
    let mut f = func_with(vec![
        (AArch64Opcode::LdrRI, vec![vfp(0), vg(10), imm(512)]),
        (AArch64Opcode::LdrRI, vec![vfp(1), vg(10), imm(520)]),
    ]);
    assert!(!MemPairFormation.run(&mut f));
}

// --- Windowed load pairing (a later load hoisted over a hoist-safe gap) ---

#[test]
fn windowed_pairs_loads_across_a_benign_compute_op() {
    // ldr d0,[x10,#0]; fmadd d5,d1,d2,d3 (pure, no store/base-redef);
    // ldr d4,[x10,#8]  ->  ldp d0,d4,[x10,#0]; fmadd ...
    let mut f = func_with(vec![
        (AArch64Opcode::LdrRI, vec![vfp(0), vg(10), imm(0)]),
        (AArch64Opcode::FmaddRR, vec![vfp(5), vfp(1), vfp(2), vfp(3)]),
        (AArch64Opcode::LdrRI, vec![vfp(4), vg(10), imm(8)]),
    ]);
    assert!(MemPairFormation.run(&mut f));
    assert_eq!(
        opcodes(&f),
        vec![AArch64Opcode::LdpRI, AArch64Opcode::FmaddRR]
    );
    let p = f.inst(f.blocks[0].insts[0]);
    assert_eq!(p.operands[0], vfp(0));
    assert_eq!(p.operands[1], vfp(4)); // hoisted partner
}

#[test]
fn windowed_bails_on_intervening_store() {
    // A store between could alias the loaded slot — must not hoist.
    let mut f = func_with(vec![
        (AArch64Opcode::LdrRI, vec![vfp(0), vg(10), imm(0)]),
        (AArch64Opcode::StrRI, vec![vfp(9), vg(11), imm(0)]),
        (AArch64Opcode::LdrRI, vec![vfp(4), vg(10), imm(8)]),
    ]);
    assert!(!MemPairFormation.run(&mut f));
    assert_eq!(count_op(&f, AArch64Opcode::LdpRI), 0);
}

#[test]
fn windowed_bails_on_base_redefinition() {
    // The base x10 is rewritten before the second load — hoisting would read a
    // different address.
    let mut f = func_with(vec![
        (AArch64Opcode::LdrRI, vec![vfp(0), vg(10), imm(0)]),
        (AArch64Opcode::AddRR, vec![vg(10), vg(10), vg(12)]), // base redef
        (AArch64Opcode::LdrRI, vec![vfp(4), vg(10), imm(8)]),
    ]);
    assert!(!MemPairFormation.run(&mut f));
    assert_eq!(count_op(&f, AArch64Opcode::LdpRI), 0);
}

#[test]
fn windowed_bails_when_gap_reads_the_moved_dest() {
    // An op between reads d4 (the moved load's dest) before its original def —
    // hoisting the def earlier would change what it reads.
    let mut f = func_with(vec![
        (AArch64Opcode::LdrRI, vec![vfp(0), vg(10), imm(0)]),
        (AArch64Opcode::FmaddRR, vec![vfp(5), vfp(4), vfp(2), vfp(3)]), // reads d4
        (AArch64Opcode::LdrRI, vec![vfp(4), vg(10), imm(8)]),
    ]);
    assert!(!MemPairFormation.run(&mut f));
    assert_eq!(count_op(&f, AArch64Opcode::LdpRI), 0);
}

#[test]
fn greedy_pairs_a_run_of_four_stores() {
    // Four consecutive stores -> two STPs.
    let mut f = func_with(vec![
        (AArch64Opcode::StrRI, vec![vfp(0), vg(10), imm(0)]),
        (AArch64Opcode::StrRI, vec![vfp(1), vg(10), imm(8)]),
        (AArch64Opcode::StrRI, vec![vfp(2), vg(10), imm(16)]),
        (AArch64Opcode::StrRI, vec![vfp(3), vg(10), imm(24)]),
    ]);
    assert!(MemPairFormation.run(&mut f));
    assert_eq!(
        opcodes(&f),
        vec![AArch64Opcode::StpRI, AArch64Opcode::StpRI]
    );
}

#[test]
fn load_pair_vetoed_when_a_slot_aliases_a_same_base_store() {
    // ldr d0,[x10,#8]; ldr d1,[x10,#16]  would pair, but a same-base store to
    // [x10,#16] in the block straddles the LDP's [8,24) range: the wider LDP
    // cannot forward from the narrower store (loop store-forwarding stall), so
    // the pair is vetoed and both loads stay scalar.
    let mut f = func_with(vec![
        (AArch64Opcode::LdrRI, vec![vfp(0), vg(10), imm(8)]),
        (AArch64Opcode::LdrRI, vec![vfp(1), vg(10), imm(16)]),
        (AArch64Opcode::StrRI, vec![vfp(2), vg(10), imm(16)]),
    ]);
    assert!(!MemPairFormation.run(&mut f));
    assert_eq!(count_op(&f, AArch64Opcode::LdpRI), 0);
    assert_eq!(count_op(&f, AArch64Opcode::LdrRI), 2);
}

#[test]
fn load_pair_kept_when_store_is_to_a_different_base() {
    // Same two loads, but the aliasing store is to a DIFFERENT base (x11): we
    // cannot prove aliasing, so the pair is still formed.
    let mut f = func_with(vec![
        (AArch64Opcode::LdrRI, vec![vfp(0), vg(10), imm(8)]),
        (AArch64Opcode::LdrRI, vec![vfp(1), vg(10), imm(16)]),
        (AArch64Opcode::StrRI, vec![vfp(2), vg(11), imm(16)]),
    ]);
    assert!(MemPairFormation.run(&mut f));
    assert_eq!(count_op(&f, AArch64Opcode::LdpRI), 1);
}

#[test]
fn load_pair_kept_when_store_slot_is_outside_the_pair_range() {
    // Store to [x10,#24] does not overlap the LDP's [8,24) range (24 is the
    // exclusive end), so the pair is formed.
    let mut f = func_with(vec![
        (AArch64Opcode::LdrRI, vec![vfp(0), vg(10), imm(8)]),
        (AArch64Opcode::LdrRI, vec![vfp(1), vg(10), imm(16)]),
        (AArch64Opcode::StrRI, vec![vfp(2), vg(10), imm(24)]),
    ]);
    assert!(MemPairFormation.run(&mut f));
    assert_eq!(count_op(&f, AArch64Opcode::LdpRI), 1);
}

#[test]
fn store_pair_not_vetoed_by_the_load_hazard_guard() {
    // The guard only vetoes LOAD pairs; a store pair straddling a same-base
    // store (itself) still forms.
    let mut f = func_with(vec![
        (AArch64Opcode::StrRI, vec![vfp(0), vg(10), imm(8)]),
        (AArch64Opcode::StrRI, vec![vfp(1), vg(10), imm(16)]),
    ]);
    assert!(MemPairFormation.run(&mut f));
    assert_eq!(count_op(&f, AArch64Opcode::StpRI), 1);
}

#[test]
fn hazard_guard_kill_switch_re_enables_aggressive_pairing() {
    let insts = vec![
        (AArch64Opcode::LdrRI, vec![vfp(0), vg(10), imm(8)]),
        (AArch64Opcode::LdrRI, vec![vfp(1), vg(10), imm(16)]),
        (AArch64Opcode::StrRI, vec![vfp(2), vg(10), imm(16)]),
    ];
    // The thread-local kill switch is restored on scope exit, even on panic.
    let (f, formed) =
        crate::env_lock::with_env_overrides(&[("TCG_NO_MEM_PAIR_HAZARD_GUARD", "1")], || {
            let mut f = func_with(insts);
            let formed = MemPairFormation.run(&mut f);
            (f, formed)
        });
    assert!(formed);
    assert_eq!(count_op(&f, AArch64Opcode::LdpRI), 1);
}

// --- AddRI base fold-back (register-materialized adjacency) ---

#[test]
fn resolves_addri_base_and_pairs_loads() {
    // x11 = x10 + 8 ; ldr d0,[x10,#0] ; ldr d1,[x11,#0]  ->  ldp d0,d1,[x10,#0]
    // (the second base folds back onto x10 with offset 8, exposing the pair).
    let mut f = func_with(vec![
        (AArch64Opcode::AddRI, vec![vg(11), vg(10), imm(8)]),
        (AArch64Opcode::LdrRI, vec![vfp(0), vg(10), imm(0)]),
        (AArch64Opcode::LdrRI, vec![vfp(1), vg(11), imm(0)]),
    ]);
    assert!(MemPairFormation.run(&mut f));
    assert_eq!(count_op(&f, AArch64Opcode::LdpRI), 1);
    let p = f.inst(
        *f.blocks[0]
            .insts
            .iter()
            .find(|&&id| f.inst(id).opcode == AArch64Opcode::LdpRI)
            .unwrap(),
    );
    assert_eq!(p.operands[0], vfp(0));
    assert_eq!(p.operands[1], vfp(1));
    assert_eq!(p.operands[2], vg(10)); // folded onto the root base
    assert_eq!(p.operands[3], imm(0));
}

#[test]
fn does_not_resolve_when_root_redefined_between() {
    // x11 = x10 + 8 ; x10 = x10 + x12 (root redef!) ; ldr d0,[x10] ; ldr d1,[x11]
    // Folding x11 onto the NEW x10 would read the wrong address — must not pair.
    let mut f = func_with(vec![
        (AArch64Opcode::AddRI, vec![vg(11), vg(10), imm(8)]),
        (AArch64Opcode::AddRR, vec![vg(10), vg(10), vg(12)]),
        (AArch64Opcode::LdrRI, vec![vfp(0), vg(10), imm(0)]),
        (AArch64Opcode::LdrRI, vec![vfp(1), vg(11), imm(0)]),
    ]);
    let formed = MemPairFormation.run(&mut f);
    assert_eq!(count_op(&f, AArch64Opcode::LdpRI), 0);
    assert!(!formed);
}

#[test]
fn does_not_resolve_when_base_has_two_defs() {
    // x11 defined twice (only its AddRI is a fold candidate, but a second def
    // makes the value at the load ambiguous) — must not fold/pair.
    let mut f = func_with(vec![
        (AArch64Opcode::AddRI, vec![vg(11), vg(10), imm(8)]),
        (AArch64Opcode::AddRR, vec![vg(11), vg(12), vg(13)]), // 2nd def of x11
        (AArch64Opcode::LdrRI, vec![vfp(0), vg(10), imm(0)]),
        (AArch64Opcode::LdrRI, vec![vfp(1), vg(11), imm(0)]),
    ]);
    MemPairFormation.run(&mut f);
    assert_eq!(count_op(&f, AArch64Opcode::LdpRI), 0);
}

// --- Windowed STORE sinking across a memory-pure gap ---

#[test]
fn store_sink_pairs_across_pure_gap() {
    // x11 = x10 + 8 ; str d0,[x10,#0] ; fadd (pure) ; str d3,[x11,#0]
    // The later store's value is computed between the two stores, so the earlier
    // store SINKS down to it: stp d0,d3,[x10,#0].
    let mut f = func_with(vec![
        (AArch64Opcode::AddRI, vec![vg(11), vg(10), imm(8)]),
        (AArch64Opcode::StrRI, vec![vfp(0), vg(10), imm(0)]),
        (AArch64Opcode::FaddRR, vec![vfp(3), vfp(1), vfp(2)]),
        (AArch64Opcode::StrRI, vec![vfp(3), vg(11), imm(0)]),
    ]);
    assert!(MemPairFormation.run(&mut f));
    assert_eq!(count_op(&f, AArch64Opcode::StpRI), 1);
    assert_eq!(count_op(&f, AArch64Opcode::StrRI), 0);
    // The STP lands at the partner's position (after the fadd), not before it.
    assert_eq!(opcodes(&f).last(), Some(&AArch64Opcode::StpRI));
}

#[test]
fn store_sink_bails_across_a_memory_op() {
    // A load sits between the two stores: sinking the first store past it could
    // reorder aliasing memory — must not fuse.
    let mut f = func_with(vec![
        (AArch64Opcode::AddRI, vec![vg(11), vg(10), imm(8)]),
        (AArch64Opcode::StrRI, vec![vfp(0), vg(10), imm(0)]),
        (AArch64Opcode::LdrRI, vec![vfp(5), vg(13), imm(0)]), // memory in the gap
        (AArch64Opcode::StrRI, vec![vfp(3), vg(11), imm(0)]),
    ]);
    MemPairFormation.run(&mut f);
    assert_eq!(count_op(&f, AArch64Opcode::StpRI), 0);
    assert_eq!(count_op(&f, AArch64Opcode::StrRI), 2);
}

#[test]
fn store_sink_bails_when_gap_redefines_sunk_data() {
    // The gap recomputes d0 (the earlier store's data) — sinking would store the
    // wrong value; must not fuse.
    let mut f = func_with(vec![
        (AArch64Opcode::AddRI, vec![vg(11), vg(10), imm(8)]),
        (AArch64Opcode::StrRI, vec![vfp(0), vg(10), imm(0)]),
        (AArch64Opcode::FaddRR, vec![vfp(0), vfp(1), vfp(2)]), // redefines d0
        (AArch64Opcode::StrRI, vec![vfp(3), vg(11), imm(0)]),
    ]);
    MemPairFormation.run(&mut f);
    assert_eq!(count_op(&f, AArch64Opcode::StpRI), 0);
}

// --- Loop-variant (block-local) base hazard exception ---

#[test]
fn load_pair_kept_when_block_local_base_store_only_follows() {
    // x10 is recomputed in-block (loop-variant): a same-base store that only
    // FOLLOWS the load pair cannot forward into it, so the pair still forms.
    let mut f = func_with(vec![
        (AArch64Opcode::AddRR, vec![vg(10), vg(12), vg(13)]), // block-local base
        (AArch64Opcode::LdrRI, vec![vfp(0), vg(10), imm(0)]),
        (AArch64Opcode::LdrRI, vec![vfp(1), vg(10), imm(8)]),
        (AArch64Opcode::StrRI, vec![vfp(2), vg(10), imm(0)]), // store FOLLOWS
    ]);
    assert!(MemPairFormation.run(&mut f));
    assert_eq!(count_op(&f, AArch64Opcode::LdpRI), 1);
}

#[test]
fn load_pair_vetoed_when_block_local_base_store_precedes() {
    // Same block-local base, but the aliasing store now PRECEDES the loads
    // (within-iteration read-after-write) — the pair is vetoed.
    let mut f = func_with(vec![
        (AArch64Opcode::AddRR, vec![vg(10), vg(12), vg(13)]),
        (AArch64Opcode::StrRI, vec![vfp(2), vg(10), imm(0)]), // store PRECEDES
        (AArch64Opcode::LdrRI, vec![vfp(0), vg(10), imm(0)]),
        (AArch64Opcode::LdrRI, vec![vfp(1), vg(10), imm(8)]),
    ]);
    MemPairFormation.run(&mut f);
    assert_eq!(count_op(&f, AArch64Opcode::LdpRI), 0);
}

#[test]
fn windowed_gpr_pair_over_movz_gap_keeps_dests_distinct_from_each_other_and_base() {
    // The exact fc_c8 `spec_from_iter_nested...::from_iter` block-4 shape that
    // exposed the spilled-LDP IP-scratch-clobber miscompile — both u64 lanes of
    // a `(u64, u64)` iterator element read through one base, with a `movz` in
    // the hoist gap:
    //   add  v20, v3, #8
    //   ldr  v21, [v20, #0]   <- anchor
    //   movz v19, #8          <- gap: pure, no mem write, no base redef
    //   ldr  v26, [v20, #8]   <- partner, hoisted up to the anchor
    //   mov  v137, v21
    //   mov  v138, v26
    // The vreg-level rewrite is sound and must KEEP firing (the miscompile was
    // never here): the formed `ldp v21, v26, [v20, #0]` must have DISTINCT dest
    // vregs, neither aliasing the base (same-dest / dest==base LDP is
    // CONSTRAINED UNPREDICTABLE). When regalloc later spills BOTH GPR dests
    // while the base stays in a real register, the spill lowering must SPLIT
    // the pair rather than occupy X16+X17 simultaneously — that contract lives
    // in trust-cg-codegen (pipeline.rs `materialize_spilled_load_pair` split +
    // frame.rs fail-closed `scratch_live_after` guard, eafc04f1; see the
    // module docs). This test pins the exposing shape so those codegen guards
    // stay reachable.
    let mut f = func_with(vec![
        (AArch64Opcode::AddRI, vec![vg(20), vg(3), imm(8)]),
        (AArch64Opcode::LdrRI, vec![vg(21), vg(20), imm(0)]),
        (AArch64Opcode::Movz, vec![vg(19), imm(8)]),
        (AArch64Opcode::LdrRI, vec![vg(26), vg(20), imm(8)]),
        (AArch64Opcode::MovR, vec![vg(137), vg(21)]),
        (AArch64Opcode::MovR, vec![vg(138), vg(26)]),
    ]);
    assert!(MemPairFormation.run(&mut f));
    assert_eq!(
        opcodes(&f),
        vec![
            AArch64Opcode::AddRI,
            AArch64Opcode::LdpRI,
            AArch64Opcode::Movz,
            AArch64Opcode::MovR,
            AArch64Opcode::MovR,
        ]
    );
    let p = f.inst(f.blocks[0].insts[1]);
    assert_eq!(p.operands[0], vg(21)); // anchor lane (lower offset) first
    assert_eq!(p.operands[1], vg(26)); // hoisted partner lane
    assert_eq!(p.operands[2], vg(20)); // base unchanged
    assert_eq!(p.operands[3], imm(0)); // lower offset
    // Structural soundness of the LDP itself: two distinct dests, neither
    // equal to the address register.
    assert_ne!(p.operands[0], p.operands[1]);
    assert_ne!(p.operands[0], p.operands[2]);
    assert_ne!(p.operands[1], p.operands[2]);
}

// ---------------------------------------------------------------------------
// GPR cross-store sink (`TCG_NO_MEM_PAIR_XSTORE` feature): sinking an integer
// field store past a PROVABLY-DISJOINT store to fuse with its pair partner —
// the Stanford/Towers `Move` push-tail shape (`cellspace[el].next = ...;
// stack[s] = el; cellspace[el].discsize = ...`).
// ---------------------------------------------------------------------------

fn vg32(id: u32) -> MachOperand {
    MachOperand::VReg(VReg::new(id, RegClass::Gpr32))
}
fn sym(s: &str) -> MachOperand {
    MachOperand::Symbol(s.to_string())
}

/// The Towers push tail: two same-base GPR32 field stores at #4/#0 split by a
/// register-offset store rooted at a DIFFERENT global symbol. The first field
/// store must sink past the disjoint store and fuse into `StpRI` at the
/// partner's position.
#[test]
fn gpr_store_sinks_across_distinct_symbol_store() {
    let mut f = func_with(vec![
        (AArch64Opcode::Adrp, vec![vg(1), sym("cellspace")]),
        (
            AArch64Opcode::AddPCRel,
            vec![vg(2), vg(1), sym("cellspace")],
        ),
        (AArch64Opcode::Adrp, vec![vg(3), sym("stack")]),
        (AArch64Opcode::AddPCRel, vec![vg(4), vg(3), sym("stack")]),
        // el-scaled cellspace element address: v5 = v2 + v6<<3
        (AArch64Opcode::AddRRShift, vec![vg(5), vg(2), vg(6), imm(3)]),
        // cellspace[el].next = w20
        (AArch64Opcode::StrRI, vec![vg32(20), vg(5), imm(4)]),
        // stack[s] = w21 (register-offset store, distinct symbol root)
        (AArch64Opcode::StrRO, vec![vg32(21), vg(4), vg(7)]),
        // cellspace[el].discsize = w22
        (AArch64Opcode::StrRI, vec![vg32(22), vg(5), imm(0)]),
    ]);
    assert!(MemPairFormation.run(&mut f));
    assert_eq!(count_op(&f, AArch64Opcode::StpRI), 1);
    assert_eq!(count_op(&f, AArch64Opcode::StrRI), 0);
    // The disjoint store stays put; the pair lands at the partner's position.
    let ops = opcodes(&f);
    let stro_pos = ops
        .iter()
        .position(|&o| o == AArch64Opcode::StrRO)
        .expect("gap store kept");
    let stp_pos = ops
        .iter()
        .position(|&o| o == AArch64Opcode::StpRI)
        .expect("pair formed");
    assert!(stro_pos < stp_pos, "pair lands at the partner position");
    let p = f.inst(f.blocks[0].insts[stp_pos]);
    assert_eq!(p.operands[0], vg32(22)); // lower-offset (#0) data first
    assert_eq!(p.operands[1], vg32(20));
    assert_eq!(p.operands[2], vg(5));
    assert_eq!(p.operands[3], imm(0));
}

/// SAME symbol root on both sides: the gap store may overlap (unknown
/// indices), so the scan must halt and no pair may form.
#[test]
fn gpr_store_does_not_sink_across_same_symbol_store() {
    let mut f = func_with(vec![
        (AArch64Opcode::Adrp, vec![vg(1), sym("cellspace")]),
        (
            AArch64Opcode::AddPCRel,
            vec![vg(2), vg(1), sym("cellspace")],
        ),
        (AArch64Opcode::AddRRShift, vec![vg(5), vg(2), vg(6), imm(3)]),
        (AArch64Opcode::StrRI, vec![vg32(20), vg(5), imm(4)]),
        // Same-symbol register-offset store (cellspace[k].x = ...): may alias.
        (AArch64Opcode::StrRO, vec![vg32(21), vg(2), vg(7)]),
        (AArch64Opcode::StrRI, vec![vg32(22), vg(5), imm(0)]),
    ]);
    assert!(!MemPairFormation.run(&mut f));
    assert_eq!(count_op(&f, AArch64Opcode::StpRI), 0);
}

/// Untraceable gap-store base (no AddPCRel root): fail closed, no pair.
#[test]
fn gpr_store_does_not_sink_across_unknown_base_store() {
    let mut f = func_with(vec![
        (AArch64Opcode::Adrp, vec![vg(1), sym("cellspace")]),
        (
            AArch64Opcode::AddPCRel,
            vec![vg(2), vg(1), sym("cellspace")],
        ),
        (AArch64Opcode::AddRRShift, vec![vg(5), vg(2), vg(6), imm(3)]),
        (AArch64Opcode::StrRI, vec![vg32(20), vg(5), imm(4)]),
        // v9 has no def at all (function argument / unknown pointer).
        (AArch64Opcode::StrRO, vec![vg32(21), vg(9), vg(7)]),
        (AArch64Opcode::StrRI, vec![vg32(22), vg(5), imm(0)]),
    ]);
    assert!(!MemPairFormation.run(&mut f));
    assert_eq!(count_op(&f, AArch64Opcode::StpRI), 0);
}

/// Same-base gap store with a DISJOINT immediate range (rule 1): the sink may
/// cross it even with no symbol provenance at all.
#[test]
fn gpr_store_sinks_across_same_base_disjoint_range_store() {
    let mut f = func_with(vec![
        (AArch64Opcode::StrRI, vec![vg32(20), vg(5), imm(4)]),
        // [v5+12, v5+16) does not overlap [v5+4, v5+8).
        (AArch64Opcode::StrRI, vec![vg32(21), vg(5), imm(12)]),
        (AArch64Opcode::StrRI, vec![vg32(22), vg(5), imm(0)]),
    ]);
    assert!(MemPairFormation.run(&mut f));
    assert_eq!(count_op(&f, AArch64Opcode::StpRI), 1);
    // The middle store survives as the only remaining scalar StrRI.
    assert_eq!(count_op(&f, AArch64Opcode::StrRI), 1);
}

/// Same-base gap store whose range OVERLAPS the sunk store: must halt. (The
/// gap store is a BYTE store inside the sunk word — a shape the adjacent
/// fuser cannot legally absorb either, isolating the sink decision.)
#[test]
fn gpr_store_does_not_sink_across_same_base_overlapping_store() {
    let mut f = func_with(vec![
        (AArch64Opcode::StrRI, vec![vg32(20), vg(5), imm(4)]),
        (AArch64Opcode::StrbRI, vec![vg32(21), vg(5), imm(5)]), // [5,6) in [4,8)
        (AArch64Opcode::StrRI, vec![vg32(22), vg(5), imm(0)]),
    ]);
    assert!(!MemPairFormation.run(&mut f));
    assert_eq!(count_op(&f, AArch64Opcode::StpRI), 0);
}

/// A bare `Adrp` root (page granularity — several objects can share a page)
/// must NOT license disjointness even across distinct symbols.
#[test]
fn gpr_store_does_not_sink_across_bare_adrp_rooted_store() {
    let mut f = func_with(vec![
        (AArch64Opcode::Adrp, vec![vg(1), sym("cellspace")]),
        (
            AArch64Opcode::AddPCRel,
            vec![vg(2), vg(1), sym("cellspace")],
        ),
        (AArch64Opcode::AddRRShift, vec![vg(5), vg(2), vg(6), imm(3)]),
        (AArch64Opcode::StrRI, vec![vg32(20), vg(5), imm(4)]),
        // Gap store addressed straight off an Adrp page base.
        (AArch64Opcode::Adrp, vec![vg(8), sym("stack")]),
        (AArch64Opcode::StrRO, vec![vg32(21), vg(8), vg(7)]),
        (AArch64Opcode::StrRI, vec![vg32(22), vg(5), imm(0)]),
    ]);
    assert!(!MemPairFormation.run(&mut f));
    assert_eq!(count_op(&f, AArch64Opcode::StpRI), 0);
}

/// A multi-def base vreg is untraceable (its value depends on position):
/// fail closed.
#[test]
fn gpr_store_does_not_sink_when_gap_base_is_multi_def() {
    let mut f = func_with(vec![
        (AArch64Opcode::Adrp, vec![vg(1), sym("cellspace")]),
        (
            AArch64Opcode::AddPCRel,
            vec![vg(2), vg(1), sym("cellspace")],
        ),
        (AArch64Opcode::AddRRShift, vec![vg(5), vg(2), vg(6), imm(3)]),
        (AArch64Opcode::Adrp, vec![vg(3), sym("stack")]),
        (AArch64Opcode::AddPCRel, vec![vg(4), vg(3), sym("stack")]),
        // Second def of v4 — now multi-def, must refuse the trace.
        (AArch64Opcode::AddRI, vec![vg(4), vg(4), imm(8)]),
        (AArch64Opcode::StrRI, vec![vg32(20), vg(5), imm(4)]),
        (AArch64Opcode::StrRO, vec![vg32(21), vg(4), vg(7)]),
        (AArch64Opcode::StrRI, vec![vg32(22), vg(5), imm(0)]),
    ]);
    assert!(!MemPairFormation.run(&mut f));
    assert_eq!(count_op(&f, AArch64Opcode::StpRI), 0);
}
