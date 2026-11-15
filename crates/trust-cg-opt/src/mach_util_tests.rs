// trust-cg-opt/mach_util_tests.rs - every-path resolver unit tests
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! The every-path resolvers in `mach_util` against the shapes that made the
//! last-wins def map wrong: a register written on several paths (per-edge
//! `Movz`, phi copies), a copy that is not the register's only def, and
//! `Movz`+`Movk` runs that are and are not contiguous. Each multi-def case also
//! asserts what the last-wins map names, so the test shows the map would have
//! answered differently.

use super::*;
use trust_cg_ir::{RegClass, Signature};

fn x(id: u32) -> VReg {
    VReg::new(id, RegClass::Gpr64)
}
fn w(id: u32) -> VReg {
    VReg::new(id, RegClass::Gpr32)
}
fn vr(v: VReg) -> MachOperand {
    MachOperand::VReg(v)
}
fn im(k: i64) -> MachOperand {
    MachOperand::Imm(k)
}
fn bl(b: BlockId) -> MachOperand {
    MachOperand::Block(b)
}

fn new_func() -> MachFunction {
    MachFunction::new("t".into(), Signature::new(vec![], vec![]))
}

fn emit(f: &mut MachFunction, b: BlockId, op: AArch64Opcode, ops: Vec<MachOperand>) -> InstId {
    let id = f.push_inst(MachInst::new(op, ops));
    f.append_inst(b, id);
    id
}

/// `entry -> {left, right} -> join`; `left` and `right` each run `arm`.
fn diamond(
    arm: impl Fn(&mut MachFunction, BlockId, bool),
) -> (MachFunction, BlockId, BlockId, BlockId) {
    let mut f = new_func();
    let e = f.entry;
    let (left, right, join) = (f.create_block(), f.create_block(), f.create_block());
    f.add_edge(e, left);
    f.add_edge(e, right);
    f.add_edge(left, join);
    f.add_edge(right, join);
    emit(&mut f, e, AArch64Opcode::CmpRI, vec![vr(x(90)), im(0)]);
    emit(&mut f, e, AArch64Opcode::BCond, vec![im(0), bl(left)]);
    emit(&mut f, e, AArch64Opcode::B, vec![bl(right)]);
    arm(&mut f, left, true);
    emit(&mut f, left, AArch64Opcode::B, vec![bl(join)]);
    arm(&mut f, right, false);
    emit(&mut f, right, AArch64Opcode::B, vec![bl(join)]);
    (f, left, right, join)
}

fn last_wins(f: &MachFunction) -> HashMap<u32, InstId> {
    crate::effects::build_reaching_def_map(f)
}

/// An index that answers like a scan, to exercise the indexed fast paths.
struct Indexed(HashMap<u32, InstId>);

impl DefLookup for Indexed {
    fn last_def(&self, id: u32) -> Option<InstId> {
        self.0.get(&id).copied()
    }
    fn indexed_def_count(&self, func: &MachFunction, id: u32) -> Option<usize> {
        Some(crate::effects::live_def_count(func, id))
    }
}

#[test]
fn a_single_movz_is_a_constant() {
    let mut f = new_func();
    let e = f.entry;
    emit(&mut f, e, AArch64Opcode::Movz, vec![vr(w(1)), im(41)]);
    emit(&mut f, e, AArch64Opcode::Ret, vec![]);
    let def = last_wins(&f);
    assert_eq!(const_value(&f, &def, w(1)), Some(41));
    assert_eq!(const_value(&f, &Indexed(def.clone()), w(1)), Some(41));
    assert_eq!(materialized_value(&f, &def, w(1)), Some(41));
    assert_eq!(copied_const(&f, &def, w(1)), Some(41));
}

/// The per-exit-edge shape: one `Movz` per path into the same register.
#[test]
fn a_register_written_with_different_constants_is_not_a_constant() {
    let (f, _, right, _) = diamond(|f, b, left| {
        emit(
            f,
            b,
            AArch64Opcode::Movz,
            vec![vr(x(1)), im(if left { 3 } else { 8 })],
        );
    });
    let def = last_wins(&f);
    // The last-wins map names the right arm's `Movz #8`.
    assert!(f.block(right).insts.contains(&def[&1]));
    assert_eq!(const_value(&f, &def, x(1)), None);
    assert_eq!(const_value(&f, &Indexed(def.clone()), x(1)), None);
    assert_eq!(materialized_value(&f, &def, x(1)), None);
    assert_eq!(materialized_value(&f, &Indexed(def.clone()), x(1)), None);
    assert_eq!(copied_const(&f, &def, x(1)), None);
}

/// A phi of one constant on both edges holds it on every path.
#[test]
fn a_register_written_with_the_same_constant_everywhere_is_that_constant() {
    let (f, ..) = diamond(|f, b, _| {
        emit(f, b, AArch64Opcode::Movz, vec![vr(x(1)), im(16)]);
    });
    let def = last_wins(&f);
    assert_eq!(const_value(&f, &def, x(1)), Some(16));
    assert_eq!(const_value(&f, &Indexed(def.clone()), x(1)), Some(16));
    assert_eq!(materialized_value(&f, &def, x(1)), Some(16));
}

/// A write through the other register class is a write: the id is matched,
/// not the full vreg.
#[test]
fn a_write_through_the_other_class_counts() {
    let (f, ..) = diamond(|f, b, left| {
        let v = if left { w(1) } else { x(1) };
        emit(
            f,
            b,
            AArch64Opcode::Movz,
            vec![vr(v), im(if left { 3 } else { 8 })],
        );
    });
    let def = last_wins(&f);
    assert_eq!(const_value(&f, &def, x(1)), None);
    assert_eq!(materialized_value(&f, &def, x(1)), None);
}

#[test]
fn any_other_def_makes_the_register_unknown() {
    let (f, ..) = diamond(|f, b, left| {
        if left {
            emit(f, b, AArch64Opcode::AddRI, vec![vr(x(1)), vr(x(2)), im(8)]);
        } else {
            emit(f, b, AArch64Opcode::Movz, vec![vr(x(1)), im(8)]);
        }
    });
    let def = last_wins(&f);
    assert_eq!(const_value(&f, &def, x(1)), None);
    assert_eq!(materialized_value(&f, &def, x(1)), None);
}

/// Instructions outside the layout never run and are not defs.
#[test]
fn a_detached_def_is_ignored() {
    let mut f = new_func();
    let e = f.entry;
    emit(&mut f, e, AArch64Opcode::Movz, vec![vr(x(1)), im(5)]);
    emit(&mut f, e, AArch64Opcode::Ret, vec![]);
    f.push_inst(MachInst::new(AArch64Opcode::Movz, vec![vr(x(1)), im(9)]));
    let def = last_wins(&f);
    assert_eq!(const_value(&f, &def, x(1)), Some(5));
}

#[test]
fn a_shifted_or_out_of_range_movz_is_not_folded() {
    let mut f = new_func();
    let e = f.entry;
    emit(
        &mut f,
        e,
        AArch64Opcode::Movz,
        vec![vr(x(1)), im(7), im(16)],
    );
    emit(&mut f, e, AArch64Opcode::Movz, vec![vr(x(2)), im(7), im(0)]);
    emit(&mut f, e, AArch64Opcode::Movz, vec![vr(x(3)), im(0x1_0000)]);
    emit(&mut f, e, AArch64Opcode::Ret, vec![]);
    let def = last_wins(&f);
    assert_eq!(const_value(&f, &def, x(1)), None);
    assert_eq!(
        const_value(&f, &def, x(2)),
        Some(7),
        "an explicit lsl #0 is the same value"
    );
    assert_eq!(const_value(&f, &def, x(3)), None);
}

/// `Movz` + `Movk` right after it: one run, one value (500001).
#[test]
fn a_contiguous_movz_movk_run_is_its_value() {
    let mut f = new_func();
    let e = f.entry;
    emit(&mut f, e, AArch64Opcode::Movz, vec![vr(x(1)), im(41249)]);
    emit(
        &mut f,
        e,
        AArch64Opcode::Movk,
        vec![vr(x(1)), im(7), im(16)],
    );
    emit(&mut f, e, AArch64Opcode::Ret, vec![]);
    let def = last_wins(&f);
    assert_eq!(materialized_value(&f, &def, x(1)), Some(500_001));
    assert_eq!(
        materialized_value(&f, &Indexed(def.clone()), x(1)),
        Some(500_001)
    );
    assert_eq!(copied_const(&f, &def, x(1)), Some(500_001));
    // The narrow resolver folds a lone 16-bit `Movz` only.
    assert_eq!(const_value(&f, &def, x(1)), None);
}

/// A read between the `Movz` and its `Movk` sees the low half only, so a run
/// another instruction interrupts is not a constant.
#[test]
fn an_interrupted_run_is_not_a_constant() {
    let mut f = new_func();
    let e = f.entry;
    emit(&mut f, e, AArch64Opcode::Movz, vec![vr(x(1)), im(41249)]);
    emit(
        &mut f,
        e,
        AArch64Opcode::AddRI,
        vec![vr(x(2)), vr(x(1)), im(1)],
    );
    emit(
        &mut f,
        e,
        AArch64Opcode::Movk,
        vec![vr(x(1)), im(7), im(16)],
    );
    emit(&mut f, e, AArch64Opcode::Ret, vec![]);
    let def = last_wins(&f);
    assert_eq!(materialized_value(&f, &def, x(1)), None);
}

/// One `Movz` + `Movk` run per path, of different values: the last-wins
/// `Movk` patched only its own block's `Movz`.
#[test]
fn runs_of_different_values_are_not_a_constant() {
    let (f, ..) = diamond(|f, b, left| {
        emit(
            f,
            b,
            AArch64Opcode::Movz,
            vec![vr(x(1)), im(if left { 1 } else { 2 })],
        );
        emit(f, b, AArch64Opcode::Movk, vec![vr(x(1)), im(7), im(16)]);
    });
    let def = last_wins(&f);
    assert_eq!(materialized_value(&f, &def, x(1)), None);
}

#[test]
fn runs_of_one_value_are_that_value() {
    let (f, ..) = diamond(|f, b, _| {
        emit(f, b, AArch64Opcode::Movz, vec![vr(x(1)), im(0xFFFF)]);
        emit(
            f,
            b,
            AArch64Opcode::Movk,
            vec![vr(x(1)), im(0xFFFF), im(16)],
        );
    });
    let def = last_wins(&f);
    assert_eq!(materialized_value(&f, &def, x(1)), Some(0xFFFF_FFFF));
}

/// A `Movk` patching a `Movz` in another block is not a run.
#[test]
fn a_movk_patching_another_block_is_not_a_run() {
    let mut f = new_func();
    let e = f.entry;
    let b = f.create_block();
    f.add_edge(e, b);
    emit(&mut f, e, AArch64Opcode::Movz, vec![vr(x(1)), im(1)]);
    emit(&mut f, e, AArch64Opcode::B, vec![bl(b)]);
    emit(
        &mut f,
        b,
        AArch64Opcode::Movk,
        vec![vr(x(1)), im(7), im(16)],
    );
    emit(&mut f, b, AArch64Opcode::Ret, vec![]);
    let def = last_wins(&f);
    assert_eq!(materialized_value(&f, &def, x(1)), None);
}

/// A copy that is the register's only def is walked; the same copy into a
/// register written elsewhere too is not (the outer-latch copy of the inner
/// induction).
#[test]
fn only_a_sole_def_copy_is_walked() {
    let mut f = new_func();
    let e = f.entry;
    emit(&mut f, e, AArch64Opcode::Movz, vec![vr(x(3)), im(12)]);
    emit(&mut f, e, AArch64Opcode::MovR, vec![vr(x(2)), vr(x(3))]);
    emit(&mut f, e, AArch64Opcode::Ret, vec![]);
    let def = last_wins(&f);
    assert_eq!(sole_copy_source(&f, &def, x(2)), Some(x(3)));
    assert_eq!(strip_copies(&f, &def, x(2)), x(3));
    assert!(copies_reg(&f, &def, x(2), x(3)));
    assert_eq!(copied_const(&f, &def, x(2)), Some(12));

    let (f, _, right, _) = diamond(|f, b, left| {
        let src = if left { x(4) } else { x(9) };
        emit(f, b, AArch64Opcode::MovR, vec![vr(x(2)), vr(src)]);
    });
    let def = last_wins(&f);
    // The last-wins map names the right arm's copy of x9.
    assert!(f.block(right).insts.contains(&def[&2]));
    assert_eq!(sole_copy_source(&f, &def, x(2)), None);
    assert_eq!(sole_copy_source(&f, &Indexed(def.clone()), x(2)), None);
    assert_eq!(strip_copies(&f, &def, x(2)), x(2));
    assert!(!copies_reg(&f, &def, x(2), x(9)));
    assert!(
        copies_reg(&f, &def, x(9), x(9)),
        "the target itself is never walked"
    );
    assert_eq!(sole_def(&f, &def, 2), None);
    assert_eq!(sole_def(&f, &def, 90), None, "no def at all");
}

/// A map from another function state is not trusted: the scan must find the
/// instruction the map names.
#[test]
fn a_stale_map_is_not_trusted() {
    let mut f = new_func();
    let e = f.entry;
    let old = emit(&mut f, e, AArch64Opcode::MovR, vec![vr(x(2)), vr(x(3))]);
    emit(&mut f, e, AArch64Opcode::Ret, vec![]);
    let def = last_wins(&f);
    // The copy is replaced by a different def after the map was built.
    f.block_mut(e).insts.retain(|&i| i != old);
    let new = f.push_inst(MachInst::new(AArch64Opcode::MovR, vec![vr(x(2)), vr(x(5))]));
    f.block_mut(e).insts.insert(0, new);
    assert_eq!(sole_def(&f, &def, 2), None);
    assert_eq!(sole_copy_source(&f, &def, x(2)), None);
}

/// `b0` with successors `succs` and instructions `insts`, in a function whose
/// other blocks are `b1..=b3`.
fn edge_fixture(insts: Vec<(AArch64Opcode, Vec<MachOperand>)>, succs: &[u32]) -> MachFunction {
    let mut f = new_func();
    for _ in 0..3 {
        f.create_block();
    }
    let b0 = f.entry;
    for (op, ops) in insts {
        emit(&mut f, b0, op, ops);
    }
    for &s in succs {
        f.add_edge(b0, BlockId(s));
    }
    f
}

#[test]
fn a_block_whose_edges_are_its_branch_operands_is_reproducible() {
    let f = edge_fixture(
        vec![
            (AArch64Opcode::CmpRI, vec![vr(x(1)), im(0)]),
            (AArch64Opcode::BCond, vec![im(0), bl(BlockId(1))]),
            (AArch64Opcode::B, vec![bl(BlockId(2))]),
        ],
        &[1, 2],
    );
    assert!(clone_reproduces_out_edges(&f, f.entry));
    // The comparison is over sets: a successor recorded twice is one edge.
    let f = edge_fixture(
        vec![
            (AArch64Opcode::CmpRI, vec![vr(x(1)), im(0)]),
            (AArch64Opcode::BCond, vec![im(0), bl(BlockId(1))]),
            (AArch64Opcode::B, vec![bl(BlockId(1))]),
        ],
        &[1, 1],
    );
    assert!(clone_reproduces_out_edges(&f, f.entry));
    assert!(body_clone_reproduces_out_edges(&f, &[f.entry]));
}

/// The switch lowering's dispatch: its case edges live in the jump table.
#[test]
fn a_jump_table_dispatch_is_not_reproducible() {
    let mut f = edge_fixture(
        vec![
            (AArch64Opcode::CmpRI, vec![vr(x(1)), im(1)]),
            (AArch64Opcode::BCond, vec![im(8), bl(BlockId(3))]),
            (
                AArch64Opcode::Adr,
                vec![vr(x(2)), MachOperand::JumpTableIndex(0)],
            ),
            (AArch64Opcode::LdrswRO, vec![vr(x(3)), vr(x(2)), vr(x(1))]),
            (AArch64Opcode::AddRR, vec![vr(x(4)), vr(x(2)), vr(x(3))]),
            (AArch64Opcode::Br, vec![vr(x(4))]),
        ],
        &[3, 1, 2],
    );
    f.jump_tables.push(trust_cg_ir::function::JumpTableData {
        min_val: 0,
        targets: vec![BlockId(1), BlockId(2)],
    });
    assert!(!clone_reproduces_out_edges(&f, f.entry));
    assert!(!body_clone_reproduces_out_edges(&f, &[f.entry]));
}

/// The same dispatch after its `Adr` was hoisted elsewhere: no operand reads
/// the table any more, but the recorded case edges are still unnamed.
#[test]
fn a_dispatch_without_its_adr_is_not_reproducible() {
    let f = edge_fixture(
        vec![
            (AArch64Opcode::LdrswRO, vec![vr(x(3)), vr(x(2)), vr(x(1))]),
            (AArch64Opcode::AddRR, vec![vr(x(4)), vr(x(2)), vr(x(3))]),
            (AArch64Opcode::Br, vec![vr(x(4))]),
        ],
        &[1, 2],
    );
    assert!(!clone_reproduces_out_edges(&f, f.entry));
}

/// A fall-through edge, and an operand naming a block that is not a
/// successor, each break the correspondence.
#[test]
fn an_unnamed_edge_or_an_unrecorded_operand_is_not_reproducible() {
    let fall_through = edge_fixture(
        vec![
            (AArch64Opcode::CmpRI, vec![vr(x(1)), im(0)]),
            (AArch64Opcode::BCond, vec![im(0), bl(BlockId(1))]),
        ],
        &[1, 2],
    );
    assert!(!clone_reproduces_out_edges(
        &fall_through,
        fall_through.entry
    ));
    let unrecorded = edge_fixture(vec![(AArch64Opcode::B, vec![bl(BlockId(2))])], &[1]);
    assert!(!clone_reproduces_out_edges(&unrecorded, unrecorded.entry));
}
