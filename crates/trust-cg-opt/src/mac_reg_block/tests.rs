// Unit tests for mac-reg-block. The end-to-end gate is the native on/off/C
// reference differential `trust-cg-codegen/tests/e2e_aarch64_mac_reg_block_differential.rs`
// (fires on every admitted square nest, which it counts; negative controls
// stay untransformed and still compute the reference). Here we white-box the
// subtle counted-loop recognizer (`resolve_to_carried` / `verify_counted_0_n`)
// that must see through the conventional-SSA MovR-phi, body-copy and
// self-copy forms, the kill switch, and every named review-bar refusal
// (`NestReject`) on hand-built MachIR.

use crate::fast_hash::FxHashSet as HashSet;

use trust_cg_ir::{
    AArch64Opcode as Op, BlockId, MachFunction, MachInst, MachOperand, RegClass, Signature,
    StackSlot, VReg,
};

use super::*;

fn g(id: u32) -> VReg {
    VReg::new(id, RegClass::Gpr64)
}
fn vr(id: u32) -> MachOperand {
    MachOperand::VReg(g(id))
}
fn im(v: i64) -> MachOperand {
    MachOperand::Imm(v)
}
fn bl(b: BlockId) -> MachOperand {
    MachOperand::Block(b)
}
fn push(f: &mut MachFunction, b: BlockId, op: Op, ops: Vec<MachOperand>) {
    let id = f.push_inst(MachInst::new(op, ops));
    f.append_inst(b, id);
}

/// Build a canonical `for iv in 0..N` counted loop in the header-phi / body-copy
/// form (the shape p4's i/k loops take after copy coalescing), optionally with a
/// degenerate `body_iv = MovR(body_iv)` self-copy artifact, an off-by init, or a
/// stride-2 step. Returns `(func, body, header, index_iv)`.
fn build_counted_loop(
    n: i64,
    init: i64,
    step: i64,
    self_copy: bool,
) -> (MachFunction, HashSet<BlockId>, BlockId, VReg) {
    // vregs: 1=phi, 2=t(header), 3=body_iv, 4=index_iv, 5=inc
    let mut f = MachFunction::new("cl".into(), Signature::new(vec![], vec![]));
    let bb0 = f.entry;
    let hdr = f.create_block();
    let body = f.create_block();
    let latch = f.create_block();
    let exit = f.create_block();

    // bb0 preheader: phi = init ; -> hdr
    push(&mut f, bb0, Op::Movz, vec![vr(1), im(init)]);
    push(&mut f, bb0, Op::B, vec![bl(hdr)]);
    // hdr: t = MovR(phi) ; Cmp(t, n) ; BCond LO -> body ; B -> exit
    push(&mut f, hdr, Op::MovR, vec![vr(2), vr(1)]);
    push(&mut f, hdr, Op::CmpRI, vec![vr(2), im(n)]);
    push(&mut f, hdr, Op::BCond, vec![im(3), bl(body)]); // LO
    push(&mut f, hdr, Op::B, vec![bl(exit)]);
    // body: body_iv = MovR(phi) ; [self-copy] ; index_iv = MovR(body_iv) ; -> latch
    push(&mut f, body, Op::MovR, vec![vr(3), vr(1)]);
    if self_copy {
        push(&mut f, body, Op::MovR, vec![vr(3), vr(3)]);
    }
    push(&mut f, body, Op::MovR, vec![vr(4), vr(3)]);
    push(&mut f, body, Op::B, vec![bl(latch)]);
    // latch: inc = AddRI(body_iv, step) ; phi = MovR(inc) ; -> hdr
    push(&mut f, latch, Op::AddRI, vec![vr(5), vr(3), im(step)]);
    push(&mut f, latch, Op::MovR, vec![vr(1), vr(5)]);
    push(&mut f, latch, Op::B, vec![bl(hdr)]);
    // exit
    push(&mut f, exit, Op::Ret, vec![]);

    f.add_edge(bb0, hdr);
    f.add_edge(hdr, body);
    f.add_edge(hdr, exit);
    f.add_edge(body, latch);
    f.add_edge(latch, hdr);

    let body_set: HashSet<BlockId> = [hdr, body, latch].into_iter().collect();
    (f, body_set, hdr, g(4))
}

#[test]
fn tile_is_twelve_when_it_divides_n_else_eight() {
    assert_eq!(TILES, [12, 8]);
    assert_eq!(MIN_TILE, 8);
    for (n, tile) in [
        (8, Some(8)),
        (12, Some(12)),
        (16, Some(8)),
        (24, Some(12)),
        (32, Some(8)),
        (36, Some(12)),
        (48, Some(12)),
        (504, Some(12)),
        (0, None),
        (4, None),
        (6, None),
        (9, None),
        (20, None),
        (63, None),
    ] {
        assert_eq!(tile_for(n), tile, "N = {n}");
    }
}

#[test]
fn counted_loop_phi_copy_form_recognized() {
    let (f, body, hdr, idx) = build_counted_loop(24, 0, 1, false);
    let def = crate::effects::build_reaching_def_map(&f);
    assert!(verify_counted_0_n(&f, &def, &body, hdr, idx, 24, false).is_some());
}

#[test]
fn counted_loop_survives_self_copy_artifact() {
    // The exact fragility that first broke recognition: a `body_iv = MovR(body_iv)`
    // self-copy that `build_def_map` (last-def-wins) resolves to. Must still work.
    let (f, body, hdr, idx) = build_counted_loop(24, 0, 1, true);
    let def = crate::effects::build_reaching_def_map(&f);
    assert!(verify_counted_0_n(&f, &def, &body, hdr, idx, 24, false).is_some());
    // resolve_to_carried must land on the loop-carried phi (vreg 1), not spin on
    // the self-copy (vreg 3).
    assert_eq!(
        resolve_to_carried(&f, idx, latch_of(&f, hdr, &body)),
        Some(g(1))
    );
}

#[test]
fn counted_loop_rejects_nonzero_init() {
    let (f, body, hdr, idx) = build_counted_loop(24, 3, 1, false);
    let def = crate::effects::build_reaching_def_map(&f);
    assert!(verify_counted_0_n(&f, &def, &body, hdr, idx, 24, false).is_none());
}

#[test]
fn counted_loop_rejects_stride_two() {
    let (f, body, hdr, idx) = build_counted_loop(24, 0, 2, false);
    let def = crate::effects::build_reaching_def_map(&f);
    assert!(verify_counted_0_n(&f, &def, &body, hdr, idx, 24, false).is_none());
}

#[test]
fn counted_loop_rejects_wrong_bound() {
    let (f, body, hdr, idx) = build_counted_loop(24, 0, 1, false);
    let def = crate::effects::build_reaching_def_map(&f);
    // header tests against 24, but caller expects N=16 -> reject.
    assert!(verify_counted_0_n(&f, &def, &body, hdr, idx, 16, false).is_none());
}

/// A counter whose only `= 0` definition sits INSIDE the loop body is reset
/// on every iteration: the scalar loop never terminates while the fast path
/// would. The old check accepted any non-latch zero def as the init.
#[test]
fn counted_loop_rejects_an_init_inside_the_body() {
    let (mut f, body, hdr, idx) = build_counted_loop(24, 0, 1, false);
    let init = f.block(f.entry).insts[0];
    assert_eq!(f.inst(init).opcode, Op::Movz);
    f.block_mut(f.entry).insts.remove(0);
    let body_block = *f
        .block(hdr)
        .succs
        .iter()
        .find(|b| body.contains(b))
        .expect("body block");
    f.block_mut(body_block).insts.insert(0, init);
    let def = crate::effects::build_reaching_def_map(&f);
    assert!(verify_counted_0_n(&f, &def, &body, hdr, idx, 24, false).is_none());
}

fn latch_of(f: &MachFunction, header: BlockId, body: &HashSet<BlockId>) -> BlockId {
    single_latch(f, header, body).expect("latch")
}

#[test]
fn kill_switch_disables_pass() {
    // With TCG_NO_MAC_REG_BLOCK set, run() is a no-op even on a fireable shape.
    let env_scope = crate::env_lock::override_scope();
    let _kill_switch = crate::env_lock::ScopedEnvVar::set(&env_scope, "TCG_NO_MAC_REG_BLOCK", "1");
    let mut pass = MacRegBlock::new();
    let mut f = build_matmul_nest();
    assert!(!<MacRegBlock as MachinePass>::run(&mut pass, &mut f));
    assert_eq!(pass.fired(), 0);
}

#[test]
fn no_madd_prefilter_skips_cached_cfg_analyses() {
    // This counted loop has enough CFG structure to make both analyses do real
    // work, but no Madd, so no mac-reg-block recognition can possibly succeed.
    let (mut f, _, _, _) = build_counted_loop(24, 0, 1, false);
    assert!(!has_live_madd(&f));

    let mut direct_pass = MacRegBlock::new();
    assert!(!<MacRegBlock as MachinePass>::run(&mut direct_pass, &mut f,));
    assert_eq!(direct_pass.fired(), 0);

    let mut pass = MacRegBlock::new();
    let mut analyses = AnalysisCache::new();
    assert!(!<MacRegBlock as MachinePass>::run_with_analyses(
        &mut pass,
        &mut f,
        &mut analyses,
    ));
    assert_eq!(pass.fired(), 0);
    let stats = analyses.stats();
    assert_eq!(stats.domtree_computations, 0);
    assert_eq!(stats.loop_analysis_computations, 0);
}

/// WRONG-CODE REGRESSION (2026-08-17): recognition used to accept any positive
/// element scale while `apply` emits 64-bit lanes unconditionally, so an i32
/// matmul (scale 4) became 64-bit loads at 4-byte strides — two packed i32s per
/// lane and a 4-byte over-read past the array. It miscompiled silently and
/// NON-DETERMINISTICALLY (repeat runs of one binary disagreed) at O2/O3 for
/// square i32 N in {8,16,24,32,64,128}, all now matching LLVM.
///
/// The end-to-end differential coverage for this pass was i64-only, which is
/// exactly how it survived; this pins the width invariant directly.
#[test]
fn kernel_rejects_non_eight_byte_elements() {
    assert!(kernel_supports_scale(8), "i64 lanes are what apply() emits");
    for bad in [1, 2, 4, 16, 3, -8, 0] {
        assert!(
            !kernel_supports_scale(bad),
            "scale {bad} must fail closed: apply() would emit 64-bit lanes for it"
        );
    }
}

// --- k-loop pointer-writeback gate ---------------------------------------
//
// `pair_writeback_ok` is the fail-closed guard in front of the `LdrPostIndex` /
// `LdpRI` / `LdpPostIndex` k-loop shape. Anything it rejects must fall back to
// the original `LdrRI` + two `AddRI` body, so the pass never emits a pair
// offset outside the LDP signed-imm7 range or a pair load of the wrong width.

#[test]
fn pair_writeback_accepts_the_shipped_tiles() {
    // i64 elements, N = 24: tile 12 -> lane offsets 0..80, tile 8 -> 0..48,
    // writeback 192.
    for tile in TILES {
        assert!(pair_writeback_ok(8, 24 * 8, tile));
    }
}

#[test]
fn pair_writeback_rejects_non_i64_scale() {
    // LDP of a Gpr64 pair always transfers 8 bytes per lane; a 4-byte element
    // scale would silently load the wrong width.
    for tile in TILES {
        assert!(!pair_writeback_ok(4, 24 * 4, tile));
        assert!(!pair_writeback_ok(1, 24, tile));
    }
}

#[test]
fn pair_writeback_rejects_odd_tile() {
    // Lanes are consumed two at a time.
    assert!(!pair_writeback_ok(8, 24 * 8, 7));
    assert!(!pair_writeback_ok(8, 24 * 8, 1));
    assert!(!pair_writeback_ok(8, 24 * 8, 0));
}

#[test]
fn pair_writeback_rejects_out_of_range_writeback() {
    // The post-index amount is N*scale; LDP's scaled imm7 tops out at 504.
    for tile in TILES {
        assert!(pair_writeback_ok(8, 504, tile)); // N = 63, exactly encodable
        assert!(!pair_writeback_ok(8, 512, tile)); // N = 64, one step too far
        assert!(!pair_writeback_ok(8, 8 * 1024, tile));
    }
}

#[test]
fn pair_writeback_rejects_out_of_range_lane_offset() {
    // Highest lane offset is (tile-2)*scale, so at scale 8 the last encodable
    // tile is 64 ((64-2)*8 = 496 <= 504) and 66 is one past it.
    assert!(pair_writeback_ok(8, 8, 64));
    assert!(!pair_writeback_ok(8, 8, 66)); // (66-2)*8 = 512 > 504
}

fn nx(id: u32) -> MachOperand {
    MachOperand::VReg(VReg {
        id,
        class: RegClass::Gpr64,
    })
}
fn nw(id: u32) -> MachOperand {
    MachOperand::VReg(VReg {
        id,
        class: RegClass::Gpr32,
    })
}
fn ni(v: i64) -> MachOperand {
    MachOperand::Imm(v)
}
fn nbl(b: BlockId) -> MachOperand {
    MachOperand::Block(b)
}

/// One mutation of the canonical nest per review-bar guard. Every field's
/// default reproduces the admitted nest exactly.
#[derive(Clone, Copy)]
struct NestOptions {
    /// The square size `N` (every loop bound, `N*N` lengths and slots).
    n: i64,
    /// Constant the k-loop's `a[i*N+k]` bounds check compares against
    /// (default `N*N`).
    a_check_len: Option<i64>,
    /// Elements in `c`'s backing stack slot (default `N*N`).
    c_slot_elems: Option<u32>,
    /// `c`'s base addresses `a`'s stack slot (c overlaps a).
    c_aliases_a: bool,
    /// `c`'s base `AddPCRel` carries an extra offset operand.
    c_base_with_offset: bool,
    /// The loaded `c` element is a 32-bit register (i32 data, 8-byte stride).
    narrow_c_value: bool,
    /// The j-loop leaves the nest when `j <u 5` fails: a branch shaped like a
    /// bounds check on a value that is not an array index (an early exit).
    early_exit_on_j: bool,
    /// The j-loop skips the store when `j == 5`: an internal diamond that
    /// makes the store conditional.
    conditional_store: bool,
    /// The nest exit reads `aik`, a value the nest defines.
    exit_reads_aik: bool,
    /// The j-latch reads `j` after its `+1` step.
    read_j_after_step: bool,
    /// A second definition of the `c` index register before the nest.
    second_cidx_def: bool,
    /// A `Copy` into the physical ABI lane `x0` inside the j-loop.
    physical_copy_in_nest: bool,
    /// The `c[i*N+j]` load check compares against a length REGISTER
    /// (`CmpRR`) materialized once before the nest.
    cidx_len_in_register: bool,
    /// That length register is also defined after the nest, so the last-wins
    /// definition (576) is not the one that reaches the check (100).
    cidx_len_register_split: bool,
    /// The j-header compares against a bound register defined before the
    /// nest (9) and again after it (24, the last-wins value).
    j_bound_register_split: bool,
    /// The `c` index `i*N+j` is computed in the j-header, before its test,
    /// and checked again after the j-loop exits, where it is `i*N+N`.
    c_index_in_j_header: bool,
    /// The whole j-loop body (indices, loads, multiply-add, store) sits in
    /// the j-header before its test, so the scalar nest runs it `N+1` times.
    j_work_in_j_header: bool,
    /// The `c` index is computed in the k-loop before the j-loop (with `j`
    /// just reset to 0), so every j iteration addresses `c[i*N]`.
    c_index_before_j_loop: bool,
    /// The `c` index reads a copy of `j` taken in the k-loop before `j` is
    /// reset, i.e. `N` from the previous k iteration.
    c_index_from_stale_j_copy: bool,
    /// The `a` element is loaded in the k-latch, after the j-loop that
    /// multiplies by it: the j-loop reads the previous k iteration's value.
    a_load_in_k_latch: bool,
    /// `j = 0` runs in the k-preheader, once per i instead of once per k.
    j_init_in_k_preheader: bool,
    /// `k = 0` runs in the function entry, once instead of once per i.
    k_init_in_entry: bool,
    /// The scale register reaching the nest is 4, set in the i-preheader
    /// after an `= 8` in a block placed later in the layout (the last-wins
    /// definition).
    scale_register_split: bool,
    /// Every bounds check is the rustc bridge's proof-only carrier
    /// `TrapBoundsCheckExact [idx, idx, #len]` in a straight-line block
    /// (no failure edge), instead of the expanded `cmp; b.lo; b trap` form.
    carrier_checks: bool,
    /// With `carrier_checks`: the `c`-load carrier compares against a length
    /// REGISTER (the dynamic-length carrier form).
    carrier_len_in_register: bool,
    /// With `carrier_checks`: an extra carrier in the j-loop checks `j`
    /// itself against 5, a value that is not an array index.
    carrier_on_j: bool,
    /// With `carrier_checks`: the `c` index is checked again by a carrier in
    /// the k-latch, after the j-loop exited (where it is stale).
    carrier_on_stale_c_index: bool,
    /// With `carrier_checks`: a carrier on the `a` index sits in the j-header.
    carrier_in_j_header: bool,
    /// Expanded form: a carrier on the `c` index sits between the `c` check's
    /// compare and its branch; once expanded, its own compare would set the
    /// branch's flags.
    carrier_between_compare_and_branch: bool,
    /// How an outer value `v` (x50, set to 7 before the nest and read at the
    /// nest exit) is threaded through the i-loop, the way the rustc bridge
    /// passes live values through inner loops as block parameters.
    pass_through: PassThrough,
}

/// The i-loop's treatment of the outer value `v` (x50) read at the nest exit.
#[derive(Clone, Copy, PartialEq, Eq)]
enum PassThrough {
    /// Not present.
    None,
    /// `w = copy(v)` in the i-body entry, `v = copy(w)` in the i-latch.
    Copies,
    /// `v = w + 1` in the i-latch: the nest changes `v`.
    Modified,
    /// As `Copies`, but the exit also reads `w`, which only the nest defines.
    ExitReadsCopy,
    /// `w = copy(v)` only in the k-body, which does not dominate the latch.
    CopyNotDominating,
    /// `w = copy(i)`: the latch writes another value into `v`.
    CopyOfOtherValue,
    /// `w` is a 32-bit copy of the 64-bit `v`.
    NarrowCopy,
}

impl Default for NestOptions {
    fn default() -> Self {
        Self {
            n: 24,
            a_check_len: None,
            c_slot_elems: None,
            c_aliases_a: false,
            c_base_with_offset: false,
            narrow_c_value: false,
            early_exit_on_j: false,
            conditional_store: false,
            exit_reads_aik: false,
            read_j_after_step: false,
            second_cidx_def: false,
            physical_copy_in_nest: false,
            cidx_len_in_register: false,
            cidx_len_register_split: false,
            j_bound_register_split: false,
            c_index_in_j_header: false,
            j_work_in_j_header: false,
            c_index_before_j_loop: false,
            c_index_from_stale_j_copy: false,
            a_load_in_k_latch: false,
            j_init_in_k_preheader: false,
            k_init_in_entry: false,
            scale_register_split: false,
            carrier_checks: false,
            carrier_len_in_register: false,
            carrier_on_j: false,
            carrier_on_stale_c_index: false,
            carrier_in_j_header: false,
            carrier_between_compare_and_branch: false,
            pass_through: PassThrough::None,
        }
    }
}

/// The bridge's 3-deep bounds-checked scalar matmul nest (N = 24, L = 576,
/// element scale 8, a/b/c in three distinct stack slots):
/// `for i { for k { aik = a[i*N+k]; for j { c[i*N+j] = c[i*N+j] + aik*b[k*N+j] } } }`.
fn build_matmul_nest() -> MachFunction {
    build_matmul_nest_with(NestOptions::default())
}

#[allow(clippy::too_many_lines)]
fn build_matmul_nest_with(opts: NestOptions) -> MachFunction {
    let n = opts.n;
    let nn = n * n;
    let slot_elems = u32::try_from(nn).expect("test N*N fits u32");
    let mut func = MachFunction::new("k".to_string(), Signature::new(vec![], vec![]));
    let pre = func.entry;
    let ihdr = func.create_block();
    let kpre = func.create_block();
    let khdr = func.create_block();
    let kbody = func.create_block();
    let kbody2 = func.create_block();
    let jhdr = func.create_block();
    let bc1 = func.create_block();
    let bc2 = func.create_block();
    let probe = func.create_block();
    let work = func.create_block();
    let jlatch = func.create_block();
    let klatch = func.create_block();
    let ilatch = func.create_block();
    let exit = func.create_block();
    let trap = func.create_block();
    // Blocks only some mutations use, created last so the canonical block ids
    // never move.
    let kcheck = opts.c_index_in_j_header.then(|| func.create_block());
    let scale_blocks = opts
        .scale_register_split
        .then(|| (func.create_block(), func.create_block()));
    let push = |func: &mut MachFunction, blk: BlockId, op, ops| {
        let id = func.push_inst(MachInst::new(op, ops));
        func.append_inst(blk, id);
    };
    use AArch64Opcode::*;
    let sp = MachOperand::PReg(trust_cg_ir::aarch64_regs::SP);
    let (sc, sb, sa) = (
        func.alloc_stack_slot(StackSlot::new(
            opts.c_slot_elems.unwrap_or(slot_elems) * 8,
            8,
        )),
        func.alloc_stack_slot(StackSlot::new(slot_elems * 8, 8)),
        func.alloc_stack_slot(StackSlot::new(slot_elems * 8, 8)),
    );
    let c_slot = if opts.c_aliases_a { sa } else { sc };
    let mut c_base = vec![nx(0), sp.clone(), MachOperand::StackSlot(c_slot)];
    if opts.c_base_with_offset {
        c_base.push(ni(8));
    }
    if opts.second_cidx_def {
        push(&mut func, pre, Movz, vec![nx(10), ni(0)]);
    }
    push(&mut func, pre, AddPCRel, c_base); // c
    push(
        &mut func,
        pre,
        AddPCRel,
        vec![nx(1), sp.clone(), MachOperand::StackSlot(sb)],
    ); // b
    push(
        &mut func,
        pre,
        AddPCRel,
        vec![nx(8), sp.clone(), MachOperand::StackSlot(sa)],
    ); // a
    push(&mut func, pre, Movz, vec![nx(5), ni(n)]); // N
    if !opts.scale_register_split {
        push(&mut func, pre, Movz, vec![nx(6), ni(8)]); // scale
    }
    push(&mut func, pre, Movz, vec![nx(9), ni(0)]); // zero, copied into the inner ivs
    push(&mut func, pre, Movz, vec![nx(3), ni(0)]); // i
    if opts.pass_through != PassThrough::None {
        push(&mut func, pre, Movz, vec![nx(50), ni(7)]); // v
    }
    if opts.cidx_len_in_register || opts.cidx_len_register_split || opts.carrier_len_in_register {
        let reaching = if opts.cidx_len_register_split {
            100
        } else {
            nn
        };
        push(&mut func, pre, Movz, vec![nx(40), ni(reaching)]);
    }
    if opts.j_bound_register_split {
        push(&mut func, pre, Movz, vec![nx(41), ni(9)]);
    }
    if opts.k_init_in_entry {
        push(&mut func, pre, MovR, vec![nx(4), nx(9)]); // k = 0, once
    }
    // The i-preheader: `pre`, or the second scale block.
    let mut pre_edges = vec![];
    match scale_blocks {
        // Layout: ..., late (x6 = 4), early (x6 = 8). Execution: pre -> early
        // -> late -> ihdr, so 4 reaches the nest and the last-wins
        // definition in the layout is the 8.
        Some((late, early)) => {
            push(&mut func, pre, B, vec![nbl(early)]);
            push(&mut func, early, Movz, vec![nx(6), ni(8)]);
            push(&mut func, early, B, vec![nbl(late)]);
            push(&mut func, late, Movz, vec![nx(6), ni(4)]);
            push(&mut func, late, B, vec![nbl(ihdr)]);
            pre_edges.extend([(pre, early), (early, late), (late, ihdr)]);
        }
        None => {
            push(&mut func, pre, B, vec![nbl(ihdr)]);
            pre_edges.push((pre, ihdr));
        }
    }
    let mut edges = vec![];

    push(&mut func, ihdr, CmpRI, vec![nx(3), ni(n)]);
    push(&mut func, ihdr, BCond, vec![ni(CC_LT), nbl(kpre)]);
    push(&mut func, ihdr, B, vec![nbl(exit)]);

    match opts.pass_through {
        PassThrough::Copies | PassThrough::Modified | PassThrough::ExitReadsCopy => {
            push(&mut func, kpre, MovR, vec![nx(51), nx(50)]); // w = v
        }
        PassThrough::CopyOfOtherValue => {
            push(&mut func, kpre, MovR, vec![nx(51), nx(3)]); // w = i
        }
        PassThrough::NarrowCopy => {
            push(&mut func, kpre, MovR, vec![nw(51), nx(50)]); // w = v (32-bit)
        }
        PassThrough::CopyNotDominating | PassThrough::None => {}
    }
    if !opts.k_init_in_entry {
        push(&mut func, kpre, MovR, vec![nx(4), nx(9)]); // k = 0
    }
    if opts.j_init_in_k_preheader {
        push(&mut func, kpre, MovR, vec![nx(7), nx(9)]); // j = 0, once per i
    }
    push(&mut func, kpre, B, vec![nbl(khdr)]);

    push(&mut func, khdr, CmpRI, vec![nx(4), ni(n)]);
    push(&mut func, khdr, BCond, vec![ni(CC_LT), nbl(kbody)]);
    push(&mut func, khdr, B, vec![nbl(ilatch)]);

    push(&mut func, kbody, Madd, vec![nx(20), nx(3), nx(5), nx(4)]); // aidx = i*N + k
    let a_len = ni(opts.a_check_len.unwrap_or(nn));
    if opts.carrier_checks {
        push(
            &mut func,
            kbody,
            TrapBoundsCheckExact,
            vec![nx(20), nx(20), a_len],
        );
        push(&mut func, kbody, B, vec![nbl(kbody2)]);
    } else {
        push(&mut func, kbody, CmpRI, vec![nx(20), a_len]);
        push(&mut func, kbody, BCond, vec![ni(CC_LO), nbl(kbody2)]);
        push(&mut func, kbody, B, vec![nbl(trap)]);
        edges.push((kbody, trap));
    }

    let a_load = |func: &mut MachFunction, blk: BlockId| {
        push(func, blk, Madd, vec![nx(21), nx(20), nx(6), nx(8)]); // aaddr
        push(func, blk, LdrRI, vec![nx(2), nx(21), ni(0)]); // aik
    };
    if !opts.a_load_in_k_latch {
        a_load(&mut func, kbody2);
    }
    if opts.c_index_from_stale_j_copy {
        push(&mut func, kbody2, MovR, vec![nx(32), nx(7)]); // j before its reset
    }
    if !opts.j_init_in_k_preheader {
        push(&mut func, kbody2, MovR, vec![nx(7), nx(9)]); // j = 0
    }
    // cidx = i*N + j (or the stale copy of j).
    let j_in_cidx = if opts.c_index_from_stale_j_copy {
        nx(32)
    } else {
        nx(7)
    };
    let cidx = |func: &mut MachFunction, blk: BlockId| {
        push(
            func,
            blk,
            Madd,
            vec![nx(10), nx(3), nx(5), j_in_cidx.clone()],
        );
    };
    // The j-loop's accesses: c and b addresses and loads, the multiply-add
    // and the store.
    let cval = if opts.narrow_c_value { nw(13) } else { nx(13) };
    let j_work = |func: &mut MachFunction, blk: BlockId| {
        push(func, blk, Madd, vec![nx(12), nx(10), nx(6), nx(0)]); // caddr
        push(func, blk, LdrRI, vec![cval.clone(), nx(12), ni(0)]); // cval
        push(func, blk, Madd, vec![nx(14), nx(11), nx(6), nx(1)]); // baddr
        push(func, blk, LdrRI, vec![nx(15), nx(14), ni(0)]); // bval
        push(func, blk, Madd, vec![nx(16), nx(2), nx(15), cval.clone()]); // aik*b + c
        push(func, blk, StrRI, vec![nx(16), nx(12), ni(0)]);
    };
    let bidx = |func: &mut MachFunction, blk: BlockId| {
        push(func, blk, Madd, vec![nx(11), nx(4), nx(5), nx(7)]);
    };
    if opts.c_index_before_j_loop {
        cidx(&mut func, kbody2);
    }
    push(&mut func, kbody2, B, vec![nbl(jhdr)]);

    if opts.c_index_in_j_header || opts.j_work_in_j_header {
        cidx(&mut func, jhdr);
    }
    if opts.j_work_in_j_header {
        bidx(&mut func, jhdr);
        j_work(&mut func, jhdr);
    }
    if opts.carrier_in_j_header {
        push(
            &mut func,
            jhdr,
            TrapBoundsCheckExact,
            vec![nx(20), nx(20), ni(nn)],
        );
    }
    if opts.j_bound_register_split {
        push(&mut func, jhdr, CmpRR, vec![nx(7), nx(41)]);
    } else {
        push(&mut func, jhdr, CmpRI, vec![nx(7), ni(n)]);
    }
    push(&mut func, jhdr, BCond, vec![ni(CC_LT), nbl(bc1)]);
    let j_exit = kcheck.unwrap_or(klatch);
    push(&mut func, jhdr, B, vec![nbl(j_exit)]);

    if !(opts.c_index_in_j_header || opts.j_work_in_j_header || opts.c_index_before_j_loop) {
        cidx(&mut func, bc1);
    }
    if opts.carrier_checks {
        let c_len = if opts.carrier_len_in_register {
            nx(40)
        } else {
            ni(nn)
        };
        push(
            &mut func,
            bc1,
            TrapBoundsCheckExact,
            vec![nx(10), nx(10), c_len],
        );
        if opts.carrier_on_j {
            push(
                &mut func,
                bc1,
                TrapBoundsCheckExact,
                vec![nx(7), nx(7), ni(5)],
            );
        }
        push(&mut func, bc1, B, vec![nbl(bc2)]);
    } else {
        if opts.cidx_len_in_register || opts.cidx_len_register_split {
            push(&mut func, bc1, CmpRR, vec![nx(10), nx(40)]);
        } else {
            push(&mut func, bc1, CmpRI, vec![nx(10), ni(nn)]);
        }
        if opts.carrier_between_compare_and_branch {
            push(
                &mut func,
                bc1,
                TrapBoundsCheckExact,
                vec![nx(10), nx(10), ni(nn)],
            );
        }
        push(&mut func, bc1, BCond, vec![ni(CC_LO), nbl(bc2)]);
        push(&mut func, bc1, B, vec![nbl(trap)]);
        edges.push((bc1, trap));
    }

    if !opts.j_work_in_j_header {
        bidx(&mut func, bc2);
    }
    if opts.carrier_checks {
        push(
            &mut func,
            bc2,
            TrapBoundsCheckExact,
            vec![nx(11), nx(11), ni(nn)],
        );
        push(&mut func, bc2, B, vec![nbl(probe)]);
    } else {
        push(&mut func, bc2, CmpRI, vec![nx(11), ni(nn)]);
        push(&mut func, bc2, BCond, vec![ni(CC_LO), nbl(probe)]);
        push(&mut func, bc2, B, vec![nbl(trap)]);
        edges.push((bc2, trap));
    }

    // `probe` is an empty fall-through in the admitted nest; the mandatory
    // control-flow mutations put their extra branch here.
    edges.push((probe, work));
    if opts.early_exit_on_j {
        push(&mut func, probe, CmpRI, vec![nx(7), ni(5)]);
        push(&mut func, probe, BCond, vec![ni(CC_LO), nbl(work)]);
        push(&mut func, probe, B, vec![nbl(exit)]);
        edges.push((probe, exit));
    } else if opts.conditional_store {
        push(&mut func, probe, CmpRI, vec![nx(7), ni(5)]);
        push(&mut func, probe, BCond, vec![ni(0), nbl(jlatch)]); // EQ
        push(&mut func, probe, B, vec![nbl(work)]);
        edges.push((probe, jlatch));
    } else {
        push(&mut func, probe, B, vec![nbl(work)]);
    }

    if !opts.j_work_in_j_header {
        j_work(&mut func, work);
    }
    if opts.physical_copy_in_nest {
        push(
            &mut func,
            work,
            Copy,
            vec![MachOperand::PReg(trust_cg_ir::aarch64_regs::X0), nx(16)],
        );
    }
    push(&mut func, work, B, vec![nbl(jlatch)]);

    push(&mut func, jlatch, AddRI, vec![nx(7), nx(7), ni(1)]);
    if opts.read_j_after_step {
        push(&mut func, jlatch, MovR, vec![nx(30), nx(7)]);
    }
    push(&mut func, jlatch, B, vec![nbl(jhdr)]);
    // The stale index, checked again once the j-loop has exited.
    if let Some(kcheck) = kcheck {
        push(&mut func, kcheck, CmpRI, vec![nx(10), ni(nn)]);
        push(&mut func, kcheck, BCond, vec![ni(CC_LO), nbl(klatch)]);
        push(&mut func, kcheck, B, vec![nbl(trap)]);
        edges.extend([(kcheck, klatch), (kcheck, trap)]);
    }
    if opts.a_load_in_k_latch {
        a_load(&mut func, klatch);
    }
    if opts.pass_through == PassThrough::CopyNotDominating {
        push(&mut func, klatch, MovR, vec![nx(51), nx(50)]); // w = v, per k
    }
    if opts.carrier_on_stale_c_index {
        push(
            &mut func,
            klatch,
            TrapBoundsCheckExact,
            vec![nx(10), nx(10), ni(nn)],
        );
    }
    push(&mut func, klatch, AddRI, vec![nx(4), nx(4), ni(1)]);
    push(&mut func, klatch, B, vec![nbl(khdr)]);
    push(&mut func, ilatch, AddRI, vec![nx(3), nx(3), ni(1)]);
    match opts.pass_through {
        PassThrough::None => {}
        PassThrough::Modified => push(&mut func, ilatch, AddRI, vec![nx(50), nx(51), ni(1)]),
        PassThrough::NarrowCopy => push(&mut func, ilatch, MovR, vec![nx(50), nw(51)]),
        _ => push(&mut func, ilatch, MovR, vec![nx(50), nx(51)]), // v = w
    }
    push(&mut func, ilatch, B, vec![nbl(ihdr)]);
    if opts.exit_reads_aik {
        push(
            &mut func,
            exit,
            Copy,
            vec![MachOperand::PReg(trust_cg_ir::aarch64_regs::X0), nx(2)],
        );
    }
    if opts.pass_through != PassThrough::None {
        push(
            &mut func,
            exit,
            Copy,
            vec![MachOperand::PReg(trust_cg_ir::aarch64_regs::X1), nx(50)],
        );
    }
    if opts.pass_through == PassThrough::ExitReadsCopy {
        push(
            &mut func,
            exit,
            Copy,
            vec![MachOperand::PReg(trust_cg_ir::aarch64_regs::X2), nx(51)],
        );
    }
    // Late redefinitions after the nest: last in layout, so the last-wins
    // definition map names them, but they never reach the nest.
    if opts.cidx_len_register_split {
        push(&mut func, exit, Movz, vec![nx(40), ni(nn)]);
    }
    if opts.j_bound_register_split {
        push(&mut func, exit, Movz, vec![nx(41), ni(n)]);
    }
    push(&mut func, exit, Ret, vec![]);
    push(&mut func, trap, Ret, vec![]);

    for (a, b) in pre_edges
        .into_iter()
        .chain([
            (ihdr, kpre),
            (ihdr, exit),
            (kpre, khdr),
            (khdr, kbody),
            (khdr, ilatch),
            (kbody, kbody2),
            (kbody2, jhdr),
            (jhdr, bc1),
            (jhdr, j_exit),
            (bc1, bc2),
            (bc2, probe),
            (work, jlatch),
            (jlatch, jhdr),
            (klatch, khdr),
            (ilatch, ihdr),
        ])
        .chain(edges)
    {
        func.add_edge(a, b);
    }
    func
}

/// Run recognition on the nest's innermost (depth-3) loop, as `run_core` does.
fn recognize_nest(func: &MachFunction) -> Result<Recognized, NestReject> {
    let dom = DomTree::compute(func);
    let loops = LoopAnalysis::compute(func, &dom);
    let def = crate::effects::build_reaching_def_map(func);
    let j_header = loops
        .all_loops()
        .find(|lp| lp.depth == 3)
        .map(|lp| lp.header)
        .expect("the nest has a depth-3 loop");
    Recognized::recognize(func, &dom, &def, &loops, j_header)
}

/// Assert that `opts` is refused for exactly `reason`, and that the pass then
/// leaves the function untouched.
fn assert_refused(opts: NestOptions, reason: NestReject) {
    let mut func = build_matmul_nest_with(opts);
    assert_eq!(recognize_nest(&func).err(), Some(reason));
    let (insts, blocks) = (func.insts.len(), func.blocks.len());
    let mut pass = MacRegBlock::new();
    assert!(!pass.run(&mut func), "a refused nest must not be rewritten");
    assert_eq!(pass.fired(), 0);
    assert_eq!((func.insts.len(), func.blocks.len()), (insts, blocks));
}

/// A nest whose `reg` is defined on two paths with different constants, the
/// last-wins definition map naming the wrong one, is refused on BOTH lines.
///
/// The shape match refuses it first: its constant reader,
/// `mach_util::copied_const`, folds a register only when every definition of
/// it writes the same constant, so the match no longer reads the last-wins
/// value (`Shape`). The review bar would refuse it
/// for `review_reason`; its re-proof of the register, [`review_bar::nest_constant`],
/// is asserted directly so that the second line stays a real check.
fn assert_misread_register_refused(opts: NestOptions, reg: VReg, review_reason: NestReject) {
    assert_refused(opts, NestReject::Shape);
    let func = build_matmul_nest_with(opts);
    let dom = DomTree::compute(&func);
    let loops = LoopAnalysis::compute(&func, &dom);
    let def = crate::effects::build_reaching_def_map(&func);
    assert!(
        crate::effects::live_def_count(&func, reg.id) > 1,
        "the register must be multi-def for the {review_reason:?} case"
    );
    let i_body = &loops
        .all_loops()
        .find(|lp| lp.depth == 1)
        .expect("the nest has a depth-1 loop")
        .body;
    assert_eq!(review_bar::nest_constant(&func, &def, i_body, reg), None);
    assert_eq!(crate::mach_util::const_value(&func, &def, reg), None);
}

#[test]
fn fires_on_the_matmul_nest() {
    let mut func = build_matmul_nest();
    assert!(
        recognize_nest(&func).is_ok(),
        "every review-bar guard admits the canonical nest"
    );
    let mut pass = MacRegBlock::new();
    assert!(
        pass.run(&mut func),
        "the 3-deep matmul nest must register-block"
    );
    assert_eq!(pass.fired(), 1);
}

/// IDEMPOTENCE: the blocked nest no longer contains the scalar j-loop shape,
/// so a second run must change nothing.
#[test]
fn second_run_is_a_no_op() {
    let mut func = build_matmul_nest();
    assert!(MacRegBlock::new().run(&mut func), "first run must fire");
    let (insts, blocks) = (func.insts.len(), func.blocks.len());
    for again in 2..=4 {
        assert!(
            !MacRegBlock::new().run(&mut func),
            "run {again} re-fired on its own output"
        );
        assert_eq!(func.insts.len(), insts, "run {again} added instructions");
        assert_eq!(func.blocks.len(), blocks, "run {again} added blocks");
    }
}

// --- the publication review bar (L10-P4) ----------------------------------
//
// One test per named refusal. Each mutation leaves the rest of the nest
// admissible, so the named guard — not an earlier shape mismatch — refuses.

/// Data width: i32 data in 8-byte cells has the admitted 8-byte stride but a
/// 32-bit value; the kernel's 64-bit lanes would rewrite the upper half of
/// every `c` cell.
#[test]
fn review_bar_refuses_narrow_element_values() {
    assert_refused(
        NestOptions {
            narrow_c_value: true,
            ..NestOptions::default()
        },
        NestReject::DataWidth,
    );
}

/// All array bounds: the `a[i*N+k]` check in the k-loop was never inspected;
/// a length below `N*N` means the scalar nest traps where the unchecked fast
/// path would not.
#[test]
fn review_bar_refuses_an_a_bounds_check_that_can_fail() {
    assert_refused(
        NestOptions {
            a_check_len: Some(575),
            ..NestOptions::default()
        },
        NestReject::BoundsCheckMayFail,
    );
}

/// All array bounds (storage): the fast path touches all `N*N` elements of
/// each array unchecked, so each backing slot must hold them.
#[test]
fn review_bar_refuses_an_undersized_backing_slot() {
    assert_refused(
        NestOptions {
            c_slot_elems: Some(575),
            ..NestOptions::default()
        },
        NestReject::SlotTooSmall,
    );
}

/// Mandatory control flow: a branch shaped exactly like a bounds check
/// (`LO` into the loop, the other edge out of the nest) on a value that is
/// not an array index is an early exit the fast path would skip.
#[test]
fn review_bar_refuses_an_early_exit_disguised_as_a_bounds_check() {
    assert_refused(
        NestOptions {
            early_exit_on_j: true,
            ..NestOptions::default()
        },
        NestReject::UnprovenConditionalBranch,
    );
}

/// Mandatory control flow: an internal diamond makes the single `c` store
/// conditional; the fast path would store unconditionally.
#[test]
fn review_bar_refuses_a_conditional_store() {
    assert_refused(
        NestOptions {
            conditional_store: true,
            ..NestOptions::default()
        },
        NestReject::UnprovenConditionalBranch,
    );
}

/// Bypassed live-out: the fast path never defines the nest's registers, so a
/// read of `aik` after the nest would see its pre-nest value.
#[test]
fn review_bar_refuses_a_bypassed_live_out() {
    assert_refused(
        NestOptions {
            exit_reads_aik: true,
            ..NestOptions::default()
        },
        NestReject::BypassedLiveOut,
    );
}

/// Induction: after the latch step `j` already holds the next iteration's
/// value, so any read of it there is not the iteration's index.
#[test]
fn review_bar_refuses_a_counter_read_after_its_step() {
    assert_refused(
        NestOptions {
            read_j_after_step: true,
            ..NestOptions::default()
        },
        NestReject::CounterReadAfterStep,
    );
}

/// Every value the shape match resolved through the last-wins definition map
/// must have one definition.
#[test]
fn review_bar_refuses_a_multiply_defined_index() {
    assert_refused(
        NestOptions {
            second_cidx_def: true,
            ..NestOptions::default()
        },
        NestReject::MultiDefValue,
    );
}

/// Closed world: a copy into a physical ABI lane inside the nest is an
/// effect the fast path does not replay.
#[test]
fn closed_world_refuses_physical_register_traffic_in_the_nest() {
    assert_refused(
        NestOptions {
            physical_copy_in_nest: true,
            ..NestOptions::default()
        },
        NestReject::OpenWorld,
    );
}

/// Aliasing: `c` overlapping `a` (the same stack slot) breaks store sinking.
#[test]
fn aliasing_refuses_c_overlapping_a() {
    assert_refused(
        NestOptions {
            c_aliases_a: true,
            ..NestOptions::default()
        },
        NestReject::AliasedArrays,
    );
}

/// Only the exact `AddPCRel [dst, sp, StackSlot]` form names a slot's start.
#[test]
fn array_base_refuses_a_stack_address_with_an_extra_operand() {
    assert_refused(
        NestOptions {
            c_base_with_offset: true,
            ..NestOptions::default()
        },
        NestReject::ArrayBaseNotStackSlot,
    );
}

/// The facts `recognize` hands the review bar for a nest from
/// `build_matmul_nest_with`, read off the builder's fixed vreg numbering, with
/// the given nest exit.
fn nest_facts<'a>(
    func: &MachFunction,
    loops: &'a LoopAnalysis,
    exit_target: BlockId,
) -> review_bar::NestFacts<'a> {
    let lp = |depth| {
        loops
            .all_loops()
            .find(|lp| lp.depth == depth)
            .expect("nest loop")
    };
    let (i, k, j) = (lp(1), lp(2), lp(3));
    let counted = |lp: &crate::loops::NaturalLoop, counter: u32| {
        let latch = single_latch(func, lp.header, &lp.body).expect("latch");
        let defs = find_all_defs(func, g(counter));
        let in_latch = |id: &InstId| block_of_inst(func, *id) == Some(latch);
        review_bar::CountedLoop {
            counter: g(counter),
            latch,
            step: *defs.iter().find(|id| in_latch(id)).expect("step"),
            init: *defs.iter().find(|id| !in_latch(id)).expect("init"),
        }
    };
    let store = *func
        .block_order
        .iter()
        .flat_map(|&b| func.block(b).insts.iter())
        .find(|&&id| func.inst(id).opcode == Op::StrRI)
        .expect("store");
    review_bar::NestFacts {
        i_body: &i.body,
        k_body: &k.body,
        j_body: &j.body,
        headers: [i.header, k.header, j.header],
        counters: [counted(i, 3), counted(k, 4), counted(j, 7)],
        exit_target,
        // aidx, cidx (load), bidx, cidx (store).
        indices: [g(20), g(10), g(11), g(10)],
        lane_values: [g(2), g(2), g(15), g(13), g(16)],
        k_level_values: [g(20), g(21), g(2)],
        j_level_values: [
            g(10),
            g(12),
            g(13),
            g(11),
            g(14),
            g(15),
            g(10),
            g(12),
            g(16),
        ],
        store,
        slots: [StackSlotId(2), StackSlotId(1), StackSlotId(0)],
        scale_reg: g(6),
        n: 24,
        scale: 8,
    }
}

/// The nest exit: the i-header's successor outside the i-loop.
fn nest_exit(func: &MachFunction, loops: &LoopAnalysis) -> BlockId {
    let i = loops.all_loops().find(|lp| lp.depth == 1).expect("i-loop");
    *func
        .block(i.header)
        .succs
        .iter()
        .find(|b| !i.body.contains(b))
        .expect("nest exit")
}

/// The loop-exit rule itself: each header must leave exactly to its parent
/// (the i-header to the recognized nest exit), checked here directly against
/// the canonical nest with a deliberately wrong exit.
#[test]
fn mandatory_control_flow_requires_each_header_to_exit_to_its_parent() {
    let func = build_matmul_nest();
    let dom = DomTree::compute(&func);
    let loops = LoopAnalysis::compute(&func, &dom);
    let def = crate::effects::build_reaching_def_map(&func);
    let exit = nest_exit(&func, &loops);
    // The shared bounds-check failure block: the other successor-less block.
    let trap = *func
        .block_order
        .iter()
        .find(|b| func.block(**b).succs.is_empty() && **b != exit)
        .expect("trap block");
    let i_body = &loops
        .all_loops()
        .find(|lp| lp.depth == 1)
        .expect("i-loop")
        .body;
    assert!(review_bar::check(&func, &dom, &def, &nest_facts(&func, &loops, exit)).is_ok());
    assert_eq!(
        review_bar::check_mandatory_control_flow(
            &func,
            &dom,
            &def,
            &nest_facts(&func, &loops, trap)
        ),
        Err(NestReject::UnmodeledLoopExit)
    );
    // Nothing the nest writes is live into its exit: the loop-state contract
    // admits the nest with no carrier at all, given the i-header test and the
    // checks the review bar proved. Without those proofs the same nest is
    // refused: the bounds checks' failure edges leave the i-loop.
    let i_header = loops
        .all_loops()
        .find(|lp| lp.depth == 1)
        .expect("i-loop")
        .header;
    let proven = review_bar::check_mandatory_control_flow(
        &func,
        &dom,
        &def,
        &nest_facts(&func, &loops, exit),
    )
    .expect("the canonical nest's control flow is proved");
    assert!(!proven.is_empty(), "the canonical nest has bounds checks");
    let check = |proven: &[crate::loop_contract::LoopExit<BlockId>]| {
        let exits = proven.iter().fold(
            crate::loop_contract::ExitPlan::loop_test(i_header, exit),
            |plan, &check| plan.and_proved_not_taken(check),
        );
        crate::loop_contract::LoopLocality::check(
            &func,
            i_body.iter().copied(),
            i_header,
            &exits,
            crate::loop_contract::Handoff::Only(&[exit]),
            &[],
        )
    };
    assert!(check(&proven).is_ok());
    assert!(matches!(
        check(&[]),
        Err(crate::loop_contract::LoopStateEscape::Exit(_))
    ));
}

/// A length held in a register is admitted when one `Movz` before the nest
/// materializes it: the canonical nest with its `c` check in `CmpRR` form
/// still fires.
#[test]
fn a_bounds_check_against_a_nest_constant_register_is_admitted() {
    let mut func = build_matmul_nest_with(NestOptions {
        cidx_len_in_register: true,
        ..NestOptions::default()
    });
    assert!(recognize_nest(&func).is_ok());
    assert!(MacRegBlock::new().run(&mut func));
}

/// All array bounds: a length register defined on two paths. The last-wins
/// definition map says 576, but the value reaching the check is 100, so the
/// scalar nest traps where the fast path would not.
#[test]
fn review_bar_refuses_a_length_register_the_def_map_misreads() {
    assert_misread_register_refused(
        NestOptions {
            cidx_len_register_split: true,
            ..NestOptions::default()
        },
        g(40),
        NestReject::UnprovenConditionalBranch,
    );
}

/// Mandatory control flow: the j-loop's bound register reaching the header
/// is 9, the last-wins definition says 24; the scalar j-loop runs 9 times.
#[test]
fn review_bar_refuses_a_loop_bound_register_the_def_map_misreads() {
    assert_misread_register_refused(
        NestOptions {
            j_bound_register_split: true,
            ..NestOptions::default()
        },
        g(41),
        NestReject::UnprovenConditionalBranch,
    );
}

/// Mandatory control flow (header): the `c` index computed in the j-header
/// before its test is `i*N+N` on the exiting pass, and a check of it after
/// the loop fails for `i = N-1`, where the fast path would return normally.
/// Reached natively from trust-ir (`stale_c_index16` in the codegen
/// differential); the header rule refuses it before any check is classified.
#[test]
fn review_bar_refuses_an_index_computed_in_a_loop_header() {
    let opts = NestOptions {
        c_index_in_j_header: true,
        ..NestOptions::default()
    };
    assert_refused(opts, NestReject::HeaderWork);
    // The bounds-check rule refuses it on its own too: an index defined in
    // a header is not the current iteration's value at any check.
    let func = build_matmul_nest_with(opts);
    let dom = DomTree::compute(&func);
    let loops = LoopAnalysis::compute(&func, &dom);
    let def = crate::effects::build_reaching_def_map(&func);
    let facts = nest_facts(&func, &loops, nest_exit(&func, &loops));
    assert_eq!(
        review_bar::check_mandatory_control_flow(&func, &dom, &def, &facts),
        Err(NestReject::UnprovenConditionalBranch)
    );
}

/// Mandatory control flow (header): the whole j-body before the j-header's
/// test runs `N+1` times per j-loop in the scalar nest; the extra store
/// writes `c[i*N+N]`, which the fast path never does.
#[test]
fn review_bar_refuses_loop_work_in_its_header() {
    assert_refused(
        NestOptions {
            j_work_in_j_header: true,
            ..NestOptions::default()
        },
        NestReject::HeaderWork,
    );
}

/// Placement: a `c` index computed in the k-loop before the j-loop is
/// `i*N+0` for every j; the fast path addresses `c[i*N+j]`.
#[test]
fn review_bar_refuses_an_index_computed_outside_its_loop() {
    assert_refused(
        NestOptions {
            c_index_before_j_loop: true,
            ..NestOptions::default()
        },
        NestReject::MisplacedAccess,
    );
}

/// Induction: a copy of `j` taken in the k-loop before `j` is reset holds
/// `N` (or nothing, on the first k iteration); an index built from it is not
/// the current `j`.
#[test]
fn review_bar_refuses_an_index_from_a_stale_counter_copy() {
    assert_refused(
        NestOptions {
            c_index_from_stale_j_copy: true,
            ..NestOptions::default()
        },
        NestReject::CounterReadOutsideLoop,
    );
}

/// Reaching values: the `a` element loaded in the k-latch, after the j-loop
/// that multiplies by it, is the previous k iteration's value (nothing on
/// the first), not `a[i*N+k]`.
#[test]
fn review_bar_refuses_a_value_read_before_its_definition() {
    assert_refused(
        NestOptions {
            a_load_in_k_latch: true,
            ..NestOptions::default()
        },
        NestReject::UseNotDominated,
    );
}

/// Induction (reset): `j = 0` once per i leaves the j-loop empty for every k
/// after the first, and `k = 0` once in the entry leaves the k-loop empty
/// for every i after the first. The fast path computes the full product.
#[test]
fn review_bar_refuses_a_counter_reset_outside_its_parent_loop() {
    assert_refused(
        NestOptions {
            j_init_in_k_preheader: true,
            ..NestOptions::default()
        },
        NestReject::CounterInitOutsideParent,
    );
    assert_refused(
        NestOptions {
            k_init_in_entry: true,
            ..NestOptions::default()
        },
        NestReject::CounterInitOutsideParent,
    );
}

/// Tile: `N = 12` is in range but not a multiple of the 8-lane tile; below
/// the tile the nest is not the modeled shape at all.
#[test]
fn recognition_refuses_n_that_is_not_a_tile_multiple() {
    assert_refused(
        NestOptions {
            n: 20,
            ..NestOptions::default()
        },
        NestReject::NotTileMultiple,
    );
    assert_refused(
        NestOptions {
            n: 4,
            ..NestOptions::default()
        },
        NestReject::Shape,
    );
    // The builder's `N` is honoured: 16 is admitted with an 8-lane tile,
    // 12, 24 and 36 with a 12-lane tile.
    for (n, tile) in [(16, 8), (12, 12), (24, 12), (36, 12)] {
        let mut func = build_matmul_nest_with(NestOptions {
            n,
            ..NestOptions::default()
        });
        assert_eq!(recognize_nest(&func).map(|rec| rec.tile).ok(), Some(tile));
        assert!(MacRegBlock::new().run(&mut func));
    }
}

/// Element stride: the scale register reaching the nest is 4, while the
/// last-wins definition map reads the 8 set in a block placed later in the
/// layout but run earlier. The fast path hard-codes 8-byte lanes.
#[test]
fn review_bar_refuses_a_scale_register_the_def_map_misreads() {
    assert_misread_register_refused(
        NestOptions {
            scale_register_split: true,
            ..NestOptions::default()
        },
        g(6),
        NestReject::ElementScale,
    );
}

/// `nest_constant` accepts exactly one `Movz` (plus `Movk` chunks) in one
/// block outside the nest, through single-definition copies.
#[test]
fn nest_constant_requires_one_materialization_outside_the_nest() {
    let (mut f, body, _, _) = build_counted_loop(24, 0, 1, false);
    let entry = f.entry;
    let exit = *f.block_order.last().expect("exit block");
    let first_body = *body.iter().min().expect("body");
    let insert_front = |f: &mut MachFunction, block: BlockId, op: Op, ops: Vec<MachOperand>| {
        let id = f.push_inst(MachInst::new(op, ops));
        f.block_mut(block).insts.insert(0, id);
    };
    // 60: Movz + Movk chain in the entry block -> 0x0002_0010.
    insert_front(&mut f, entry, Op::Movk, vec![vr(60), im(2), im(16)]);
    insert_front(&mut f, entry, Op::Movz, vec![vr(60), im(0x10)]);
    // 61: a copy of 60.
    insert_front(&mut f, exit, Op::MovR, vec![vr(61), vr(60)]);
    // 62: defined in the entry and again after the loop.
    insert_front(&mut f, entry, Op::Movz, vec![vr(62), im(7)]);
    insert_front(&mut f, exit, Op::Movz, vec![vr(62), im(9)]);
    // 63: defined inside the loop body.
    insert_front(&mut f, first_body, Op::Movz, vec![vr(63), im(5)]);
    // 64: two Movz in one block.
    insert_front(&mut f, entry, Op::Movz, vec![vr(64), im(1)]);
    insert_front(&mut f, entry, Op::Movz, vec![vr(64), im(2)]);
    let def = crate::effects::build_reaching_def_map(&f);
    assert_eq!(
        review_bar::nest_constant(&f, &def, &body, g(60)),
        Some(0x0002_0010)
    );
    assert_eq!(
        review_bar::nest_constant(&f, &def, &body, g(61)),
        Some(0x0002_0010)
    );
    for refused in [62, 63, 64] {
        assert_eq!(review_bar::nest_constant(&f, &def, &body, g(refused)), None);
    }
}

/// Every named refusal has a distinct, non-empty reason for the dump log.
#[test]
fn every_named_refusal_has_a_distinct_reason() {
    let all = [
        NestReject::Shape,
        NestReject::ArrayBaseNotStackSlot,
        NestReject::AliasedArrays,
        NestReject::OpenWorld,
        NestReject::NotTileMultiple,
        NestReject::ElementScale,
        NestReject::DataWidth,
        NestReject::MultiDefValue,
        NestReject::SlotTooSmall,
        NestReject::BoundsCheckMayFail,
        NestReject::UnprovenConditionalBranch,
        NestReject::UnmodeledLoopExit,
        NestReject::CounterReadAfterStep,
        NestReject::BypassedLiveOut,
        NestReject::HeaderWork,
        NestReject::MisplacedAccess,
        NestReject::UseNotDominated,
        NestReject::CounterReadOutsideLoop,
        NestReject::CounterInitOutsideParent,
        NestReject::UnprovenBoundsCarrier,
    ];
    let reasons: HashSet<String> = all.iter().map(ToString::to_string).collect();
    assert_eq!(reasons.len(), all.len());
    assert!(reasons.iter().all(|reason| !reason.is_empty()));
}

// --- bounds-check carriers (the rustc bridge's check form) -----------------
//
// The bridge lowers a constant-length slice or array check (MIR
// `Assert(BoundsCheck)`) to the proof-only carrier
// `TrapBoundsCheckExact [idx, idx, #len]`, which traps on failure and has no
// CFG edge. The p4_matmul nest reaches this pass in that form only.

fn carrier_nest(opts: NestOptions) -> NestOptions {
    NestOptions {
        carrier_checks: true,
        ..opts
    }
}

/// The carrier-checked nest is admitted and register-blocked exactly once.
#[test]
fn fires_on_the_carrier_checked_nest() {
    let mut func = build_matmul_nest_with(carrier_nest(NestOptions::default()));
    let carriers = func
        .block_order
        .iter()
        .flat_map(|&b| func.block(b).insts.iter())
        .filter(|&&id| func.inst(id).opcode == Op::TrapBoundsCheckExact)
        .count();
    assert_eq!(carriers, 3, "the a, c and b checks are carriers");
    assert!(
        recognize_nest(&func).is_ok(),
        "every review-bar guard admits the carrier-checked nest"
    );
    let mut pass = MacRegBlock::new();
    assert!(
        pass.run(&mut func),
        "the carrier-checked nest must register-block"
    );
    assert_eq!(pass.fired(), 1);
    assert!(
        !MacRegBlock::new().run(&mut func),
        "the rewritten nest must not be blocked again"
    );
}

/// A carrier whose length is below `N*N` can trap where the unchecked fast
/// path would not: the `a` carrier.
#[test]
fn carrier_refuses_an_a_length_that_can_fail() {
    assert_refused(
        carrier_nest(NestOptions {
            a_check_len: Some(575),
            ..NestOptions::default()
        }),
        NestReject::BoundsCheckMayFail,
    );
}

/// A carrier comparing against a length register (the dynamic-length form)
/// has no compile-time length to prove.
#[test]
fn carrier_refuses_a_register_length() {
    assert_refused(
        carrier_nest(NestOptions {
            carrier_len_in_register: true,
            ..NestOptions::default()
        }),
        NestReject::Shape,
    );
}

/// The register-length carrier is refused by the review bar too, if the
/// shape match found the length elsewhere.
#[test]
fn review_bar_refuses_a_register_length_carrier() {
    let func = build_matmul_nest_with(carrier_nest(NestOptions {
        carrier_len_in_register: true,
        ..NestOptions::default()
    }));
    let dom = DomTree::compute(&func);
    let loops = LoopAnalysis::compute(&func, &dom);
    let def = crate::effects::build_reaching_def_map(&func);
    let exit = nest_exit(&func, &loops);
    assert_eq!(
        review_bar::check_mandatory_control_flow(
            &func,
            &dom,
            &def,
            &nest_facts(&func, &loops, exit)
        ),
        Err(NestReject::UnprovenBoundsCarrier)
    );
}

/// A carrier on a value that is not a recognized index (`j < 5`) is a trap
/// the scalar nest takes and the fast path would skip.
#[test]
fn carrier_refuses_a_check_of_a_non_index_value() {
    assert_refused(
        carrier_nest(NestOptions {
            carrier_on_j: true,
            ..NestOptions::default()
        }),
        NestReject::UnprovenBoundsCarrier,
    );
}

/// A carrier on the `c` index after the j-loop exited checks `i*N+N`, not a
/// current index. The read is also not dominated by the index's definition
/// (the j-loop may run zero times), which refuses first; the carrier rule
/// refuses it on its own as well.
#[test]
fn carrier_refuses_a_stale_index() {
    let opts = carrier_nest(NestOptions {
        carrier_on_stale_c_index: true,
        ..NestOptions::default()
    });
    assert_refused(opts, NestReject::UseNotDominated);
    let func = build_matmul_nest_with(opts);
    let dom = DomTree::compute(&func);
    let loops = LoopAnalysis::compute(&func, &dom);
    let def = crate::effects::build_reaching_def_map(&func);
    let exit = nest_exit(&func, &loops);
    assert_eq!(
        review_bar::check_mandatory_control_flow(
            &func,
            &dom,
            &def,
            &nest_facts(&func, &loops, exit)
        ),
        Err(NestReject::UnprovenBoundsCarrier)
    );
}

/// A carrier in a loop header runs once more than the body.
#[test]
fn carrier_refuses_a_check_in_a_loop_header() {
    assert_refused(
        carrier_nest(NestOptions {
            carrier_in_j_header: true,
            ..NestOptions::default()
        }),
        NestReject::HeaderWork,
    );
}

/// A carrier between a check's compare and its branch would supply the
/// branch's flags once expanded, so the compare is not the one the branch
/// reads.
#[test]
fn review_bar_refuses_a_carrier_between_compare_and_branch() {
    assert_refused(
        NestOptions {
            carrier_between_compare_and_branch: true,
            ..NestOptions::default()
        },
        NestReject::UnprovenConditionalBranch,
    );
}

/// The carrier-form negative controls the branch form already pins stay
/// refused: aliasing, a bypassed live-out, an undersized slot, narrow values.
#[test]
fn carrier_nest_keeps_the_other_refusals() {
    for (opts, reason) in [
        (
            NestOptions {
                c_aliases_a: true,
                ..NestOptions::default()
            },
            NestReject::AliasedArrays,
        ),
        (
            NestOptions {
                exit_reads_aik: true,
                ..NestOptions::default()
            },
            NestReject::BypassedLiveOut,
        ),
        (
            NestOptions {
                c_slot_elems: Some(575),
                ..NestOptions::default()
            },
            NestReject::SlotTooSmall,
        ),
        (
            NestOptions {
                narrow_c_value: true,
                ..NestOptions::default()
            },
            NestReject::DataWidth,
        ),
        (
            NestOptions {
                j_init_in_k_preheader: true,
                ..NestOptions::default()
            },
            NestReject::CounterInitOutsideParent,
        ),
    ] {
        assert_refused(carrier_nest(opts), reason);
    }
}

// --- pass-through carriers (outer values threaded through the nest) --------

/// An outer value the i-loop only copies out and back leaves the nest with
/// its pre-nest value, so the fast path may bypass the copies: the nest is
/// admitted in both check forms.
#[test]
fn pass_through_carrier_is_admitted() {
    for carrier_checks in [false, true] {
        let mut func = build_matmul_nest_with(NestOptions {
            pass_through: PassThrough::Copies,
            carrier_checks,
            ..NestOptions::default()
        });
        assert!(
            recognize_nest(&func).is_ok(),
            "carrier_checks={carrier_checks}: a pass-through carrier is admitted"
        );
        assert!(MacRegBlock::new().run(&mut func));
    }
}

/// Every other way a live-out value is written in the nest stays refused.
#[test]
fn pass_through_refuses_values_the_nest_changes() {
    // A copy whose source is not defined on every path to it is refused
    // earlier, as a read its definition does not dominate; the live-out rule
    // refuses it on its own as well (checked directly below).
    for (mode, first_refusal) in [
        (PassThrough::Modified, NestReject::BypassedLiveOut),
        (PassThrough::ExitReadsCopy, NestReject::BypassedLiveOut),
        (PassThrough::CopyNotDominating, NestReject::UseNotDominated),
        (PassThrough::CopyOfOtherValue, NestReject::BypassedLiveOut),
        (PassThrough::NarrowCopy, NestReject::BypassedLiveOut),
    ] {
        for carrier_checks in [false, true] {
            let opts = NestOptions {
                pass_through: mode,
                carrier_checks,
                ..NestOptions::default()
            };
            assert_refused(opts, first_refusal);
            let func = build_matmul_nest_with(opts);
            let dom = DomTree::compute(&func);
            let loops = LoopAnalysis::compute(&func, &dom);
            let exit = nest_exit(&func, &loops);
            let facts = nest_facts(&func, &loops, exit);
            let def = crate::effects::build_reaching_def_map(&func);
            let proven = review_bar::check_mandatory_control_flow(&func, &dom, &def, &facts)
                .expect("the pass-through modes keep the nest's control flow");
            assert_eq!(
                review_bar::check_no_bypassed_live_out(&func, &dom, &facts, &proven),
                Err(NestReject::BypassedLiveOut)
            );
        }
    }
}

/// The premise of `Handoff::Only(&[exit])`: the fast path, the new blocks the
/// rewrite runs INSTEAD of the nest, leaves only for the nest's exit. The one
/// new block that reaches the untouched nest is the dispatch guard, which runs
/// before any iteration is skipped, so it hands off nothing stale.
#[test]
fn fast_path_hands_off_only_to_the_nest_exit() {
    let mut func = build_matmul_nest_with(NestOptions::default());
    let dom = DomTree::compute(&func);
    let loops = LoopAnalysis::compute(&func, &dom);
    let exit = nest_exit(&func, &loops);
    let i_header = loops
        .all_loops()
        .find(|lp| lp.depth == 1)
        .expect("i-loop")
        .header;
    let before = func.num_blocks();
    assert!(MacRegBlock::new().run(&mut func));
    let created: Vec<BlockId> = (before..func.num_blocks())
        .map(|id| BlockId(id as u32))
        .collect();
    let guards: Vec<BlockId> = created
        .iter()
        .copied()
        .filter(|&block| func.block(block).succs.contains(&i_header))
        .collect();
    assert_eq!(
        guards.len(),
        1,
        "one dispatch guard reaches the fallback nest"
    );
    let fast_path: Vec<BlockId> = created
        .iter()
        .copied()
        .filter(|block| !guards.contains(block))
        .collect();
    assert!(crate::loop_contract::hands_off_only_to(
        &func, &fast_path, exit
    ));
    assert!(
        func.block(guards[0])
            .succs
            .iter()
            .all(|succ| *succ == i_header || fast_path.contains(succ))
    );
}
