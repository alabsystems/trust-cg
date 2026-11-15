// Unit tests for alias-versioned load hoisting.
//
// Each test builds a small machine function and checks whether the pass fires
// (transforms the CFG) or fails closed. The canonical firing shape is a counted
// inner loop carrying a loop-invariant plain load and an indexed store whose
// index is a `[0, bound)` induction variable — the matrix j-loop in miniature.

use super::*;
use crate::pass_manager::MachinePass;
use trust_cg_ir::{
    AArch64Opcode, BlockId, MachFunction, MachInst, MachOperand, RegClass, Signature, VReg,
};

const PACKED_LSL_SCALED: i64 = 7; // (OPTION_LSL << 1) | 1
const PACKED_UXTW_SCALED: i64 = 5; // (OPTION_UXTW << 1) | 1
const PACKED_SXTW_SCALED: i64 = 13; // (OPTION_SXTW << 1) | 1
const CC_NE: i64 = 1;

fn g64(id: u32) -> MachOperand {
    MachOperand::VReg(VReg::new(id, RegClass::Gpr64))
}
fn g32(id: u32) -> MachOperand {
    MachOperand::VReg(VReg::new(id, RegClass::Gpr32))
}
fn i(v: i64) -> MachOperand {
    MachOperand::Imm(v)
}
fn blk(b: BlockId) -> MachOperand {
    MachOperand::Block(b)
}
fn push(func: &mut MachFunction, b: BlockId, op: AArch64Opcode, ops: Vec<MachOperand>) {
    let id = func.push_inst(MachInst::new(op, ops));
    func.append_inst(b, id);
}
fn nblocks(func: &MachFunction) -> usize {
    func.block_order.len()
}

/// Knobs to derive the canonical firing shape and its fail-closed variants.
struct Shape {
    conditional_preheader: bool,
    plain_load: bool,
    opaque_writer: bool,
    counted_store: bool,
}

/// Build a counted inner loop (self-loop header==latch) with:
///  * an invariant plain load `v20 = ldr [v0, #0]`  (base v0 defined in preheader)
///  * an indexed store `str v20, [v1, v10, lsl #3]`  (base v1 invariant, idx v10)
///  * idx `v10`: init 0 in the preheader, step `v11 = v10 + 1`, `v10 = v11`
///  * exit test `cmp v11, v2(=bound 4); b.eq exit`
fn build(shape: Shape) -> MachFunction {
    let mut func = MachFunction::new("k".to_string(), Signature::new(vec![], vec![]));
    let ph = func.entry; // preheader
    let hdr = func.create_block(); // header == latch (self-loop)
    let exit = func.create_block();

    // Preheader: invariant bases + bound + idx init.
    push(&mut func, ph, AArch64Opcode::Movz, vec![g64(0), i(4096)]); // load base
    push(&mut func, ph, AArch64Opcode::Movz, vec![g64(1), i(65536)]); // store base
    push(&mut func, ph, AArch64Opcode::Movz, vec![g64(2), i(4)]); // bound
    push(&mut func, ph, AArch64Opcode::Movz, vec![g64(10), i(0)]); // idx init = 0
    if shape.conditional_preheader {
        push(&mut func, ph, AArch64Opcode::CmpRR, vec![g64(2), g64(10)]);
        push(&mut func, ph, AArch64Opcode::BCond, vec![i(1), blk(hdr)]);
        push(&mut func, ph, AArch64Opcode::B, vec![blk(exit)]);
        func.add_edge(ph, hdr);
        func.add_edge(ph, exit);
    } else {
        push(&mut func, ph, AArch64Opcode::B, vec![blk(hdr)]);
        func.add_edge(ph, hdr);
    }

    // Header/latch body.
    if shape.plain_load {
        push(
            &mut func,
            hdr,
            AArch64Opcode::LdrRI,
            vec![g64(20), g64(0), i(0)],
        );
    } else {
        // register-offset load — not a plain hoistable load.
        push(
            &mut func,
            hdr,
            AArch64Opcode::LdrRO,
            vec![g64(20), g64(0), g64(10), i(PACKED_LSL_SCALED)],
        );
    }
    if shape.opaque_writer {
        push(
            &mut func,
            hdr,
            AArch64Opcode::Bl,
            vec![MachOperand::Symbol("f".to_string())],
        );
    }
    push(
        &mut func,
        hdr,
        AArch64Opcode::StrRO,
        vec![g64(20), g64(1), g64(10), i(PACKED_LSL_SCALED)],
    );
    push(
        &mut func,
        hdr,
        AArch64Opcode::AddRI,
        vec![g64(11), g64(10), i(1)],
    ); // step
    push(&mut func, hdr, AArch64Opcode::MovR, vec![g64(10), g64(11)]); // idx <- step
    if shape.counted_store {
        push(&mut func, hdr, AArch64Opcode::CmpRR, vec![g64(11), g64(2)]);
        push(&mut func, hdr, AArch64Opcode::BCond, vec![i(0), blk(exit)]); // b.eq exit
        push(&mut func, hdr, AArch64Opcode::B, vec![blk(hdr)]);
    } else {
        // Exit predicate that never references the step: the index is unbounded.
        push(&mut func, hdr, AArch64Opcode::CmpRR, vec![g64(20), g64(2)]);
        push(&mut func, hdr, AArch64Opcode::BCond, vec![i(0), blk(exit)]);
        push(&mut func, hdr, AArch64Opcode::B, vec![blk(hdr)]);
    }
    func.add_edge(hdr, exit);
    func.add_edge(hdr, hdr);

    push(&mut func, exit, AArch64Opcode::Ret, vec![]);
    func
}

fn ok() -> Shape {
    Shape {
        conditional_preheader: false,
        plain_load: true,
        opaque_writer: false,
        counted_store: true,
    }
}

#[test]
fn fires_on_counted_invariant_load_store_shape() {
    let mut func = build(ok());
    let before = nblocks(&func);
    let mut pass = AliasVersionedLoadHoist;
    assert!(pass.run(&mut func), "should fire on the matrix-like shape");
    assert!(
        nblocks(&func) > before,
        "firing must add the version-check diamond + clone blocks"
    );
    // An unsigned-LS disjointness branch (b.ls) must be emitted.
    let has_ls = func.block_order.iter().any(|&b| {
        func.block(b).insts.iter().any(|&id| {
            let inst = func.inst(id);
            inst.opcode == AArch64Opcode::BCond
                && matches!(inst.operands.first(), Some(MachOperand::Imm(9)))
        })
    });
    assert!(has_ls, "an unsigned-LS disjointness branch must be emitted");
}

#[test]
fn refuses_header_missing_from_layout_without_mutation() {
    let mut func = build(ok());
    let dom = DomTree::compute(&func);
    let loops = LoopAnalysis::compute(&func, &dom);
    let lp = loops.all_loops().next().expect("fixture has a loop");
    func.block_order.retain(|b| *b != lp.header);
    let before = format!("{func:?}");
    assert!(!try_version_hoist(&mut func, &dom, lp));
    assert_eq!(format!("{func:?}"), before);
}

#[test]
fn refuses_conditional_preheader() {
    let mut func = build(Shape {
        conditional_preheader: true,
        ..ok()
    });
    let before = nblocks(&func);
    let mut pass = AliasVersionedLoadHoist;
    assert!(
        !pass.run(&mut func),
        "must refuse a non-unconditional preheader"
    );
    assert_eq!(nblocks(&func), before);
}

#[test]
fn refuses_non_plain_load() {
    let mut func = build(Shape {
        plain_load: false,
        ..ok()
    });
    let mut pass = AliasVersionedLoadHoist;
    assert!(
        !pass.run(&mut func),
        "no plain LdrRI load => no hoist candidate"
    );
}

#[test]
fn refuses_opaque_writer() {
    let mut func = build(Shape {
        opaque_writer: true,
        ..ok()
    });
    let mut pass = AliasVersionedLoadHoist;
    assert!(
        !pass.run(&mut func),
        "a call in the loop is an unbounded writer"
    );
}

#[test]
fn refuses_unbounded_store_index() {
    let mut func = build(Shape {
        counted_store: false,
        ..ok()
    });
    let mut pass = AliasVersionedLoadHoist;
    assert!(
        !pass.run(&mut func),
        "store index without a [0,bound) counted-IV test must fail closed"
    );
}

/// A load base produced by a CSEL is NOT loop-invariant: `CSEL` consumes NZCV,
/// which is not in its operand list, so the flag writer in the body changes the
/// selected pointer every iteration.
///
/// The operand-only invariance test admitted it (both explicit sources are
/// invariant) and `MemoryEffect::Pure` let it through the purity gate, so the
/// pass hoisted `ldr [csel_result]` into the fast preheader AND
/// re-materialized the CSEL in the preamble, where NO compare has run — it
/// then selects on the CALLER's leftover NZCV. Reproduced end-to-end: a raw
/// pointer kernel `p = if s & 1 == 0 { a } else { b }; s += *p; *out = s;`
/// returned 30 under trust-cg vs 39 under LLVM and under
/// `TRUST_CG_DISABLE_PASSES=aliashoist`.
#[test]
fn refuses_flag_reading_load_base() {
    let mut func = MachFunction::new("csel_base".to_string(), Signature::new(vec![], vec![]));
    let ph = func.entry;
    let hdr = func.create_block();
    let exit = func.create_block();

    // Preheader: two candidate load bases, a store base, the bound, idx init.
    push(&mut func, ph, AArch64Opcode::Movz, vec![g64(0), i(4096)]); // cand A
    push(&mut func, ph, AArch64Opcode::Movz, vec![g64(1), i(8192)]); // cand B
    push(&mut func, ph, AArch64Opcode::Movz, vec![g64(3), i(65536)]); // store base
    push(&mut func, ph, AArch64Opcode::Movz, vec![g64(2), i(4)]); // bound
    push(&mut func, ph, AArch64Opcode::Movz, vec![g64(10), i(0)]); // idx init
    push(&mut func, ph, AArch64Opcode::B, vec![blk(hdr)]);
    func.add_edge(ph, hdr);

    // Body: a LOOP-VARIANT compare feeding a CSEL that picks the load base.
    push(&mut func, hdr, AArch64Opcode::CmpRI, vec![g64(10), i(2)]);
    push(
        &mut func,
        hdr,
        AArch64Opcode::Csel,
        vec![g64(4), g64(0), g64(1), i(0)], // v4 = (idx == 2) ? v0 : v1
    );
    push(
        &mut func,
        hdr,
        AArch64Opcode::LdrRI,
        vec![g64(20), g64(4), i(0)], // ldr v20, [v4] -- base is the CSEL result
    );
    push(
        &mut func,
        hdr,
        AArch64Opcode::StrRI,
        vec![g64(20), g64(3), i(0)], // boundable fixed store
    );
    push(
        &mut func,
        hdr,
        AArch64Opcode::AddRI,
        vec![g64(11), g64(10), i(1)],
    );
    push(&mut func, hdr, AArch64Opcode::MovR, vec![g64(10), g64(11)]);
    push(&mut func, hdr, AArch64Opcode::CmpRR, vec![g64(11), g64(2)]);
    push(&mut func, hdr, AArch64Opcode::BCond, vec![i(0), blk(exit)]);
    push(&mut func, hdr, AArch64Opcode::B, vec![blk(hdr)]);
    func.add_edge(hdr, exit);
    func.add_edge(hdr, hdr);
    push(&mut func, exit, AArch64Opcode::Ret, vec![]);

    let before = nblocks(&func);
    let mut pass = AliasVersionedLoadHoist;
    assert!(
        !pass.run(&mut func),
        "a CSEL result is not loop-invariant: NZCV is an unmodelled input"
    );
    assert_eq!(nblocks(&func), before);
}

/// The movement contract itself: every flag READER that `opcode_effect`
/// classifies as memory-pure must still be refused, so a future opcode cannot
/// silently re-open the hole above.
#[test]
fn flag_readers_are_never_invariance_movable() {
    for op in [
        AArch64Opcode::Csel,
        AArch64Opcode::CSet,
        AArch64Opcode::Csinc,
        AArch64Opcode::Csinv,
        AArch64Opcode::Csneg,
        AArch64Opcode::FcselRR,
        AArch64Opcode::Adc,
        AArch64Opcode::Sbc,
    ] {
        assert!(
            crate::effects::opcode_effect(op).is_pure(),
            "{op:?} is memory-pure, which is exactly why the weaker gate let it through"
        );
        let inst = MachInst::new(op, vec![]);
        assert!(
            !super::is_invariance_movable(&inst),
            "{op:?} reads NZCV and must fail the invariance movement contract"
        );
    }
    // A genuinely movable pure op still passes.
    let add = MachInst::new(AArch64Opcode::AddRR, vec![]);
    assert!(super::is_invariance_movable(&add));
}

#[test]
fn no_loops_is_noop() {
    let mut func = MachFunction::new("flat".to_string(), Signature::new(vec![], vec![]));
    let e = func.entry;
    push(&mut func, e, AArch64Opcode::Ret, vec![]);
    let mut pass = AliasVersionedLoadHoist;
    assert!(!pass.run(&mut func));
}

/// The clobber/read range of a 128-bit access must be 16 bytes.
///
/// This number is the ONLY thing standing between the runtime disjointness
/// check and an unsound hoist: it is used both as a load range's width and as
/// the SCALE of an indexed store's range (`[base, base + bound*scale)`), so an
/// under-estimate shrinks the region the check proves disjoint while the
/// hardware still writes the full width. The pass previously reached `Fpr128`
/// through a `_ => 8` catch-all and credited a 16-byte `STR Q` / `LDR Q` with 8
/// bytes — half of every vector access invisible to the check.
///
/// Errors in the other direction are safe (a too-wide range can only fail the
/// check and take the untouched slow loop), which is why the narrow classes may
/// keep the conservative 8; only "never smaller than the true width" is
/// asserted here.
#[test]
fn class_byte_ranges_never_understate_the_access_width() {
    let true_width = |c: RegClass| -> i64 {
        match c {
            RegClass::Fpr128 => 16,
            RegClass::Gpr64 | RegClass::Fpr64 | RegClass::System => 8,
            RegClass::Gpr32 | RegClass::Fpr32 => 4,
            RegClass::Fpr16 => 2,
            RegClass::Fpr8 => 1,
        }
    };
    for c in [
        RegClass::Fpr128,
        RegClass::Gpr64,
        RegClass::Fpr64,
        RegClass::System,
        RegClass::Gpr32,
        RegClass::Fpr32,
        RegClass::Fpr16,
        RegClass::Fpr8,
    ] {
        assert!(
            class_bytes(c) >= true_width(c),
            "{c:?}: range {} understates a {}-byte access",
            class_bytes(c),
            true_width(c)
        );
    }
    assert_eq!(class_bytes(RegClass::Fpr128), 16, "Q access is 16 bytes");
}

// ---------------------------------------------------------------------------
// The store range must cover what the do-while actually executes.
// ---------------------------------------------------------------------------

/// The exit test's right-hand side in [`build_store_first`].
#[derive(Clone, Copy, Debug)]
enum ExitBound {
    /// `cmp step, n` against the parameter `n` (x3).
    Reg,
    /// `cmp step, #k`.
    Imm(i64),
    /// `cmp step, n` against `n = movz #k` in the preheader: the selector's
    /// spelling of a constant bound that does not fold into the compare.
    Movz(i64),
}

/// The importer's do-while with the STORE FIRST, the body order the bridge
/// emits for `loop { *a.add(i) = 7; *out = *p; i += c; if <exit> { break } }`:
///
/// ```text
///   entry: v1=a(x0)  v0=p(x1)  v3=out(x2)  v2=n(x3)  v10=0  v30=7 ; b hdr
///   hdr:   str v30, [v1, v10, lsl #3]      ; a[i] = 7
///          v20 = ldr [v0, #0]              ; *p   (the hoist candidate)
///          str v20, [v3, #0]               ; *out = *p
///          v11 = v10 + c ; v10 = v11
///          cmp v11, <bound> ; b.<cc> exit ; b hdr
/// ```
///
/// The preheader enters the loop unconditionally, so iteration 0 stores `a[0]`
/// before any exit test has looked at the bound.
fn build_store_first(exit_cc: i64, step: i64, bound: ExitBound) -> MachFunction {
    build_store_first_with(StoreFirst {
        exit_cc,
        step,
        bound,
        index: StoreIndex::Lsl64,
        step_before_store: false,
    })
}

/// How the indexed store in [`build_store_first_with`] reads the index.
#[derive(Clone, Copy, Debug)]
enum StoreIndex {
    /// A 64-bit index, `[a, i, lsl #3]`: the shape a `u64`/`i64` index gives.
    Lsl64,
    /// A 32-bit index, `[a, w_i, sxtw #3]`: an `i32` index after ext-addr.
    Sxtw32,
    /// A 32-bit index, `[a, w_i, uxtw #3]`: a `u32` index after ext-addr.
    Uxtw32,
}

/// [`build_store_first`] with the index width and the position of the index
/// update chosen.
#[derive(Clone, Copy, Debug)]
struct StoreFirst {
    exit_cc: i64,
    step: i64,
    bound: ExitBound,
    /// For a 32-bit index, `i`, its step and the bound `n` are Gpr32, the
    /// classes the selector gives an `i32`/`u32` induction variable.
    index: StoreIndex,
    /// Emit `v11 = v10 + c ; v10 = v11` BEFORE the store, so the store reads
    /// the stepped index.
    step_before_store: bool,
}

fn build_store_first_with(shape: StoreFirst) -> MachFunction {
    use trust_cg_ir::regs::{X0, X1, X2, X3};
    let StoreFirst {
        exit_cc,
        step,
        bound,
        index,
        step_before_store,
    } = shape;
    let (iv, packed) = match index {
        StoreIndex::Lsl64 => (g64 as fn(u32) -> MachOperand, PACKED_LSL_SCALED),
        StoreIndex::Sxtw32 => (g32 as fn(u32) -> MachOperand, PACKED_SXTW_SCALED),
        StoreIndex::Uxtw32 => (g32 as fn(u32) -> MachOperand, PACKED_UXTW_SCALED),
    };
    let mut func = MachFunction::new("k".to_string(), Signature::new(vec![], vec![]));
    let ph = func.entry;
    let hdr = func.create_block();
    let exit = func.create_block();
    let preg = MachOperand::PReg;

    push(&mut func, ph, AArch64Opcode::Copy, vec![g64(1), preg(X0)]); // a
    push(&mut func, ph, AArch64Opcode::Copy, vec![g64(0), preg(X1)]); // p
    push(&mut func, ph, AArch64Opcode::Copy, vec![g64(3), preg(X2)]); // out
    match bound {
        ExitBound::Movz(k) => push(&mut func, ph, AArch64Opcode::Movz, vec![iv(2), i(k)]),
        _ => push(&mut func, ph, AArch64Opcode::Copy, vec![iv(2), preg(X3)]), // n
    }
    push(&mut func, ph, AArch64Opcode::Movz, vec![iv(10), i(0)]); // i = 0
    push(&mut func, ph, AArch64Opcode::Movz, vec![g64(30), i(7)]); // 7
    push(&mut func, ph, AArch64Opcode::B, vec![blk(hdr)]);
    func.add_edge(ph, hdr);

    let step_index = |func: &mut MachFunction| {
        push(
            func,
            hdr,
            AArch64Opcode::AddRI,
            vec![iv(11), iv(10), i(step)],
        );
        push(func, hdr, AArch64Opcode::MovR, vec![iv(10), iv(11)]);
    };
    if step_before_store {
        step_index(&mut func);
    }
    push(
        &mut func,
        hdr,
        AArch64Opcode::StrRO,
        vec![g64(30), g64(1), iv(10), i(packed)],
    );
    push(
        &mut func,
        hdr,
        AArch64Opcode::LdrRI,
        vec![g64(20), g64(0), i(0)],
    );
    push(
        &mut func,
        hdr,
        AArch64Opcode::StrRI,
        vec![g64(20), g64(3), i(0)],
    );
    if !step_before_store {
        step_index(&mut func);
    }
    match bound {
        ExitBound::Reg | ExitBound::Movz(_) => {
            push(&mut func, hdr, AArch64Opcode::CmpRR, vec![iv(11), iv(2)])
        }
        ExitBound::Imm(k) => push(&mut func, hdr, AArch64Opcode::CmpRI, vec![iv(11), i(k)]),
    }
    push(
        &mut func,
        hdr,
        AArch64Opcode::BCond,
        vec![i(exit_cc), blk(exit)],
    );
    push(&mut func, hdr, AArch64Opcode::B, vec![blk(hdr)]);
    func.add_edge(hdr, exit);
    func.add_edge(hdr, hdr);
    push(&mut func, exit, AArch64Opcode::Ret, vec![]);
    func
}

/// Where the version check sends control.
#[derive(Debug, PartialEq, Eq)]
enum Route {
    /// The fast preheader (hoisted loads) and the clone.
    Fast,
    /// The original, untouched loop.
    Slow,
}

/// Whether AArch64 condition `cc` holds after `cmp lhs, rhs` (64-bit).
fn cond_holds(cc: i64, (lhs, rhs): (u64, u64)) -> bool {
    let (sl, sr) = (lhs as i64, rhs as i64);
    match cc {
        0 => lhs == rhs,
        1 => lhs != rhs,
        2 => lhs >= rhs,
        3 => lhs < rhs,
        8 => lhs > rhs,
        9 => lhs <= rhs,
        10 => sl >= sr,
        11 => sl < sr,
        12 => sl > sr,
        13 => sl <= sr,
        _ => panic!("unmodelled condition code {cc}"),
    }
}

fn block_operand(op: &MachOperand) -> BlockId {
    match op {
        MachOperand::Block(b) => *b,
        other => panic!("branch target {other:?} is not a block"),
    }
}

/// Execute the entry block, the preamble and the check chain with `args` in
/// x0..x3 until control reaches `slow_header` (the original loop) or executes
/// a load (only the fast preheader's hoisted loads can be reached first).
/// Every opcode the chain is built from is modelled; any other one panics, so
/// a new chain shape cannot be silently mis-evaluated.
fn route(func: &MachFunction, slow_header: BlockId, args: [u64; 4]) -> Route {
    use trust_cg_ir::regs::{X0, X1, X2, X3};
    let mut regs: HashMap<u32, u64> = HashMap::default();
    let mut flags = (0u64, 0u64);
    let mut b = func.entry;
    for _ in 0..64 {
        if b == slow_header {
            return Route::Slow;
        }
        let mut next = None;
        for &id in &func.block(b).insts {
            let inst = func.inst(id);
            let val = |k: usize| -> u64 {
                match &inst.operands[k] {
                    MachOperand::VReg(v) => *regs
                        .get(&v.id)
                        .unwrap_or_else(|| panic!("v{} read before def in {inst:?}", v.id)),
                    MachOperand::Imm(x) => *x as u64,
                    MachOperand::PReg(p) => {
                        let at = [X0, X1, X2, X3].iter().position(|r| r == p);
                        args[at.unwrap_or_else(|| panic!("unmodelled preg in {inst:?}"))]
                    }
                    other => panic!("unmodelled operand {other:?} in {inst:?}"),
                }
            };
            let dst = || inst.operands[0].as_vreg().expect("vreg def").id;
            match inst.opcode {
                AArch64Opcode::Copy | AArch64Opcode::MovR => {
                    let v = val(1);
                    regs.insert(dst(), v);
                }
                AArch64Opcode::Movz => {
                    assert_eq!(inst.operands.len(), 2, "shifted movz: {inst:?}");
                    let v = val(1);
                    regs.insert(dst(), v);
                }
                AArch64Opcode::AddRI | AArch64Opcode::AddRR => {
                    let v = val(1).wrapping_add(val(2));
                    regs.insert(dst(), v);
                }
                AArch64Opcode::LslRI => {
                    let v = val(1) << val(2);
                    regs.insert(dst(), v);
                }
                AArch64Opcode::LsrRI => {
                    let v = val(1) >> val(2);
                    regs.insert(dst(), v);
                }
                AArch64Opcode::CmpRR | AArch64Opcode::CmpRI => flags = (val(0), val(1)),
                AArch64Opcode::BCond => {
                    let cc = inst.operands[0].as_imm().expect("cc");
                    if cond_holds(cc, flags) {
                        next = Some(block_operand(&inst.operands[1]));
                        break;
                    }
                }
                AArch64Opcode::B => {
                    next = Some(block_operand(&inst.operands[0]));
                    break;
                }
                _ if load_access_size(inst).is_some() => return Route::Fast,
                op => panic!("unmodelled opcode {op:?} on the version-check path"),
            }
        }
        b = next.expect("block fell through without a branch");
    }
    panic!("version check did not reach either loop");
}

/// Run the pass on a fresh [`build_store_first`] function and route `args`.
fn route_after_pass(exit_cc: i64, step: i64, bound: ExitBound, args: [u64; 4]) -> Route {
    route_shape_after_pass(
        StoreFirst {
            exit_cc,
            step,
            bound,
            index: StoreIndex::Lsl64,
            step_before_store: false,
        },
        args,
    )
}

/// Run the pass on a fresh [`build_store_first_with`] function and route
/// `args`.
fn route_shape_after_pass(shape: StoreFirst, args: [u64; 4]) -> Route {
    let mut func = build_store_first_with(shape);
    let header = BlockId(1);
    assert_eq!(func.block_order[1], header, "fixture header id");
    let _ = AliasVersionedLoadHoist.run(&mut func);
    route(&func, header, args)
}

const A: u64 = 0x1_0000;
const OUT: u64 = 0x9_0000;

/// One input the version check must send to the original loop: the store
/// range the loop really writes overlaps the hoisted load at `p`.
type SlowCase = (&'static str, i64, i64, ExitBound, [u64; 4]);

/// The names of the `cases` the version check sends to the fast clone.
fn routed_fast(cases: &[SlowCase]) -> Vec<&'static str> {
    cases
        .iter()
        .filter(|&&(_, cc, step, bound, args)| {
            route_after_pass(cc, step, bound, args) != Route::Slow
        })
        .map(|case| case.0)
        .collect()
}

/// `n == 0` with `p == a`: the do-while still runs once and stores `a[0] = 7`
/// BEFORE loading `*p`, so `*out` must be 7. Sizing the store range from `n`
/// alone gives the empty `[a, a)`, which every load range "clears", and the
/// fast clone reads `*p` (stale) ahead of the store. Under `b.eq` an `n` of 0
/// is never met by the test at all, so the index is unbounded.
#[test]
fn zero_register_bound_does_not_prove_the_first_iterations_store_disjoint() {
    let cases: [SlowCase; 3] = [
        ("b.hs n=0 p=a", CC_HS, 1, ExitBound::Reg, [A, A, OUT, 0]),
        ("b.ge n=0 p=a", CC_GE, 1, ExitBound::Reg, [A, A, OUT, 0]),
        (
            "b.eq n=0 p=a+16",
            CC_EQ,
            1,
            ExitBound::Reg,
            [A, A + 16, OUT, 0],
        ),
    ];
    assert_eq!(routed_fast(&cases), Vec::<&str>::new());
}

/// Signed `b.ge` with `n <= -1`: the loop runs once (step 1 >= n), storing
/// `a[0]`. `n << 3` is negative, so `a + (n << 3)` wraps BELOW `a` and the
/// "store entirely below the load" test passes for `p == a`.
#[test]
fn negative_signed_register_bound_does_not_wrap_the_store_range() {
    let cases: [SlowCase; 2] = [
        (
            "b.ge n=-1 p=a",
            CC_GE,
            1,
            ExitBound::Reg,
            [A, A, OUT, u64::MAX],
        ),
        (
            "b.ge n=-4 p=a",
            CC_GE,
            1,
            ExitBound::Reg,
            [A, A, OUT, (-4i64) as u64],
        ),
    ];
    assert_eq!(routed_fast(&cases), Vec::<&str>::new());
}

/// `n << 3` overflowing 64 bits: `n = 2^61 + 2` gives 16 bytes, so `p = a + 16`
/// looks clear of a range that really covers it (a[2] is stored on iteration
/// 2); `n = usize::MAX` used as "no limit" wraps `hi` below `a`.
#[test]
fn overflowing_register_bound_does_not_wrap_the_store_range() {
    let cases: [SlowCase; 3] = [
        (
            "b.hs n=2^61+2 p=a+16",
            CC_HS,
            1,
            ExitBound::Reg,
            [A, A + 16, OUT, (1 << 61) + 2],
        ),
        (
            "b.eq n=2^61+2 p=a+16",
            CC_EQ,
            1,
            ExitBound::Reg,
            [A, A + 16, OUT, (1 << 61) + 2],
        ),
        (
            "b.eq n=MAX p=a+16",
            CC_EQ,
            1,
            ExitBound::Reg,
            [A, A + 16, OUT, u64::MAX],
        ),
    ];
    assert_eq!(routed_fast(&cases), Vec::<&str>::new());
}

/// `b.eq` with a step of 2 against an odd bound never fires (2, 4, 6, ... skip
/// 5), so the index walks past `bound`: `[0, bound)` under-approximates the
/// stores and a load at `a + 48` (a[6]) is clobbered on iteration 3.
#[test]
fn equality_exit_with_a_non_unit_step_does_not_bound_the_index() {
    let cases: [SlowCase; 2] = [
        (
            "b.eq step=2 n=5 p=a+48",
            CC_EQ,
            2,
            ExitBound::Reg,
            [A, A + 48, OUT, 5],
        ),
        (
            "b.eq step=2 #5 p=a+48",
            CC_EQ,
            2,
            ExitBound::Imm(5),
            [A, A + 48, OUT, 5],
        ),
    ];
    assert_eq!(routed_fast(&cases), Vec::<&str>::new());
}

/// The guard leaves the fast path to every bound it can size: the transform
/// still fires, takes the clone when the load sits just outside `[a, a+8n)`,
/// and takes the original loop when it sits inside.
#[test]
fn sized_register_bounds_keep_the_fast_path() {
    for cc in [CC_EQ, CC_HS, CC_GE] {
        let mut func = build_store_first(cc, 1, ExitBound::Reg);
        assert!(AliasVersionedLoadHoist.run(&mut func), "cc {cc} fires");
        let hdr = BlockId(1);
        assert_eq!(route(&func, hdr, [A, A + 32, OUT, 4]), Route::Fast);
        assert_eq!(route(&func, hdr, [A, A + 24, OUT, 4]), Route::Slow);
        assert_eq!(route(&func, hdr, [A, A + 8, OUT, 1]), Route::Fast);
        assert_eq!(route(&func, hdr, [A, A, OUT, 1]), Route::Slow);
        assert_eq!(route(&func, hdr, [A, A - 8, OUT, 4]), Route::Fast);
    }
    for step in [1, 3] {
        assert_eq!(
            route_after_pass(CC_HS, step, ExitBound::Reg, [A, A + 32, OUT, 4]),
            Route::Fast,
            "b.hs with step {step} stays in [0, n)"
        );
    }
}

// ---------------------------------------------------------------------------
// Must-execute inside the loop: a guard that runs before the load.
// ---------------------------------------------------------------------------

/// Where [`build_guarded`] puts the guard on `k` (v4) relative to the hoist
/// candidate `ldr [v0, #0]`.
#[derive(Clone, Copy, Debug)]
enum Guard {
    /// A `TrapBoundsCheckExact` carrier earlier in the load's block: it traps
    /// with no CFG edge and otherwise falls through to the load.
    CarrierBeforeLoad,
    /// `select_assert`'s unfused spelling earlier in the load's block:
    /// `cmp k, #0 ; b.eq trap` in the middle of the block.
    BranchBeforeLoad,
    /// The carrier ends the header and the load sits in the latch, which is
    /// also the exiting block: the latch dominates every latch and exit, yet
    /// the header's guard runs first.
    CarrierInHeader,
    /// The carrier after the load: iteration 0 runs the load first.
    CarrierAfterLoad,
    /// No guard: the header ends by entering `spin: cmp k, #0 ; b.ne spin ;
    /// b latch`, a self-loop that never exits while `k != 0`, and the load
    /// sits in the latch, which is also the exiting block. The latch
    /// dominates every latch and exit, yet iteration 0 spins forever first.
    SpinInHeader,
}

/// A store-first do-while (`b.hs` exit, step 1, register bound) with a guard
/// on `k`. Both stores are fixed, so the loop needs no counted store index:
/// the counted-index recognizer reads only the first `b.eq/ge/hs` leaving a
/// block, so with an indexed store `BranchBeforeLoad`'s `b.eq trap` would
/// refuse the loop whatever the must-execute test decides.
///
/// ```text
///   entry: v1=a  v0=p  v3=out  v2=n  v4=k  v10=0  v30=7 ; b hdr
///   hdr:   str v30, [v1, #0]
///          <guard>                           ; before or after the load
///          v20 = ldr [v0, #0]
///          str v20, [v3, #0]
///          v11 = v10 + 1 ; v10 = v11 ; cmp v11, v2 ; b.hs exit ; b hdr
///   trap:  brk                               ; `BranchBeforeLoad` only
///   exit:  ret
/// ```
///
/// `CarrierInHeader` ends `hdr` with `b latch` after the guard and moves the
/// load and the rest of the body to `latch`; `SpinInHeader` does the same with
/// an inner self-loop between `hdr` and `latch` in place of the guard.
fn build_guarded(guard: Guard) -> MachFunction {
    let mut func = MachFunction::new("guarded".to_string(), Signature::new(vec![], vec![]));
    let ph = func.entry;
    let hdr = func.create_block();
    let latch = match guard {
        Guard::CarrierInHeader | Guard::SpinInHeader => func.create_block(),
        _ => hdr,
    };
    let exit = func.create_block();

    push(&mut func, ph, AArch64Opcode::Movz, vec![g64(1), i(0x1000)]); // a
    push(&mut func, ph, AArch64Opcode::Movz, vec![g64(0), i(0x2000)]); // p
    push(&mut func, ph, AArch64Opcode::Movz, vec![g64(3), i(0x3000)]); // out
    push(&mut func, ph, AArch64Opcode::Movz, vec![g64(2), i(4)]); // n
    push(&mut func, ph, AArch64Opcode::Movz, vec![g64(4), i(1)]); // k
    push(&mut func, ph, AArch64Opcode::Movz, vec![g64(10), i(0)]); // i = 0
    push(&mut func, ph, AArch64Opcode::Movz, vec![g64(30), i(7)]); // 7
    push(&mut func, ph, AArch64Opcode::B, vec![blk(hdr)]);
    func.add_edge(ph, hdr);

    let carrier = |func: &mut MachFunction, b: BlockId| {
        push(
            func,
            b,
            AArch64Opcode::TrapBoundsCheckExact,
            vec![g64(4), g64(4), i(16)],
        );
    };
    push(
        &mut func,
        hdr,
        AArch64Opcode::StrRI,
        vec![g64(30), g64(1), i(0)],
    );
    match guard {
        Guard::CarrierBeforeLoad => carrier(&mut func, hdr),
        Guard::BranchBeforeLoad => {
            let trap = func.create_block();
            push(&mut func, hdr, AArch64Opcode::CmpRI, vec![g64(4), i(0)]);
            push(
                &mut func,
                hdr,
                AArch64Opcode::BCond,
                vec![i(CC_EQ), blk(trap)],
            );
            func.add_edge(hdr, trap);
            push(&mut func, trap, AArch64Opcode::Brk, vec![]);
        }
        Guard::CarrierInHeader => {
            carrier(&mut func, hdr);
            push(&mut func, hdr, AArch64Opcode::B, vec![blk(latch)]);
            func.add_edge(hdr, latch);
        }
        Guard::CarrierAfterLoad => {}
        Guard::SpinInHeader => {
            let spin = func.create_block();
            push(&mut func, hdr, AArch64Opcode::B, vec![blk(spin)]);
            func.add_edge(hdr, spin);
            push(&mut func, spin, AArch64Opcode::CmpRI, vec![g64(4), i(0)]);
            push(
                &mut func,
                spin,
                AArch64Opcode::BCond,
                vec![i(CC_NE), blk(spin)],
            );
            push(&mut func, spin, AArch64Opcode::B, vec![blk(latch)]);
            func.add_edge(spin, spin);
            func.add_edge(spin, latch);
        }
    }
    push(
        &mut func,
        latch,
        AArch64Opcode::LdrRI,
        vec![g64(20), g64(0), i(0)],
    );
    if let Guard::CarrierAfterLoad = guard {
        carrier(&mut func, latch);
    }
    push(
        &mut func,
        latch,
        AArch64Opcode::StrRI,
        vec![g64(20), g64(3), i(0)],
    );
    push(
        &mut func,
        latch,
        AArch64Opcode::AddRI,
        vec![g64(11), g64(10), i(1)],
    );
    push(
        &mut func,
        latch,
        AArch64Opcode::MovR,
        vec![g64(10), g64(11)],
    );
    push(
        &mut func,
        latch,
        AArch64Opcode::CmpRR,
        vec![g64(11), g64(2)],
    );
    push(
        &mut func,
        latch,
        AArch64Opcode::BCond,
        vec![i(CC_HS), blk(exit)],
    );
    push(&mut func, latch, AArch64Opcode::B, vec![blk(hdr)]);
    func.add_edge(latch, exit);
    func.add_edge(latch, hdr);
    push(&mut func, exit, AArch64Opcode::Ret, vec![]);
    func
}

/// With `k` out of bounds, iteration 0 traps on the guard before it reads `p`.
/// Hoisting `ldr [p]` into the fast preheader reads `p` first: a fault the
/// program did not have. Every guard that runs before the load must refuse it
/// and leave the function unchanged.
#[test]
fn refuses_a_load_an_in_loop_guard_runs_before() {
    let hoisted: Vec<Guard> = [
        Guard::CarrierBeforeLoad,
        Guard::BranchBeforeLoad,
        Guard::CarrierInHeader,
    ]
    .into_iter()
    .filter(|&guard| {
        let mut func = build_guarded(guard);
        let before = format!("{func:?}");
        let fired = AliasVersionedLoadHoist.run(&mut func);
        assert_eq!(
            fired,
            format!("{func:?}") != before,
            "{guard:?}: the change flag must match the function"
        );
        fired
    })
    .collect();
    assert!(
        hoisted.is_empty(),
        "hoisted a load above an in-loop guard that runs first: {hoisted:?}"
    );
}

/// With `k != 0`, iteration 0 spins in the inner loop forever and never reads
/// `p`; neither Rust nor trust-ir assumes forward progress. Hoisting `ldr [p]`
/// into the fast preheader turns that non-termination into a fault, so the
/// loop must be left unchanged.
#[test]
fn refuses_a_load_an_inner_loop_runs_before() {
    let mut func = build_guarded(Guard::SpinInHeader);
    let before = format!("{func:?}");
    assert!(
        !AliasVersionedLoadHoist.run(&mut func),
        "hoisted a load above an inner loop that may never exit"
    );
    assert_eq!(format!("{func:?}"), before);
}

/// POSITIVE CONTROL: a guard that runs only after the load cannot stop it, so
/// the load still version-hoists.
#[test]
fn hoists_a_load_that_runs_before_the_guard() {
    let mut func = build_guarded(Guard::CarrierAfterLoad);
    let before = nblocks(&func);
    assert!(
        AliasVersionedLoadHoist.run(&mut func),
        "a load before the guard version-hoists"
    );
    assert!(nblocks(&func) > before);
}

// ---------------------------------------------------------------------------
// In-loop synchronization: a load-acquire anywhere in the loop.
// ---------------------------------------------------------------------------

/// Every load-acquire opcode ([`is_load_acquire`]).
const ACQUIRE_LOADS: [AArch64Opcode; 4] = [
    AArch64Opcode::Ldar,
    AArch64Opcode::Ldarb,
    AArch64Opcode::Ldarh,
    AArch64Opcode::Ldaxr,
];

/// Where [`build_with_acquire`] puts `acq v40, [v5]` in the canonical loop.
#[derive(Clone, Copy, Debug)]
enum AcquireAt {
    /// First in the header, ahead of the hoist candidate `ldr [v0, #0]`.
    BeforeLoad,
    /// Right after the hoist candidate: the next iteration's read follows it.
    AfterLoad,
    /// In the preheader: every read of the loop already follows it.
    Preheader,
}

/// [`build`]`(ok())` with a flag base `v5` defined first in the preheader and
/// a load-acquire `acq v40, [v5]` at `at`.
fn build_with_acquire(acq: AArch64Opcode, at: AcquireAt) -> MachFunction {
    let mut func = build(ok());
    let ph = func.entry;
    let hdr = func.block(ph).succs[0];
    let flag = func.push_inst(MachInst::new(AArch64Opcode::Movz, vec![g64(5), i(8192)]));
    func.block_mut(ph).insts.insert(0, flag);
    let acquire = func.push_inst(MachInst::new(acq, vec![g64(40), g64(5)]));
    let (block, pos) = match at {
        AcquireAt::BeforeLoad => (hdr, 0),
        AcquireAt::AfterLoad => (hdr, 1),
        AcquireAt::Preheader => (ph, 1),
    };
    func.block_mut(block).insts.insert(pos, acquire);
    func
}

/// The fast preheader reads the hoisted address once, ahead of every in-loop
/// acquire. A read that follows an acquire which saw a release must see what
/// that release published: iteration 1's read when the acquire comes first,
/// the later iterations' reads when it comes after. Every acquire opcode in
/// either position must refuse the loop and leave the function unchanged.
#[test]
fn refuses_a_loop_with_a_load_acquire() {
    let mut hoisted = Vec::new();
    for acq in ACQUIRE_LOADS {
        for at in [AcquireAt::BeforeLoad, AcquireAt::AfterLoad] {
            let mut func = build_with_acquire(acq, at);
            let before = format!("{func:?}");
            let fired = AliasVersionedLoadHoist.run(&mut func);
            assert_eq!(
                fired,
                format!("{func:?}") != before,
                "{acq:?} {at:?}: the change flag must match the function"
            );
            if fired {
                hoisted.push((acq, at));
            }
        }
    }
    assert!(
        hoisted.is_empty(),
        "hoisted a load out of a loop that contains a load-acquire: {hoisted:?}"
    );
}

/// POSITIVE CONTROL: an acquire before the loop is ahead of the fast
/// preheader too, so the loop still version-hoists.
#[test]
fn hoists_when_the_acquire_precedes_the_loop() {
    for acq in ACQUIRE_LOADS {
        let mut func = build_with_acquire(acq, AcquireAt::Preheader);
        let before = nblocks(&func);
        assert!(
            AliasVersionedLoadHoist.run(&mut func),
            "{acq:?}: an acquire in the preheader does not block the hoist"
        );
        assert!(nblocks(&func) > before);
    }
}

// ---------------------------------------------------------------------------
// The store must index exactly the counted value `[0, bound)` describes.
// ---------------------------------------------------------------------------

/// An array base high enough that the cases below can place `p` far below it.
const A_HIGH: u64 = 1 << 40;

/// The names of the `cases` the version check sends to the fast clone.
fn shapes_routed_fast(cases: &[(&'static str, StoreFirst, [u64; 4])]) -> Vec<&'static str> {
    cases
        .iter()
        .filter(|&&(_, shape, args)| route_shape_after_pass(shape, args) != Route::Slow)
        .map(|case| case.0)
        .collect()
}

/// A 32-bit index is stepped and compared in 32-bit arithmetic, and the store
/// reads only its low word (`sxtw`/`uxtw`), while the register-bound guard
/// sizes `[a, a + 8n)` in 64-bit arithmetic. The index can leave that range
/// with every guard passing:
///  * `sxtw` under an unsigned `b.hs` bound above 2^31: index 0x8000_0000 is
///    stored at `a + sxtw(0x8000_0000) * 8 = a - 2^34`, below `a`;
///  * `uxtw` under a signed `b.ge` bound with a step of 3: `idx + 3` passes
///    `i32::MAX` and wraps negative, which `b.ge` reads as below `n`, so index
///    0x8000_0001 is stored at `a + 2^34 + 8`, past `a + 8n`.
///
/// The guard's `cmp (8n >> 3), n` also compares an X register with the W
/// register a Gpr32 `n` gets, which the encoder refuses; the JIT test
/// `aarch64_alias_hoist_store_index` reproduces that at O2/O3.
#[test]
fn a_32_bit_index_with_a_register_bound_is_not_versioned() {
    let sxtw = StoreFirst {
        exit_cc: CC_HS,
        step: 1,
        bound: ExitBound::Reg,
        index: StoreIndex::Sxtw32,
        step_before_store: false,
    };
    let uxtw = StoreFirst {
        exit_cc: CC_GE,
        step: 3,
        index: StoreIndex::Uxtw32,
        ..sxtw
    };
    let cases = [
        (
            "sxtw b.hs n=2^31+1 p=a-2^34",
            sxtw,
            [A_HIGH, A_HIGH - (1 << 34), OUT, (1 << 31) + 1],
        ),
        (
            "uxtw b.ge step=3 n=i32::MAX p=a+2^34+8",
            uxtw,
            [A_HIGH, A_HIGH + (1 << 34) + 8, OUT, i32::MAX as u64],
        ),
    ];
    assert_eq!(shapes_routed_fast(&cases), Vec::<&str>::new());
    for shape in [
        sxtw,
        uxtw,
        StoreFirst {
            exit_cc: CC_EQ,
            step: 1,
            ..sxtw
        },
    ] {
        let mut func = build_store_first_with(shape);
        assert!(!AliasVersionedLoadHoist.run(&mut func), "{shape:?}");
    }
}

/// A constant bound keeps a 32-bit index far from either wrap: `k * 8 <=
/// 0xFFFF` and an `add #imm12` step keep every index and step below 2^14, where
/// `sxtw` and `uxtw` read the index unchanged. These loops are still versioned,
/// whether the constant is a compare immediate or a `movz` into a register,
/// and still take the clone when `p` lies past `a + 8k`.
#[test]
fn a_32_bit_index_with_a_constant_bound_keeps_the_fast_path() {
    for index in [StoreIndex::Sxtw32, StoreIndex::Uxtw32] {
        for (exit_cc, bound) in [CC_EQ, CC_HS, CC_GE]
            .into_iter()
            .flat_map(|cc| [(cc, ExitBound::Imm(4)), (cc, ExitBound::Movz(4))])
        {
            let shape = StoreFirst {
                exit_cc,
                step: 1,
                bound,
                index,
                step_before_store: false,
            };
            let mut func = build_store_first_with(shape);
            assert!(AliasVersionedLoadHoist.run(&mut func), "{shape:?} fires");
            let hdr = BlockId(1);
            assert_eq!(route(&func, hdr, [A, A + 32, OUT, 0]), Route::Fast);
            assert_eq!(route(&func, hdr, [A, A + 24, OUT, 0]), Route::Slow);
        }
    }
}

/// With `i = i + 1` ahead of the store, iteration t stores element `t + 1`, so
/// a `b.hs`/`b.eq` loop against `n` writes `a[1..=n]`: the load at `a + 8n`
/// (the last element written) lies outside `[a, a + 8n)`, the range sized
/// from the value `i` enters each iteration with.
#[test]
fn a_store_after_the_index_update_is_not_versioned() {
    let hs = StoreFirst {
        exit_cc: CC_HS,
        step: 1,
        bound: ExitBound::Reg,
        index: StoreIndex::Lsl64,
        step_before_store: true,
    };
    let cases = [
        ("b.hs n=4 p=a+32", hs, [A, A + 32, OUT, 4]),
        (
            "b.eq n=4 p=a+32",
            StoreFirst {
                exit_cc: CC_EQ,
                ..hs
            },
            [A, A + 32, OUT, 4],
        ),
        (
            "b.hs #4 p=a+32",
            StoreFirst {
                bound: ExitBound::Imm(4),
                ..hs
            },
            [A, A + 32, OUT, 4],
        ),
    ];
    assert_eq!(shapes_routed_fast(&cases), Vec::<&str>::new());
}

// ---------------------------------------------------------------------------
// The init, step and bound are each the ONE definition reaching their use.
// ---------------------------------------------------------------------------

/// The value [`build_two_defs`]'s do-while writes twice.
#[derive(Clone, Copy, Debug)]
enum TwoDefs {
    /// `n = flag ? 100 : 4`: a copy into `n` in each arm of a diamond ahead of
    /// the loop, the 4 laid out last.
    PhiBound,
    /// `n` carried around the loop: 100 from the preheader, 1 from a latch
    /// laid out after the header; stride 50.
    CarriedBound,
    /// `i = flag ? 5 : 0` through a diamond, copied into `i` in the preheader,
    /// the 0 laid out last; `n = movz #4`.
    PhiInit,
    /// `step = i + 1` in the header (laid out last), and `step += 4095` in a
    /// latch laid out ahead of it, whose value `i = step` copies; `n` is x3.
    StepRewrittenBeforeTheCopy,
    /// `step = i + 1; i = step` in the header (laid out last), then
    /// `step -= 1` in the exit block laid out ahead of it, whose value the
    /// exit compare reads; `n` is x3.
    StepRewrittenBeforeTheCompare,
}

/// The store-first do-while of [`build_store_first_with`] (`a` x0, `p` x1,
/// `out` x2, `flag` or `n` x3, `b.hs` exit) with one value written twice, as
/// [`TwoDefs`] describes. Returns the function and its loop header.
fn build_two_defs(shape: TwoDefs, index: StoreIndex) -> (MachFunction, BlockId) {
    use trust_cg_ir::regs::{X0, X1, X2, X3};
    let (iv, packed) = match index {
        StoreIndex::Lsl64 => (g64 as fn(u32) -> MachOperand, PACKED_LSL_SCALED),
        StoreIndex::Sxtw32 => (g32 as fn(u32) -> MachOperand, PACKED_SXTW_SCALED),
        StoreIndex::Uxtw32 => (g32 as fn(u32) -> MachOperand, PACKED_UXTW_SCALED),
    };
    let preg = MachOperand::PReg;
    let jump = |func: &mut MachFunction, from: BlockId, to: BlockId| {
        push(func, from, AArch64Opcode::B, vec![blk(to)]);
        func.add_edge(from, to);
    };
    let mut func = MachFunction::new("k".to_string(), Signature::new(vec![], vec![]));
    let entry = func.entry;
    push(
        &mut func,
        entry,
        AArch64Opcode::Copy,
        vec![g64(1), preg(X0)],
    ); // a
    push(
        &mut func,
        entry,
        AArch64Opcode::Copy,
        vec![g64(0), preg(X1)],
    ); // p
    push(
        &mut func,
        entry,
        AArch64Opcode::Copy,
        vec![g64(3), preg(X2)],
    ); // out
    push(&mut func, entry, AArch64Opcode::Movz, vec![g64(30), i(7)]); // 7

    // `v9 = flag != 0 ? k_a : k_b` through a diamond; returns its join.
    let diamond = |func: &mut MachFunction, k_a: i64, k_b: i64| {
        let (arm_a, arm_b, join) = (
            func.create_block(),
            func.create_block(),
            func.create_block(),
        );
        push(func, entry, AArch64Opcode::Copy, vec![g64(40), preg(X3)]); // flag
        push(func, entry, AArch64Opcode::CmpRI, vec![g64(40), i(0)]);
        push(
            func,
            entry,
            AArch64Opcode::BCond,
            vec![i(CC_EQ), blk(arm_b)],
        );
        func.add_edge(entry, arm_b);
        jump(func, entry, arm_a);
        for (arm, k, tmp) in [(arm_a, k_a, 7), (arm_b, k_b, 12)] {
            push(func, arm, AArch64Opcode::Movz, vec![iv(tmp), i(k)]);
            push(func, arm, AArch64Opcode::MovR, vec![iv(9), iv(tmp)]);
            jump(func, arm, join);
        }
        join
    };
    // The preheader, the bound register and the stride.
    let (ph, bound, stride) = match shape {
        TwoDefs::PhiBound => {
            let ph = diamond(&mut func, 100, 4);
            push(&mut func, ph, AArch64Opcode::Movz, vec![iv(10), i(0)]);
            (ph, 9, 1)
        }
        TwoDefs::PhiInit => {
            let ph = diamond(&mut func, 5, 0);
            push(&mut func, ph, AArch64Opcode::MovR, vec![iv(10), iv(9)]);
            push(&mut func, ph, AArch64Opcode::Movz, vec![iv(2), i(4)]);
            (ph, 2, 1)
        }
        TwoDefs::CarriedBound => {
            push(&mut func, entry, AArch64Opcode::Movz, vec![iv(10), i(0)]);
            push(&mut func, entry, AArch64Opcode::Movz, vec![iv(7), i(100)]);
            push(&mut func, entry, AArch64Opcode::MovR, vec![iv(9), iv(7)]);
            (entry, 9, 50)
        }
        TwoDefs::StepRewrittenBeforeTheCopy | TwoDefs::StepRewrittenBeforeTheCompare => {
            push(&mut func, entry, AArch64Opcode::Copy, vec![iv(2), preg(X3)]); // n
            push(&mut func, entry, AArch64Opcode::Movz, vec![iv(10), i(0)]);
            (entry, 2, 1)
        }
    };
    let early = matches!(
        shape,
        TwoDefs::StepRewrittenBeforeTheCopy | TwoDefs::StepRewrittenBeforeTheCompare
    )
    .then(|| func.create_block());
    let hdr = func.create_block();
    let late = matches!(shape, TwoDefs::CarriedBound).then(|| func.create_block());
    let exit = func.create_block();
    jump(&mut func, ph, hdr);

    // hdr: a[i] = 7; *out = *p; step = i + stride
    push(
        &mut func,
        hdr,
        AArch64Opcode::StrRO,
        vec![g64(30), g64(1), iv(10), i(packed)],
    );
    push(
        &mut func,
        hdr,
        AArch64Opcode::LdrRI,
        vec![g64(20), g64(0), i(0)],
    );
    push(
        &mut func,
        hdr,
        AArch64Opcode::StrRI,
        vec![g64(20), g64(3), i(0)],
    );
    push(
        &mut func,
        hdr,
        AArch64Opcode::AddRI,
        vec![iv(11), iv(10), i(stride)],
    );
    // `cmp step, n ; b.hs exit` at the end of `b`.
    let exit_test = |func: &mut MachFunction, b: BlockId| {
        push(func, b, AArch64Opcode::CmpRR, vec![iv(11), iv(bound)]);
        push(func, b, AArch64Opcode::BCond, vec![i(CC_HS), blk(exit)]);
        func.add_edge(b, exit);
    };
    match shape {
        TwoDefs::PhiBound | TwoDefs::PhiInit => {
            push(&mut func, hdr, AArch64Opcode::MovR, vec![iv(10), iv(11)]);
            exit_test(&mut func, hdr);
            jump(&mut func, hdr, hdr);
        }
        TwoDefs::CarriedBound => {
            let latch = late.expect("latch");
            push(&mut func, hdr, AArch64Opcode::MovR, vec![iv(10), iv(11)]);
            exit_test(&mut func, hdr);
            jump(&mut func, hdr, latch);
            push(&mut func, latch, AArch64Opcode::Movz, vec![iv(8), i(1)]);
            push(&mut func, latch, AArch64Opcode::MovR, vec![iv(9), iv(8)]);
            jump(&mut func, latch, hdr);
        }
        TwoDefs::StepRewrittenBeforeTheCopy => {
            let latch = early.expect("latch");
            exit_test(&mut func, hdr);
            jump(&mut func, hdr, latch);
            push(
                &mut func,
                latch,
                AArch64Opcode::AddRI,
                vec![iv(11), iv(11), i(4095)],
            );
            push(&mut func, latch, AArch64Opcode::MovR, vec![iv(10), iv(11)]);
            jump(&mut func, latch, hdr);
        }
        TwoDefs::StepRewrittenBeforeTheCompare => {
            let test = early.expect("exit block");
            push(&mut func, hdr, AArch64Opcode::MovR, vec![iv(10), iv(11)]);
            jump(&mut func, hdr, test);
            push(
                &mut func,
                test,
                AArch64Opcode::SubRI,
                vec![iv(11), iv(11), i(1)],
            );
            exit_test(&mut func, test);
            jump(&mut func, test, hdr);
        }
    }
    push(&mut func, exit, AArch64Opcode::Ret, vec![]);
    (func, hdr)
}

/// One input whose loop really stores to `p`, which the version check must
/// therefore send to the original loop.
type TwoDefsCase = (&'static str, TwoDefs, StoreIndex, [u64; 4]);

/// The names of the `cases` the version check sends to the fast clone.
fn two_defs_routed_fast(cases: &[TwoDefsCase]) -> Vec<&'static str> {
    cases
        .iter()
        .filter(|&&(_, shape, index, args)| {
            let (mut func, hdr) = build_two_defs(shape, index);
            let _ = AliasVersionedLoadHoist.run(&mut func);
            route(&func, hdr, args) != Route::Slow
        })
        .map(|case| case.0)
        .collect()
}

/// A bound two definitions reach is not one value: with `n = flag ? 100 : 4`
/// and `flag = 1` the loop stores `a[0..100]`, and with `n` carried as 100 then
/// 1 at stride 50 it stores `a[0]` and `a[50]`. Sizing the store range from
/// the def laid out last (4, or 1) leaves `p = a + 32` (a[4]) or `p = a + 400`
/// (a[50]) outside it, and the clone reads `*p` before the store.
#[test]
fn a_bound_two_definitions_reach_is_not_a_counted_bound() {
    use StoreIndex::{Lsl64, Sxtw32, Uxtw32};
    let phi = [A, A + 32, OUT, 1];
    let carried = [A, A + 400, OUT, 0];
    let cases: [TwoDefsCase; 6] = [
        ("phi n, lsl", TwoDefs::PhiBound, Lsl64, phi),
        ("phi n, sxtw", TwoDefs::PhiBound, Sxtw32, phi),
        ("phi n, uxtw", TwoDefs::PhiBound, Uxtw32, phi),
        ("carried n, lsl", TwoDefs::CarriedBound, Lsl64, carried),
        ("carried n, sxtw", TwoDefs::CarriedBound, Sxtw32, carried),
        ("carried n, uxtw", TwoDefs::CarriedBound, Uxtw32, carried),
    ];
    assert_eq!(two_defs_routed_fast(&cases), Vec::<&str>::new());
}

/// An index two initial values reach is not counted from 0: with
/// `i = flag ? 5 : 0` and `flag = 1`, iteration 0 stores `a[5]`, outside the
/// `[a, a + 32)` that `i = 0` and `n = 4` give.
#[test]
fn an_index_two_initial_values_reach_is_not_counted_from_zero() {
    use StoreIndex::{Lsl64, Sxtw32, Uxtw32};
    let args = [A, A + 40, OUT, 1];
    let cases: [TwoDefsCase; 3] = [
        ("phi i, lsl", TwoDefs::PhiInit, Lsl64, args),
        ("phi i, sxtw", TwoDefs::PhiInit, Sxtw32, args),
        ("phi i, uxtw", TwoDefs::PhiInit, Uxtw32, args),
    ];
    assert_eq!(two_defs_routed_fast(&cases), Vec::<&str>::new());
}

/// The step the index copies and the step the exit test compares must both be
/// `i + c`. With `n = 2`: copying `step + 4095` stores `a[0]` then `a[4096]`;
/// comparing `step - 1` lets `i` reach `n` and stores `a[0..=2]`. Both fall
/// outside `[a, a + 16)`.
#[test]
fn a_step_another_definition_rewrites_is_not_counted() {
    let cases: [TwoDefsCase; 2] = [
        (
            "copy reads step + 4095",
            TwoDefs::StepRewrittenBeforeTheCopy,
            StoreIndex::Lsl64,
            [A, A + 8 * 4096, OUT, 2],
        ),
        (
            "compare reads step - 1",
            TwoDefs::StepRewrittenBeforeTheCompare,
            StoreIndex::Lsl64,
            [A, A + 16, OUT, 2],
        ),
    ];
    assert_eq!(two_defs_routed_fast(&cases), Vec::<&str>::new());
}

/// How the two-block fixture's header reaches its body block.
#[derive(Clone, Copy)]
enum HeaderExit {
    /// `B body`: the edge is the operand.
    Branch,
    /// `Adr t, JumpTableIndex(0); Br t` with `jump_tables[0] = [body]`.
    JumpTable,
    /// No branch: the recorded edge is a fall-through no operand names.
    FallThrough,
}

/// The canonical counted loop split over two blocks:
///  * `hdr`: the invariant load, then `exit` into `body`;
///  * `body`: the indexed store, the step and `cmp; b.eq exit; b hdr`.
fn build_two_block(exit_form: HeaderExit) -> MachFunction {
    let mut func = MachFunction::new("k2".to_string(), Signature::new(vec![], vec![]));
    let ph = func.entry;
    let hdr = func.create_block();
    let body = func.create_block();
    let exit = func.create_block();

    push(&mut func, ph, AArch64Opcode::Movz, vec![g64(0), i(4096)]);
    push(&mut func, ph, AArch64Opcode::Movz, vec![g64(1), i(65536)]);
    push(&mut func, ph, AArch64Opcode::Movz, vec![g64(2), i(4)]);
    push(&mut func, ph, AArch64Opcode::Movz, vec![g64(10), i(0)]);
    push(&mut func, ph, AArch64Opcode::B, vec![blk(hdr)]);
    func.add_edge(ph, hdr);

    push(
        &mut func,
        hdr,
        AArch64Opcode::LdrRI,
        vec![g64(20), g64(0), i(0)],
    );
    match exit_form {
        HeaderExit::Branch => push(&mut func, hdr, AArch64Opcode::B, vec![blk(body)]),
        HeaderExit::JumpTable => {
            func.jump_tables.push(trust_cg_ir::function::JumpTableData {
                min_val: 0,
                targets: vec![body],
            });
            push(
                &mut func,
                hdr,
                AArch64Opcode::Adr,
                vec![g64(30), MachOperand::JumpTableIndex(0)],
            );
            push(&mut func, hdr, AArch64Opcode::Br, vec![g64(30)]);
        }
        HeaderExit::FallThrough => {}
    }
    func.add_edge(hdr, body);

    push(
        &mut func,
        body,
        AArch64Opcode::StrRO,
        vec![g64(20), g64(1), g64(10), i(PACKED_LSL_SCALED)],
    );
    push(
        &mut func,
        body,
        AArch64Opcode::AddRI,
        vec![g64(11), g64(10), i(1)],
    );
    push(&mut func, body, AArch64Opcode::MovR, vec![g64(10), g64(11)]);
    push(&mut func, body, AArch64Opcode::CmpRR, vec![g64(11), g64(2)]);
    push(&mut func, body, AArch64Opcode::BCond, vec![i(0), blk(exit)]);
    push(&mut func, body, AArch64Opcode::B, vec![blk(hdr)]);
    func.add_edge(body, exit);
    func.add_edge(body, hdr);

    push(&mut func, exit, AArch64Opcode::Ret, vec![]);
    func
}

/// Control: with every edge named by a `Block` operand the two-block loop is
/// versioned.
#[test]
fn fires_on_the_two_block_loop_whose_edges_are_operands() {
    let mut func = build_two_block(HeaderExit::Branch);
    let before = nblocks(&func);
    assert!(AliasVersionedLoadHoist.run(&mut func));
    assert!(nblocks(&func) > before);
}

/// The fast clone rewrites `Block` operands only. A cloned `Adr t,
/// JumpTableIndex(0)` would keep indexing the shared table, whose entry is the
/// ORIGINAL body block, so the fast loop would run its iterations in the slow
/// loop's blocks. Decline, leaving the function untouched.
#[test]
fn refuses_a_body_that_dispatches_through_a_jump_table() {
    let mut func = build_two_block(HeaderExit::JumpTable);
    let before = format!("{func:?}");
    assert!(!AliasVersionedLoadHoist.run(&mut func));
    assert_eq!(format!("{func:?}"), before);
}

/// A recorded edge no operand names (a fall-through) follows the layout, and
/// the clone is laid out elsewhere. Decline.
#[test]
fn refuses_a_body_edge_no_operand_names() {
    let mut func = build_two_block(HeaderExit::FallThrough);
    let before = format!("{func:?}");
    assert!(!AliasVersionedLoadHoist.run(&mut func));
    assert_eq!(format!("{func:?}"), before);
}
