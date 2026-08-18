// crates/rustc-codegen-trust-cg/src/trust_ir_interp.rs
//
// Item 6 (proof-gap program) — LOOP-CARRIED block-arg threading VC, wired LIVE.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0
//
// WHY AN INTERPRETER (the anti-tautology requirement)
// ---------------------------------------------------
// `trust_cg_verify::mir_semantics::check_loop_carried_threading` validates that
// the values a bridge threads across a loop header's two in-edges (preheader
// entry + latch back-edge) equal the SOURCE-MIR dataflow. The naive wiring —
// building BOTH sides of the VC from the bridge's own decision map (the
// `ScalarizedState` out-values `patch_loop_header_edge` reads) — is a TAUTOLOGY:
// `var(x) == var(x)` refines no matter how wrong the threading is.
//
// This module breaks the tautology with an INDEPENDENT derivation of the bridge
// side: a minimal SCALAR SYMBOLIC INTERPRETER over the trust-ir instructions the
// bridge ACTUALLY EMITTED. The bridge side of every obligation is produced by
// folding the emitted header+body chain's `Inst`s into `ValueId -> SmtExpr`
// (seeded ONLY with the header-param ValueIds as free vars) and resolving the
// `Inst::Br` back-edge arguments the patch pass attached. The MIR side is the
// verifier's `MirLoop` model built from the SOURCE MIR statements. The two
// derivations meet only on the shared header-param/arg var names, so a bridge
// that threads a STALE, SWAPPED, or WRONG value (the #71 / euclid class) yields
// a bridge-side expression that genuinely differs from the MIR spec -> Refuted.
//
// SMT SEMANTICS MIRRORING (the anti-false-refute requirement)
// -----------------------------------------------------------
// Each interpreted `Inst` is encoded EXACTLY as the verifier's own encoders
// define the trust-ir op (`trust_cg_verify::trust_ir_semantics` + the
// `BridgeLowering` models in `mir_semantics`):
//   * BinOp Add/Sub/Mul        -> bvadd / bvsub / bvmul
//   * BinOp UDiv               -> bvudiv
//   * BinOp URem               -> a - bvudiv(a, b) * b   (the encoder's form)
//   * BinOp And/Or/Xor         -> bvand / bvor / bvxor
//   * BinOp Shl/LShr/AShr      -> MASKED shift (amount & (width-1)), matching
//     `BridgeLowering::MaskedShift` — the audited P3c model of the bridge's raw
//     trust-ir shift (Rust/x86/AArch64 modulo-width count semantics).
//   * BinOp SDiv/SRem          -> OUT OF SLICE (skip). Deliberate, mirroring
//     `refine_binop_opcode`: the MIR spec models the signed INT_MIN/-1 overflow
//     trap as a sentinel value, and `MirLoop` has no per-statement precondition
//     channel to exclude that input, so a raw bvsdiv/bvsrem interpretation
//     would FALSE-REFUTE correct code. Loops whose latch contains a SIGNED
//     Div/Rem are skipped (sound: less coverage, never a wrong verdict).
//   * UnOp Neg/Not             -> bvneg / xor-all-ones
//   * ICmp (all 10)            -> 1-bit ite(cmp, 1, 0) (CSET shape)
//   * Cast SExt/ZExt/Trunc     -> sign_ext / zero_ext / extract
//   * Const Int/Bool, Copy     -> bv_const / identity
// ANY other instruction (Load/Store/Call/float/Alloca/GEP/...) bails the whole
// loop out of the slice — the loop is SKIPPED, never guessed at.
//
// WHAT IS COVERED vs SKIPPED (the honest slice)
// ---------------------------------------------
// COVERED: single-latch natural loops over integer/bool scalar header params
// whose MIR body is a straight-line Goto/Assert chain of scalar statements
// (Use/BinaryOp/UnaryOp/IntToInt-Cast over plain locals + int consts), with a
// loop condition that is either reconstructible as `param != 0` (`while b != 0`
// — directly or via a Ne/Eq-zero temp) or absent (unconditional back-edge with
// no Div/Rem in the body), and whose preheader entry values resolve to integer
// constants or never-reassigned function arguments (preheader = START_BLOCK).
// SKIPPED (silently, soundly): everything else — multi-latch/conditional
// back-edges, bodies with calls/branches/memory ops, float or 128-bit carried
// state, signed Div/Rem bodies, non-reconstructible guards over trapping
// bodies, memory-backed/celled loop state (which has no header phi at all).
//
// GATING: solver-lane ONLY (`TCG_P3C_REFINE` / legacy `TCG_REFINE`); loop ints
// are wider than the fast lane's exhaustive 8-bit subset. FAIL-CLOSED on
// Refuted/Inconclusive, exactly like the P3c rvalue tail.

use std::collections::{HashMap, HashSet};

use rustc_index::Idx;
use rustc_middle::mir::{
    self, Body, Local, Operand, Place, Rvalue, Statement, StatementKind, TerminatorKind,
};
use rustc_middle::ty;

use trust_cg_lower::types::Type as LowerType;
use trust_cg_verify::mir_semantics as refine;
use trust_cg_verify::SmtExpr;
use trust_ir::{
    BinOp as TrustIrBinOp, Block, BlockId, CastOp, Constant, Function as TrustIrFunction,
    ICmpOp, Inst, InstrNode, Ty as TrustIrTy, UnOp as TrustIrUnOp, ValueId,
};

use crate::{MirLoweringCtx, ScalarBlockParam};

// ===========================================================================
// 1. The scalar symbolic interpreter over EMITTED trust-ir instructions
//    (pure trust-ir + SmtExpr; no rustc types — unit-testable in isolation)
// ===========================================================================

/// Bit width of a scalar integer/bool trust-ir type. `None` for anything the
/// interpreter does not model (pointers, floats, 128-bit, composites).
fn int_width(ty: &TrustIrTy) -> Option<u32> {
    Some(match ty {
        TrustIrTy::I8 | TrustIrTy::U8 => 8,
        TrustIrTy::I16 | TrustIrTy::U16 => 16,
        TrustIrTy::I32 | TrustIrTy::U32 => 32,
        TrustIrTy::I64 | TrustIrTy::U64 => 64,
        TrustIrTy::Bool => 1,
        _ => return None,
    })
}

/// Low-`width`-bits mask as a u64 (width <= 64).
fn low_mask(width: u32) -> u64 {
    if width >= 64 {
        u64::MAX
    } else {
        (1u64 << width) - 1
    }
}

/// Encode an emitted `Inst::Const` payload. Integer constants are masked to the
/// type width (negative `i128` payloads keep their two's-complement low bits).
fn const_expr(ty: &TrustIrTy, value: &Constant) -> Option<SmtExpr> {
    let w = int_width(ty)?;
    match value {
        Constant::Int(v) => Some(SmtExpr::bv_const((*v as u64) & low_mask(w), w)),
        Constant::Bool(b) => Some(SmtExpr::bv_const(u64::from(*b), 1)),
        _ => None,
    }
}

/// Mask a shift amount to `width-1` bits at the operand width — the EXACT form
/// `mir_semantics::mask_shift_amount` / `BridgeLowering::MaskedShift` use, so
/// the two sides of a shift VC are structurally comparable.
fn mask_shift_amount(amount: SmtExpr, width: u32) -> SmtExpr {
    let m = SmtExpr::bv_const(u64::from(width) - 1, width);
    amount.bvand(m)
}

/// Resolve an operand `ValueId` through the environment. `None` = the value was
/// produced by something outside the interpreted slice (bail).
fn env_get(env: &HashMap<ValueId, SmtExpr>, v: &ValueId) -> Option<SmtExpr> {
    env.get(v).cloned()
}

/// Fold ONE emitted instruction into the environment. Returns `None` for any
/// instruction outside the scalar slice (the caller must skip the whole loop —
/// never guess). Mirrors the verifier's SMT semantics op-for-op (module doc).
pub(crate) fn interp_inst(env: &mut HashMap<ValueId, SmtExpr>, node: &InstrNode) -> Option<()> {
    let expr = match &node.inst {
        Inst::Const { ty, value } => const_expr(ty, value)?,
        Inst::Copy { ty: _, operand } => env_get(env, operand)?,
        Inst::BinOp { op, ty, lhs, rhs } => {
            let w = int_width(ty)?;
            let l = env_get(env, lhs)?;
            let r = env_get(env, rhs)?;
            if l.try_bv_width().ok() != Some(w) || r.try_bv_width().ok() != Some(w) {
                return None;
            }
            match op {
                TrustIrBinOp::Add => l.bvadd(r),
                TrustIrBinOp::Sub => l.bvsub(r),
                TrustIrBinOp::Mul => l.bvmul(r),
                TrustIrBinOp::UDiv => l.bvudiv(r),
                // The encoder's Urem form: a - (a udiv b) * b.
                TrustIrBinOp::URem => {
                    let q = l.clone().bvudiv(r.clone());
                    l.bvsub(q.bvmul(r))
                }
                TrustIrBinOp::And => l.bvand(r),
                TrustIrBinOp::Or => l.bvor(r),
                TrustIrBinOp::Xor => l.bvxor(r),
                // Masked shifts (BridgeLowering::MaskedShift — see module doc).
                TrustIrBinOp::Shl => l.bvshl(mask_shift_amount(r, w)),
                TrustIrBinOp::LShr => l.bvlshr(mask_shift_amount(r, w)),
                TrustIrBinOp::AShr => l.bvashr(mask_shift_amount(r, w)),
                // Signed Div/Rem: out of slice (INT_MIN/-1 trap sentinel — see
                // module doc / refine_binop_opcode). Floats: out of slice.
                TrustIrBinOp::SDiv
                | TrustIrBinOp::SRem
                | TrustIrBinOp::FAdd
                | TrustIrBinOp::FSub
                | TrustIrBinOp::FMul
                | TrustIrBinOp::FDiv
                | TrustIrBinOp::FRem
                | TrustIrBinOp::FMin
                | TrustIrBinOp::FMax => return None,
                // BOOLEAN connectives (trust-ir 4b06918): UNREACHABLE from this
                // bridge, not merely unsupported. Rust MIR has no boolean-connective
                // BinOp — `&&`/`||` lower to control flow — and this bridge's sole
                // producer, `rust_binop_to_trust_ir_binop`, maps mir BitAnd/BitOr/
                // BitXor to the BITWISE `And`/`Or`/`Xor` above. Nothing here ever
                // constructs BAnd/BOr/BXor. Skipping is the sound answer: these
                // carry 0/1-carrier logical semantics (any nonzero is true), which
                // is NOT bvand/bvor/bvxor, so a reflexive bitwise encoding would
                // silently disagree with `trust_ir::interpret` and the Lean
                // `semIntBinOp`. If the bridge ever learns to emit them, encode the
                // carrier explicitly here — do not fold them into the arms above.
                TrustIrBinOp::BAnd | TrustIrBinOp::BOr | TrustIrBinOp::BXor => {
                    return None;
                }
            }
        }
        Inst::UnOp { op, ty, operand } => {
            let w = int_width(ty)?;
            let o = env_get(env, operand)?;
            if o.try_bv_width().ok() != Some(w) {
                return None;
            }
            match op {
                TrustIrUnOp::Neg => o.bvneg(),
                // encode_trust_ir_bnot: xor with all-ones.
                TrustIrUnOp::Not => o.bvxor(SmtExpr::bv_const(low_mask(w), w)),
                // trust-ir's float-rounding unops (FFloor/FCeil/FTrunc) have no
                // bit-vector SMT encoding here; like the other float unops, fail
                // closed (return None) rather than mis-encode.
                TrustIrUnOp::FNeg
                | TrustIrUnOp::FAbs
                | TrustIrUnOp::FSqrt
                | TrustIrUnOp::FFloor
                | TrustIrUnOp::FCeil
                | TrustIrUnOp::FTrunc
                | TrustIrUnOp::CtPop => return None,
            }
        }
        Inst::ICmp { op, ty, lhs, rhs } => {
            let w = int_width(ty)?;
            let l = env_get(env, lhs)?;
            let r = env_get(env, rhs)?;
            if l.try_bv_width().ok() != Some(w) || r.try_bv_width().ok() != Some(w) {
                return None;
            }
            let cmp = match op {
                ICmpOp::Eq => l.eq_expr(r),
                ICmpOp::Ne => l.eq_expr(r).not_expr(),
                ICmpOp::Ult => l.bvult(r),
                ICmpOp::Ule => l.bvule(r),
                ICmpOp::Ugt => l.bvugt(r),
                ICmpOp::Uge => l.bvuge(r),
                ICmpOp::Slt => l.bvslt(r),
                ICmpOp::Sle => l.bvsle(r),
                ICmpOp::Sgt => l.bvsgt(r),
                ICmpOp::Sge => l.bvsge(r),
            };
            // 1-bit CSET shape, matching encode_trust_ir_icmp.
            SmtExpr::ite(cmp, SmtExpr::bv_const(1, 1), SmtExpr::bv_const(0, 1))
        }
        Inst::Cast { op, src_ty, dst_ty, operand } => {
            let sw = int_width(src_ty)?;
            let dw = int_width(dst_ty)?;
            let o = env_get(env, operand)?;
            if o.try_bv_width().ok() != Some(sw) {
                return None;
            }
            match op {
                CastOp::SExt if dw > sw => o.sign_ext(dw - sw),
                CastOp::ZExt if dw > sw => o.zero_ext(dw - sw),
                CastOp::Trunc if dw < sw => o.extract(dw - 1, 0),
                // Same-width extend/truncate degenerates to the identity.
                CastOp::SExt | CastOp::ZExt | CastOp::Trunc if dw == sw => o,
                _ => return None,
            }
        }
        // EVERYTHING else — Load/Store/Call/Alloca/GEP/float/atomics/aggregates/
        // Select/Overflow/terminators/... — is out of the scalar slice: bail.
        _ => return None,
    };
    let [result] = node.results.as_slice() else {
        return None;
    };
    env.insert(*result, expr);
    Some(())
}

/// The argument lists an emitted terminator threads on each of its edges to
/// `target` (a terminator can reach the same target on several arms).
fn edges_to<'a>(inst: &'a Inst, target: BlockId) -> Vec<&'a Vec<ValueId>> {
    match inst {
        Inst::Br { target: t, args } if *t == target => vec![args],
        Inst::CondBr { cond: _, then_target, then_args, else_target, else_args } => {
            let mut out = Vec::new();
            if *then_target == target {
                out.push(then_args);
            }
            if *else_target == target {
                out.push(else_args);
            }
            out
        }
        Inst::Switch { value: _, default, default_args, cases, .. } => {
            let mut out = Vec::new();
            if *default == target {
                out.push(default_args);
            }
            for case in cases {
                if case.target == target {
                    out.push(&case.args);
                }
            }
            out
        }
        _ => Vec::new(),
    }
}

/// Interpret an emitted header+body chain and resolve the LATCH back-edge args.
///
/// `blocks[0]` is the emitted loop-HEADER block (its params were seeded into
/// `env` by the caller as free header-param vars); the rest is the emitted body
/// chain, in order; the LAST block's terminator must thread the back-edge to
/// `header_id` on exactly one arm. Every instruction of every block is folded
/// through [`interp_inst`]; each intermediate edge must carry NO args (a chain
/// block with params is out of slice). Returns the back-edge args resolved to
/// `SmtExpr`s over the seeded vars, or `None` (out of slice — skip the loop).
pub(crate) fn interpret_chain_to_back_edge(
    blocks: &[&Block],
    header_id: BlockId,
    mut env: HashMap<ValueId, SmtExpr>,
) -> Option<Vec<SmtExpr>> {
    for (i, block) in blocks.iter().enumerate() {
        // Only the header (i == 0) may carry block params (the seeded ones); a
        // chain block with params means branch-varying state we do not model.
        if i > 0 && !block.params.is_empty() {
            return None;
        }
        let (terminator, insts) = block.body.split_last()?;
        for node in insts {
            interp_inst(&mut env, node)?;
        }
        if i + 1 == blocks.len() {
            // The latch: exactly ONE arm to the header; its args are the
            // bridge's back-edge threading, resolved through the interpreted env.
            let edges = edges_to(&terminator.inst, header_id);
            let [args] = edges.as_slice() else {
                return None;
            };
            let mut resolved = Vec::with_capacity(args.len());
            for v in args.iter() {
                resolved.push(env_get(&env, v)?);
            }
            return Some(resolved);
        }
        // Intermediate edge to the next chain block: must exist and carry no args.
        let next = blocks[i + 1].id;
        let edges = edges_to(&terminator.inst, next);
        if edges.is_empty() || edges.iter().any(|args| !args.is_empty()) {
            return None;
        }
        // AUDIT FIX (rogue mid-chain back-edge): an INTERMEDIATE block may not
        // have ANY arm targeting the header — such an arm threads back-edge args
        // this fold never inspects (e.g. the header params themselves, a stale
        // identity re-entry that passes the structural P1.3 gate), so the loop
        // would be reported Refined while a real back-edge goes unchecked. The
        // caller additionally enforces the whole-function header-predecessor
        // check; this is local defense for direct users of this fold.
        if !edges_to(&terminator.inst, header_id).is_empty() {
            return None;
        }
    }
    None
}

/// Single-result definition map over a whole emitted function (SSA: each
/// `ValueId` has at most one defining instruction).
fn build_def_map(func: &TrustIrFunction) -> HashMap<ValueId, &Inst> {
    let mut defs = HashMap::new();
    for block in &func.blocks {
        for node in &block.body {
            if let [result] = node.results.as_slice() {
                defs.insert(*result, &node.inst);
            }
        }
    }
    defs
}

/// Resolve an emitted `ValueId` to an `SmtExpr` through Const/Copy definitions,
/// bottoming out at `base` (the caller's faithful naming of UNDEFINED values —
/// in production, the entry-block function-argument params). `None` = out of
/// slice.
fn resolve_value_through_defs(
    defs: &HashMap<ValueId, &Inst>,
    v: ValueId,
    base: &dyn Fn(ValueId) -> Option<SmtExpr>,
    depth: u32,
) -> Option<SmtExpr> {
    if depth > 64 {
        return None;
    }
    match defs.get(&v) {
        Some(Inst::Const { ty, value }) => const_expr(ty, value),
        Some(Inst::Copy { ty: _, operand }) => {
            resolve_value_through_defs(defs, *operand, base, depth + 1)
        }
        // Defined by anything else (arithmetic, load, call, ...): out of the
        // entry-edge resolution slice. (The MIR side only resolves consts and
        // untouched function args, so anything richer must skip anyway.)
        Some(_) => None,
        None => base(v),
    }
}

/// Resolve the args an emitted block threads on its (single-arm) edge to
/// `to`, through Const/Copy defs down to `base`. Used for the PREHEADER entry
/// edge. `None` = no/ambiguous edge or unresolvable arg (skip).
pub(crate) fn resolve_edge_args_through_defs(
    func: &TrustIrFunction,
    from: BlockId,
    to: BlockId,
    base: &dyn Fn(ValueId) -> Option<SmtExpr>,
) -> Option<Vec<SmtExpr>> {
    let block = func.blocks.iter().find(|b| b.id == from)?;
    let terminator = block.body.last()?;
    let edges = edges_to(&terminator.inst, to);
    let [args] = edges.as_slice() else {
        return None;
    };
    let defs = build_def_map(func);
    args.iter()
        .map(|v| resolve_value_through_defs(&defs, *v, base, 0))
        .collect()
}

// ===========================================================================
// 2. MIR side: build the verifier's MirLoop from the SOURCE MIR
// ===========================================================================

/// Canonical MIR-side var name for a local: `p<index>`. Shared by the latch
/// statements, the header params, and the bridge-side interpreter seeds.
fn canonical_name(local: Local) -> String {
    format!("p{}", local.index())
}

/// The verifier scalar type of a Rust type — integer/bool only (the loop slice;
/// floats, 128-bit, char, pointers are out). `isize`/`usize` use the 64-bit
/// pointer width the bridge targets (anything else is out of slice).
fn mir_scalar_ty_of_rust_ty<'tcx>(
    tcx: ty::TyCtxt<'tcx>,
    rust_ty: ty::Ty<'tcx>,
) -> Option<refine::MirScalarTy> {
    let ptr64 = tcx.data_layout.pointer_size().bits() == 64;
    Some(match rust_ty.kind() {
        ty::Bool => refine::MirScalarTy::Bool,
        ty::Int(int_ty) => refine::MirScalarTy::SInt(match int_ty {
            ty::IntTy::I8 => LowerType::I8,
            ty::IntTy::I16 => LowerType::I16,
            ty::IntTy::I32 => LowerType::I32,
            ty::IntTy::I64 => LowerType::I64,
            ty::IntTy::Isize if ptr64 => LowerType::I64,
            _ => return None,
        }),
        ty::Uint(uint_ty) => refine::MirScalarTy::UInt(match uint_ty {
            ty::UintTy::U8 => LowerType::I8,
            ty::UintTy::U16 => LowerType::I16,
            ty::UintTy::U32 => LowerType::I32,
            ty::UintTy::U64 => LowerType::I64,
            ty::UintTy::Usize if ptr64 => LowerType::I64,
            _ => return None,
        }),
        _ => return None,
    })
}

fn mir_scalar_ty_of_local<'tcx>(
    ctx: &MirLoweringCtx<'tcx>,
    body: &Body<'tcx>,
    local: Local,
) -> Option<refine::MirScalarTy> {
    mir_scalar_ty_of_rust_ty(ctx.tcx, crate::local_rust_ty(ctx, body, local))
}

/// The base local of an unprojected place.
fn plain_local(place: &Place<'_>) -> Option<Local> {
    place.projection.is_empty().then_some(place.local)
}

fn operand_plain_local(operand: &Operand<'_>) -> Option<Local> {
    match operand {
        Operand::Copy(place) | Operand::Move(place) => plain_local(place),
        _ => None,
    }
}

/// Evaluate a constant operand to its integer scalar value (None = not an
/// integer constant).
fn const_int_value<'tcx>(ctx: &MirLoweringCtx<'tcx>, operand: &Operand<'tcx>) -> Option<i128> {
    let Operand::Constant(constant) = operand else {
        return None;
    };
    let evaluated = ctx.eval_const_operand(constant);
    crate::const_to_scalar_i128(&evaluated)
}

/// Convert a MIR operand into the verifier's `MirOperand` over canonical names.
/// Reads are restricted to header params and chain-defined locals (`readable`),
/// so the latch store's FREE vars are exactly the header params.
fn conv_operand<'tcx>(
    ctx: &MirLoweringCtx<'tcx>,
    body: &Body<'tcx>,
    operand: &Operand<'tcx>,
    readable: &HashSet<Local>,
) -> Option<refine::MirOperand> {
    match operand {
        Operand::Copy(place) | Operand::Move(place) => {
            let local = plain_local(place)?;
            if !readable.contains(&local) {
                return None;
            }
            let scalar_ty = mir_scalar_ty_of_local(ctx, body, local)?;
            Some(refine::MirOperand::Var { name: canonical_name(local), ty: scalar_ty })
        }
        Operand::Constant(constant) => {
            let evaluated = ctx.eval_const_operand(constant);
            let scalar_ty = mir_scalar_ty_of_rust_ty(ctx.tcx, evaluated.ty())?;
            let value = crate::const_to_scalar_i128(&evaluated)?;
            Some(refine::MirOperand::ConstInt { value: value as u64, ty: scalar_ty })
        }
        _ => None,
    }
}

/// Map a MIR `BinOp` (arith or comparison, incl. the `*Unchecked` forms) to the
/// verifier's `MirBinOp`. Checked/overflow forms are out of slice.
fn conv_binop(op: mir::BinOp) -> Option<refine::MirBinOp> {
    crate::refine_mir_binop_for_arith(op).or_else(|| crate::refine_mir_binop_for_cmp(op))
}

/// Convert the statements of the header + chain blocks into verifier `MirStmt`s
/// over canonical names. Returns the statements plus whether any (unsigned)
/// Div/Rem appears (a trapping op that requires a reconstructed guard).
/// `None` = some statement is out of the scalar slice (skip the loop).
fn conv_statements<'tcx>(
    ctx: &MirLoweringCtx<'tcx>,
    body: &Body<'tcx>,
    chain_blocks: &[mir::BasicBlock],
    params: &HashSet<Local>,
) -> Option<(Vec<refine::MirStmt>, bool)> {
    let mut stmts = Vec::new();
    let mut has_div_rem = false;
    // Reads may name a header param (free var) or a local already defined in
    // the chain. Anything else (a loop-invariant local defined outside) is out
    // of slice: its bridge-side ValueId would be foreign to the interpreter too.
    let mut readable: HashSet<Local> = params.clone();
    for bb in chain_blocks {
        for statement in &body.basic_blocks[*bb].statements {
            let (place, rvalue) = match &statement.kind {
                StatementKind::Assign(assign) => (&assign.0, &assign.1),
                // Value-irrelevant bookkeeping.
                StatementKind::StorageLive(_)
                | StatementKind::StorageDead(_)
                | StatementKind::Nop
                | StatementKind::ConstEvalCounter
                | StatementKind::PlaceMention(_)
                | StatementKind::AscribeUserType(..)
                | StatementKind::Coverage(_)
                | StatementKind::FakeRead(_)
                | StatementKind::BackwardIncompatibleDropHint { .. } => continue,
                // SetDiscriminant / Retag / Intrinsic / ... : out of slice.
                _ => return None,
            };
            let dst = plain_local(place)?;
            let dst_ty = mir_scalar_ty_of_local(ctx, body, dst)?;
            let converted = match rvalue {
                Rvalue::Use(operand) => refine::MirRvalue::Use {
                    src: conv_operand(ctx, body, operand, &readable)?,
                },
                Rvalue::BinaryOp(op, operands) => {
                    let spec_op = conv_binop(*op)?;
                    let lhs_rust_ty =
                        crate::operand_rust_ty(ctx, body, &operands.0).ok()?;
                    let operand_ty = mir_scalar_ty_of_rust_ty(ctx.tcx, lhs_rust_ty)?;
                    // Signed Div/Rem: out of slice (trap-sentinel spec — module doc).
                    if matches!(spec_op, refine::MirBinOp::Div | refine::MirBinOp::Rem) {
                        if operand_ty.is_signed() {
                            return None;
                        }
                        has_div_rem = true;
                    }
                    // Both operand widths must agree (the encoder builds the rhs
                    // at its own width; a mixed-width shift would be ill-sorted).
                    let rhs_rust_ty =
                        crate::operand_rust_ty(ctx, body, &operands.1).ok()?;
                    let rhs_ty = mir_scalar_ty_of_rust_ty(ctx.tcx, rhs_rust_ty)?;
                    if rhs_ty.bits() != operand_ty.bits() {
                        return None;
                    }
                    refine::MirRvalue::BinaryOp {
                        op: spec_op,
                        ty: operand_ty,
                        lhs: conv_operand(ctx, body, &operands.0, &readable)?,
                        rhs: conv_operand(ctx, body, &operands.1, &readable)?,
                    }
                }
                Rvalue::UnaryOp(op, operand) => {
                    let spec_op = match op {
                        mir::UnOp::Neg => refine::MirUnOp::Neg,
                        mir::UnOp::Not => refine::MirUnOp::Not,
                        _ => return None,
                    };
                    let operand_rust_ty = crate::operand_rust_ty(ctx, body, operand).ok()?;
                    let operand_ty = mir_scalar_ty_of_rust_ty(ctx.tcx, operand_rust_ty)?;
                    refine::MirRvalue::UnaryOp {
                        op: spec_op,
                        ty: operand_ty,
                        operand: conv_operand(ctx, body, operand, &readable)?,
                    }
                }
                Rvalue::Cast(mir::CastKind::IntToInt, operand, target_ty) => {
                    let src_rust_ty = crate::operand_rust_ty(ctx, body, operand).ok()?;
                    let src_ty = mir_scalar_ty_of_rust_ty(ctx.tcx, src_rust_ty)?;
                    let dst_ty =
                        mir_scalar_ty_of_rust_ty(ctx.tcx, ctx.monomorphize_ty(*target_ty))?;
                    refine::MirRvalue::Cast {
                        kind: refine::MirCastKind::IntToInt,
                        src_ty,
                        dst_ty,
                        operand: conv_operand(ctx, body, operand, &readable)?,
                    }
                }
                _ => return None,
            };
            let _ = dst_ty;
            stmts.push(refine::MirStmt { dst: canonical_name(dst), rvalue: converted });
            readable.insert(dst);
        }
    }
    Some((stmts, has_div_rem))
}

/// The reconstructed loop-continue condition shape at the header.
enum CondShape {
    /// `switchInt(p)` directly on a header param: continue on `otherwise`.
    Param(Local),
    /// `c = Ne(p, 0); switchInt(c)`: continue on `otherwise`.
    NeZero(Local),
    /// `c = Eq(p, 0); switchInt(c)`: continue on the `0` arm.
    EqZero(Local),
}

/// Resolve `local` upward through pure `Use`-copies of plain locals within
/// `stmts[..upto]`, stopping at a header param. `None` if the chain leaves the
/// copy slice before reaching a param.
fn resolve_to_param(
    stmts: &[Statement<'_>],
    upto: usize,
    mut local: Local,
    params: &HashSet<Local>,
) -> Option<Local> {
    let mut idx = upto;
    loop {
        if params.contains(&local) {
            return Some(local);
        }
        let (i, rvalue) = (0..idx).rev().find_map(|i| match &stmts[i].kind {
            StatementKind::Assign(assign) if plain_local(&assign.0) == Some(local) => {
                Some((i, &assign.1))
            }
            _ => None,
        })?;
        match rvalue {
            Rvalue::Use(op) => {
                local = operand_plain_local(op)?;
                idx = i;
            }
            _ => return None,
        }
    }
}

/// Reconstruct the loop condition from the header's `SwitchInt` discriminant:
/// either the param itself, or a `Ne(param, 0)` / `Eq(param, 0)` comparison
/// temp (resolved through plain copies). The named param must NOT be reassigned
/// within the header block — the verifier's guard reads the header-ENTRY param
/// value, so a pre-switch update would change the guarded input set (LOOP-1).
fn resolve_cond_shape<'tcx>(
    ctx: &MirLoweringCtx<'tcx>,
    stmts: &[Statement<'tcx>],
    discr: Local,
    params: &HashSet<Local>,
) -> Option<CondShape> {
    let mut local = discr;
    let mut idx = stmts.len();
    let shape = loop {
        if params.contains(&local) {
            break CondShape::Param(local);
        }
        let (i, rvalue) = (0..idx).rev().find_map(|i| match &stmts[i].kind {
            StatementKind::Assign(assign) if plain_local(&assign.0) == Some(local) => {
                Some((i, &assign.1))
            }
            _ => None,
        })?;
        match rvalue {
            Rvalue::Use(op) => {
                local = operand_plain_local(op)?;
                idx = i;
            }
            Rvalue::BinaryOp(op @ (mir::BinOp::Ne | mir::BinOp::Eq), operands) => {
                // One side a (copy-resolved) header param, the other const 0.
                let (var_side, const_side) = if operand_plain_local(&operands.0).is_some() {
                    (&operands.0, &operands.1)
                } else {
                    (&operands.1, &operands.0)
                };
                let m = operand_plain_local(var_side)?;
                let param = resolve_to_param(stmts, i, m, params)?;
                if const_int_value(ctx, const_side)? != 0 {
                    return None;
                }
                break if matches!(op, mir::BinOp::Ne) {
                    CondShape::NeZero(param)
                } else {
                    CondShape::EqZero(param)
                };
            }
            _ => return None,
        }
    };
    // Guard param must carry its header-ENTRY value at the switch.
    let guard_param = match &shape {
        CondShape::Param(p) | CondShape::NeZero(p) | CondShape::EqZero(p) => *p,
    };
    let reassigned = stmts.iter().any(|s| match &s.kind {
        StatementKind::Assign(assign) => assign.0.local == guard_param,
        _ => false,
    });
    if reassigned {
        return None;
    }
    Some(shape)
}

/// Resolve a loop-carried param's value at the END of the preheader block, from
/// the SOURCE MIR: an integer constant, or (when the preheader is START_BLOCK
/// and the local is an untouched function argument) the argument itself, named
/// `arg<index>` — the same canonical name the bridge-side resolver gives the
/// entry-block argument `ValueId`. The preheader must be free of indirect
/// writes (projected stores / intrinsics) so the plain-assignment scan is a
/// faithful last-writer analysis.
fn resolve_entry_value<'tcx>(
    ctx: &MirLoweringCtx<'tcx>,
    body: &Body<'tcx>,
    preheader: mir::BasicBlock,
    param: Local,
) -> Option<refine::MirOperand> {
    let stmts = &body.basic_blocks[preheader].statements;
    // Any projected/indirect write in the preheader invalidates the scan.
    for statement in stmts {
        match &statement.kind {
            StatementKind::Assign(assign) => {
                if !assign.0.projection.is_empty() {
                    return None;
                }
            }
            StatementKind::StorageLive(_)
            | StatementKind::StorageDead(_)
            | StatementKind::Nop
            | StatementKind::ConstEvalCounter
            | StatementKind::PlaceMention(_)
            | StatementKind::AscribeUserType(..)
            | StatementKind::Coverage(_)
            | StatementKind::FakeRead(_)
            | StatementKind::BackwardIncompatibleDropHint { .. } => {}
            _ => return None,
        }
    }
    // The preheader terminator must not write a local either (a Call's
    // destination would be invisible to the statement scan).
    if !matches!(
        body.basic_blocks[preheader].terminator().kind,
        TerminatorKind::Goto { .. } | TerminatorKind::SwitchInt { .. } | TerminatorKind::Assert { .. }
    ) {
        return None;
    }
    let mut local = param;
    let mut idx = stmts.len();
    loop {
        let found = (0..idx).rev().find_map(|i| match &stmts[i].kind {
            StatementKind::Assign(assign) if plain_local(&assign.0) == Some(local) => {
                Some((i, &assign.1))
            }
            _ => None,
        });
        let Some((i, rvalue)) = found else {
            // Unresolved at block entry: only the START_BLOCK + untouched
            // function-argument case is in slice (no predecessor can have
            // assigned it).
            if preheader == mir::START_BLOCK && crate::is_entry_arg(body, local) {
                let scalar_ty = mir_scalar_ty_of_local(ctx, body, local)?;
                return Some(refine::MirOperand::Var {
                    name: format!("arg{}", local.index()),
                    ty: scalar_ty,
                });
            }
            return None;
        };
        match rvalue {
            Rvalue::Use(op) => {
                if let Some(m) = operand_plain_local(op) {
                    local = m;
                    idx = i;
                    continue;
                }
                if let Operand::Constant(constant) = op {
                    let evaluated = ctx.eval_const_operand(constant);
                    let scalar_ty = mir_scalar_ty_of_rust_ty(ctx.tcx, evaluated.ty())?;
                    let value = crate::const_to_scalar_i128(&evaluated)?;
                    return Some(refine::MirOperand::ConstInt {
                        value: value as u64,
                        ty: scalar_ty,
                    });
                }
                return None;
            }
            _ => return None,
        }
    }
}

/// The MIR-side loop model plus the chain layout the bridge side mirrors.
struct MirLoopModel {
    mir_loop: refine::MirLoop,
    /// The loop-body blocks from the header's continue-arm to the latch
    /// (excludes the header itself).
    chain: Vec<mir::BasicBlock>,
    preheader: mir::BasicBlock,
    /// Verifier scalar type per header param, in slot order.
    param_tys: Vec<refine::MirScalarTy>,
}

/// Build the verifier `MirLoop` for one loop header from the SOURCE MIR.
/// `None` = out of the covered slice (skip silently — sound).
fn build_mir_loop_model<'tcx>(
    ctx: &MirLoweringCtx<'tcx>,
    body: &Body<'tcx>,
    predecessors: &[Vec<mir::BasicBlock>],
    header: mir::BasicBlock,
    params: &[ScalarBlockParam],
) -> Option<MirLoopModel> {
    let dominators = body.basic_blocks.dominators();

    // Exactly one forward (preheader) and one back-edge (latch) predecessor.
    let mut forward = Vec::new();
    let mut back = Vec::new();
    for pred in &predecessors[header.index()] {
        if dominators.is_reachable(*pred) && dominators.dominates(header, *pred) {
            back.push(*pred);
        } else {
            forward.push(*pred);
        }
    }
    let (&[preheader], &[latch]) = (forward.as_slice(), back.as_slice()) else {
        return None;
    };

    // Header params: int/bool scalars only, canonical `p<idx>` names.
    let mut header_params = Vec::with_capacity(params.len());
    let mut param_tys = Vec::with_capacity(params.len());
    let mut param_set = HashSet::new();
    for param in params {
        let scalar_ty = mir_scalar_ty_of_local(ctx, body, param.local)?;
        header_params.push((canonical_name(param.local), scalar_ty.clone()));
        param_tys.push(scalar_ty);
        param_set.insert(param.local);
    }

    // Loop condition + the continue arm (and the EXIT arm, checked below).
    let header_data = &body.basic_blocks[header];
    let (guard_param, body_entry, exit_arm) = match &header_data.terminator().kind {
        TerminatorKind::Goto { target } => (None, *target, None),
        TerminatorKind::SwitchInt { discr, targets } => {
            // Canonical two-way shape: one explicit `0` case + otherwise.
            let mut iter = targets.iter();
            let (case_value, zero_target) = iter.next()?;
            if iter.next().is_some() || case_value != 0 {
                return None;
            }
            let otherwise = targets.otherwise();
            let discr_local = operand_plain_local(discr)?;
            match resolve_cond_shape(ctx, &header_data.statements, discr_local, &param_set)? {
                // continue iff p != 0.
                CondShape::Param(p) | CondShape::NeZero(p) => {
                    (Some(p), otherwise, Some(zero_target))
                }
                // c = Eq(p, 0): continue (body) on the 0 arm, also iff p != 0.
                CondShape::EqZero(p) => (Some(p), zero_target, Some(otherwise)),
            }
        }
        _ => return None,
    };

    // Walk the straight-line body chain (Goto/Assert only) back to the header.
    let mut chain = Vec::new();
    let mut visited = HashSet::new();
    let mut current = body_entry;
    loop {
        if current == header || !visited.insert(current) {
            return None;
        }
        chain.push(current);
        let next = match &body.basic_blocks[current].terminator().kind {
            TerminatorKind::Goto { target } => *target,
            TerminatorKind::Assert { target, .. } => *target,
            _ => return None,
        };
        if next == header {
            break;
        }
        if chain.len() > body.basic_blocks.len() {
            return None;
        }
        current = next;
    }
    // The chain must end at THE back-edge predecessor (reaching the header any
    // other way means we walked out of the loop).
    if *chain.last()? != latch {
        return None;
    }
    // AUDIT FIX (side-entry): the chain must be TRULY straight-line — every
    // chain block's only predecessor is the previous element (chain head: the
    // header). Otherwise an in-loop join re-enters the chain on an arm this
    // model never folds, and the reconstructed `param != 0` guard can restrict
    // the VC to exactly the traversals where the unmodeled arm does NOT run —
    // certifying a phi-drop on the modeled half while the correct lowering is
    // anti-selectively skipped (adversarial-audit finding). Such shapes SKIP.
    let mut prev = header;
    for bb in &chain {
        if predecessors[bb.index()] != [prev] {
            return None;
        }
        prev = *bb;
    }
    // AUDIT FIX (exit arm): the header's non-body arm must LEAVE the loop. An
    // exit arm pointing back into the chain (or at the header) is a second,
    // unmodeled entry — same hazard as above. Skip.
    if let Some(exit) = exit_arm {
        if exit == header || chain.contains(&exit) {
            return None;
        }
    }

    // Encode header statements (the per-iteration condition computation) + the
    // body chain into one latch statement list over the header params.
    let mut all_blocks = Vec::with_capacity(chain.len() + 1);
    all_blocks.push(header);
    all_blocks.extend(chain.iter().copied());
    let (stmts, has_div_rem) = conv_statements(ctx, body, &all_blocks, &param_set)?;

    // Guard policy: a trapping (unsigned) Div/Rem in the body needs the
    // reconstructed `param != 0` guard to exclude the divisor-0 trap inputs
    // from the universal VC; without it, skip. (Signed Div/Rem already bailed.)
    if guard_param.is_none() && has_div_rem {
        return None;
    }
    let back_edge_guard = match guard_param {
        None => None,
        Some(p) => Some(refine::MirOperand::Var {
            name: canonical_name(p),
            ty: mir_scalar_ty_of_local(ctx, body, p)?,
        }),
    };

    // The MIR back-edge threads each param local's CURRENT value (its updated
    // store binding, or the free header value if the chain never reassigns it).
    let latch_args = params
        .iter()
        .zip(param_tys.iter())
        .map(|(param, scalar_ty)| refine::MirOperand::Var {
            name: canonical_name(param.local),
            ty: scalar_ty.clone(),
        })
        .collect();

    // Preheader entry values, independently derived from the SOURCE MIR.
    let mut preheader_args = Vec::with_capacity(params.len());
    for (param, scalar_ty) in params.iter().zip(param_tys.iter()) {
        let arg = resolve_entry_value(ctx, body, preheader, param.local)?;
        // Slot sort discipline: the entry value must be at the param's width.
        if arg.ty().bits() != scalar_ty.bits() {
            return None;
        }
        preheader_args.push(arg);
    }

    let mir_loop = refine::MirLoop {
        header_params,
        preheader_args,
        latch: refine::MirBlock {
            stmts,
            terminator: refine::MirTerminator::Goto { target: header.index(), args: latch_args },
        },
        back_edge_guard,
    };
    Some(MirLoopModel { mir_loop, chain, preheader, param_tys })
}

// ===========================================================================
// 3. Bridge side: interpret the EMITTED trust-ir for the same loop
// ===========================================================================

fn block_by_id<'f>(func: &'f TrustIrFunction, id: BlockId) -> Option<&'f Block> {
    func.blocks.iter().find(|b| b.id == id)
}

/// Build the bridge side of the VC — (preheader edge, latch edge) — from the
/// EMITTED trust-ir only. The latch edge comes from the symbolic interpreter
/// over the emitted header+chain instructions; the preheader edge from the
/// emitted entry-edge args resolved through Const/Copy defs to function-arg
/// params. `None` = out of slice (skip).
fn build_bridge_edges<'tcx>(
    ctx: &MirLoweringCtx<'tcx>,
    body: &Body<'tcx>,
    func: &TrustIrFunction,
    header: mir::BasicBlock,
    params: &[ScalarBlockParam],
    model: &MirLoopModel,
) -> Option<(refine::BridgeEdgeArgs, refine::BridgeEdgeArgs)> {
    let header_id = BlockId::new(header.index() as u32);
    let header_block = block_by_id(func, header_id)?;

    // AUDIT FIX (rogue back-edges, whole-function): the EMITTED header's
    // predecessor set must be exactly {preheader, latch}, each reaching it on a
    // single arm. Any other emitted edge into the header — from a mid-chain
    // CondBr arm or from a block outside the modeled chain entirely — is a
    // back-edge whose threaded args this VC never inspects (a rogue arm
    // threading the header params themselves passes the structural P1.3 gate
    // and would be reported Refined/covered here). Such shapes SKIP.
    {
        let latch_id = BlockId::new(model.chain.last()?.index() as u32);
        let preheader_id = BlockId::new(model.preheader.index() as u32);
        for b in &func.blocks {
            let Some(term) = b.body.last() else { continue };
            let arms = edges_to(&term.inst, header_id).len();
            if arms == 0 {
                continue;
            }
            let legitimate = arms == 1 && (b.id == preheader_id || b.id == latch_id);
            if !legitimate {
                return None;
            }
        }
    }

    // The emitted header must carry EXACTLY the loop scalar params (any extra
    // projected/borrowed/forward params mean threading state this slice does
    // not model). Param k of the block must be the k-th loop param's ValueId,
    // at the MIR-side width.
    if header_block.params.len() != params.len() {
        return None;
    }
    let mut seed: HashMap<ValueId, SmtExpr> = HashMap::new();
    for ((value, ty), (param, scalar_ty)) in header_block
        .params
        .iter()
        .zip(params.iter().zip(model.param_tys.iter()))
    {
        if *value != param.value || int_width(ty)? != scalar_ty.bits() {
            return None;
        }
        seed.insert(
            param.value,
            SmtExpr::var(canonical_name(param.local), scalar_ty.bits()),
        );
    }

    // Emitted header + body chain blocks, in MIR chain order (BlockIds mirror
    // MIR block indices by construction).
    let mut blocks = Vec::with_capacity(model.chain.len() + 1);
    blocks.push(header_block);
    for bb in &model.chain {
        blocks.push(block_by_id(func, BlockId::new(bb.index() as u32))?);
    }

    // LATCH back-edge: interpret the emitted instructions, resolve the Br args.
    let latch_args = interpret_chain_to_back_edge(&blocks, header_id, seed)?;
    if latch_args.len() != params.len() {
        return None;
    }
    for (expr, scalar_ty) in latch_args.iter().zip(model.param_tys.iter()) {
        if expr.try_bv_width().ok() != Some(scalar_ty.bits()) {
            return None;
        }
    }

    // PREHEADER entry edge: the emitted args on preheader -> header, resolved
    // through Const/Copy defs; an undefined ValueId is faithful-named as the
    // function argument it IS by construction (`ValueId(i)` for 1 <= i <=
    // arg_count is minted ONLY as the entry-block param of argument local `i`).
    let base = |v: ValueId| -> Option<SmtExpr> {
        let index = v.index() as usize;
        if index == 0 || index > body.arg_count {
            return None;
        }
        let local = Local::new(index);
        if !crate::is_entry_arg(body, local) {
            return None;
        }
        let scalar_ty = mir_scalar_ty_of_local(ctx, body, local)?;
        Some(SmtExpr::var(format!("arg{index}"), scalar_ty.bits()))
    };
    let preheader_id = BlockId::new(model.preheader.index() as u32);
    let preheader_args = resolve_edge_args_through_defs(func, preheader_id, header_id, &base)?;
    if preheader_args.len() != params.len() {
        return None;
    }
    for (expr, scalar_ty) in preheader_args.iter().zip(model.param_tys.iter()) {
        if expr.try_bv_width().ok() != Some(scalar_ty.bits()) {
            return None;
        }
    }

    Some((
        refine::BridgeEdgeArgs { edge: refine::EdgeKind::Goto, args: preheader_args },
        refine::BridgeEdgeArgs { edge: refine::EdgeKind::Goto, args: latch_args },
    ))
}

// ===========================================================================
// 4. Per-loop discharge (the refinement-tail entry; emit_refinements lane only)
// ===========================================================================

/// Discharge the loop-carried threading VC for every loop header the bridge
/// created params for. Called from the `mir_to_trust_ir` refinement tail,
/// gated behind `emit_refinements` (the solver lane — loop ints are wider than
/// the fast lane's exhaustive subset). FAILS THE COMPILE CLOSED on a Refuted or
/// Inconclusive verdict, mirroring the P3c rvalue tail; out-of-slice loops and
/// verifier structural `Err`s are skipped (sound: less coverage, never a wrong
/// verdict — structural arity/dominance bugs are the default-on P1.3 gate's
/// job).
pub(crate) fn check_loop_threading_refinements<'tcx>(
    ctx: &MirLoweringCtx<'tcx>,
    body: &Body<'tcx>,
    func: &TrustIrFunction,
    predecessors: &[Vec<mir::BasicBlock>],
    header_scalar_params: &HashMap<mir::BasicBlock, Vec<ScalarBlockParam>>,
    symbol: &str,
) -> Result<(), String> {
    if header_scalar_params.is_empty() {
        return Ok(());
    }
    let trace = std::env::var_os("TCG_REFINE_TRACE").is_some();
    let config = trust_cg_verify::ay_bridge::AYConfig::default();

    // Deterministic order; dedup identical (loop, edges) obligations.
    let mut headers: Vec<mir::BasicBlock> = header_scalar_params.keys().copied().collect();
    headers.sort_by_key(|bb| bb.index());
    let mut seen: HashSet<String> = HashSet::new();

    for header in headers {
        let params = &header_scalar_params[&header];
        let name = format!("{symbol}_loop_bb{}", header.index());
        let Some(model) = build_mir_loop_model(ctx, body, predecessors, header, params) else {
            if trace {
                eprintln!("TCG_REFINE_TRACE {symbol}: loop-threading {name} SKIPPED (MIR side out of slice)");
            }
            continue;
        };
        let Some((preheader_edge, latch_edge)) =
            build_bridge_edges(ctx, body, func, header, params, &model)
        else {
            if trace {
                eprintln!("TCG_REFINE_TRACE {symbol}: loop-threading {name} SKIPPED (emitted trust-ir out of the interpreter slice)");
            }
            continue;
        };
        let fingerprint = format!(
            "{:?}|{:?}|{:?}",
            model.mir_loop, preheader_edge.args, latch_edge.args
        );
        if !seen.insert(fingerprint) {
            continue;
        }
        match refine::check_loop_carried_threading(
            &name,
            &model.mir_loop,
            &preheader_edge,
            &latch_edge,
            &config,
        ) {
            Ok(refine::RefinementOutcome::Refined) => {
                if trace {
                    eprintln!(
                        "TCG_REFINE_TRACE {symbol}: loop-threading {name} REFINED ({} slot(s), {} chain block(s))",
                        params.len(),
                        model.chain.len()
                    );
                }
            }
            Ok(refine::RefinementOutcome::Refuted { counterexample }) => {
                // Additive diagnostics: same message, [TCG-REFINE-071]-prefixed
                // (+ typed JSON under TCG_DIAG_JSON=1). No gate decision changes.
                let why = format!(
                    "{symbol}: MIR->trust-ir loop-threading refinement failed: {name} REFUTED \
                     (counterexample: {counterexample})"
                );
                return Err(trust_cg_verify::diag::loop_threading_message(
                    symbol,
                    &why,
                    &format!("{name} REFUTED (counterexample: {counterexample})"),
                ));
            }
            Ok(refine::RefinementOutcome::Inconclusive { reason }) => {
                let why = format!(
                    "{symbol}: MIR->trust-ir loop-threading refinement failed: {name} \
                     INCONCLUSIVE ({reason})"
                );
                return Err(trust_cg_verify::diag::loop_threading_message(
                    symbol,
                    &why,
                    &format!("{name} INCONCLUSIVE ({reason})"),
                ));
            }
            // Verifier structural error (e.g. an arity it rejects): out of the
            // encodable slice, not a verdict — skip, like the rvalue tail's Err.
            Err(e) => {
                if trace {
                    eprintln!("TCG_REFINE_TRACE {symbol}: loop-threading {name} SKIPPED (verifier: {e})");
                }
            }
        }
    }
    Ok(())
}

// ===========================================================================
// Unit tests: the interpreter side is LOAD-BEARING (hand-built emitted latches)
// ===========================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use trust_cg_verify::ay_bridge::AYConfig;

    const HEADER: BlockId = BlockId::new(1);
    const LATCH: BlockId = BlockId::new(2);
    const EXIT: BlockId = BlockId::new(3);
    const PRE: BlockId = BlockId::new(0);

    // ValueIds for the hand-built euclid: header params (a, b) and the latch
    // temporaries.
    const V_A: ValueId = ValueId::new(10);
    const V_B: ValueId = ValueId::new(11);
    const V_ZERO: ValueId = ValueId::new(20);
    const V_COND: ValueId = ValueId::new(21);
    const V_T: ValueId = ValueId::new(22);
    const V_REM: ValueId = ValueId::new(23);
    const V_A2: ValueId = ValueId::new(24);

    fn node(inst: Inst, result: ValueId) -> InstrNode {
        InstrNode::new(inst).with_result(result)
    }

    /// The EMITTED euclid header: params (a, b); cond = (b != 0); CondBr.
    fn emitted_header() -> Block {
        let mut block = Block::new(HEADER);
        block.params.push((V_A, TrustIrTy::U8));
        block.params.push((V_B, TrustIrTy::U8));
        block.body.push(node(
            Inst::Const { ty: TrustIrTy::U8, value: Constant::Int(0) },
            V_ZERO,
        ));
        block.body.push(node(
            Inst::ICmp { op: ICmpOp::Ne, ty: TrustIrTy::U8, lhs: V_B, rhs: V_ZERO },
            V_COND,
        ));
        block.body.push(InstrNode::new(Inst::CondBr {
            cond: V_COND,
            then_target: LATCH,
            then_args: Vec::new(),
            else_target: EXIT,
            else_args: Vec::new(),
        }));
        block
    }

    /// The EMITTED euclid latch (`t = b; b' = a % b; a' = t`) threading
    /// `back_args` to the header — the CORRECT rotation is `(t, a % b)`.
    fn emitted_latch(back_args: Vec<ValueId>) -> Block {
        let mut block = Block::new(LATCH);
        block
            .body
            .push(node(Inst::Copy { ty: TrustIrTy::U8, operand: V_B }, V_T));
        block.body.push(node(
            Inst::BinOp { op: TrustIrBinOp::URem, ty: TrustIrTy::U8, lhs: V_A, rhs: V_B },
            V_REM,
        ));
        block
            .body
            .push(node(Inst::Copy { ty: TrustIrTy::U8, operand: V_T }, V_A2));
        block
            .body
            .push(InstrNode::new(Inst::Br { target: HEADER, args: back_args }));
        block
    }

    fn seed() -> HashMap<ValueId, SmtExpr> {
        let mut env = HashMap::new();
        env.insert(V_A, SmtExpr::var("a", 8));
        env.insert(V_B, SmtExpr::var("b", 8));
        env
    }

    /// The MIR-side euclid loop over u8 (mirrors the production model: latch
    /// statements rebind the param names; the Goto threads the param names).
    /// Unsigned `%` so the spec carries no signed-overflow trap sentinel; the
    /// `b != 0` guard excludes the divide-by-zero trap inputs.
    fn euclid_mir_loop() -> refine::MirLoop {
        let u8t = refine::MirScalarTy::UInt(LowerType::I8);
        let var = |n: &str| refine::MirOperand::Var { name: n.to_string(), ty: u8t.clone() };
        refine::MirLoop {
            header_params: vec![("a".to_string(), u8t.clone()), ("b".to_string(), u8t.clone())],
            preheader_args: vec![var("arg1"), var("arg2")],
            latch: refine::MirBlock {
                stmts: vec![
                    refine::MirStmt { dst: "t".to_string(), rvalue: refine::MirRvalue::Use { src: var("b") } },
                    refine::MirStmt {
                        dst: "b".to_string(),
                        rvalue: refine::MirRvalue::BinaryOp {
                            op: refine::MirBinOp::Rem,
                            ty: u8t.clone(),
                            lhs: var("a"),
                            rhs: var("b"),
                        },
                    },
                    refine::MirStmt { dst: "a".to_string(), rvalue: refine::MirRvalue::Use { src: var("t") } },
                ],
                terminator: refine::MirTerminator::Goto { target: 1, args: vec![var("a"), var("b")] },
            },
            back_edge_guard: Some(var("b")),
        }
    }

    /// Run the interpreter over a hand-built emitted header+latch and discharge
    /// the full loop-carried VC against the MIR side.
    fn discharge(back_args: Vec<ValueId>) -> refine::RefinementOutcome {
        let header = emitted_header();
        let latch = emitted_latch(back_args);
        let blocks = [&header, &latch];
        let latch_exprs = interpret_chain_to_back_edge(&blocks, HEADER, seed())
            .expect("euclid chain is inside the interpreter slice");
        // Preheader: a synthetic entry block threading the raw function args,
        // resolved through the def-walker with the faithful arg naming.
        let mut pre = Block::new(PRE);
        pre.body.push(InstrNode::new(Inst::Br {
            target: HEADER,
            args: vec![ValueId::new(1), ValueId::new(2)],
        }));
        let mut func =
            TrustIrFunction::new(trust_ir::FuncId::new(0), "euclid_test", trust_ir::FuncTyId::new(0), PRE);
        func.blocks.push(pre);
        let base = |v: ValueId| -> Option<SmtExpr> {
            match v.index() {
                1 => Some(SmtExpr::var("arg1", 8)),
                2 => Some(SmtExpr::var("arg2", 8)),
                _ => None,
            }
        };
        let pre_args = resolve_edge_args_through_defs(&func, PRE, HEADER, &base)
            .expect("preheader edge resolves");
        refine::check_loop_carried_threading(
            "unit_euclid",
            &euclid_mir_loop(),
            &refine::BridgeEdgeArgs { edge: refine::EdgeKind::Goto, args: pre_args },
            &refine::BridgeEdgeArgs { edge: refine::EdgeKind::Goto, args: latch_exprs },
            &AYConfig::default(),
        )
        .expect("obligations build")
    }

    /// (1) CORRECT rotation: emitted back-edge args (t, a%b) -> Refined. The
    /// positive control that makes the two refutations below load-bearing.
    #[test]
    fn interpreted_correct_rotation_refines() {
        match discharge(vec![V_A2, V_REM]) {
            refine::RefinementOutcome::Refined => {}
            other => panic!("correct emitted rotation must Refine, got {other:?}"),
        }
    }

    /// (2) SWAPPED emitted back-edge args (a%b, t) — the euclid swap — the
    /// interpreter faithfully reports the swapped expressions -> Refuted.
    #[test]
    fn interpreted_swapped_back_edge_is_refuted() {
        match discharge(vec![V_REM, V_A2]) {
            refine::RefinementOutcome::Refuted { counterexample } => {
                assert!(!counterexample.is_empty(), "refutation carries a counterexample");
            }
            other => panic!("swapped emitted back-edge must be Refuted, got {other:?}"),
        }
    }

    /// (3) STALE emitted back-edge arg: slot 0 threads the ENTRY `a` (the raw
    /// header param) instead of the rotated `t` — the #71 drop -> Refuted.
    #[test]
    fn interpreted_stale_back_edge_is_refuted() {
        match discharge(vec![V_A, V_REM]) {
            refine::RefinementOutcome::Refuted { counterexample } => {
                assert!(!counterexample.is_empty(), "refutation carries a counterexample");
            }
            other => panic!("stale emitted back-edge must be Refuted, got {other:?}"),
        }
    }

    /// The interpreter's MASKED shift semantics mirror the verifier's masked
    /// MIR spec exactly: a `x <<= s`-style latch Refines at u8 INCLUDING the
    /// `s >= width` inputs (a raw-shift mismatch would refute there).
    #[test]
    fn interpreted_masked_shift_matches_spec() {
        let u8t = refine::MirScalarTy::UInt(LowerType::I8);
        let var = |n: &str| refine::MirOperand::Var { name: n.to_string(), ty: u8t.clone() };
        let mir_loop = refine::MirLoop {
            header_params: vec![("a".to_string(), u8t.clone()), ("b".to_string(), u8t.clone())],
            preheader_args: vec![var("arg1"), var("arg2")],
            latch: refine::MirBlock {
                stmts: vec![refine::MirStmt {
                    dst: "a".to_string(),
                    rvalue: refine::MirRvalue::BinaryOp {
                        op: refine::MirBinOp::Shl,
                        ty: u8t.clone(),
                        lhs: var("a"),
                        rhs: var("b"),
                    },
                }],
                terminator: refine::MirTerminator::Goto { target: 1, args: vec![var("a"), var("b")] },
            },
            back_edge_guard: None,
        };
        // Emitted: a' = Shl(a, b); back-edge (a', b). Header passes through.
        let mut header = Block::new(HEADER);
        header.params.push((V_A, TrustIrTy::U8));
        header.params.push((V_B, TrustIrTy::U8));
        header.body.push(InstrNode::new(Inst::Br { target: LATCH, args: Vec::new() }));
        let mut latch = Block::new(LATCH);
        latch.body.push(node(
            Inst::BinOp { op: TrustIrBinOp::Shl, ty: TrustIrTy::U8, lhs: V_A, rhs: V_B },
            V_T,
        ));
        latch
            .body
            .push(InstrNode::new(Inst::Br { target: HEADER, args: vec![V_T, V_B] }));
        let blocks = [&header, &latch];
        let latch_exprs =
            interpret_chain_to_back_edge(&blocks, HEADER, seed()).expect("shift chain interprets");
        let pre = refine::BridgeEdgeArgs {
            edge: refine::EdgeKind::Goto,
            args: vec![SmtExpr::var("arg1", 8), SmtExpr::var("arg2", 8)],
        };
        let latch_edge = refine::BridgeEdgeArgs { edge: refine::EdgeKind::Goto, args: latch_exprs };
        match refine::check_loop_carried_threading(
            "unit_shift",
            &mir_loop,
            &pre,
            &latch_edge,
            &AYConfig::default(),
        )
        .expect("obligations build")
        {
            refine::RefinementOutcome::Refined => {}
            other => panic!("masked-shift mirror must Refine, got {other:?}"),
        }
    }

    /// Out-of-slice instructions bail the interpreter (no guessing): a latch
    /// containing a `Load` returns `None`.
    #[test]
    fn interpreter_bails_on_memory_inst() {
        let header = emitted_header();
        let mut latch = Block::new(LATCH);
        latch.body.push(node(
            Inst::Load { ty: TrustIrTy::U8, ptr: V_A, volatile: false, align: None },
            V_T,
        ));
        latch
            .body
            .push(InstrNode::new(Inst::Br { target: HEADER, args: vec![V_T, V_B] }));
        let blocks = [&header, &latch];
        assert!(
            interpret_chain_to_back_edge(&blocks, HEADER, seed()).is_none(),
            "a Load in the latch must bail the interpreter (out of slice)"
        );
    }

    /// AUDIT FIX (rogue mid-chain back-edge): an INTERMEDIATE chain block with
    /// an arm targeting the header — here a CondBr arm threading the header
    /// params themselves, the stale identity re-entry that passes the
    /// structural P1.3 dominance/slot checks — must take the loop OUT of slice
    /// (`None`), never report the latch edge as covered. LOAD-BEARING: the
    /// same chain WITHOUT the rogue arm resolves (the fix is not over-broad).
    #[test]
    fn rogue_mid_chain_header_arm_skips() {
        const MID: BlockId = BlockId::new(4);
        // Header branches to MID (continue) / EXIT.
        let mut header = emitted_header();
        let term = header.body.pop().expect("header terminator");
        let _ = term;
        header.body.push(InstrNode::new(Inst::CondBr {
            cond: V_COND,
            then_target: MID,
            then_args: Vec::new(),
            else_target: EXIT,
            else_args: Vec::new(),
        }));
        // Clean MID: falls through to the latch on both arms' worth of a plain Br.
        let mut mid_clean = Block::new(MID);
        mid_clean
            .body
            .push(InstrNode::new(Inst::Br { target: LATCH, args: Vec::new() }));
        // Rogue MID: one arm to the latch, one arm BACK TO THE HEADER threading
        // the header params themselves (V_A, V_B).
        let mut mid_rogue = Block::new(MID);
        mid_rogue.body.push(InstrNode::new(Inst::CondBr {
            cond: V_COND,
            then_target: LATCH,
            then_args: Vec::new(),
            else_target: HEADER,
            else_args: vec![V_A, V_B],
        }));
        let latch = emitted_latch(vec![V_A2, V_REM]);

        // Positive control: the clean 3-block chain resolves the back-edge.
        let clean = [&header, &mid_clean, &latch];
        assert!(
            interpret_chain_to_back_edge(&clean, HEADER, seed()).is_some(),
            "control: a clean intermediate block must not bail the fold"
        );
        // The rogue arm must skip the loop entirely.
        let rogue = [&header, &mid_rogue, &latch];
        assert!(
            interpret_chain_to_back_edge(&rogue, HEADER, seed()).is_none(),
            "a mid-chain arm to the header threads uninspected back-edge args \
             and must take the loop out of slice"
        );
    }

    /// Signed SRem is deliberately out of slice (the MIR spec's INT_MIN/-1
    /// trap sentinel has no precondition channel here): the interpreter bails.
    #[test]
    fn interpreter_bails_on_signed_rem() {
        let mut env = seed();
        let srem = node(
            Inst::BinOp { op: TrustIrBinOp::SRem, ty: TrustIrTy::U8, lhs: V_A, rhs: V_B },
            V_REM,
        );
        assert!(interp_inst(&mut env, &srem).is_none(), "SRem must be out of slice");
    }
}
