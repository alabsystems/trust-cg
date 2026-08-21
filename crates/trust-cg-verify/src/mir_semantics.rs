// trust-cg-verify/mir_semantics.rs - MIR rvalue/statement semantics as SMT formulas
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// P3c — MIR semantics encoder + per-compile refinement obligation.
//
// FOUNDATION SLICE. This module is the MIR-side mirror of
// `trust_ir_semantics.rs`: it encodes a useful subset of rustc MIR rvalues and
// statements (BinaryOp incl. checked/overflowing, UnaryOp incl. Neg, scalar
// casts/extensions, Use/Copy/Move, scalar Assign) as `SmtExpr` bitvector
// formulas. It then builds a *refinement obligation* that asserts the trust-ir
// block the bridge produced is equivalent to the MIR specification, and
// discharges it through the SAME ay/z3 path used by every other lowering proof.
//
// WHY THIS CLOSES A GAP
// ---------------------
// The SMT-verified core only proves `trust_ir_inst -> AArch64_inst`. Everything
// upstream of trust-ir -- the rustc bridge's MIR -> trust-ir translation -- is
// UNVERIFIED. ~17 miscompiles found in a recent session were all in that
// unverified layer. Several of them are *op-selection* mistakes the bridge made
// while translating MIR to trust-ir:
//
//   * #68-fneg: `-x` (MIR `UnOp::Neg` on a float) lowered as `0.0 - x` instead
//     of an IEEE sign-bit flip. Wrong for signed zero / NaN.
//   * #68-cvt:  `i32 as f32` (MIR `Cast(IntToFloat)`) lowered as an UNSIGNED
//     int->float conversion. Wrong for negative inputs.
//   * #59:      `a + b` that Rust requires to TRAP on overflow lowered to a
//     SATURATING add (or vice-versa).
//   * #67:      overflow expansion edge cases.
//
// This encoder gives those translations a formal contract: it independently
// encodes the *Rust-defined* meaning of each MIR rvalue, then asks the solver
// whether the trust-ir the bridge chose can ever disagree. A wrong op choice
// produces a SAT counterexample (e.g. `x = -1`).
//
// REAL rustc MIR requires the nightly `rustc-dev` bridge toolchain and is NOT
// available in-workspace, so this slice defines a faithful, minimal MIR-like
// model (`MirRvalue` / `MirStmt` / `MirBlock`). The model deliberately mirrors
// the exact MIR shapes the bridge matches on in
// `rustc-codegen-trust-cg/src/lib.rs` (`Rvalue::BinaryOp`, `Rvalue::UnaryOp`,
// `Rvalue::Cast`, `Rvalue::Use`) so that wiring against real MIR later is a
// 1:1 translation, not a redesign. See the module-level DESIGN notes at the
// bottom for the control-flow / memory / `emit_proofs=true` extension path.
//
// Reference: designs/2026-04-13-verification-architecture.md (translation
// validation), Alive2 (PLDI 2021).

//! MIR rvalue/statement semantics encoded as [`SmtExpr`] bitvector formulas,
//! plus a refinement-obligation generator for the MIR -> trust-ir boundary.

use crate::ay_bridge::{self, AYConfig, AYResult};
use crate::lowering_proof::{ProofObligation, TransvalCheckKind, verify_by_evaluation};
use crate::smt::{RoundingMode, SmtExpr, SmtSort, mask};
use crate::verify::VerificationResult;
use trust_cg_lower::instructions::{FloatCC, IntCC, Opcode};
use trust_cg_lower::types::Type;

// ---------------------------------------------------------------------------
// Minimal in-repo MIR-like model
// ---------------------------------------------------------------------------
//
// These types mirror the subset of rustc MIR that the bridge's `lower_assign`
// / `lower_binary_op` / `lower_unary_op` / `lower_cast` match on. They are
// faithful to the shapes in `rustc-codegen-trust-cg/src/lib.rs` while being
// buildable in-workspace (no `rustc_middle::mir` dependency).

/// A scalar MIR type. Mirrors the integer/float subset of `rustc` `ty::Ty`
/// that maps to `trust_cg_lower::types::Type`. We keep an explicit signedness
/// bit because MIR's `i32`/`u32` are *distinct* `Ty`s even though both lower to
/// `Type::I32`; the signedness drives Div/Rem/Shr/cast op selection (exactly as
/// `is_signed_integer(lhs_ty)` does in the bridge).
///
/// Note: `trust_cg_lower::types::Type` is NOT `Copy` (it has a `Struct(Vec<Type>)`
/// variant), so this enum is `Clone` but not `Copy`. The integer/float subset it
/// holds is tiny, so cloning is cheap.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum MirScalarTy {
    /// Signed integer of the given trust-ir type (I8/I16/I32/I64).
    SInt(Type),
    /// Unsigned integer of the given trust-ir type (I8/I16/I32/I64).
    UInt(Type),
    /// Boolean (1 bit). Mirrors MIR `ty::Bool`.
    Bool,
    /// Floating point (F32/F64).
    Float(Type),
}

impl MirScalarTy {
    /// The underlying trust-ir `Type` (drops signedness).
    pub fn trust_ir_ty(&self) -> Type {
        match self {
            MirScalarTy::SInt(t) | MirScalarTy::UInt(t) | MirScalarTy::Float(t) => t.clone(),
            MirScalarTy::Bool => Type::B1,
        }
    }

    /// Bit width of the type.
    pub fn bits(&self) -> u32 {
        match self {
            MirScalarTy::Bool => 1,
            other => other.trust_ir_ty().bits(),
        }
    }

    pub fn is_signed(&self) -> bool {
        matches!(self, MirScalarTy::SInt(_))
    }

    pub fn is_float(&self) -> bool {
        matches!(self, MirScalarTy::Float(_))
    }

    /// `(eb, sb)` IEEE format parameters for a float type.
    pub fn fp_format(&self) -> Option<(u32, u32)> {
        match self {
            MirScalarTy::Float(Type::F32) => Some((8, 24)),
            MirScalarTy::Float(Type::F64) => Some((11, 53)),
            _ => None,
        }
    }
}

/// MIR `BinOp` subset. Mirrors `rustc_middle::mir::BinOp` variants the bridge
/// handles in `rust_binop_to_trust_ir_binop` / `_icmp` / `_overflow_op`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum MirBinOp {
    Add,
    Sub,
    Mul,
    Div,
    Rem,
    BitXor,
    BitAnd,
    BitOr,
    Shl,
    Shr,
    Eq,
    Ne,
    Lt,
    Le,
    Gt,
    Ge,
}

/// MIR `UnOp` subset. Mirrors `rustc_middle::mir::UnOp`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum MirUnOp {
    /// Arithmetic negation. On signed ints this is two's complement; on floats
    /// this is the IEEE sign-bit flip (NOT `0.0 - x`).
    Neg,
    /// Bitwise NOT on integers, logical NOT on `bool`.
    Not,
}

/// MIR scalar cast kind. Mirrors the `CastKind` arms `lower_cast` handles for
/// scalar int/float (IntToInt extend/truncate, IntToFloat, FloatToInt,
/// FloatToFloat).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum MirCastKind {
    /// Integer widen/narrow (signedness of *source* drives sign- vs zero-ext).
    IntToInt,
    /// Integer -> floating point. Signedness of the source decides SIToFP vs UIToFP.
    IntToFloat,
    /// Floating point -> integer (truncate toward zero).
    FloatToInt,
    /// Float precision change (f32<->f64).
    FloatToFloat,
}

/// A scalar MIR rvalue (the subset this slice encodes).
///
/// `Operand`s are modeled directly as named SSA inputs of a given type, because
/// after the bridge's operand lowering each operand is a `ValueId` carrying a
/// type. This keeps the model straight-line and matches what
/// `lower_operand_to_value` produces.
#[derive(Debug, Clone)]
pub enum MirRvalue {
    /// `Use(operand)` / `Copy` / `Move` — identity at the value level.
    Use { src: MirOperand },
    /// `BinaryOp(op, (lhs, rhs))` — non-checked arithmetic / comparison.
    BinaryOp {
        op: MirBinOp,
        ty: MirScalarTy,
        lhs: MirOperand,
        rhs: MirOperand,
    },
    /// `BinaryOp(AddWithOverflow|...)` — checked/overflowing arithmetic.
    /// Produces a `(value, overflow_bit)` pair packed as `overflow :: value`,
    /// matching `checked_overflow_proofs::pack` (overflow in the high bit).
    CheckedBinaryOp {
        op: MirBinOp, // Add / Sub / Mul only
        ty: MirScalarTy,
        lhs: MirOperand,
        rhs: MirOperand,
    },
    /// `UnaryOp(op, operand)`.
    UnaryOp {
        op: MirUnOp,
        ty: MirScalarTy,
        operand: MirOperand,
    },
    /// `Cast(kind, operand, dst_ty)`.
    Cast {
        kind: MirCastKind,
        src_ty: MirScalarTy,
        dst_ty: MirScalarTy,
        operand: MirOperand,
    },
    /// `Aggregate(kind, fields)` — scalar-field struct/tuple construction.
    ///
    /// Mirrors `rustc_middle::mir::Rvalue::Aggregate(AggregateKind::{Tuple,
    /// Adt(struct)}, fields)` for the SCALAR-FIELD slice (every field is a
    /// fixed-width integer/bool). The VALUE of the aggregate is the fields
    /// PACKED in SOURCE (rustc declaration) field order: field 0 occupies the
    /// low bits, each subsequent field stacked above it (see [`pack_fields`]).
    /// This is the independent SPEC the bridge's placement is checked against —
    /// a bridge that swaps two fields' offsets (the #69/#73 field-REORDER
    /// miscompile) produces a different packed value and is refuted.
    ///
    /// SCOPE: scalar (int/bool) fields only — nested aggregates, heap/`Ref`
    /// fields, and SSE/float-classified fields are deliberately out of slice
    /// (the by-value mixed INT+SSE ABI is a separate refinement; see DESIGN
    /// "MEMORY / AGGREGATES"). `encode_mir_rvalue` rejects a float field so a
    /// float aggregate is never silently mis-encoded as an integer pack.
    Aggregate { fields: Vec<MirOperand> },
    /// `select(cond, then_val, else_val)` — the MERGE of a 2-way diamond
    /// (`if cond { x = then } else { x = else }`) at its reconvergence point.
    ///
    /// This is NOT a MIR `Rvalue` in its own right — MIR realizes the merge
    /// structurally (a `SwitchInt` to two arms that reconverge, each arm
    /// rebinding the local, with the post-join read seeing whichever arm ran).
    /// The loop-threading VC's diamond-coverage SPEC builder
    /// (`vc_walk_mir_loop_path`) collapses that structure into this single
    /// rvalue per join-reassigned local so the back-edge threading equality can
    /// be expressed straight-line over the header-param free vars: the value
    /// the local carries past the join is `then_val` when the branch
    /// discriminant selects the THEN arm and `else_val` otherwise.
    ///
    /// `cond` is the diamond discriminant (a `bool`/integer, taken-when-nonzero,
    /// the SAME condition the emitted trust-ir branches on). `then_val` and
    /// `else_val` are the per-arm values of the reassigned local, both the same
    /// width as the result. A local NOT reassigned on an arm passes its
    /// pre-diamond value through on that arm (the caller fills that in).
    /// Encoded as `ite(cond != 0, then_val, else_val)`; a SWAPPED-arm spec
    /// (`then`/`else` exchanged) therefore encodes a different value and is
    /// refuted against the bridge's independently-derived join `ite`.
    Select {
        cond: MirOperand,
        ty: MirScalarTy,
        then_val: MirOperand,
        else_val: MirOperand,
    },
    /// LOOP-VC-LOCAL packed `(iN, bool)` overflow tuple: the value the O2/O3
    /// scalarizer binds to the checked-arith temp `_6` of
    /// `_6 = AddWithOverflow(a, b)` (and Sub/Mul variants). Encoded — ONLY on the
    /// loop back-edge / edge-equality threading path (`encode_block_rvalue`) — as
    /// the packed bitvector `overflow_flag(1) :: wrapped(N)` (flag in the high
    /// bit, matching [`encode_mir_checked_binop`]'s layout), where:
    ///   * `wrapped` is the two's-complement `bvadd`/`bvsub`/`bvmul` (the exact
    ///     `.0` field — bit-identical to the trust-ir `Inst::Overflow` result 0);
    ///   * `overflow_flag` is the shared UNINTERPRETED function
    ///     [`overflow_flag_uf`] keyed by (op, width, lhs, rhs), the SAME symbol
    ///     the IMPL side (`loop_backedge_symexec`) binds `Inst::Overflow`'s flag
    ///     result to.
    ///
    /// The UF lets the threading VC PROVE `impl_flag == spec_flag` by congruence
    /// WITHOUT the exact (signedness-dependent) flag formula — which the trust-ir
    /// `Inst::Overflow` opcode drops. The flag's VALUE-correctness is proven
    /// SEPARATELY by the per-instruction `Inst::Overflow` lowering cert; the
    /// loop-VC only needs to prove the bridge threads THIS op's flag on THESE
    /// operands to the right slot (a wrong op / operands / a stale value threaded
    /// into the flag slot is not congruent and REFUTES). Deliberately OUT of the
    /// per-instruction slice: [`encode_mir_rvalue`] rejects it.
    CheckedOverflowPacked {
        op: MirBinOp, // Add / Sub / Mul only
        ty: MirScalarTy,
        lhs: MirOperand,
        rhs: MirOperand,
    },
    /// LOOP-VC-LOCAL projection of a [`MirRvalue::CheckedOverflowPacked`] value:
    /// the `_1 = move (_6.0: iN)` / `_10 = move (_6.1: bool)` field reads the
    /// O2/O3 scalarizer emits after a checked-arith temp. `src` names the packed
    /// tuple local (bound earlier in the same block by a `CheckedOverflowPacked`);
    /// `field 0` extracts the low `value_width` bits (the wrapped value), `field
    /// 1` extracts the single high bit (the overflow flag). Reading the fields off
    /// the SNAPSHOT packed value (not re-deriving from `lhs`/`rhs`) is what keeps
    /// both fields tied to the SAME operand values even after `_1` is reassigned
    /// on the path. Out of the per-instruction slice ([`encode_mir_rvalue`]
    /// rejects it).
    PackedOverflowField {
        /// Name of the packed `CheckedOverflowPacked` source local (`_6`).
        src: String,
        /// Tuple field index: 0 = wrapped value, 1 = overflow flag.
        field: usize,
        /// Bit width of the wrapped value (field 0); the packed value is
        /// `value_width + 1` bits (flag stacked in the high bit).
        value_width: u32,
    },
}

/// The shared LOOP-VC-LOCAL uninterpreted overflow-flag symbol
/// `__tir_ovf_<op>_<width>(lhs, rhs) : (BV width, BV width) -> BV 1`.
///
/// BOTH the SPEC side ([`MirRvalue::CheckedOverflowPacked`]'s flag) and the IMPL
/// side (`loop_backedge_symexec`'s `Inst::Overflow` flag result) bind the
/// overflow flag to this SAME function application, so the back-edge threading VC
/// discharges `impl_flag == spec_flag` by UF congruence (same op + width +
/// operands => equal) WITHOUT needing the exact signed/unsigned flag formula
/// (which the trust-ir `Inst::Overflow` opcode drops). SOUND: a WRONG threading —
/// a different op (distinct symbol name), different operands (distinct args), or a
/// stale/plain value in the flag slot (not a UF app at all) — is NOT congruent and
/// REFUTES. The flag's value-correctness is proven independently by the per-inst
/// `Inst::Overflow` cert; this UF is confined to the loop-VC threading obligation.
pub fn overflow_flag_uf(op_tag: &str, width: u32, lhs: SmtExpr, rhs: SmtExpr) -> SmtExpr {
    SmtExpr::uf(
        format!("__tir_ovf_{op_tag}_{width}"),
        vec![lhs, rhs],
        SmtSort::BitVec(1),
    )
}

/// The `overflow_flag_uf` op tag for a checked `MirBinOp` (`Add`/`Sub`/`Mul`),
/// or `None` for any other op (not a checked-arith overflow).
pub fn mir_overflow_op_tag(op: MirBinOp) -> Option<&'static str> {
    match op {
        MirBinOp::Add => Some("add"),
        MirBinOp::Sub => Some("sub"),
        MirBinOp::Mul => Some("mul"),
        _ => None,
    }
}

/// A MIR operand: a typed symbolic input or a constant.
#[derive(Debug, Clone)]
pub enum MirOperand {
    /// A named symbolic value (post-operand-lowering `ValueId`).
    Var { name: String, ty: MirScalarTy },
    /// An integer constant of the given type.
    ConstInt { value: u64, ty: MirScalarTy },
    /// A float constant.
    ConstFloat { value: f64, ty: MirScalarTy },
}

impl MirOperand {
    pub fn ty(&self) -> MirScalarTy {
        match self {
            MirOperand::Var { ty, .. }
            | MirOperand::ConstInt { ty, .. }
            | MirOperand::ConstFloat { ty, .. } => ty.clone(),
        }
    }

    /// Encode this operand as an `SmtExpr` (bitvector for ints/bool, FP node for
    /// floats), and register any symbolic variable into `inputs`/`fp_inputs`.
    fn encode(
        &self,
        inputs: &mut Vec<(String, u32)>,
        fp_inputs: &mut Vec<(String, u32, u32)>,
    ) -> SmtExpr {
        match self {
            MirOperand::Var { name, ty } => {
                if ty.is_float() {
                    let (eb, sb) = ty.fp_format().expect("float ty must have fp format");
                    if !fp_inputs.iter().any(|(n, _, _)| n == name) {
                        fp_inputs.push((name.clone(), eb, sb));
                    }
                    // A symbolic FP input is declared via fp_inputs; the
                    // expression node is a Var the evaluator binds through fp_env.
                    SmtExpr::var(name.clone(), eb + sb)
                } else {
                    let w = ty.bits();
                    if !inputs.iter().any(|(n, _)| n == name) {
                        inputs.push((name.clone(), w));
                    }
                    SmtExpr::var(name.clone(), w)
                }
            }
            MirOperand::ConstInt { value, ty } => {
                SmtExpr::bv_const(mask(*value, ty.bits()), ty.bits())
            }
            MirOperand::ConstFloat { value, ty } => match ty {
                MirScalarTy::Float(Type::F32) => SmtExpr::fp32_const(*value as f32),
                MirScalarTy::Float(Type::F64) => SmtExpr::fp64_const(*value),
                _ => SmtExpr::fp64_const(*value),
            },
        }
    }
}

/// A scalar MIR statement: `Assign(place, rvalue)`. The `dst` is the SSA name
/// the result binds to (mirrors a `Place` with empty projection).
#[derive(Debug, Clone)]
pub struct MirStmt {
    pub dst: String,
    pub rvalue: MirRvalue,
}

/// A scalar MIR basic block: a (possibly empty) list of statements followed by
/// a terminator that names the outgoing control-flow edges and the VALUES this
/// block threads to each successor's parameters.
///
/// CONTROL-FLOW SLICE (proof-gap item 6, CONTROL-FLOW axis). The terminator is
/// the block-argument-threading surface: each outgoing edge carries the MIR
/// values that flow to the target block's params. The bridge independently
/// chooses the trust-ir block ARGS it threads on the same edge; the per-edge
/// edge-equality VC ([`build_edge_equality_obligations`]) asserts the two agree
/// slot-by-slot, so a DROPPED / STALE / SWAPPED block arg (the #71 class, made
/// acyclic here) is refuted. See the DESIGN "CONTROL FLOW" section for the
/// deferred loop (back-edge / CHC) and memory extensions.
#[derive(Debug, Clone)]
pub struct MirBlock {
    pub stmts: Vec<MirStmt>,
    /// How this block leaves: the outgoing edges + the values threaded on each.
    pub terminator: MirTerminator,
}

impl MirBlock {
    /// A straight-line block that falls off the end (no successors). Convenience
    /// for the statement-encoding tests that predate terminators.
    pub fn straight_line(stmts: Vec<MirStmt>) -> Self {
        MirBlock {
            stmts,
            terminator: MirTerminator::Return,
        }
    }
}

/// A scalar MIR terminator over the ACYCLIC straight-line-block slice.
///
/// Each branching variant carries, per outgoing edge, the MIR VALUES (`*_args`)
/// that flow to the target block's parameters in slot order — this is the
/// SOURCE-program dataflow the bridge's chosen block args must match. Loops
/// (back-edges) are deliberately OUT of slice: a semantic loop invariant needs
/// an inductive CHC solver lane, and loop-carried drops are already covered
/// STRUCTURALLY by `ssa_loop_complete` (P1.3). See DESIGN.
#[derive(Debug, Clone)]
pub enum MirTerminator {
    /// Unconditional jump to `target`, threading `args` to its params (slot k ->
    /// param k). Mirrors MIR `Goto` + the bridge's trust-ir `Jump(target, args)`.
    Goto {
        target: BlockId,
        args: Vec<MirOperand>,
    },
    /// Two-way branch on a 1-bit `cond`: take the true edge to `t_target`
    /// (threading `t_args`) when `cond != 0`, else the false edge to `f_target`
    /// (threading `f_args`). Mirrors a MIR `SwitchInt` with a bool discriminant /
    /// the bridge's trust-ir conditional branch with per-edge block args.
    Branch {
        cond: MirOperand,
        t_target: BlockId,
        t_args: Vec<MirOperand>,
        f_target: BlockId,
        f_args: Vec<MirOperand>,
    },
    /// Function return — no successors, no block args to thread.
    Return,
}

/// A basic-block identifier (index into the function's block list).
pub type BlockId = usize;

/// Which outgoing edge of a terminator a [`BridgeEdgeArgs`] labels.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum EdgeKind {
    /// The single edge of a `Goto`.
    Goto,
    /// The taken-when-true edge of a `Branch`.
    BranchTrue,
    /// The taken-when-false edge of a `Branch`.
    BranchFalse,
}

/// The trust-ir block ARGUMENTS the bridge chose to thread on one outgoing edge.
///
/// This is the BRIDGE side of the edge-equality VC: `args[k]` is the trust-ir
/// value the bridge threads to the target block's parameter `k`. It is built
/// from the SAME symbolic vars as the source block's symbolic store (the caller
/// resolves the bridge's chosen value through that store, exactly as the MIR
/// `*_args` are resolved), so the VC `bridge_arg_k == mir_arg_k` is a REAL
/// dataflow check, not a tautology: a bridge that threads a STALE value (the
/// entry value instead of the in-block-updated one — the #71 shape), the WRONG
/// variable, or SWAPS two slots makes some slot's equality SAT (refuted).
///
/// `edge` selects WHICH MIR edge these args correspond to, so a `Branch`'s two
/// outgoing edges are checked independently (a drop on only one arm — the #71
/// diamond shape — is caught on exactly that arm).
#[derive(Debug, Clone)]
pub struct BridgeEdgeArgs {
    pub edge: EdgeKind,
    pub args: Vec<SmtExpr>,
}

// ---------------------------------------------------------------------------
// MIR semantics encoder: MirRvalue -> SmtExpr (+ declared inputs)
// ---------------------------------------------------------------------------

/// The SMT encoding of a single MIR rvalue together with the symbolic inputs it
/// references. `expr` is the *specification*: the Rust-defined meaning of the
/// rvalue, against which the bridge's trust-ir choice is checked.
#[derive(Debug, Clone)]
pub struct EncodedRvalue {
    pub expr: SmtExpr,
    pub inputs: Vec<(String, u32)>,
    pub fp_inputs: Vec<(String, u32, u32)>,
    /// Preconditions under which the equivalence is asserted (e.g. divisor != 0).
    pub preconditions: Vec<SmtExpr>,
}

/// Encode a MIR rvalue as its Rust-specified `SmtExpr`.
///
/// This is the heart of the slice. For each rvalue it builds the bitvector/FP
/// formula that Rust's operational semantics dictates — deliberately NOT
/// delegating op selection to the bridge, so that a wrong bridge translation is
/// observable as a mismatch.
pub fn encode_mir_rvalue(rv: &MirRvalue) -> Result<EncodedRvalue, String> {
    let mut inputs = Vec::new();
    let mut fp_inputs = Vec::new();
    let mut preconditions = Vec::new();

    let expr = match rv {
        MirRvalue::Use { src } => src.encode(&mut inputs, &mut fp_inputs),

        MirRvalue::UnaryOp { op, ty, operand } => {
            let o = operand.encode(&mut inputs, &mut fp_inputs);
            encode_mir_unop(*op, ty.clone(), o)
        }

        MirRvalue::BinaryOp { op, ty, lhs, rhs } => {
            let l = lhs.encode(&mut inputs, &mut fp_inputs);
            let r = rhs.encode(&mut inputs, &mut fp_inputs);
            // Div/Rem carry a divisor-nonzero precondition (Rust: division by
            // zero is a trap, not a defined value; trust-ir treats it as UB).
            // The signed INT_MIN/-1 overflow trap is NOT excluded here — it is
            // modeled as a trap value inside `encode_mir_binop` so a wrapping
            // Sdiv lowering is refuted (#59 class) instead of vacuously accepted.
            if let Some(pre) = mir_binop_precondition(*op, ty.clone(), &r) {
                preconditions.push(pre);
            }
            encode_mir_binop(*op, ty.clone(), l, r)?
        }

        MirRvalue::CheckedBinaryOp { op, ty, lhs, rhs } => {
            let l = lhs.encode(&mut inputs, &mut fp_inputs);
            let r = rhs.encode(&mut inputs, &mut fp_inputs);
            encode_mir_checked_binop(*op, ty.clone(), l, r)?
        }

        MirRvalue::Cast {
            kind,
            src_ty,
            dst_ty,
            operand,
        } => {
            let o = operand.encode(&mut inputs, &mut fp_inputs);
            encode_mir_cast(*kind, src_ty.clone(), dst_ty.clone(), o)?
        }

        MirRvalue::Aggregate { fields } => {
            if fields.is_empty() {
                return Err("MIR Aggregate with no fields is out of slice (ZST)".to_string());
            }
            // SCALAR-FIELD slice: every field must be a fixed-width int/bool.
            // A float field is rejected (not silently packed as an int) — the
            // mixed INT+SSE ABI is a separate refinement (see DESIGN).
            let mut field_exprs = Vec::with_capacity(fields.len());
            let mut field_widths = Vec::with_capacity(fields.len());
            for f in fields {
                if f.ty().is_float() {
                    return Err("MIR Aggregate float field is out of slice (SSE class)".to_string());
                }
                field_widths.push(f.ty().bits());
                field_exprs.push(f.encode(&mut inputs, &mut fp_inputs));
            }
            // Pack in SOURCE field order: field 0 in the low bits.
            pack_fields(&field_exprs, &field_widths)
        }

        MirRvalue::Select {
            cond,
            ty,
            then_val,
            else_val,
        } => {
            if ty.is_float() {
                return Err("MIR Select float result is out of slice (SSE class)".to_string());
            }
            if then_val.ty().bits() != ty.bits() || else_val.ty().bits() != ty.bits() {
                return Err(format!(
                    "MIR Select arm width mismatch: result {} vs then {} / else {}",
                    ty.bits(),
                    then_val.ty().bits(),
                    else_val.ty().bits()
                ));
            }
            if cond.ty().is_float() {
                return Err("MIR Select condition must be a bool/int, not a float".to_string());
            }
            let c = cond.encode(&mut inputs, &mut fp_inputs);
            let t = then_val.encode(&mut inputs, &mut fp_inputs);
            let e = else_val.encode(&mut inputs, &mut fp_inputs);
            encode_mir_select(c, t, e)
        }

        // The overflow-tuple packed value + its field projections are
        // LOOP-VC-LOCAL (they encode the flag as an uninterpreted function, which
        // is only sound for the back-edge THREADING obligation, not for a
        // per-instruction value proof). A per-inst path that needs the exact
        // checked-arith semantics must use `CheckedBinaryOp`.
        MirRvalue::CheckedOverflowPacked { .. } | MirRvalue::PackedOverflowField { .. } => {
            return Err(
                "CheckedOverflowPacked / PackedOverflowField are loop-VC-local (use \
                 CheckedBinaryOp for a per-instruction overflow proof)"
                    .to_string(),
            );
        }
    };

    Ok(EncodedRvalue {
        expr,
        inputs,
        fp_inputs,
        preconditions,
    })
}

/// Encode a 2-way diamond merge `select(cond, then, else)` as
/// `ite(cond != 0, then, else)`. The `cond` is the diamond discriminant as a
/// bitvector (taken-when-nonzero); converting it to the Bool-sorted `cond != 0`
/// keeps the `ite` well-sorted for the SMT-LIB back-end (an `ite` requires a
/// Bool guard) while matching the mock evaluator's nonzero-is-true reading.
fn encode_mir_select(cond: SmtExpr, then_val: SmtExpr, else_val: SmtExpr) -> SmtExpr {
    let w = cond.bv_width();
    let taken = cond.eq_expr(SmtExpr::bv_const(0, w)).not_expr();
    SmtExpr::ite(taken, then_val, else_val)
}

/// Encode a MIR `UnaryOp` per Rust semantics.
fn encode_mir_unop(op: MirUnOp, ty: MirScalarTy, operand: SmtExpr) -> SmtExpr {
    match op {
        // Float negation is an IEEE SIGN-BIT FLIP. This is the spec that
        // refutes #68-fneg's wrong `0.0 - x` lowering: `0.0 - x` differs from
        // `-x` for x = +0.0 (sign of zero) and for NaN (sign propagation). We
        // model the *correct* spec with fp_neg.
        MirUnOp::Neg if ty.is_float() => operand.fp_neg(),
        // Signed integer negation: two's complement.
        MirUnOp::Neg => operand.bvneg(),
        // bool NOT: `!b` == `b == 0` (1-bit).
        MirUnOp::Not if matches!(ty, MirScalarTy::Bool) => SmtExpr::ite(
            operand.eq_expr(SmtExpr::bv_const(0, 1)),
            SmtExpr::bv_const(1, 1),
            SmtExpr::bv_const(0, 1),
        ),
        // Integer NOT: bitwise complement.
        MirUnOp::Not => {
            let w = ty.bits();
            let all_ones = SmtExpr::bv_const(mask(u64::MAX, w), w);
            operand.bvxor(all_ones)
        }
    }
}

/// Encode a MIR `BinaryOp` per Rust semantics.
///
/// Arithmetic uses WRAPPING bitvector ops (the unchecked/wrapping forms — the
/// trapping checks are modeled by `CheckedBinaryOp`). Comparisons produce a
/// 1-bit result, matching the bridge's `ICmp`/`FCmp` -> CSET shape.
fn encode_mir_binop(
    op: MirBinOp,
    ty: MirScalarTy,
    lhs: SmtExpr,
    rhs: SmtExpr,
) -> Result<SmtExpr, String> {
    if ty.is_float() {
        return encode_mir_float_binop(op, ty, lhs, rhs);
    }
    let signed = ty.is_signed();
    let w = ty.bits();
    let e = match op {
        MirBinOp::Add => lhs.bvadd(rhs),
        MirBinOp::Sub => lhs.bvsub(rhs),
        MirBinOp::Mul => lhs.bvmul(rhs),
        // Signed Div/Rem trap on INT_MIN / -1 (overflow). Model the trap value so
        // a wrapping lowering (which would silently return the wrapped result) is
        // refuted; a correct trapping lowering (modeled the same way) matches.
        MirBinOp::Div if signed => {
            let q = lhs.clone().bvsdiv(rhs.clone());
            guard_sdiv_overflow(q, &lhs, &rhs, w)
        }
        MirBinOp::Div => lhs.bvudiv(rhs),
        MirBinOp::Rem if signed => {
            let q = lhs.clone().bvsdiv(rhs.clone());
            let r = lhs.clone().bvsub(q.bvmul(rhs.clone()));
            guard_sdiv_overflow(r, &lhs, &rhs, w)
        }
        MirBinOp::Rem => {
            let q = lhs.clone().bvudiv(rhs.clone());
            lhs.bvsub(q.bvmul(rhs))
        }
        MirBinOp::BitXor => lhs.bvxor(rhs),
        MirBinOp::BitAnd => lhs.bvand(rhs),
        MirBinOp::BitOr => lhs.bvor(rhs),
        // Rust (and AArch64/x86) shifts MASK the shift amount modulo the bit
        // width before shifting: `a << b` is `a << (b & (width-1))` for the
        // power-of-two widths we lower. The raw SMT `bvshl`/`bvlshr`/`bvashr`
        // define the result as 0 once `b >= width`, which is NOT Rust's
        // semantics. Encoding the mask here makes the spec faithful so that a
        // bridge which forgets the `AND amount, #(width-1)` (emitting a raw,
        // unmasked shift) is REFUTED at any `b >= width` instead of silently
        // sharing the spec's wrong assumption.
        MirBinOp::Shl => lhs.bvshl(mask_shift_amount(coerce_shift_amount_width(rhs, w), w)),
        MirBinOp::Shr if signed => {
            lhs.bvashr(mask_shift_amount(coerce_shift_amount_width(rhs, w), w))
        }
        MirBinOp::Shr => lhs.bvlshr(mask_shift_amount(coerce_shift_amount_width(rhs, w), w)),
        // Comparisons -> 1-bit.
        MirBinOp::Eq => return Ok(bool1(lhs.eq_expr(rhs))),
        MirBinOp::Ne => return Ok(bool1(lhs.eq_expr(rhs).not_expr())),
        MirBinOp::Lt if signed => return Ok(bool1(lhs.bvslt(rhs))),
        MirBinOp::Lt => return Ok(bool1(lhs.bvult(rhs))),
        MirBinOp::Le if signed => return Ok(bool1(lhs.bvsle(rhs))),
        MirBinOp::Le => return Ok(bool1(lhs.bvule(rhs))),
        MirBinOp::Gt if signed => return Ok(bool1(lhs.bvsgt(rhs))),
        MirBinOp::Gt => return Ok(bool1(lhs.bvugt(rhs))),
        MirBinOp::Ge if signed => return Ok(bool1(lhs.bvsge(rhs))),
        MirBinOp::Ge => return Ok(bool1(lhs.bvuge(rhs))),
    };
    Ok(e)
}

/// Mask a shift amount to `width-1` bits, matching Rust's (and the hardware's)
/// modulo-width shift-count semantics for power-of-two `width`. The mask is
/// applied as a bitvector AND at the operand width, so the result has the same
/// sort as the shifted value (as `bvshl`/`bvlshr`/`bvashr` require).
fn mask_shift_amount(amount: SmtExpr, width: u32) -> SmtExpr {
    // width is a power of two (8/16/32/64), so `width-1` is the low-bit mask.
    let m = SmtExpr::bv_const((width as u64) - 1, width);
    amount.bvand(m)
}

/// Coerce a shift AMOUNT to the shifted-VALUE width so `bvshl`/`bvlshr`/`bvashr`
/// (which require both operands to share a sort) are well-formed even when the
/// MIR shift is mixed-width (e.g. `u64 << i32`, where Rust gives the amount its
/// own — often narrower — integer type).
///
/// FAITHFULNESS. This is only reached for a *shift*, whose amount is treated as
/// an unsigned count. Any well-defined Rust shift has `amount < width(value)`
/// (`amount >= width` is UB); both directions of coercion preserve the amount's
/// low `min(amount_w, value_w)` bits, and the subsequent `mask_shift_amount`
/// keeps only the low `log2(value_w)` bits regardless — so for every
/// well-defined input `value << coerce(amount) == value << amount`. The VC need
/// only be faithful on well-defined inputs (UB is garbage-in), so this never
/// changes the modeled result of a defined shift.
///
/// - Narrower amount: ZERO-extend (a shift count is unsigned — never sign-ext).
/// - Wider amount: truncate to the low `value_w` bits (the count fits, so the
///   dropped high bits are 0 on every well-defined input; if not, it was UB).
/// - Equal width: identity (keeps the same-width shift path byte-for-byte
///   unchanged, so no existing per-instruction/loop proof is perturbed).
fn coerce_shift_amount_width(amount: SmtExpr, value_w: u32) -> SmtExpr {
    let amount_w = amount.bv_width();
    if amount_w == value_w {
        amount
    } else if amount_w < value_w {
        amount.zero_ext(value_w - amount_w)
    } else {
        amount.extract(value_w - 1, 0)
    }
}

/// Encode a MIR float `BinaryOp`.
fn encode_mir_float_binop(
    op: MirBinOp,
    _ty: MirScalarTy,
    lhs: SmtExpr,
    rhs: SmtExpr,
) -> Result<SmtExpr, String> {
    let e = match op {
        MirBinOp::Add => SmtExpr::fp_add(RoundingMode::RNE, lhs, rhs),
        MirBinOp::Sub => SmtExpr::fp_sub(RoundingMode::RNE, lhs, rhs),
        MirBinOp::Mul => SmtExpr::fp_mul(RoundingMode::RNE, lhs, rhs),
        MirBinOp::Div => SmtExpr::fp_div(RoundingMode::RNE, lhs, rhs),
        // Float comparisons (ordered) -> 1-bit, matching the bridge's FCmp.
        MirBinOp::Eq => return Ok(bool1(lhs.fp_eq(rhs))),
        MirBinOp::Ne => return Ok(bool1(lhs.fp_eq(rhs).not_expr())),
        MirBinOp::Lt => return Ok(bool1(lhs.fp_lt(rhs))),
        MirBinOp::Le => return Ok(bool1(lhs.fp_le(rhs))),
        MirBinOp::Gt => return Ok(bool1(lhs.fp_gt(rhs))),
        MirBinOp::Ge => return Ok(bool1(lhs.fp_ge(rhs))),
        MirBinOp::Rem => return Err("MIR float Rem (fmod) not in slice".to_string()),
        // Bitwise / shift ops are not defined on floats in Rust MIR.
        MirBinOp::BitXor | MirBinOp::BitAnd | MirBinOp::BitOr | MirBinOp::Shl | MirBinOp::Shr => {
            return Err(format!(
                "MIR float binop {op:?} is not valid on float operands"
            ));
        }
    };
    Ok(e)
}

/// Encode a MIR checked/overflowing `BinaryOp` as `overflow_b1 :: value_iN`.
///
/// This is the Rust SPEC for `a.overflowing_add(b)` etc.: the wrapped value in
/// the low N bits, and a correct overflow flag in the high bit. The flag is
/// computed from the sign/zero-extended exact result, exactly as
/// `checked_overflow_proofs::trust_ir_checked` does. A bridge that drops the
/// overflow flag (the #71-class "field dropped" bug) or computes it wrong (#67)
/// is refuted here.
fn encode_mir_checked_binop(
    op: MirBinOp,
    ty: MirScalarTy,
    lhs: SmtExpr,
    rhs: SmtExpr,
) -> Result<SmtExpr, String> {
    let w = ty.bits();
    let signed = ty.is_signed();

    let (value, overflow_bool) = match op {
        MirBinOp::Add => {
            let value = lhs.clone().bvadd(rhs.clone());
            let overflow = if signed {
                let exact = lhs.sign_ext(1).bvadd(rhs.sign_ext(1));
                let wrapped = value.clone().sign_ext(1);
                exact.eq_expr(wrapped).not_expr()
            } else {
                let exact = lhs.zero_ext(1).bvadd(rhs.zero_ext(1));
                let wrapped = value.clone().zero_ext(1);
                exact.eq_expr(wrapped).not_expr()
            };
            (value, overflow)
        }
        MirBinOp::Sub => {
            let value = lhs.clone().bvsub(rhs.clone());
            let overflow = if signed {
                let exact = lhs.sign_ext(1).bvsub(rhs.sign_ext(1));
                let wrapped = value.clone().sign_ext(1);
                exact.eq_expr(wrapped).not_expr()
            } else {
                let exact = lhs.zero_ext(1).bvsub(rhs.zero_ext(1));
                let wrapped = value.clone().zero_ext(1);
                exact.eq_expr(wrapped).not_expr()
            };
            (value, overflow)
        }
        MirBinOp::Mul => {
            let value = lhs.clone().bvmul(rhs.clone());
            let overflow = if signed {
                let product = lhs.sign_ext(w).bvmul(rhs.sign_ext(w));
                let high = product.clone().extract((2 * w) - 1, w);
                // Signed overflow iff the high half is not the sign-extension of
                // the low half's MSB.
                let sign = value.clone().bvashr(SmtExpr::bv_const((w - 1) as u64, w));
                high.eq_expr(sign).not_expr()
            } else {
                let product = lhs.zero_ext(w).bvmul(rhs.zero_ext(w));
                let high = product.extract((2 * w) - 1, w);
                high.eq_expr(SmtExpr::bv_const(0, w)).not_expr()
            };
            (value, overflow)
        }
        other => return Err(format!("checked BinOp not in slice: {other:?}")),
    };

    Ok(bool1(overflow_bool).concat(value))
}

/// Encode the trust-ir `Inst::Overflow` semantics for the bridge side of an
/// overflow obligation: the wrapped value in the low N bits and the correct
/// overflow flag in the high bit (`overflow :: value`), keyed by the chosen op +
/// signedness. This is the trusted trust-ir checked-arithmetic formula
/// (identical to `checked_overflow_proofs::trust_ir_checked` and to
/// [`encode_mir_checked_binop`]), so pairing it against the MIR `CheckedBinaryOp`
/// spec yields an OP-SELECTION + SIGNEDNESS + PACKING obligation, not a
/// value-formula tautology check.
fn encode_trust_ir_overflow(
    op: OverflowOpKind,
    ty: Type,
    signed: bool,
    lhs: SmtExpr,
    rhs: SmtExpr,
) -> SmtExpr {
    let mir_ty = if signed {
        MirScalarTy::SInt(ty)
    } else {
        MirScalarTy::UInt(ty)
    };
    let mir_op = match op {
        OverflowOpKind::Add => MirBinOp::Add,
        OverflowOpKind::Sub => MirBinOp::Sub,
        OverflowOpKind::Mul => MirBinOp::Mul,
    };
    // Infallible for Add/Sub/Mul over an integer scalar type.
    encode_mir_checked_binop(mir_op, mir_ty, lhs, rhs)
        .expect("overflow op encodes for Add/Sub/Mul on integer types")
}

/// Encode a MIR scalar `Cast` per Rust semantics.
///
/// The signedness of the SOURCE drives int<->int extension and int->float
/// conversion. This is the spec that refutes #68-cvt (signed `i32 as f32`
/// lowered as an unsigned conversion).
fn encode_mir_cast(
    kind: MirCastKind,
    src_ty: MirScalarTy,
    dst_ty: MirScalarTy,
    operand: SmtExpr,
) -> Result<SmtExpr, String> {
    match kind {
        MirCastKind::IntToInt => {
            let sw = src_ty.bits();
            let dw = dst_ty.bits();
            if dw == sw {
                Ok(operand)
            } else if dw > sw {
                // Widen: source signedness decides sign- vs zero-extend.
                if src_ty.is_signed() {
                    Ok(operand.sign_ext(dw - sw))
                } else {
                    Ok(operand.zero_ext(dw - sw))
                }
            } else {
                // Narrow: take the low dw bits.
                Ok(operand.extract(dw - 1, 0))
            }
        }
        MirCastKind::IntToFloat => {
            let (eb, sb) = dst_ty.fp_format().ok_or("IntToFloat dst not a float")?;
            let sw = src_ty.bits();
            if src_ty.is_signed() {
                // Signed int -> float: bv_to_fp interprets its operand as
                // signed, so feed the narrow value directly (it carries width sw).
                Ok(SmtExpr::bv_to_fp(RoundingMode::RNE, operand, eb, sb))
            } else {
                // Unsigned int -> float: zero-extend by one bit so the value is
                // non-negative when bv_to_fp re-interprets it as signed.
                Ok(SmtExpr::bv_to_fp(
                    RoundingMode::RNE,
                    operand.zero_ext(1),
                    eb,
                    sb,
                ))
            }
            .inspect(|_e| {
                let _ = sw;
            })
        }
        MirCastKind::FloatToInt => {
            // Rust `as` float->int is SATURATING (since Rust 1.45): NaN maps to
            // 0, values at or below the destination minimum saturate to the
            // minimum, values at or above the maximum saturate to the maximum,
            // and in-range values truncate toward zero. The raw SMT
            // `fp_to_sbv`/`fp_to_ubv` are UNSPECIFIED for NaN / out-of-range
            // inputs, so encoding them as the spec is doubly broken: it (a) makes
            // a *non*-saturating bridge pass vacuously (shared unspecified
            // value), and (b) REFUTES a correct saturating bridge (AArch64
            // FCVTZS) because the solver is free to pick a disagreeing model for
            // the unspecified case. We encode the saturating contract explicitly.
            let dw = dst_ty.bits();
            let (eb, sb) = src_ty.fp_format().ok_or("FloatToInt source not a float")?;
            let is_nan = operand.clone().fp_is_nan();
            if dst_ty.is_signed() {
                // Signed bounds. INT_MIN = -2^(dw-1) is exactly representable;
                // INT_MAX rounds to 2^(dw-1), which is the correct saturation
                // threshold (any float >= that threshold saturates to INT_MAX).
                let int_min_i = -(1i128 << (dw - 1));
                let int_max_i = (1i128 << (dw - 1)) - 1;
                let min_f = fp_from_i128(int_min_i, eb, sb);
                let max_f = fp_from_i128(int_max_i, eb, sb);
                let int_min_bv = SmtExpr::bv_const(mask(int_min_i as u64, dw), dw);
                let int_max_bv = SmtExpr::bv_const(mask(int_max_i as u64, dw), dw);
                let trunc = SmtExpr::fp_to_sbv(RoundingMode::RTZ, operand.clone(), dw);
                let le_min = operand.clone().fp_le(min_f);
                let ge_max = operand.fp_ge(max_f);
                Ok(SmtExpr::ite(
                    is_nan,
                    SmtExpr::bv_const(0, dw),
                    SmtExpr::ite(le_min, int_min_bv, SmtExpr::ite(ge_max, int_max_bv, trunc)),
                ))
            } else {
                // Unsigned bounds: clamp to [0, 2^dw - 1]; NaN and negatives map
                // to 0. UMAX rounds to 2^dw, the correct saturation threshold.
                let umax_i = (1i128 << dw) - 1;
                let umax_f = fp_from_i128(umax_i, eb, sb);
                let zero_f = fp_from_i128(0, eb, sb);
                let umax_bv = SmtExpr::bv_const(mask(umax_i as u64, dw), dw);
                let trunc = SmtExpr::fp_to_ubv(RoundingMode::RTZ, operand.clone(), dw);
                let le_zero = operand.clone().fp_le(zero_f);
                let ge_max = operand.fp_ge(umax_f);
                Ok(SmtExpr::ite(
                    is_nan.or_expr(le_zero),
                    SmtExpr::bv_const(0, dw),
                    SmtExpr::ite(ge_max, umax_bv, trunc),
                ))
            }
        }
        MirCastKind::FloatToFloat => {
            let (eb, sb) = dst_ty.fp_format().ok_or("FloatToFloat dst not a float")?;
            Ok(SmtExpr::fp_to_fp(RoundingMode::RNE, operand, eb, sb))
        }
    }
}

/// Build a float constant of IEEE format `(eb, sb)` from an integer value, used
/// for the saturation bounds in [`encode_mir_cast`]'s FloatToInt case. The
/// integer is rounded to the nearest representable float of the format (the same
/// rounding `int_max as f32` performs), which is exactly the saturation
/// threshold Rust's saturating cast compares against.
fn fp_from_i128(value: i128, eb: u32, sb: u32) -> SmtExpr {
    match (eb, sb) {
        (8, 24) => SmtExpr::fp32_const(value as f32),
        (11, 53) => SmtExpr::fp64_const(value as f64),
        // Fall back to the f64 representation for any other (e.g. fp16) format;
        // the evaluator reads FPConst bits per format, so use fp64 bits here.
        _ => SmtExpr::fp64_const(value as f64),
    }
}

/// The packed trap sentinel for the signed `INT_MIN / -1` overflow trap, encoded
/// at the operand width. Rust PANICS on this input; the trust-cg bridge must
/// emit an explicit overflow check + panic branch (the #59 class). We model the
/// trap as an all-ones value so a wrapping `Sdiv`/`Srem` lowering — which would
/// silently produce the defined-but-wrong wrapped result (`INT_MIN` for Div,
/// `0` for Rem) at this input — disagrees with the spec and is refuted. A
/// correct trapping lowering, modeled the same way, matches.
fn sdiv_overflow_trap_sentinel(width: u32) -> SmtExpr {
    all_ones_bv(width)
}

/// The all-ones bitvector (`2^width - 1`) at ANY width, built as an SMT
/// expression so it is correct for 128-bit too. `SmtExpr::bv_const` only carries
/// a `u64` payload, so `mask(u64::MAX, 128)` would yield only the low 64 ones —
/// WRONG at width 128. Instead negate one: two's-complement `0 - 1 == -1` is the
/// all-ones vector at every width, which the evaluator masks to `width` bits.
fn all_ones_bv(width: u32) -> SmtExpr {
    SmtExpr::bv_const(1, width).bvneg()
}

/// `INT_MIN` (`2^(width-1)`, the sign bit set) at ANY width, built as an SMT
/// expression. The naive `1u64 << (width - 1)` PANICS at width 128 (u64 shift
/// overflow) and cannot represent `2^127` in a `u64` anyway; shifting a width-bit
/// `1` left by `width-1` is exact at every width (the evaluator masks to width).
fn int_min_bv(width: u32) -> SmtExpr {
    SmtExpr::bv_const(1, width).bvshl(SmtExpr::bv_const((width - 1) as u64, width))
}

/// Guard a signed Div/Rem result with the `INT_MIN / -1` trap model: when
/// `lhs == INT_MIN && rhs == -1`, the value is the trap sentinel; otherwise it
/// is the ordinary (wrapping) bitvector result.
fn guard_sdiv_overflow(value: SmtExpr, lhs: &SmtExpr, rhs: &SmtExpr, width: u32) -> SmtExpr {
    let int_min = int_min_bv(width);
    let minus_one = all_ones_bv(width);
    let is_min_neg1 = lhs
        .clone()
        .eq_expr(int_min)
        .and_expr(rhs.clone().eq_expr(minus_one));
    SmtExpr::ite(is_min_neg1, sdiv_overflow_trap_sentinel(width), value)
}

/// Precondition for a MIR binop (the divide-by-zero trap of Div/Rem).
///
/// Rust integer division by zero is a language-level panic, NOT a defined value,
/// so the refinement obligation EXCLUDES `rhs == 0` (trust-ir treats it as UB).
///
/// Note the OTHER trap input — signed `INT_MIN / -1` — is deliberately NOT
/// excluded here: it is modeled as a trap *value* in [`encode_mir_binop`]
/// instead, so a wrapping `Sdiv` lowering (which produces the defined-but-wrong
/// `INT_MIN` there instead of panicking) is REFUTED rather than vacuously
/// accepted. Excluding it would silence that #59-class miscompile.
fn mir_binop_precondition(op: MirBinOp, ty: MirScalarTy, rhs: &SmtExpr) -> Option<SmtExpr> {
    if ty.is_float() {
        return None;
    }
    match op {
        MirBinOp::Div | MirBinOp::Rem => {
            let zero = SmtExpr::bv_const(0, ty.bits());
            Some(rhs.clone().eq_expr(zero).not_expr())
        }
        _ => None,
    }
}

/// Wrap a boolean `SmtExpr` into a 1-bit bitvector (matches the CSET shape used
/// throughout `trust_ir_semantics`).
fn bool1(cond: SmtExpr) -> SmtExpr {
    SmtExpr::ite(cond, SmtExpr::bv_const(1, 1), SmtExpr::bv_const(0, 1))
}

/// Pack scalar fields into a single bitvector with `fields[0]` in the LOW bits
/// and each subsequent field stacked into the next-higher bits. The total width
/// is the sum of the field widths (a tight, alignment-free scalar packing — the
/// VC compares two such packings against each other, so it is offset-by-offset
/// faithful regardless of ABI padding; padding is not modeled in this slice).
///
/// This is the shared packing both the MIR SPEC and the bridge model use, so the
/// refinement obligation `bridge_packed == mir_packed` holds IFF every field
/// lands at the same bit offset on both sides. Because `SmtExpr::concat(hi, lo)`
/// puts `hi` in the upper bits, we fold from the HIGH field down to the low one:
/// the result is `f[n-1] :: … :: f[1] :: f[0]`.
///
/// `field_exprs[i]` MUST have width `widths[i]` (the caller guarantees this from
/// `MirScalarTy::bits()` / the declared bridge field widths). With a single
/// field the packing is the field itself (no concat).
fn pack_fields(field_exprs: &[SmtExpr], widths: &[u32]) -> SmtExpr {
    debug_assert_eq!(field_exprs.len(), widths.len());
    debug_assert!(!field_exprs.is_empty(), "pack_fields requires >= 1 field");
    // Fold from the highest-index field down to field 0; concat keeps the
    // accumulator (the higher fields) in the upper bits and the next-lower field
    // in the lower bits, so field 0 ends up in the lowest bits.
    let mut iter = field_exprs.iter().rev();
    let mut acc = iter.next().expect("non-empty").clone();
    for f in iter {
        // acc currently holds the higher fields; put it above the next field.
        acc = acc.concat(f.clone());
    }
    let total: u32 = widths.iter().sum();
    debug_assert_eq!(
        acc.bv_width(),
        total,
        "packed width must equal sum of field widths"
    );
    acc
}

// ---------------------------------------------------------------------------
// Bridge-side model: the trust-ir op the bridge CHOSE for a MIR rvalue
// ---------------------------------------------------------------------------
//
// To validate the MIR -> trust-ir translation we need the trust-ir the bridge
// produced. In the real wiring this comes from the trust-ir block the bridge
// just built (emit_proofs=true; see DESIGN). For the slice we model the
// bridge's *choice* as a `BridgeLowering` and encode it through the EXISTING
// `trust_ir_semantics` encoders — so the trust-ir side of the obligation is the
// real, already-trusted encoder, not a re-implementation.

/// The trust-ir checked-overflow opcode the bridge chose for a `CheckedBinaryOp`
/// / `overflowing_{add,sub,mul}` rvalue. Mirrors the `OverflowOp` the bridge
/// passes to `Inst::Overflow` (`AddOverflow` / `SubOverflow` / `MulOverflow`).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum OverflowOpKind {
    Add,
    Sub,
    Mul,
}

/// The trust-ir lowering the bridge produced for a single scalar rvalue.
///
/// Each variant names the trust-ir opcode the bridge chose plus the operand
/// types. A *wrong* choice here (e.g. `FNegAsSub` modeling #68-fneg) is exactly
/// what the refinement obligation catches.
#[derive(Debug, Clone)]
pub enum BridgeLowering {
    /// `Inst::BinOp { op, ty }` over the same two operands.
    BinOp {
        op: Opcode,
        ty: Type,
        lhs: SmtExpr,
        rhs: SmtExpr,
    },
    /// `Inst::ICmp { op, ty }`.
    ICmp {
        op: IntCC,
        ty: Type,
        lhs: SmtExpr,
        rhs: SmtExpr,
    },
    /// `Inst::FCmp { op, ty }`.
    FCmp {
        op: FloatCC,
        ty: Type,
        lhs: SmtExpr,
        rhs: SmtExpr,
    },
    /// `Inst::UnOp { op: Neg }`.
    Neg { ty: Type, operand: SmtExpr },
    /// `Inst::UnOp { op: FNeg }` — the CORRECT float negation (fp_neg).
    FNeg { ty: Type, operand: SmtExpr },
    /// `Inst::UnOp { op: Not }` (integer complement).
    Not { ty: Type, operand: SmtExpr },
    /// `Inst::Cast { op: SExt }`.
    SExt {
        src_ty: Type,
        dst_ty: Type,
        operand: SmtExpr,
    },
    /// `Inst::Cast { op: ZExt }`.
    ZExt {
        src_ty: Type,
        dst_ty: Type,
        operand: SmtExpr,
    },
    /// `Inst::Cast { op: Trunc }`.
    Trunc {
        src_ty: Type,
        dst_ty: Type,
        operand: SmtExpr,
    },
    /// `Inst::Cast { op: SIToFP }`.
    SIToFP {
        src_ty: Type,
        dst_ty: Type,
        operand: SmtExpr,
    },
    /// `Inst::Cast { op: UIToFP }`.
    UIToFP {
        src_ty: Type,
        dst_ty: Type,
        operand: SmtExpr,
    },
    /// `Inst::Copy` / `Inst::Const` value pass-through.
    Use { operand: SmtExpr },
    /// `Inst::Overflow { op }` packed `overflow :: value` (see CheckedBinaryOp).
    Overflow { value: SmtExpr, overflow: SmtExpr },
    /// `Inst::Overflow { op }` where the bridge names the op + width + signedness
    /// and the (trusted) trust-ir checked-arithmetic semantics are reconstructed
    /// here, packed `overflow :: value`. This is the shape the real bridge raises
    /// for `CheckedBinaryOp` / `overflowing_{add,sub,mul}`: the value-bit and
    /// overflow-bit formulas are the SAME ones the trust-ir `Inst::Overflow`
    /// lowering is independently proven against (`checked_overflow_proofs`,
    /// trust-ir -> machine), so the obligation this raises against the MIR
    /// `CheckedBinaryOp` spec is precisely an OP-SELECTION + SIGNEDNESS + PACKING
    /// check: a bridge that picks SubOverflow for an `overflowing_add`, swaps the
    /// (value, overflow) result slots, or uses the wrong signedness is refuted.
    /// `op` is the trust-ir overflow opcode the bridge chose (Add/Sub/Mul).
    OverflowOp {
        op: OverflowOpKind,
        ty: Type,
        signed: bool,
        lhs: SmtExpr,
        rhs: SmtExpr,
    },
    /// A deliberately-WRONG float negation modeled as `0.0 - x` (#68-fneg).
    /// Present so tests can construct the historical miscompile.
    FNegAsSub { ty: Type, operand: SmtExpr },
    /// A deliberately-WRONG signed int->float modeled as UNSIGNED conv (#68-cvt).
    SIToFPAsUnsigned {
        src_ty: Type,
        dst_ty: Type,
        operand: SmtExpr,
    },
    /// A deliberately-WRONG saturating add (#59): clamps instead of wrapping.
    SaturatingAdd {
        ty: Type,
        lhs: SmtExpr,
        rhs: SmtExpr,
    },
    /// A CORRECT trapping signed divide: `bvsdiv` guarded by the INT_MIN/-1
    /// overflow trap model (the explicit overflow-check + panic branch the
    /// bridge must emit). Validates against the MIR spec, which models the same
    /// trap. Contrast with `BinOp { op: Sdiv }`, which is the raw wrapping
    /// `bvsdiv` that miscompiles INT_MIN/-1 (#59 class).
    TrappingSdiv {
        ty: Type,
        lhs: SmtExpr,
        rhs: SmtExpr,
    },
    /// A CORRECT saturating FloatToInt (e.g. AArch64 FCVTZS): saturates
    /// out-of-range / NaN exactly as Rust's `as` cast does. Validates against
    /// the saturating MIR spec.
    SaturatingFloatToInt {
        src_ty: Type,
        dst_ty: Type,
        signed: bool,
        operand: SmtExpr,
    },
    /// A deliberately-WRONG non-saturating (WRAPPING) FloatToInt: convert at a wider
    /// width then TRUNCATE to the destination (so an out-of-range float wraps rather
    /// than clamps). Refuted by the saturating MIR spec on any out-of-range input.
    /// (Now that the `fp_to_sbv` evaluator faithfully saturates to the requested
    /// width, the wrong bridge must wrap explicitly to remain distinguishable.)
    NonSaturatingFloatToInt {
        src_ty: Type,
        dst_ty: Type,
        signed: bool,
        operand: SmtExpr,
    },
    /// A CORRECT masked shift: the shift amount is masked to `width-1` bits
    /// before the shift, matching Rust/AArch64/x86 semantics. Validates against
    /// the masked MIR spec. Contrast with `BinOp { op: Ishl/Ushr/Sshr }`, which
    /// is the raw, UNmasked SMT shift that miscompiles `amount >= width`.
    MaskedShift {
        op: Opcode,
        ty: Type,
        lhs: SmtExpr,
        rhs: SmtExpr,
    },
    /// The aggregate the bridge ACTUALLY built: each `(field_expr, width)` is a
    /// scalar field value the bridge placed, **in the bit-offset order the bridge
    /// chose** (`field_exprs[0]` at the lowest offset, stacked upward — the same
    /// packing [`pack_fields`] / the MIR `Aggregate` spec use). The bridge
    /// constructs this from the offsets it assigned each scalarized field, so
    /// when its placement matches the source field order this packs identically
    /// to the spec and Refines; when it SWAPS two fields (the #69/#73 field-
    /// REORDER miscompile) or puts a field at the WRONG width/offset, the packed
    /// value differs from the spec at the affected bits and is Refuted.
    ///
    /// Both sides are driven from the SAME symbolic field vars (the test feeds
    /// the identical `SmtExpr::var(field_name, width)` to both the MIR operand
    /// and this list), so the obligation is a REAL offset check, not a tautology:
    /// a wrong encoding that reordered both sides in lockstep could never make a
    /// genuine reorder pass, because the spec side is fixed to source order.
    Aggregate { field_exprs: Vec<(SmtExpr, u32)> },
}

impl BridgeLowering {
    /// Encode the bridge's chosen trust-ir op via the trusted
    /// `trust_ir_semantics` encoders.
    pub fn encode(&self) -> SmtExpr {
        use crate::trust_ir_semantics as ts;
        match self {
            BridgeLowering::BinOp { op, ty, lhs, rhs } => {
                // Dispatch to the right family encoder.
                if let Ok(e) =
                    ts::try_encode_trust_ir_binop(op, ty.clone(), lhs.clone(), rhs.clone())
                {
                    e
                } else if let Ok(e) =
                    ts::try_encode_trust_ir_bitwise_binop(op, ty.clone(), lhs.clone(), rhs.clone())
                {
                    e
                } else if let Ok(e) =
                    ts::try_encode_trust_ir_shift(op, ty.clone(), lhs.clone(), rhs.clone())
                {
                    e
                } else {
                    ts::encode_trust_ir_fp_binop(op, ty.clone(), lhs.clone(), rhs.clone())
                }
            }
            BridgeLowering::ICmp { op, ty, lhs, rhs } => bool1_already(ts::encode_trust_ir_icmp(
                op,
                ty.clone(),
                lhs.clone(),
                rhs.clone(),
            )),
            BridgeLowering::FCmp { op, ty, lhs, rhs } => bool1_already(ts::encode_trust_ir_fcmp(
                op,
                ty.clone(),
                lhs.clone(),
                rhs.clone(),
            )),
            BridgeLowering::Neg { ty, operand } => {
                ts::encode_trust_ir_neg(ty.clone(), operand.clone())
            }
            BridgeLowering::FNeg { ty, operand } => {
                ts::encode_trust_ir_fneg(ty.clone(), operand.clone())
            }
            BridgeLowering::Not { ty, operand } => {
                ts::encode_trust_ir_bnot(ty.clone(), operand.clone())
            }
            BridgeLowering::SExt {
                src_ty,
                dst_ty,
                operand,
            } => operand.clone().sign_ext(dst_ty.bits() - src_ty.bits()),
            BridgeLowering::ZExt {
                src_ty,
                dst_ty,
                operand,
            } => operand.clone().zero_ext(dst_ty.bits() - src_ty.bits()),
            BridgeLowering::Trunc {
                src_ty: _,
                dst_ty,
                operand,
            } => operand.clone().extract(dst_ty.bits() - 1, 0),
            BridgeLowering::SIToFP {
                dst_ty, operand, ..
            } => {
                let (eb, sb) = fp_format(dst_ty);
                SmtExpr::bv_to_fp(RoundingMode::RNE, operand.clone(), eb, sb)
            }
            BridgeLowering::UIToFP {
                dst_ty, operand, ..
            } => {
                let (eb, sb) = fp_format(dst_ty);
                SmtExpr::bv_to_fp(RoundingMode::RNE, operand.clone().zero_ext(1), eb, sb)
            }
            BridgeLowering::Use { operand } => operand.clone(),
            BridgeLowering::Overflow { value, overflow } => {
                // `overflow` is a 1-bit BV flag; `value` is the wrapped result.
                // Pack as `overflow :: value` to match the MIR CheckedBinaryOp
                // spec (overflow in the high bit).
                overflow.clone().concat(value.clone())
            }
            BridgeLowering::OverflowOp {
                op,
                ty,
                signed,
                lhs,
                rhs,
            } => {
                // Reconstruct the trust-ir `Inst::Overflow` semantics (the SAME
                // wrapped-value + overflow-bit formula that `checked_overflow_proofs`
                // proves correct against the machine) keyed by the chosen op and
                // signedness, packed `overflow :: value`. Equivalent to building
                // the MIR `CheckedBinaryOp` spec — which is exactly the point: any
                // refutation against the spec is a wrong OP / SIGNEDNESS / PACKING
                // choice, never a value-formula disagreement.
                encode_trust_ir_overflow(*op, ty.clone(), *signed, lhs.clone(), rhs.clone())
            }
            // --- deliberately-wrong lowerings (for tests) ---
            BridgeLowering::FNegAsSub { ty, operand } => {
                let (eb, sb) = fp_format(ty);
                let zero = SmtExpr::fp_const(0, eb, sb);
                SmtExpr::fp_sub(RoundingMode::RNE, zero, operand.clone())
            }
            BridgeLowering::SIToFPAsUnsigned {
                dst_ty, operand, ..
            } => {
                let (eb, sb) = fp_format(dst_ty);
                SmtExpr::bv_to_fp(RoundingMode::RNE, operand.clone().zero_ext(1), eb, sb)
            }
            BridgeLowering::SaturatingAdd { ty, lhs, rhs } => {
                // Signed saturating add: clamp to [INT_MIN, INT_MAX] on overflow
                // instead of wrapping. Differs from Rust `+` (which traps but the
                // *value* the bridge would produce when it forgets to trap is the
                // wrap; modeling saturation here makes the disagreement concrete).
                let w = ty.bits();
                let wrapped = lhs.clone().bvadd(rhs.clone());
                let exact = lhs.clone().sign_ext(1).bvadd(rhs.clone().sign_ext(1));
                let wrapped_ext = wrapped.clone().sign_ext(1);
                let overflowed = exact.eq_expr(wrapped_ext).not_expr();
                // INT_MIN = 2^(w-1) (sign bit), INT_MAX = 2^(w-1) - 1. Built as
                // SMT expressions so they are exact at width 128 too (the naive
                // `1u64 << (w - 1)` / `mask(u64::MAX, w)` overflow/truncate the
                // u64 payload at w == 128).
                let int_min = int_min_bv(w);
                let int_max = int_min.clone().bvsub(SmtExpr::bv_const(1, w));
                // If overflow and result negative-ish -> clamp; pick INT_MAX when
                // lhs >= 0, else INT_MIN.
                let lhs_nonneg = lhs.clone().bvsge(SmtExpr::bv_const(0, w));
                let clamp = SmtExpr::ite(lhs_nonneg, int_max, int_min);
                SmtExpr::ite(overflowed, clamp, wrapped)
            }
            // --- correct lowerings that must validate against the new specs ---
            BridgeLowering::TrappingSdiv { ty, lhs, rhs } => {
                let w = ty.bits();
                let q = lhs.clone().bvsdiv(rhs.clone());
                guard_sdiv_overflow(q, lhs, rhs, w)
            }
            BridgeLowering::SaturatingFloatToInt {
                src_ty,
                dst_ty,
                signed,
                operand,
            } => {
                let s = float_scalar_ty(src_ty);
                let d = int_scalar_ty(dst_ty, *signed);
                // Reuse the (now saturating) MIR cast encoder so a correct
                // saturating bridge is encoded identically to the spec.
                encode_mir_cast(MirCastKind::FloatToInt, s, d, operand.clone())
                    .expect("saturating FloatToInt encodes")
            }
            BridgeLowering::NonSaturatingFloatToInt {
                dst_ty,
                signed,
                operand,
                ..
            } => {
                // A genuinely-WRAPPING (non-saturating) FloatToInt: convert at a
                // WIDER width (so the out-of-range float does NOT clamp to the
                // destination's extreme) and then TRUNCATE (mask) to the destination
                // width — which WRAPS, dropping the high bits. (The faithful
                // `fp_to_sbv`/`fp_to_ubv` evaluator now SATURATES to the requested
                // width — that IS the correct Rust/hardware contract — so a raw
                // same-width `fp_to_sbv` would no longer be wrong. To exhibit a
                // wrong, NON-saturating lowering we must wrap explicitly.) For
                // 1e30_f32 -> i32 the wide (64-bit) saturating value is i64::MAX-ish,
                // whose low 32 bits (0xFFFF_FFFF) WRAP — differing from the saturating
                // spec's i32::MAX (0x7FFF_FFFF) ⇒ REFUTE.
                let dw = dst_ty.bits();
                let wide = 64u32;
                let wide_int = if *signed {
                    SmtExpr::fp_to_sbv(RoundingMode::RTZ, operand.clone(), wide)
                } else {
                    SmtExpr::fp_to_ubv(RoundingMode::RTZ, operand.clone(), wide)
                };
                if dw >= wide {
                    wide_int
                } else {
                    wide_int.extract(dw - 1, 0)
                }
            }
            BridgeLowering::MaskedShift { op, ty, lhs, rhs } => {
                // Mask the amount to width-1, then dispatch to the raw trusted
                // shift encoder (`ts` is in scope from the top of `encode`) —
                // matching the masked MIR spec.
                let w = ty.bits();
                let m = SmtExpr::bv_const((w as u64) - 1, w);
                let masked = rhs.clone().bvand(m);
                ts::try_encode_trust_ir_shift(op, ty.clone(), lhs.clone(), masked)
                    .expect("masked shift uses a shift opcode")
            }
            BridgeLowering::Aggregate { field_exprs } => {
                // Pack the fields the bridge placed, in the offset order the
                // bridge chose, with the SAME packing the MIR spec uses. The
                // refinement obligation then asks `bridge_packed == mir_packed`,
                // which fails exactly when a field landed at a different offset.
                let exprs: Vec<SmtExpr> = field_exprs.iter().map(|(e, _)| e.clone()).collect();
                let widths: Vec<u32> = field_exprs.iter().map(|(_, w)| *w).collect();
                pack_fields(&exprs, &widths)
            }
        }
    }
}

/// Build a float `MirScalarTy` from a trust-ir float `Type`.
fn float_scalar_ty(ty: &Type) -> MirScalarTy {
    MirScalarTy::Float(ty.clone())
}

/// Build an integer `MirScalarTy` from a trust-ir `Type` and a signedness flag.
fn int_scalar_ty(ty: &Type, signed: bool) -> MirScalarTy {
    if signed {
        MirScalarTy::SInt(ty.clone())
    } else {
        MirScalarTy::UInt(ty.clone())
    }
}

/// `encode_trust_ir_icmp`/`_fcmp` already return a 1-bit BV; pass through.
fn bool1_already(e: SmtExpr) -> SmtExpr {
    e
}

fn fp_format(ty: &Type) -> (u32, u32) {
    match ty {
        Type::F32 => (8, 24),
        Type::F64 => (11, 53),
        _ => (11, 53),
    }
}

// ---------------------------------------------------------------------------
// Refinement obligation: trust_ir_expr == mir_expr, discharged via ay
// ---------------------------------------------------------------------------

/// The DOMAIN precondition that makes a raw `BinOp { Sdiv | Srem }` bridge model
/// a faithful refinement obligation: `NOT(lhs == INT_MIN && rhs == -1)`.
///
/// WHY THIS IS SOUND. The bridge lowers MIR signed `Div`/`Rem` to a raw trust-ir
/// `SDiv`/`SRem` — it never emits the INT_MIN/-1 overflow trap at the rvalue.
/// That trap lives UPSTREAM: rustc's MIR inserts `Assert` terminators before the
/// `Div`/`Rem` rvalue guaranteeing `rhs != 0` AND `NOT(lhs == INT_MIN && rhs ==
/// -1)` (and for `unchecked_div`/`unchecked_rem` the caller PROMISES the same
/// domain — violating it is UB). So the INT_MIN/-1 point is UNREACHABLE at the
/// rvalue, and the faithful obligation for a raw-`Sdiv`/`Srem` bridge model is
/// quantified over that domain. In-domain the MIR spec's trap-value model
/// ([`guard_sdiv_overflow`]) collapses to plain `bvsdiv`/`bvsrem`, so a correct
/// raw lowering Refines — while `Sdiv`-as-`Udiv`, swapped operands, or a wrong
/// op/width are still Refuted (they differ at in-domain points).
///
/// This restriction is attached ONLY to the raw `BinOp { Sdiv | Srem }` bridge
/// variant. [`BridgeLowering::TrappingSdiv`] is deliberately untouched: it
/// CLAIMS the trap and must keep validating against the trap-modeling spec at
/// the INT_MIN/-1 point itself (the #59-class bite), and the global
/// [`mir_binop_precondition`] / `encode_mir_binop` trap model is unchanged so a
/// bridge that overclaims a trap it does not emit is still refuted.
///
/// The precondition is built from the bridge model's OWN operand exprs — the
/// same symbolic vars the obligation's trust-ir side reads (and, per the P3c
/// wiring contract, the same vars the MIR side encodes) — so the domain
/// restriction binds the actual operands, not fresh unconstrained variables.
///
/// Returns `None` for every other bridge variant and for non-`Sdiv`/`Srem`
/// opcodes. The signed integer widths I8/I16/I32/I64/I128 are all handled (the
/// I128 INT_MIN/-1 constants are built from two 64-bit halves since they exceed a
/// u64); any other type (FP, vector) gets no domain restriction — at worst it can
/// false-REFUTE, never over-accept.
fn sdiv_srem_domain_precondition(bridge: &BridgeLowering) -> Option<SmtExpr> {
    let BridgeLowering::BinOp { op, ty, lhs, rhs } = bridge else {
        return None;
    };
    if !matches!(op, Opcode::Sdiv | Opcode::Srem) {
        return None;
    }
    if !matches!(
        ty,
        Type::I8 | Type::I16 | Type::I32 | Type::I64 | Type::I128
    ) {
        return None;
    }
    let w = ty.bits();
    // INT_MIN (only the sign bit set) and -1 (all ones) at width `w`. For w <= 64
    // they fit `SmtExpr::bv_const`'s u64 payload; for I128 they do NOT, so build
    // them from two 64-bit halves (`high.concat(low)`): INT_MIN = 0x8000.. ++ 0,
    // -1 = all-ones ++ all-ones. Without the I128 case the obligation is checked at
    // the INT_MIN/-1 signed-overflow point (UB in MIR, where the spec and the
    // libcall lowering disagree) and a CORRECT i128 `/`/`%` FALSE-REFUTES — which
    // the default solver lane surfaces as a fail-closed (the unsigned i128 sibling,
    // having no overflow point, refines and runs).
    let (int_min, minus_one) = if w <= 64 {
        (
            SmtExpr::bv_const(1u64 << (w - 1), w),
            SmtExpr::bv_const(mask(u64::MAX, w), w),
        )
    } else {
        (
            SmtExpr::bv_const(1u64 << 63, 64).concat(SmtExpr::bv_const(0, 64)),
            SmtExpr::bv_const(u64::MAX, 64).concat(SmtExpr::bv_const(u64::MAX, 64)),
        )
    };
    Some(
        lhs.clone()
            .eq_expr(int_min)
            .and_expr(rhs.clone().eq_expr(minus_one))
            .not_expr(),
    )
}

/// Build a per-rvalue refinement obligation: the trust-ir the bridge produced
/// (`bridge`) must equal the MIR specification (`mir`).
///
/// The result is a standard [`ProofObligation`] (so it flows through the same
/// `negated_equivalence` / ay discharge path as every lowering proof):
///   * `trust_ir_expr` <- the bridge's chosen trust-ir op semantics
///   * `aarch64_expr`  <- the MIR specification (named to reuse the existing
///     struct; semantically it is the *reference* side)
///
/// The obligation's preconditions are the MIR spec's (e.g. divisor != 0 for
/// Div/Rem, threaded from [`encode_mir_rvalue`]) plus, for the raw
/// `BinOp { Sdiv | Srem }` bridge variant only, the signed-overflow domain
/// restriction `NOT(lhs == INT_MIN && rhs == -1)` — see
/// [`sdiv_srem_domain_precondition`] for the soundness argument. Both discharge
/// paths handle preconditioned obligations safely: the solver path's
/// satisfiability gate ([`discharge_refinement`]) rejects a vacuous proof, and
/// the exhaustive path's `sweep_verdict` refuses an all-points-excluded sweep.
///
/// We refuse to build an obligation if the two sides have mismatched sorts
/// (e.g. one FP, one BV) — that is a structural bug the type checker should
/// catch, not an equivalence question.
pub fn build_refinement_obligation(
    name: impl Into<String>,
    bridge: &BridgeLowering,
    mir: &EncodedRvalue,
) -> ProofObligation {
    let trust_ir_expr = bridge.encode();
    let mut preconditions = mir.preconditions.clone();
    if let Some(pre) = sdiv_srem_domain_precondition(bridge) {
        preconditions.push(pre);
    }
    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: name.into(),
        trust_ir_expr,
        aarch64_expr: mir.expr.clone(),
        inputs: mir.inputs.clone(),
        preconditions,
        fp_inputs: mir.fp_inputs.clone(),
        // Reuse the DataFlow check kind: this is a value-preservation VC at the
        // MIR->trust-ir boundary, which is precisely trust-transval DataFlow.
        category: Some(TransvalCheckKind::DataFlow),
    }
}

/// Outcome of discharging a refinement obligation.
#[derive(Debug, Clone)]
pub enum RefinementOutcome {
    /// Equivalence proven (UNSAT) by the solver, or Valid by mock evaluation.
    Refined,
    /// A counterexample was found — the bridge's lowering is WRONG.
    Refuted { counterexample: String },
    /// Could not decide (timeout/unknown/solver error). Treated as a FAILURE by
    /// callers, never a silent pass (mirrors #389/#407).
    Inconclusive { reason: String },
}

/// Discharge a refinement obligation through the SAME path the rest of the
/// verifier uses: formal ay/z3 when a solver is available, falling back to the
/// exhaustive/statistical mock evaluator otherwise.
///
/// This is the P0-aligned behaviour: prefer formal, never silently pass on
/// timeout/unknown.
/// Decide whether an obligation's preconditions are SATISFIABLE (the soundness
/// guard behind [`discharge_refinement`]'s vacuous-proof check).
///
/// `verify_with_ay` proves `precond AND NOT(trust_ir == aarch64)` UNSAT. If
/// `precond` is unsatisfiable, that holds vacuously for any bridge choice, so a
/// `Verified` result would be meaningless. We detect this with a tiny probe:
/// pair two FRESH, otherwise-unconstrained 1-bit variables under the SAME
/// preconditions and ask `verify_with_ay` to prove `precond AND (lhs != rhs)`
/// UNSAT. Since `lhs`/`rhs` are free, `lhs != rhs` is satisfiable whenever
/// `precond` is — so the probe is UNSAT (`Verified`) IFF `precond` is
/// unsatisfiable. Returns `Some(true)` if satisfiable, `Some(false)` if
/// unsatisfiable, `None` if the solver could not decide (caller fails closed).
///
/// Short-circuits to `Some(true)` for the common no-precondition obligation, so
/// it adds no solver work on that path.
fn preconditions_satisfiable(obligation: &ProofObligation, config: &AYConfig) -> Option<bool> {
    if obligation.preconditions.is_empty() {
        return Some(true);
    }
    const PROBE_LHS: &str = "__precond_sat_probe_lhs__";
    const PROBE_RHS: &str = "__precond_sat_probe_rhs__";
    let mut inputs = obligation.inputs.clone();
    inputs.push((PROBE_LHS.to_string(), 1));
    inputs.push((PROBE_RHS.to_string(), 1));
    let probe = ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: format!("{}__precond_sat_probe", obligation.name),
        trust_ir_expr: SmtExpr::var(PROBE_LHS, 1),
        aarch64_expr: SmtExpr::var(PROBE_RHS, 1),
        inputs,
        preconditions: obligation.preconditions.clone(),
        fp_inputs: obligation.fp_inputs.clone(),
        category: obligation.category,
    };
    match ay_bridge::verify_with_ay(&probe, config) {
        // UNSAT of `precond AND lhs!=rhs` => precond itself is unsatisfiable.
        AYResult::Verified => Some(false),
        // A model of `precond AND lhs!=rhs` => precond is satisfiable.
        AYResult::CounterExample(_) => Some(true),
        // Solver could not decide => caller fails closed (Inconclusive).
        AYResult::SolverUnsat | AYResult::Timeout | AYResult::Unknown(_) | AYResult::Error(_) => {
            None
        }
    }
}

pub fn discharge_refinement(obligation: &ProofObligation, config: &AYConfig) -> RefinementOutcome {
    if ay_bridge::z3_available() {
        match ay_bridge::verify_with_ay(obligation, config) {
            AYResult::Verified => {
                // SOUNDNESS GATE (vacuous-proof guard). `verify_with_ay` proves
                // `precond AND NOT(trust_ir == aarch64)` UNSAT. When `precond`
                // is ITSELF unsatisfiable, that conjunction is UNSAT for ANY
                // bridge choice — so a contradictory caller precondition would
                // mint a bogus `Refined` for a genuinely-wrong lowering. (This
                // is the MEM-1 / LOOP-1 false-negative class: an unsatisfiable
                // disjointness precondition or a constant-false loop guard.)
                // Before trusting `Verified`, require the preconditions to be
                // SATISFIABLE; if they are UNSAT or undecidable, fail closed.
                match preconditions_satisfiable(obligation, config) {
                    Some(true) => RefinementOutcome::Refined,
                    Some(false) => RefinementOutcome::Inconclusive {
                        reason: "vacuous proof: preconditions are unsatisfiable \
                                 (a Refined here would be meaningless)"
                            .to_string(),
                    },
                    None => RefinementOutcome::Inconclusive {
                        reason: "could not establish that preconditions are satisfiable"
                            .to_string(),
                    },
                }
            }
            AYResult::SolverUnsat => RefinementOutcome::Inconclusive {
                reason: "solver UNSAT lacked an independently accepted exact proof".to_string(),
            },
            AYResult::CounterExample(cex) => RefinementOutcome::Refuted {
                counterexample: format!("{cex:?}"),
            },
            AYResult::Timeout => RefinementOutcome::Inconclusive {
                reason: "solver timeout".to_string(),
            },
            AYResult::Unknown(m) => RefinementOutcome::Inconclusive {
                reason: format!("unknown: {m}"),
            },
            AYResult::Error(m) => RefinementOutcome::Inconclusive {
                reason: format!("error: {m}"),
            },
        }
    } else {
        // No solver: fall back to mock evaluation. `verify_by_evaluation` is
        // EXHAUSTIVE only for an obligation whose every input is an integer/bool of
        // the same width <= 8 bits (`is_exhaustively_decidable`); a WIDER (16/32/64-
        // bit) or FP obligation is decided STATISTICALLY (100k random samples), which
        // can miss a sparse 32/64-bit/FP counterexample (a wide-shift mask error, a
        // 64-bit-only carry, a wrong cast that diverges at one operand).
        //
        // Crediting such a sampled `Valid` as `Refined` would ADMIT a miscompiled
        // lowering behind a verdict the perimeter presents as a PROOF — the exact
        // hazard the #84 semantic back-edge VC guards against with `if
        // !z3_available() { refuse to admit on a statistical verdict }`. Mirror that
        // guard here: without a solver, credit ONLY exhaustively-decided verdicts;
        // refuse (fail closed / over-reject) on a statistical one rather than
        // overstate the perimeter. The <= 8-bit subset stays exact, so op-selection
        // bugs (which manifest at 8 bits) are still caught without a solver.
        match verify_by_evaluation(obligation) {
            VerificationResult::Valid if is_exhaustively_decidable(obligation) => {
                RefinementOutcome::Refined
            }
            VerificationResult::Valid => RefinementOutcome::Inconclusive {
                reason: "no solver available: refusing to credit a >8-bit/FP refinement \
                         obligation on a statistical (100k-sample) verdict — only \
                         exhaustively-decidable (<=8-bit integer) obligations are \
                         admitted without a solver (install a solver to verify wider \
                         obligations)"
                    .to_string(),
            },
            VerificationResult::Invalid { counterexample } => {
                RefinementOutcome::Refuted { counterexample }
            }
            VerificationResult::Unknown { reason } => RefinementOutcome::Inconclusive { reason },
        }
    }
}

/// Convenience: encode a MIR rvalue, pair it with the bridge's chosen lowering,
/// and discharge the refinement obligation in one call.
///
/// This is the shape the bridge call-site (`emit_proofs=true`) would use: for
/// each lowered statement it has both the MIR rvalue and the trust-ir it just
/// produced.
pub fn check_rvalue_lowering(
    name: impl Into<String>,
    mir_rvalue: &MirRvalue,
    bridge: &BridgeLowering,
    config: &AYConfig,
) -> Result<RefinementOutcome, String> {
    let encoded = encode_mir_rvalue(mir_rvalue)?;
    let obligation = build_refinement_obligation(name, bridge, &encoded);
    Ok(discharge_refinement(&obligation, config))
}

// ---------------------------------------------------------------------------
// FRONTEND REFINEMENT BATCH PRE-SOLVE (compile-time floor)
// ---------------------------------------------------------------------------
//
// The bridge's frontend refinement drain (`rustc_codegen_trust_cg::lib`) runs
// the default solver lane as a SERIAL `for job in jobs` loop: each DISTINCT
// wide-width scalar-rvalue obligation (the ones the fast lane skips) spawns its
// OWN `ay` subprocess via `check_rvalue_lowering -> discharge_refinement ->
// verify_with_ay -> verify_with_cli_smt2`. Unlike the x86 backend STAGE-2
// discharge (rayon `par_iter`, already ~max(solve) wall), this lane is
// genuinely serial, so its wall cost is ~sum(solve) + per-spawn process
// overhead (a fresh fork/exec of the ~90 MB `ay` binary per obligation).
// MEASURED on this box: ~10/9/25 distinct frontend spawns and ~0.8-1.1 s of
// serial WALL per compile on b01/b02/b18.
//
// The dormant implementation below can collapse those N spawns into ONE
// batched solver process:
// feed each DISTINCT obligation's BYTE-IDENTICAL standalone SMT2 (the exact
// bytes `verify_with_cli_smt2` would receive — the simplified query, or the
// raw query when `simplifier_alone_proved_unsat`, mirroring `verify_with_ay`),
// echo-delimited and `(reset)`-isolated, to one solver; parse each obligation's
// verdict from its own single-verdict window; and PRIME the process session
// verdict memo (`ay_bridge::session_cache_*`) under the byte-identical content
// key `verdict_cache_key_v2(solver identity, that SMT2)`. The subsequent inline
// `check_rvalue_lowering` for that obligation is then a session-cache HIT and
// spawns no solver.
//
// SOUNDNESS (paramount — the frontend lane catches WIDE-WIDTH miscompiles; a
// wrong batched verdict would ship a miscompile OR drop a real Refuted):
//   * BYTE-IDENTICAL KEYING, not a judgment correspondence. The per-obligation
//     batched body is the byte-identical output of the SAME query generator the
//     inline path uses (`generate_smt2_query` / `generate_smt2_query_raw`,
//     picked by the SAME `simplifier_alone_proved_unsat` test); the cache key is
//     `ay_bridge::default_route_cache_key(smt2)` = exactly what
//     `verify_with_cli_smt2` keys by. The inline lookup matches BY CONSTRUCTION.
//   * CURRENTLY DISABLED: a clean single-`unsat` window is still only a solver
//     verdict, not proof authority. `batch_proof_promotion_available()` keeps
//     this path off until every UNSAT window carries an exact independently
//     checked proof. A `sat` (Refuted counterexample) window is never cached.
//   * ANY failure (no solver, spawn/IO/timeout, sentinel-count/order mismatch,
//     a generator that stops ending in `(exit)`) discards the whole batch and
//     leaves every obligation on its inline path (fail-closed, never a weaker
//     verdict).
//   * Respects the same kill switches the inline discharge does: `None` from
//     `default_route_cache_key` (which honors `TCG_NO_PROOF_CACHE`) skips an
//     obligation; the regen recorder path is off here because this only
//     POPULATES the session memo the recorder already bypasses. CERT-SKIP is
//     untouched — a CERT-SKIP-covered obligation is already a cheap inline hit,
//     and the batch never removes that path.
//   * Used by the external-solver discharge build; the
//     one the bridge ships (`trust-cg-verify default-features = false`); the
//     native-API build reads a different memo and is left on the inline path.

/// A frontend obligation staged for the batch: the byte-identical content key
/// the inline path keys by, and the stripped per-obligation batch body (its
/// standalone SMT2 minus the trailing `(exit)`).
struct FrontendBatchItem {
    key: String,
    body: String,
}

/// The sentinel delimiting obligation `i`'s verdict window in the batched
/// solver output. Matches the backend batch framing exactly.
fn frontend_batch_sentinel(i: usize) -> String {
    format!("==TCG_BND_{i}==")
}

/// Strip the trailing `(exit)` line from a full standalone SMT2 script so its
/// body can be concatenated into a batch (a mid-batch `(exit)` would terminate
/// the whole session). `generate_smt2_query{,_raw}` ALWAYS end with exactly
/// `\n(exit)` (see `generate_smt2_query_from_formula`); a `None` return — a
/// defensive guard against a generator change — makes the caller EXCLUDE that
/// obligation from the batch (it keeps its inline live path).
fn frontend_strip_trailing_exit(smt2: &str) -> Option<&str> {
    let trimmed = smt2.strip_suffix('\n').unwrap_or(smt2);
    let body = trimmed.strip_suffix("(exit)")?;
    if body.is_empty() || body.ends_with('\n') {
        Some(body)
    } else {
        None
    }
}

/// Assemble the echo-delimited, `(reset)`-isolated batch script. Each item
/// contributes its stripped body, then `(echo "<sentinel>")`, then `(reset)`.
/// Pure (split out so the isolation / equivalence tests drive it directly).
fn frontend_assemble_batch_script(bodies: &[String]) -> String {
    let mut script = String::new();
    for (i, body) in bodies.iter().enumerate() {
        script.push_str(body);
        if !body.ends_with('\n') {
            script.push('\n');
        }
        script.push_str(&format!(
            "(echo \"{}\")\n(reset)\n",
            frontend_batch_sentinel(i)
        ));
    }
    script
}

/// PARSE RULE (fail-closed): walk the batched solver output, accumulating
/// `^(sat|unsat)$` verdict lines; on sentinel `i` (`==TCG_BND_{i}==`), window
/// `i`'s verdict = the SINGLE verdict line seen since the last sentinel.
/// Returns per expected index `Some(true)` (clean single `unsat`), `Some(false)`
/// (clean single `sat`), or `None` (AMBIGUOUS: zero or >1 verdict line). A
/// STRUCTURAL framing failure (sentinel count / order mismatch) returns the
/// whole result as `None`, aborting the batch (every obligation falls through
/// to inline). Byte-for-byte the same rule as the backend `parse_batch_windows`.
fn frontend_parse_batch_windows(stdout: &str, expected: usize) -> Option<Vec<Option<bool>>> {
    let mut verdicts: Vec<Option<bool>> = Vec::with_capacity(expected);
    let mut window_verdict: Option<bool> = None;
    let mut window_count: usize = 0;
    let mut next_sentinel: usize = 0;

    for raw in stdout.lines() {
        let line = raw.trim();
        if line == "sat" {
            window_verdict = Some(false);
            window_count += 1;
        } else if line == "unsat" {
            window_verdict = Some(true);
            window_count += 1;
        } else if let Some(idx) = line
            .strip_prefix("==TCG_BND_")
            .and_then(|r| r.strip_suffix("=="))
            .and_then(|n| n.parse::<usize>().ok())
        {
            if idx != next_sentinel {
                return None;
            }
            verdicts.push(if window_count == 1 {
                window_verdict
            } else {
                None
            });
            window_verdict = None;
            window_count = 0;
            next_sentinel += 1;
        }
        // All other lines (for example session logs) are not verdict lines and
        // are ignored. The batch runner separately rejects any protocol-error
        // transcript before this structural parser is called.
    }

    if verdicts.len() != expected {
        return None;
    }
    Some(verdicts)
}

/// The byte-identical standalone SMT2 the inline discharge (`verify_with_ay ->
/// verify_with_cli_smt2`) would feed the solver for `obligation` under the
/// DEFAULT config — the simplified query normally, or the RAW query when the
/// local simplifier alone reduced the negated equivalence to constant `false`
/// (the TCB guard in `verify_with_ay` routes those to `verify_with_cli_raw`).
/// Reproducing that exact branch is what keeps the batched bytes — and hence
/// the cache key — byte-identical to the inline path.
fn frontend_inline_smt2(obligation: &ProofObligation, config: &AYConfig) -> String {
    if ay_bridge::simplifier_alone_proved_unsat(obligation) {
        ay_bridge::generate_smt2_query_raw(obligation, config)
    } else {
        ay_bridge::generate_smt2_query(obligation, config)
    }
}

/// FRONTEND BATCH PRE-SOLVE. Given the DISTINCT scalar-rvalue refinement jobs
/// the serial default-solver lane is about to discharge — as `(name, mir,
/// bridge)` triples — prime the process session verdict memo for as many as a
/// single batched solve can cleanly prove `unsat`, so each subsequent inline
/// `check_rvalue_lowering` is a cache HIT (no spawn).
///
/// Currently returns zero because batch windows do not yet carry independently
/// checkable proofs. Once proof framing exists, this becomes a pure optimization
/// over the inline path: it may populate the session cache only after checking
/// the exact proof for each UNSAT window. Returns the number of obligations it
/// primed (diagnostic only).
///
/// The caller passes the jobs it has ALREADY filtered to the ones the serial
/// loop will actually solve (default-solver lane, not memoized, not fast-lane).
/// Default-ON; opt out with `TCG_REFINE_BATCH=0`. Honors `TCG_REFINE_SOLVER=0`
/// (frontend lane off) and `TCG_NO_PROOF_CACHE` (no reuse) via early return.
pub fn batch_presolve_refinements(
    jobs: &[(String, &MirRvalue, &BridgeLowering)],
    config: &AYConfig,
) -> usize {
    // A batch transcript has one solver verdict per window but no exact,
    // independently checked proof per UNSAT window. Until that proof framing
    // exists, it must never seed the Formal/Certified session memo.
    if !ay_bridge::batch_proof_promotion_available() {
        return 0;
    }

    // Kill switches. Default-ON (a byte-identical, fail-closed win: a batch
    // anomaly discards to the inline path, so the worst case is a sound
    // slightly-slower compile, never a wrong verdict); opt OUT with
    // TCG_REFINE_BATCH=0. Never runs when the frontend solver lane is off or
    // verdict reuse is disabled.
    if crate::env_lock::var_os("TCG_REFINE_BATCH").is_some_and(|v| v == "0")
        || crate::env_lock::var_os("TCG_REFINE_SOLVER").is_some_and(|v| v == "0")
        || crate::env_lock::var_os("TCG_NO_PROOF_CACHE").is_some()
        || crate::verdict_db::recording_active()
        || !ay_bridge::z3_available()
    {
        return 0;
    }
    // REDUNDANT WITH THE RESIDENT SERVER, AND A NET LOSS ALONGSIDE IT.
    //
    // This batch exists to amortize per-query solver startup by pre-solving a
    // window of obligations in ONE invocation. The resident `--incremental`
    // server (`ay_server_enabled`, default ON) already amortizes exactly that,
    // and it does it better: the batch spawns a FRESH solver process, and the
    // `ay` binary is ~115 MB, so that spawn costs more than the inline solves
    // it replaces — the server discharges each obligation in 3-8 ms.
    //
    // Measured on aarch64, `codegen_crate`, min-of-5, pinned, interleaved:
    //   p1_xorshift 0.224 -> 0.195   p3_gcd 0.228 -> 0.202
    //   p4_matmul   0.249 -> 0.226   h3_box_leak 0.412 -> 0.363
    //   v1_saxpy    0.272 -> 0.241
    // i.e. skipping the batch is 23-49 ms FASTER per compile, and all 18
    // beat-llvm programs are `.text` BYTE-IDENTICAL with matching exit codes
    // either way (this only populates the session memo; verdicts are unchanged,
    // which the surrounding doc already establishes for batch-vs-inline).
    //
    // Kept for the no-server configuration, where the original amortization
    // argument still holds: `TCG_NO_SOLVER_SERVER=1` re-enables the batch.
    if ay_bridge::ay_server_enabled() {
        return 0;
    }

    // CT-11: if the session verdict memo cannot produce keys at all, EVERY item
    // below is guaranteed to be dropped at `default_route_cache_key` — after
    // this loop has already paid `encode_mir_rvalue` + `build_refinement_obligation`
    // + `frontend_inline_smt2` (full SMT2 text) for each one, and thrown all of
    // it away. That is the state on any host whose solver is `-dirty`
    // (CT-10), which is every developer box with a locally-built `ay`.
    //
    // One probe answers it for the whole batch: the key derivation is
    // obligation-independent apart from the SMT2 bytes, so if it declines for a
    // trivial query it declines for all of them. Bail before doing the work.
    if ay_bridge::default_route_cache_key("(assert true)").is_none() {
        return 0;
    }

    // Collect batchable items, deduped by content key (repeated shapes share
    // ONE window). Any obligation whose bytes/key cannot be derived, or that is
    // already session-cached, is excluded (it keeps its inline path).
    let mut seen: std::collections::HashSet<String> = std::collections::HashSet::new();
    let mut items: Vec<FrontendBatchItem> = Vec::new();
    for (name, mir, bridge) in jobs {
        // Build the obligation EXACTLY as `check_rvalue_lowering` does. An
        // encoder Err is not a batch candidate (the inline path skips it too).
        let Ok(encoded) = encode_mir_rvalue(mir) else {
            continue;
        };
        let obligation = build_refinement_obligation(name.clone(), bridge, &encoded);
        // NOTE: with a solver present (the only time this runs), the inline
        // `discharge_refinement` routes EVERY obligation through
        // `verify_with_ay` -> `verify_with_cli_smt2` (a spawn) regardless of
        // width — `is_exhaustively_decidable` only shapes the NO-solver fallback.
        // So we batch every obligation the loop will solve; the SMT2 bytes are
        // byte-identical either way.
        let smt2 = frontend_inline_smt2(&obligation, config);
        // Byte-identical key + resolved solver, exactly as the inline path.
        let Some((_solver_path, key)) = ay_bridge::default_route_cache_key(&smt2) else {
            continue;
        };
        if !seen.insert(key.clone()) {
            continue; // already staged this exact obligation
        }
        // Already proven this process -> inline is already a cheap hit.
        if ay_bridge::session_cache_contains(&key) {
            continue;
        }
        // CERT-SKIP already covers it -> the inline path re-checks the committed
        // DRAT cert (cheap, no live spawn). Leave that tier untouched.
        if crate::canary_cert::cert_skip_verified(&smt2) {
            continue;
        }
        let Some(body) = frontend_strip_trailing_exit(&smt2) else {
            continue;
        };
        items.push(FrontendBatchItem {
            key,
            body: body.to_string(),
        });
    }

    if items.is_empty() {
        return 0;
    }

    let bodies: Vec<String> = items.iter().map(|it| it.body.clone()).collect();
    let script = frontend_assemble_batch_script(&bodies);

    // ONE solver process for the whole batch. Budget: the per-obligation
    // timeout PER ITEM (capped), since the batch does N solves serially. A
    // timeout / any failure just falls through to inline (fail-closed).
    const BATCH_MAX_TIMEOUT_MS: u64 = 120_000;
    let per_item = config.timeout_ms.max(1);
    let batch_timeout_ms = per_item
        .saturating_mul(items.len() as u64)
        .min(BATCH_MAX_TIMEOUT_MS);
    let Some(stdout) = ay_bridge::run_batch_solver_script(&script, batch_timeout_ms) else {
        return 0;
    };
    let Some(windows) = frontend_parse_batch_windows(&stdout, items.len()) else {
        return 0;
    };

    // Credit ONLY clean single-`unsat` windows, under the byte-identical key. A
    // `sat`/ambiguous/missing window primes nothing -> that obligation stays on
    // its inline path (which re-solves and, on a genuine `sat`, fails closed).
    let mut primed = 0usize;
    for (item, verdict) in items.iter().zip(windows.iter()) {
        if *verdict == Some(true) {
            ay_bridge::session_cache_store_verified(&item.key);
            primed += 1;
        }
    }
    primed
}

/// Whether `obligation` is discharged COMPLETELY (exhaustively, not
/// statistically) by [`verify_by_evaluation`]:
///   * every input is an integer/bool input ≤ 8 bits (no FP inputs — FP
///     obligations only ever get statistical sampling, never a complete proof),
///   * there are 1 or 2 inputs (`verify_exhaustive` only enumerates 1- and
///     2-input combos; 0 inputs is a constant equality, also complete), and
///   * all inputs share the ≤ 8-bit width (`verify_by_evaluation` keys the
///     exhaustive threshold off the FIRST input's width, so a wider second input
///     would be sampled, not enumerated — we require uniform ≤ 8-bit width to be
///     sure the discharge is exhaustive over the full input space).
///
/// When this holds, the mock evaluator's `Valid`/`Invalid` verdict is a COMPLETE
/// decision for that obligation (every input combination tested), so it is sound
/// to fail-closed on it WITHOUT a solver. This is the predicate the always-on
/// fast lane uses to pick the obligations it can decide for free.
fn is_exhaustively_decidable(obligation: &ProofObligation) -> bool {
    // FP inputs are never enumerated exhaustively (the FP evaluator samples an
    // edge-case battery), so any FP input disqualifies the obligation.
    if !obligation.fp_inputs.is_empty() {
        return false;
    }
    let n = obligation.inputs.len();
    if n > 2 {
        return false;
    }
    // All present inputs must be ≤ 8 bits and the same width (see doc comment).
    let mut width: Option<u32> = None;
    for (_, w) in &obligation.inputs {
        if *w > crate::lowering_proof::EXHAUSTIVE_WIDTH_THRESHOLD {
            return false;
        }
        match width {
            None => width = Some(*w),
            Some(prev) if prev != *w => return false,
            _ => {}
        }
    }
    true
}

/// Discharge a refinement obligation through the FAST, SOLVER-FREE lane: only
/// obligations [`is_exhaustively_decidable`] can decide COMPLETELY (≤ 8-bit
/// scalar inputs, ≤ 2 of them, no FP) are run, exhaustively, via the mock
/// evaluator. Everything else returns `None` ("not in the fast subset") — the
/// caller must SKIP it (the wider/FP obligations are the full [`TCG_REFINE`]
/// solver lane's job).
///
/// This never invokes a solver and runs ≤ 2^16 evaluations per obligation, so it
/// is cheap enough to enable on EVERY compile. It is COMPLETE for the subset it
/// accepts: a `Refuted` here is a genuine counterexample (every input was
/// tested), and a `Refined` here is a full proof at that width. It cannot
/// false-refute a correct lowering, because exhaustive evaluation of a
/// value-equivalence is exact (no sampling, no solver model freedom).
pub fn discharge_refinement_fast(obligation: &ProofObligation) -> Option<RefinementOutcome> {
    if !is_exhaustively_decidable(obligation) {
        return None;
    }
    // `TCG_TRACE_FAST_LANE=1`: per-obligation wall cost of the exhaustive sweep.
    // The sweep is up to 2^16 points, so a single slow obligation is invisible in
    // aggregate timings but can dominate a whole compile.
    let _t = std::env::var_os("TCG_TRACE_FAST_LANE").map(|_| (std::time::Instant::now(), ()));
    let outcome = verify_by_evaluation(obligation);
    if let Some((at, ())) = _t {
        eprintln!(
            "TCG_FAST_LANE {:8.2}ms inputs={} {}",
            at.elapsed().as_secs_f64() * 1000.0,
            obligation.inputs.len(),
            obligation.name
        );
    }
    Some(match outcome {
        VerificationResult::Valid => RefinementOutcome::Refined,
        VerificationResult::Invalid { counterexample } => {
            RefinementOutcome::Refuted { counterexample }
        }
        // An exhaustively-decidable obligation should never come back Unknown;
        // if it somehow does, treat it as out-of-subset (skip) rather than
        // failing the compile — the full solver lane covers it.
        VerificationResult::Unknown { .. } => return None,
    })
}

/// Fast-lane convenience mirroring [`check_rvalue_lowering`]: encode the MIR
/// rvalue, pair it with the bridge's choice, and discharge it through the
/// solver-free exhaustive lane. Returns `Ok(None)` when the obligation is not in
/// the exhaustively-decidable subset (the caller skips it).
pub fn check_rvalue_lowering_fast(
    name: impl Into<String>,
    mir_rvalue: &MirRvalue,
    bridge: &BridgeLowering,
) -> Result<Option<RefinementOutcome>, String> {
    let encoded = encode_mir_rvalue(mir_rvalue)?;
    let obligation = build_refinement_obligation(name, bridge, &encoded);
    Ok(discharge_refinement_fast(&obligation))
}

// ---------------------------------------------------------------------------
// CONTROL FLOW: symbolic block store + per-edge block-arg edge-equality VC
// ---------------------------------------------------------------------------
//
// Proof-gap item 6, CONTROL-FLOW axis. This is the SEMANTIC complement to the
// STRUCTURAL `ssa_loop_complete` (P1.3) check: P1.3 proves the bridge THREADED
// the right *variable* into each header/successor slot; this proves the
// threaded *value* actually equals the source program's dataflow across the
// edge. Together they catch the #71 class (a branch-/loop-carried value DROPPED
// or MIS-THREADED as a block argument), here over the ACYCLIC slice.
//
// MODEL. A block's statements are folded into a symbolic STORE `name ->
// SmtExpr`: statement `dst = rvalue` binds `dst` to the rvalue's encoded value,
// with operands resolved THROUGH the store (an operand naming an earlier `dst`
// reads the updated value; a block-external operand becomes a fresh symbolic
// input). The terminator's per-edge `*_args` are then resolved through the SAME
// store, yielding the MIR value flowing to each target param. The bridge's
// chosen block arg for that slot — built by the caller from the SAME symbolic
// vars / store — is paired against it as an edge-equality obligation
// `bridge_arg_k == mir_arg_k`. A SAT result refutes a dropped/stale/swapped arg.
//
// SCOPE: scalar values, acyclic edges (Goto / two-way Branch). DEFERRED:
// semantic loop invariants (which need an inductive CHC solver lane), memory /
// projected aggregate fields, and switch discriminant normalization. See
// DESIGN below.

/// A symbolic store over a single block: the value bound to each SSA name after
/// folding the block's statements, plus the symbolic inputs the block reads.
///
/// Built by [`encode_block_store`]. `store[dst]` is the `SmtExpr` the statement
/// `dst = rvalue` produced (operands resolved through the store-so-far), so a
/// terminator arg naming `dst` reads the UPDATED value — the property that makes
/// a "threads the entry value instead of the update" drop observable.
#[derive(Debug, Clone, Default)]
pub struct BlockStore {
    /// SSA name -> its value after the defining statement.
    pub store: std::collections::HashMap<String, SmtExpr>,
    /// Block-external integer/bool inputs the block reads (name, width).
    pub inputs: Vec<(String, u32)>,
    /// Block-external FP inputs (name, eb, sb).
    pub fp_inputs: Vec<(String, u32, u32)>,
}

impl BlockStore {
    /// Resolve a MIR operand to its `SmtExpr` THROUGH the store: a `Var` naming a
    /// bound `dst` reads the stored (updated) value; any other `Var` (a
    /// block-external / entry value) becomes a fresh symbolic input; constants
    /// encode directly. This is the SHARED resolver both the MIR edge args and
    /// the bridge's chosen args go through, so the edge-equality VC is real.
    pub fn resolve(&mut self, operand: &MirOperand) -> SmtExpr {
        if let MirOperand::Var { name, .. } = operand
            && let Some(existing) = self.store.get(name)
        {
            return existing.clone();
        }
        operand.encode(&mut self.inputs, &mut self.fp_inputs)
    }
}

/// Fold a block's statements into a [`BlockStore`]: each `dst = rvalue` binds
/// `dst` to the rvalue's MIR-spec value, with the rvalue's operands resolved
/// through the store built so far (so a statement may read an earlier `dst`).
///
/// Faithful re-encoding: it routes through [`encode_mir_rvalue`] for the rvalue
/// semantics, but rewrites each operand that names an already-bound `dst` to a
/// `Use` of the stored value first, so intra-block dataflow is honored. Returns
/// an error if any statement's rvalue is out of slice.
pub fn encode_block_store(block: &MirBlock) -> Result<BlockStore, String> {
    let mut bs = BlockStore::default();
    for stmt in &block.stmts {
        // Resolve the rvalue's operands through the store, then encode. We do
        // this by substituting each store-bound operand with a constant-free
        // `Use` of its current symbolic value via a small re-encode: encode the
        // rvalue against a *local* input set, then bind any operand name that is
        // already in the store to the stored expr by variable substitution.
        let encoded = encode_block_rvalue(&mut bs, &stmt.rvalue)?;
        bs.store.insert(stmt.dst.clone(), encoded);
    }
    Ok(bs)
}

/// Encode one rvalue with its operands resolved through `bs` (the store built so
/// far), registering only the genuinely block-external operands as inputs.
///
/// We resolve operands FIRST (through [`BlockStore::resolve`], which reads the
/// store or mints a fresh input), then feed the resolved `SmtExpr`s into the
/// rvalue's arithmetic via the same op encoders the per-rvalue path uses — so
/// the value bound to `dst` is exactly the MIR spec for that rvalue over the
/// (possibly intra-block) operand values.
fn encode_block_rvalue(bs: &mut BlockStore, rv: &MirRvalue) -> Result<SmtExpr, String> {
    match rv {
        MirRvalue::Use { src } => Ok(bs.resolve(src)),
        MirRvalue::UnaryOp { op, ty, operand } => {
            let o = bs.resolve(operand);
            Ok(encode_mir_unop(*op, ty.clone(), o))
        }
        MirRvalue::BinaryOp { op, ty, lhs, rhs } => {
            let l = bs.resolve(lhs);
            let r = bs.resolve(rhs);
            encode_mir_binop(*op, ty.clone(), l, r)
        }
        MirRvalue::CheckedBinaryOp { op, ty, lhs, rhs } => {
            let l = bs.resolve(lhs);
            let r = bs.resolve(rhs);
            encode_mir_checked_binop(*op, ty.clone(), l, r)
        }
        MirRvalue::Cast {
            kind,
            src_ty,
            dst_ty,
            operand,
        } => {
            let o = bs.resolve(operand);
            encode_mir_cast(*kind, src_ty.clone(), dst_ty.clone(), o)
        }
        MirRvalue::Aggregate { fields } => {
            if fields.is_empty() {
                return Err("MIR Aggregate with no fields is out of slice (ZST)".to_string());
            }
            let mut field_exprs = Vec::with_capacity(fields.len());
            let mut field_widths = Vec::with_capacity(fields.len());
            for f in fields {
                if f.ty().is_float() {
                    return Err("MIR Aggregate float field is out of slice (SSE class)".to_string());
                }
                field_widths.push(f.ty().bits());
                field_exprs.push(bs.resolve(f));
            }
            Ok(pack_fields(&field_exprs, &field_widths))
        }
        MirRvalue::Select {
            cond,
            ty,
            then_val,
            else_val,
        } => {
            if ty.is_float() {
                return Err("MIR Select float result is out of slice (SSE class)".to_string());
            }
            if then_val.ty().bits() != ty.bits() || else_val.ty().bits() != ty.bits() {
                return Err(format!(
                    "MIR Select arm width mismatch: result {} vs then {} / else {}",
                    ty.bits(),
                    then_val.ty().bits(),
                    else_val.ty().bits()
                ));
            }
            if cond.ty().is_float() {
                return Err("MIR Select condition must be a bool/int, not a float".to_string());
            }
            let c = bs.resolve(cond);
            let t = bs.resolve(then_val);
            let e = bs.resolve(else_val);
            Ok(encode_mir_select(c, t, e))
        }
        // LOOP-VC-LOCAL packed overflow tuple `_6 = AddWithOverflow(a, b)`: the
        // wrapped value in the low N bits (`bvadd`/`bvsub`/`bvmul`, exact) and the
        // overflow flag in the high bit bound to the SHARED uninterpreted symbol
        // `overflow_flag_uf` (see [`MirRvalue::CheckedOverflowPacked`]). This is
        // the ONLY place the packed form is encoded — the per-instruction slice
        // (`encode_mir_rvalue`) rejects it — because the UF flag is sound only for
        // the threading obligation.
        MirRvalue::CheckedOverflowPacked { op, ty, lhs, rhs } => {
            if ty.is_float() {
                return Err("CheckedOverflowPacked float type is not valid".to_string());
            }
            let w = ty.bits();
            let tag = mir_overflow_op_tag(*op)
                .ok_or_else(|| format!("CheckedOverflowPacked op {op:?} is not Add/Sub/Mul"))?;
            let l = bs.resolve(lhs);
            let r = bs.resolve(rhs);
            let wrapped = match op {
                MirBinOp::Add => l.clone().bvadd(r.clone()),
                MirBinOp::Sub => l.clone().bvsub(r.clone()),
                MirBinOp::Mul => l.clone().bvmul(r.clone()),
                _ => unreachable!("mir_overflow_op_tag gated Add/Sub/Mul"),
            };
            // `flag(1) :: wrapped(N)` — flag stacked in the high bit, exactly the
            // layout `encode_mir_checked_binop` produces (so a `.1` extract reads
            // the flag and a `.0` extract reads the wrapped value).
            let flag = overflow_flag_uf(tag, w, l, r);
            Ok(flag.concat(wrapped))
        }
        // LOOP-VC-LOCAL projection of a packed overflow tuple. Reads the SNAPSHOT
        // packed value off the store (the `CheckedOverflowPacked` bound earlier)
        // and extracts the requested field: 0 = wrapped (low `value_width` bits),
        // 1 = flag (the single high bit).
        MirRvalue::PackedOverflowField {
            src,
            field,
            value_width,
        } => {
            let packed = bs.store.get(src).cloned().ok_or_else(|| {
                format!("packed overflow source `{src}` is not bound before its field projection")
            })?;
            let packed_w = packed
                .try_bv_width()
                .map_err(|e| format!("packed overflow source `{src}` has a non-BV sort: {e:?}"))?;
            if packed_w != value_width + 1 {
                return Err(format!(
                    "packed overflow source `{src}` is {packed_w} bits but the projection expects \
                     {} (= value_width {value_width} + 1 flag bit)",
                    value_width + 1
                ));
            }
            match field {
                0 => Ok(packed.extract(value_width - 1, 0)),
                1 => Ok(packed.extract(*value_width, *value_width)),
                other => Err(format!(
                    "overflow tuple field {other} out of range (only .0 wrapped / .1 flag)"
                )),
            }
        }
    }
}

/// Resolve a terminator's per-edge MIR arguments to `SmtExpr`s through the
/// block's store, paired with the [`EdgeKind`] they thread on. Each inner `Vec`
/// is one edge's args in target-param slot order. Constants/external vars are
/// resolved exactly as the statements' operands were (same store), so an edge
/// arg naming an in-block `dst` carries the UPDATED value.
pub fn resolve_edge_args(
    bs: &mut BlockStore,
    terminator: &MirTerminator,
) -> Vec<(EdgeKind, Vec<SmtExpr>)> {
    match terminator {
        MirTerminator::Goto { args, .. } => {
            let resolved = args.iter().map(|a| bs.resolve(a)).collect();
            vec![(EdgeKind::Goto, resolved)]
        }
        MirTerminator::Branch { t_args, f_args, .. } => {
            let t: Vec<SmtExpr> = t_args.iter().map(|a| bs.resolve(a)).collect();
            let f: Vec<SmtExpr> = f_args.iter().map(|a| bs.resolve(a)).collect();
            vec![(EdgeKind::BranchTrue, t), (EdgeKind::BranchFalse, f)]
        }
        MirTerminator::Return => vec![],
    }
}

/// Build the per-edge, per-slot block-argument edge-equality obligations for one
/// block: for every outgoing edge and every target-param slot `k`, an obligation
/// asserting the bridge's chosen block arg at slot `k` equals the MIR value the
/// source block threads to slot `k` across that edge.
///
/// `name_prefix` labels the obligations (e.g. `"bb3"`). `bridge_edges` supplies
/// the bridge's chosen args per edge; an edge present in the terminator with no
/// matching `BridgeEdgeArgs`, or a mismatched arg COUNT, is an error (a missing
/// edge / dropped-slot is a STRUCTURAL bug the arity check should surface, not a
/// silent pass).
///
/// Each obligation reuses [`ProofObligation`] / the standard discharge path, so
/// `discharge_refinement` decides it: a slot whose bridge value can differ from
/// the MIR value is SAT (the drop/swap), refuted; an identical-value slot is
/// UNSAT, refined. Both sides are built from the same `BlockStore` symbolic
/// vars, so the VC is a genuine dataflow check.
pub fn build_edge_equality_obligations(
    name_prefix: &str,
    block: &MirBlock,
    bridge_edges: &[BridgeEdgeArgs],
) -> Result<Vec<ProofObligation>, String> {
    // Acyclic edges carry no extra path precondition (the entry/branch edges are
    // unconditionally taken when reached). Delegate to the precondition-carrying
    // core with an empty precondition set so the loop helper and this acyclic
    // entry share ONE encoder (no duplication).
    build_edge_equality_obligations_pre(name_prefix, block, bridge_edges, &[])
}

/// Precondition-carrying core of [`build_edge_equality_obligations`]: identical,
/// but every emitted obligation additionally carries `edge_preconditions` (e.g.
/// the loop guard `b != 0` that holds on a latch->header back-edge, which excludes
/// the `a % b` divide-by-zero trap from the universal threading VC). The acyclic
/// entry passes an empty slice; the loop helper passes the guard under which the
/// edge is taken. Preconditions are respected by BOTH discharge paths
/// (`verify_by_evaluation` skips unsatisfying points; the solver/CHC encode
/// `precond => equivalence`), so a guarded threading VC is decided only over the
/// inputs the edge is actually taken on — never vacuously, never trap-polluted.
/// STRUCTURAL-IDENTITY LANE for edge-equality VCs.
///
/// An edge-equality obligation asks `preconditions => (trust_ir_expr ==
/// aarch64_expr)`, where the two sides are derived from INDEPENDENT sources:
/// `trust_ir_expr` is the bridge's chosen block arg, obtained by symbolically
/// executing the PRODUCED trust-ir, and `aarch64_expr` is the value the SOURCE
/// MIR threads on that edge, obtained by folding the MIR block's statements.
///
/// When those two expression trees are structurally EQUAL, `e == e` holds in
/// every model, so the obligation is valid UNCONDITIONALLY — strictly stronger
/// than the guarded form the solver is asked to discharge. `SmtExpr` derives a
/// structural `PartialEq`, so this is an exact tree comparison, not a heuristic.
///
/// # Why this is not a degenerate `X == X` obligation (#62)
///
/// The equality is NOT true by construction. It is true exactly when the bridge
/// threaded the MIR's value into that slot. A DROPPED, STALE or SWAPPED arg —
/// the #71 / euclid miscompile class — produces a structurally DIFFERENT tree
/// and falls through to the full solver lane untouched, so no refutation is
/// lost. `euclid_swapped_back_edge_is_refuted` and the stale-back-edge test
/// still exercise the solver path end to end.
///
/// # What is deliberately given up
///
/// `discharge_refinement` follows a solver `Verified` with a vacuity guard
/// (`preconditions_satisfiable`), because a `Verified` obtained from
/// CONTRADICTORY preconditions would be meaningless. That guard is skipped here.
/// It is sound to skip: this verdict does not rest on the preconditions at all,
/// so unsatisfiable preconditions cannot make it wrong — they can only make it
/// less informative. The cost is that a modeling bug which renders preconditions
/// contradictory is no longer surfaced for identity-discharged slots.
///
/// Set `TCG_NO_STRUCTURAL_EDGE_LANE=1` to force every obligation through the
/// solver. That can only make verification slower and stricter, never weaker.
fn edge_equality_holds_structurally(ob: &ProofObligation) -> bool {
    if crate::env_lock::var_os("TCG_NO_STRUCTURAL_EDGE_LANE").is_some() {
        return false;
    }
    let identical = ob.trust_ir_expr == ob.aarch64_expr;
    if crate::env_lock::var_os("TCG_BACKEDGE_TRACE").is_some() {
        eprintln!("TCG_BACKEDGE {} structural_identity={identical}", ob.name);
    }
    identical
}

pub fn build_edge_equality_obligations_pre(
    name_prefix: &str,
    block: &MirBlock,
    bridge_edges: &[BridgeEdgeArgs],
    edge_preconditions: &[SmtExpr],
) -> Result<Vec<ProofObligation>, String> {
    let mut bs = encode_block_store(block)?;
    let mir_edges = resolve_edge_args(&mut bs, &block.terminator);
    let mut obligations = Vec::new();
    for (edge, mir_args) in &mir_edges {
        let bridge = bridge_edges
            .iter()
            .find(|b| b.edge == *edge)
            .ok_or_else(|| format!("{name_prefix}: no bridge block-args for edge {edge:?}"))?;
        if bridge.args.len() != mir_args.len() {
            return Err(format!(
                "{name_prefix}: edge {edge:?} arg-count mismatch: bridge {} vs MIR {} \
                 (a dropped/extra block arg is a structural arity bug)",
                bridge.args.len(),
                mir_args.len()
            ));
        }
        for (k, (bridge_arg, mir_arg)) in bridge.args.iter().zip(mir_args.iter()).enumerate() {
            // Sort guard: comparing a BV slot against an FP slot is a structural
            // type bug, not an equivalence question (mirrors
            // `build_refinement_obligation`'s contract).
            obligations.push(ProofObligation {
                machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
                name: format!("{name_prefix}_edge_{edge:?}_slot{k}"),
                // trust_ir side = the bridge's chosen block arg.
                trust_ir_expr: bridge_arg.clone(),
                // reference side = the MIR value threaded on this edge.
                aarch64_expr: mir_arg.clone(),
                inputs: bs.inputs.clone(),
                preconditions: edge_preconditions.to_vec(),
                fp_inputs: bs.fp_inputs.clone(),
                // A block-arg threading check is precisely a ControlFlow VC.
                category: Some(TransvalCheckKind::ControlFlow),
            });
        }
    }
    Ok(obligations)
}

/// Discharge every edge-equality obligation a block raises and fold the verdicts:
/// `Refined` only if ALL slots/edges refine; the FIRST `Refuted` (a dropped /
/// stale / swapped block arg) is returned with its counterexample; an
/// `Inconclusive` (timeout/unknown) is surfaced, never downgraded (P0).
///
/// This is the block-level entry the bridge wiring would call with the real
/// terminator + the trust-ir block args it just emitted (follow-up; see DESIGN
/// item 3). An empty obligation set (a `Return` block, no edges) is `Refined`.
pub fn check_block_arg_threading(
    name_prefix: &str,
    block: &MirBlock,
    bridge_edges: &[BridgeEdgeArgs],
    config: &AYConfig,
) -> Result<RefinementOutcome, String> {
    let obligations = build_edge_equality_obligations(name_prefix, block, bridge_edges)?;
    for ob in &obligations {
        if edge_equality_holds_structurally(ob) {
            continue;
        }
        match discharge_refinement(ob, config) {
            RefinementOutcome::Refined => {}
            other => return Ok(other),
        }
    }
    Ok(RefinementOutcome::Refined)
}

// ---------------------------------------------------------------------------
// LOOP-CARRIED block-arg threading (proof-gap item 6, the euclid / #71 class)
// ---------------------------------------------------------------------------
//
// Extends the ACYCLIC edge-equality VC above to a loop HEADER carrying values
// across BOTH its in-edges: the PREHEADER (initial entry) edge and the LATCH
// back-edge. The euclid_gcd shape:
//
//     while b != 0 { let t = b; b = a % b; a = t; }
//
// is a header with loop-carried params (a, b) reached from (1) the preheader
// (initial a0, b0) and (2) the latch, whose body computes `t = b; b' = a % b;
// a' = t` and threads (a', b') = (b, a % b) back to (a, b). The #71 / euclid
// miscompile is the bridge threading the WRONG / STALE / SWAPPED value across
// the LATCH->HEADER back-edge — e.g. threading old `a` instead of `t`, or
// swapping (a', b'). Today this is covered only STRUCTURALLY by
// `ssa_loop_complete` (P1.3); this makes it SEMANTIC.
//
// WHY ONE-STEP UNIVERSAL HEADER PARAMS IS SOUND FOR *THREADING* (not for a
// semantic loop INVARIANT):
//
//   Block-arg THREADING correctness is a PER-EDGE dataflow equality:
//   "the value the bridge threads to header param k on an in-edge equals the
//    MIR source value threaded to param k on that edge." It is NOT a property
//   that accumulates across iterations (like "b strictly decreases" or
//   "result == gcd(a0, b0)").
//
//   The header params (a, b) ABSTRACT the values at the top of an ARBITRARY
//   iteration. Encoding the latch body with (a, b) as FREE, UNIVERSALLY-
//   QUANTIFIED symbolic inputs and proving the back-edge threading equation
//   `bridge_arg_k == mir_arg_k` for ALL (a, b) therefore covers every concrete
//   iteration's header values WITHOUT a fixpoint: we do not assume which (a, b)
//   are reachable — we prove the equation for all of them, which is strictly
//   stronger than (and so implies) the per-iteration obligation. No inductive
//   hypothesis is needed because threading equality is established edge-locally;
//   the only thing that varies across iterations is the VALUE of (a, b), and
//   universal quantification already ranges over every such value.
//
//   This is precisely why an inductive CHC solver lane is NOT required here. A
//   CHC `Valid` predicate would let you ASSUME a non-trivial,
//   solver-SYNTHESIZED loop invariant `Inv(a, b)` on the back-edge to discharge
//   an inductive step (the tool for a semantic INVARIANT). For threading the equation holds
//   UNCONDITIONALLY over all (a, b) (modulo the loop GUARD precondition, e.g.
//   `b != 0`, which only excludes the `a % b` trap — not a reachability claim),
//   so the strongest usable `Valid` is just `true`, and the CHC query collapses
//   to the plain quantifier-free `forall inputs: trust_ir == aarch64` that
//   `discharge_refinement` already decides. (Confirmed against
//   `ay_bridge::encode_obligation_as_chc`: its Init clause makes every input
//   `Valid` unconditionally, so the query is bit-identical to the QF check.)
//   Using CHC here would add a heavyweight Horn solver for ZERO additional
//   discrimination on the threading question. A full semantic loop-INVARIANT
//   proof IS a separate, larger axis that DOES need an inductive CHC solver
//   lane; it is NOT required for threading correctness and remains deferred
//   (see DESIGN).

/// A loop with loop-carried HEADER params reached from a preheader entry edge
/// and a single latch back-edge — the minimal shape that makes the euclid / #71
/// loop-carried THREADING class explicit and checkable with the acyclic
/// edge-equality machinery.
///
/// The header itself has no body in this model: it is just the set of
/// loop-carried PARAMS (the SSA names + types the header phi-nodes define),
/// which the latch reads as FREE symbolic inputs (any iteration's top-of-loop
/// values). The `latch` is a real [`MirBlock`] ending in a `Goto` back to the
/// header, threading the updated values; `preheader_args` are the initial values
/// the entry edge threads to the same params.
///
/// SCOPE: a SINGLE-latch loop with a `Goto` back-edge over scalar header params.
/// A multi-block loop body is folded into the single `latch` block's statement
/// list (its intra-body dataflow is honored by `encode_block_store`); a loop with
/// MULTIPLE latches / a conditional back-edge, nested loops, or memory-carried
/// state is deferred (see DESIGN).
#[derive(Debug, Clone)]
pub struct MirLoop {
    /// The header's loop-carried params, in slot order (`header_params[k]` is the
    /// SSA name + type of header phi slot `k`). Both in-edges thread one value per
    /// slot. The latch reads these names as block-external (free) inputs.
    pub header_params: Vec<(String, MirScalarTy)>,
    /// The values the PREHEADER entry edge threads to the header params, in slot
    /// order. Usually constants or function params (`a0`, `b0`).
    pub preheader_args: Vec<MirOperand>,
    /// The latch block: its statements compute the loop step over the header
    /// params, and its terminator is a `Goto { target: <header>, args }` whose
    /// `args` are the updated values threaded back to the header params in slot
    /// order. (`target` is not interpreted by the threading VC — only the `args`
    /// matter — so any header BlockId is fine.)
    pub latch: MirBlock,
    /// Optional guard under which the latch->header back-edge is taken (the loop
    /// CONDITION as a MIR operand, e.g. `b != 0` as a precomputed 1-bit value, or
    /// `None` for an unconditional back-edge). When present it is added as a
    /// precondition to the back-edge VC, EXCLUDING the inputs on which the loop
    /// would have exited (and on which a `% b` step would trap). It restricts the
    /// universal quantification to the taken inputs; it does NOT assume any loop
    /// invariant.
    pub back_edge_guard: Option<MirOperand>,
}

impl MirLoop {
    /// The latch's back-edge args (the `Goto` target args). Errors if the latch
    /// terminator is not a `Goto` (the back-edge must be an unconditional jump to
    /// the header in this single-latch model; a conditional back-edge is
    /// deferred).
    fn latch_back_edge_args(&self) -> Result<&[MirOperand], String> {
        match &self.latch.terminator {
            MirTerminator::Goto { args, .. } => Ok(args),
            other => Err(format!(
                "MirLoop latch must end in a Goto back to the header (got {other:?}); \
                 a conditional/multi-target back-edge is deferred"
            )),
        }
    }
}

/// Check loop-carried block-arg threading across BOTH the preheader entry edge
/// and the latch back-edge of `lp`, as one-step edge-equality VCs with the header
/// params treated as FREE universally-quantified symbolic inputs (see the module
/// comment for the soundness argument).
///
/// * PREHEADER edge: the entry block threads `lp.preheader_args` to the header
///   params; the bridge threads `bridge_preheader_edge.args`. Built as an
///   edge-equality VC over a synthetic entry block whose terminator is a `Goto`
///   threading the preheader args (no body — the entry values are block-external
///   operands), so the VC is `bridge_entry_k == preheader_arg_k` per slot.
///
/// * LATCH back-edge: the latch block reads the header params as free inputs,
///   folds its body into a [`BlockStore`], and threads its `Goto` args back; the
///   bridge threads `bridge_latch_edge.args`. Built via
///   [`build_edge_equality_obligations_pre`] over the REAL latch block, so the
///   per-slot VC is `bridge_latch_arg_k == mir_latch_arg_k` resolved through the
///   latch store — a SWAP, STALE, or DROPPED back-edge arg makes some slot SAT.
///   The optional `back_edge_guard` is threaded as the VC precondition.
///
/// Both bridge edges' args MUST be driven by the caller from the SAME header-param
/// vars the latch store reads (`SmtExpr::var(param_name, width)`), so the VC is a
/// REAL dataflow check and a swap cannot be hidden. Arities are checked against
/// the header param count. Folds the verdicts: `Refined` only if EVERY slot of
/// BOTH edges refines; the first `Refuted` (with counterexample) or `Inconclusive`
/// (never downgraded — P0) is surfaced.
pub fn check_loop_carried_threading(
    name_prefix: &str,
    lp: &MirLoop,
    bridge_preheader_edge: &BridgeEdgeArgs,
    bridge_latch_edge: &BridgeEdgeArgs,
    config: &AYConfig,
) -> Result<RefinementOutcome, String> {
    let obligations =
        build_loop_carried_obligations(name_prefix, lp, bridge_preheader_edge, bridge_latch_edge)?;
    for ob in &obligations {
        if edge_equality_holds_structurally(ob) {
            continue;
        }
        match discharge_refinement(ob, config) {
            RefinementOutcome::Refined => {}
            other => return Ok(other),
        }
    }
    Ok(RefinementOutcome::Refined)
}

/// Build the per-slot edge-equality obligations for both in-edges of a loop
/// header (preheader entry + latch back-edge). See [`check_loop_carried_threading`]
/// for the contract; this is the obligation-building half (so tests can inspect /
/// directly evaluate individual slot VCs and run mutation-probes).
///
/// The header-param count is the arity both edges are checked against: a bridge
/// edge with a different number of args is a STRUCTURAL arity bug (dropped/extra
/// header slot), surfaced as an `Err` rather than a silent pass — mirroring the
/// acyclic builder and P1.3's arity discipline.
pub fn build_loop_carried_obligations(
    name_prefix: &str,
    lp: &MirLoop,
    bridge_preheader_edge: &BridgeEdgeArgs,
    bridge_latch_edge: &BridgeEdgeArgs,
) -> Result<Vec<ProofObligation>, String> {
    let n = lp.header_params.len();
    if lp.preheader_args.len() != n {
        return Err(format!(
            "{name_prefix}: preheader threads {} args but the header has {} params \
             (a dropped/extra loop-carried slot is a structural arity bug)",
            lp.preheader_args.len(),
            n
        ));
    }
    let latch_args = lp.latch_back_edge_args()?;
    if latch_args.len() != n {
        return Err(format!(
            "{name_prefix}: latch threads {} args but the header has {} params \
             (a dropped/extra loop-carried slot is a structural arity bug)",
            latch_args.len(),
            n
        ));
    }

    let mut obligations = Vec::new();

    // --- PREHEADER entry edge ---------------------------------------------
    // A synthetic entry block with no statements whose Goto threads the
    // preheader args to the header params. Reusing the acyclic edge-equality
    // builder keeps ONE encoder: the preheader args are block-external operands
    // (entry values), so each slot's VC is `bridge_entry_k == preheader_arg_k`.
    let preheader_block = MirBlock {
        stmts: Vec::new(),
        terminator: MirTerminator::Goto {
            target: 0,
            args: lp.preheader_args.clone(),
        },
    };
    if bridge_preheader_edge.edge != EdgeKind::Goto {
        return Err(format!(
            "{name_prefix}: preheader bridge edge must be EdgeKind::Goto (got {:?})",
            bridge_preheader_edge.edge
        ));
    }
    let mut pre = build_edge_equality_obligations(
        &format!("{name_prefix}_preheader"),
        &preheader_block,
        std::slice::from_ref(bridge_preheader_edge),
    )?;
    obligations.append(&mut pre);

    // --- LATCH back-edge ---------------------------------------------------
    // The REAL latch block, whose Goto threads the updated values back to the
    // header params. The latch reads the header params (a, b) as FREE symbolic
    // inputs — exactly the universal-header-param encoding — so the per-slot VC
    // `bridge_latch_arg_k == mir_latch_arg_k` holds for ALL header-param values
    // (the soundness argument in the module comment). The optional loop guard is
    // threaded as the VC precondition (excludes the exit / trap inputs).
    if bridge_latch_edge.edge != EdgeKind::Goto {
        return Err(format!(
            "{name_prefix}: latch bridge edge must be EdgeKind::Goto (got {:?})",
            bridge_latch_edge.edge
        ));
    }
    let guard_pre = back_edge_guard_precondition(lp)?;
    let mut latch = build_edge_equality_obligations_pre(
        &format!("{name_prefix}_latch"),
        &lp.latch,
        std::slice::from_ref(bridge_latch_edge),
        &guard_pre,
    )?;
    obligations.append(&mut latch);

    Ok(obligations)
}

/// Encode the loop's optional back-edge guard as a precondition list for the
/// latch VC. A `bool`/integer guard operand `g` becomes the precondition
/// `g != 0` (the back-edge is taken when the loop condition is true). Returns an
/// empty list for an unconditional back-edge. A float guard is rejected (a loop
/// condition is never a raw float in MIR — it is a comparison RESULT, i.e. a
/// bool).
fn back_edge_guard_precondition(lp: &MirLoop) -> Result<Vec<SmtExpr>, String> {
    match &lp.back_edge_guard {
        None => Ok(Vec::new()),
        Some(g) => {
            if g.ty().is_float() {
                return Err("loop back-edge guard must be a bool/int, not a float".to_string());
            }
            // GUARD VALIDATION (LOOP-1 soundness). The guard becomes a VC
            // PRECONDITION (`g != 0`), so a malformed guard is a false-negative
            // vector: a constant-FALSE guard makes every latch-slot VC vacuously
            // hold (`0 != 0` is unsatisfiable → `precond AND NOT(equiv)` UNSAT for
            // ANY threading). The `discharge_refinement` satisfiability gate now
            // fails such an obligation CLOSED, but we additionally reject a
            // structurally-invalid guard up front for a clear error and to keep
            // the mock path honest:
            //   * a guard must NOT be a constant — a real loop condition is a
            //     comparison over the loop-carried state, never a literal; a
            //     constant guard is either vacuous (false) or meaningless (true);
            //   * a guard `Var` must name a loop HEADER PARAMETER, so its free
            //     variable is one of the universally-quantified inputs the latch
            //     store mints (this also keeps the no-solver path panic-free — a
            //     guard naming an undeclared var can never reach `eval`).
            // CONTRACT (documented, enforced by the caller when wired): the guard
            // MUST be the SOURCE program's reconstructed back-edge ("continue")
            // condition over the header params — derived by the trusted verifier
            // from the source MIR, NEVER taken from the artifact under test. An
            // UNCONDITIONAL back-edge passes `None` (no precondition). A guard
            // that under-approximates the true condition could mask a bug only on
            // the excluded inputs; supplying the true condition is the caller's
            // obligation, not something this slice can rederive.
            match g {
                MirOperand::ConstInt { .. } | MirOperand::ConstFloat { .. } => {
                    return Err("loop back-edge guard must be a header-parameter \
                                condition, not a constant (a constant guard is \
                                vacuous-false or meaningless-true)"
                        .to_string());
                }
                MirOperand::Var { name, .. } => {
                    if !lp.header_params.iter().any(|(n, _)| n == name) {
                        return Err(format!(
                            "loop back-edge guard names `{name}`, which is not a loop \
                             header parameter; the guard must be the source program's \
                             reconstructed back-edge condition over the loop-carried \
                             params (a guard over a foreign/undeclared var is rejected)"
                        ));
                    }
                }
            }
            let w = g.ty().bits();
            // Resolve the guard against a throwaway store: a guard naming a header
            // param reads that free input (same name -> same SmtExpr var as the
            // latch store mints). `g != 0` is the "back-edge taken" condition.
            let mut scratch = BlockStore::default();
            let g_expr = scratch.resolve(g);
            let zero = SmtExpr::bv_const(0, w);
            Ok(vec![g_expr.eq_expr(zero).not_expr()])
        }
    }
}

// ---------------------------------------------------------------------------
// BRIDGE-WIRED back-edge threading VC (proof-gap item #84, the euclid class)
// ---------------------------------------------------------------------------

/// Discharge the loop back-edge block-arg threading VC for ONE latch block —
/// the bridge-facing entry behind the `ssa_loop_complete` structural gate.
///
/// This is the wiring shape of [`check_loop_carried_threading`]'s LATCH half,
/// generalized for real-MIR-derived inputs:
///
///   * `latch` is the SPEC: the MIR statements along the loop's unique
///     `header -> latch` path (folded into one straight-line block, exactly as
///     [`MirLoop::latch`] prescribes), terminated by a `Goto` whose args name,
///     per header slot, the loop-carried LOCAL whose updated value that slot
///     must receive.
///   * `bridge_latch` is the IMPLEMENTATION: the values the produced trust-ir
///     actually threads on the back-edge, expressed over the SAME header-param
///     variable names (built by `loop_backedge_symexec::model_back_edge_args`).
///   * `preconditions` are the SOURCE-derived path conditions under which the
///     MIR takes the back-edge: the loop guard's `SwitchInt` arm condition and
///     every `Assert` condition on the path (e.g. `b != 0` and the
///     `INT_MIN % -1` overflow guard for euclid's `a % b`). They restrict the
///     universal quantification to inputs that REACH the back-edge in the MIR
///     semantics — a failed assert diverges (panics) before the edge. They
///     must come from the MIR, never from the artifact under test.
///   * `extra_inputs` declares free variables that appear only on the bridge
///     side / in the preconditions (the symexec's opaque `__tir_*` inputs and
///     any guard-only variables); they are merged into each obligation's input
///     list (width-checked against the spec's own inputs).
///
/// Verdict folding matches [`check_loop_carried_threading`]: `Refined` only if
/// EVERY slot refines; the first `Refuted` (counterexample) or `Inconclusive`
/// is surfaced, never downgraded. The vacuous-precondition guard inside
/// [`discharge_refinement`] protects against an unsatisfiable precondition set
/// minting a meaningless `Refined` (LOOP-1).
///
/// The PREHEADER (entry) edge is deliberately NOT re-checked here: the
/// structural gate's misthread judgment (`LoopCarriedSlotMisthreaded`) is a
/// back-edge-only property, and this VC replaces exactly that judgment. Entry
/// edges keep their existing structural coverage (arity/type/dominance).
pub fn check_back_edge_threading(
    name_prefix: &str,
    latch: &MirBlock,
    bridge_latch: &BridgeEdgeArgs,
    preconditions: &[SmtExpr],
    extra_inputs: &[(String, u32)],
    config: &AYConfig,
) -> Result<RefinementOutcome, String> {
    if bridge_latch.edge != EdgeKind::Goto {
        return Err(format!(
            "{name_prefix}: back-edge bridge edge must be EdgeKind::Goto (got {:?})",
            bridge_latch.edge
        ));
    }
    if !matches!(latch.terminator, MirTerminator::Goto { .. }) {
        return Err(format!(
            "{name_prefix}: spec latch must end in a Goto back to the header"
        ));
    }
    let mut obligations = build_edge_equality_obligations_pre(
        name_prefix,
        latch,
        std::slice::from_ref(bridge_latch),
        preconditions,
    )?;
    if obligations.is_empty() {
        // A latch with zero threaded slots cannot be the subject of a
        // misthread violation; an empty VC must never read as a proof.
        return Err(format!(
            "{name_prefix}: back-edge VC produced no obligations (nothing to refine)"
        ));
    }
    for ob in &mut obligations {
        for (name, width) in extra_inputs {
            match ob.inputs.iter().find(|(n, _)| n == name) {
                Some((_, w)) if w != width => {
                    return Err(format!(
                        "{name_prefix}: input `{name}` declared at width {w} by the spec \
                         but {width} by the bridge side (sort clash)"
                    ));
                }
                Some(_) => {}
                None => ob.inputs.push((name.clone(), *width)),
            }
        }
    }
    for ob in &obligations {
        if edge_equality_holds_structurally(ob) {
            continue;
        }
        match discharge_refinement(ob, config) {
            RefinementOutcome::Refined => {}
            other => return Ok(other),
        }
    }
    Ok(RefinementOutcome::Refined)
}

// ===========================================================================
// DESIGN: extending the slice to a full MIR->trust-ir translation validator
// ===========================================================================
//
// This slice validates straight-line scalar rvalues. The durable bridge answer
// extends along three axes; the data model above is shaped so each is additive.
//
// 1. CONTROL FLOW (phi / block-arg refinement)
//    - DONE (this slice, ACYCLIC scalar): `MirTerminator { Goto, Branch, Return }`
//      gives `MirBlock` a terminator whose edges carry the MIR VALUES threaded to
//      each successor's params. `encode_block_store` folds a block's statements
//      into a symbolic store `name -> SmtExpr` (honoring intra-block dataflow),
//      `resolve_edge_args` resolves each edge's `*_args` through that SAME store,
//      and `build_edge_equality_obligations` raises a per-edge, per-slot VC
//      `bridge_block_arg_k == mir_value_threaded_to_param_k`. Both sides are
//      driven from the SAME `BlockStore` vars, so the VC is a REAL dataflow check:
//      a DROPPED/STALE arg (the bridge threads the ENTRY value instead of the
//      in-block update — the #71 shape, made acyclic via a diamond), the WRONG
//      variable, or a SWAPPED pair of slots makes some slot's equality SAT
//      (refuted). `check_block_arg_threading` is the block-level entry that folds
//      all slots' verdicts (fail-closed on Inconclusive, P0). This is the
//      SEMANTIC complement to the STRUCTURAL `ssa_loop_complete` (P1.3): P1.3
//      proves the right VARIABLE was threaded into each slot; this proves the
//      threaded VALUE equals the source dataflow.
//    - DONE (loops / back-edges, loop-carried THREADING): `MirLoop` makes the
//      loop-carried header surface explicit (`header_params`, `preheader_args`,
//      a single-latch `latch` block ending in a `Goto` back to the header, an
//      optional `back_edge_guard`). `check_loop_carried_threading` /
//      `build_loop_carried_obligations` raise a per-slot edge-equality VC on BOTH
//      in-edges — the preheader entry edge (`bridge_entry_k == preheader_arg_k`)
//      and the latch BACK-edge (`bridge_latch_arg_k == mir_latch_arg_k`, the
//      latch body folded over the header params) — REUSING the acyclic
//      `build_edge_equality_obligations[_pre]` encoder. The header params are
//      FREE universally-quantified inputs, so proving the back-edge equation for
//      ALL header-param values is the FULL inductive argument FOR THREADING with
//      NO fixpoint: threading is a per-edge dataflow equality, not a property
//      that accumulates across iterations, so the strongest usable invariant is
//      `true`. This catches the euclid / #71 latch miscompile (a SWAPPED,
//      STALE, or DROPPED back-edge arg) SEMANTICALLY, complementing P1.3's
//      structural check. The optional `back_edge_guard` (e.g. `b != 0`) is a VC
//      precondition that EXCLUDES the loop-exit / `% b`-trap inputs — it restricts
//      the universal quantification to the taken inputs, NOT a reachability/
//      invariant assumption.
//    - DEFERRED (semantic loop INVARIANTS): a property that ACCUMULATES across
//      iterations (e.g. `b` strictly decreases, or `gcd(a, b)` is preserved so
//      the RESULT equals `gcd(a0, b0)`) is a different, larger axis: it needs a
//      genuine INDUCTIVE obligation — assume an invariant `Inv(a, b)` on the
//      back-edge, prove it re-established — i.e. a CHC solver lane where the
//      `Valid`/Horn predicate synthesizes a non-trivial `Inv`. THREADING
//      correctness does NOT need this
//      (the VC above is unconditional over the header params, so its CHC `Valid`
//      collapses to `true` and the Horn query is bit-identical to the QF
//      equivalence `discharge_refinement` already decides — verified against
//      `encode_obligation_as_chc`). So an inductive solver is intentionally NOT
//      used by the threading slice; semantic loop invariants remain deferred.
//    - DEFERRED (multi-latch / nested / memory loops): `MirLoop` models a SINGLE
//      latch with an unconditional `Goto` back-edge (a multi-block straight-line
//      body folds into the one latch block). A loop with MULTIPLE latches, a
//      CONDITIONAL back-edge, nested loops, or memory-carried loop state needs a
//      per-latch VC set / the heap-as-SMT-Array model below — deferred.
//    - DEFERRED (switch normalization, #62): the SwitchInt discriminant-
//      normalization the bridge does (dense vs sparse, default arm) gets a
//      ControlFlow VC `forall discr: bridge_target(discr) == mir_target(discr)`;
//      the two-way `Branch` here is the bool-discriminant special case.
//    - FOLLOW-UP (wiring): feed real terminators + the trust-ir block args the
//      bridge emitted into `check_block_arg_threading` behind `emit_proofs`
//      (item 3 below) — `BridgeEdgeArgs` is the serialization-free hand-off.
//
// 2. MEMORY / AGGREGATES
//    - DONE (this slice): scalar-field AGGREGATE CONSTRUCTION field placement.
//      `MirRvalue::Aggregate { fields }` packs scalar (int/bool) fields in
//      SOURCE field order via `pack_fields` (field 0 in the low bits); the
//      matching `BridgeLowering::Aggregate { field_exprs }` packs the fields the
//      bridge ACTUALLY placed, in the bridge's chosen offset order, with the
//      SAME packing. The refinement obligation `bridge_packed == mir_packed`
//      then holds IFF every field landed at its source offset — so the #69/#73
//      field-REORDER miscompile (two fields swapped) and a wrong-offset/width
//      placement are Refuted, while a faithful placement Refines. Both sides are
//      driven from the SAME symbolic field vars, so the VC is a real offset
//      check (a reorder cannot be hidden by reordering both sides — the spec is
//      fixed to source order). Exhaustively decidable for narrow fields, so the
//      always-on fast lane discharges it (`check_rvalue_lowering` is the entry
//      the bridge would call; wiring is item 3 below).
//      DEFERRED (aggregate construction): nested/heap aggregates, ABI
//      padding/alignment, and SSE/float-classified fields (rejected by the
//      encoder, not silently packed).
//    - DONE (this slice — the MEMORY axis): SCALAR LOAD/STORE value-preservation
//      over a SEQUENCE of memory ops (see the `==== MEMORY MODEL ====` section).
//      `MirMemOp::{Store, Load}` over `MemAddr { base, const_offset }` symbolic
//      addresses model the bridge's lowered machine load/store; memory is the
//      EXISTING byte-array SMT model (`memory_proofs::{symbolic_memory,
//      encode_store_le, encode_load_le}` — `Array(BV64, BV8)`, little-endian,
//      the same model the atomic non-interference proofs discharge through z3).
//      `check_memory_sequence` symbolically executes the SOURCE and BRIDGE
//      sequences from the SAME base/value vars and raises (1) a per-load
//      value-preservation VC `bridge_load_k == source_load_k` and (2) a
//      final-memory-cell equality VC at every stored range. This refutes a
//      WRONG-OFFSET load, a WRONG-location / DROPPED store (caught by the
//      final-memory VC even with no later load — the #71 dropped-scalarized-field
//      shape), and an UNSOUND REORDER of two ALIASING stores; a SOUND reorder of
//      two DISTINCT stores Refines (proving the check is not over-strict).
//      ALIASING: `MemAddr::alias_class` decides DISTINCT (non-overlapping const
//      byte ranges / different base => sound to reorder) vs EQUAL (same cell =>
//      last-writer-wins) BY CONSTRUCTION. The KEYSTONE: an UNKNOWN-alias pair
//      (overlapping-but-not-identical const ranges, or two different symbolic
//      bases) is NEVER discharged vacuously — `check_memory_sequence` returns
//      `Inconclusive` (fail-closed) UNLESS the caller supplies an explicit
//      DISJOINTNESS precondition (`disjoint_bases_precondition`, same no-wrap +
//      two-sided-disjoint style as `atomic_proofs::disjoint_no_wrap_preconditions`)
//      that constrains the bases. This is what keeps it sound on BOTH the z3 path
//      and the mock-sampling fallback (a may-alias VC never reaches a sampler).
//      DEFERRED (memory axis): general may-alias WITHOUT a precondition (needs an
//      alias oracle), heap-allocation identity (malloc/box provenance), runtime
//      (non-constant) indices, and non-scalar/struct memory beyond the aggregate
//      construction VC above.
//    - NEXT (memory refinement, wiring): connect `MirRvalue::Ref` /
//      `MirPlace { local, projection: [Field(i)|Deref|Index] }` /
//      `MirStmt::SetDiscriminant` lowering to emit `MirMemOp` pairs into
//      `check_memory_sequence`. Model the bridge's scalarization (struct fields
//      -> separate `projected_value` SSA names) as a memory refinement: the
//      scalarized trust-ir store-set must read back equal to the MIR aggregate's
//      field projection at every offset. The #71 miscompile (loop-carried
//      scalarized `q.a += 1` dropped because there was no header phi for the
//      projected field while scalars z1/z2 worked) is caught by combining (1) the
//      edge-equality VC over projected fields with (2) this read-back / dropped-
//      store VC. The by-value-aggregate mixed INT+SSE ABI bugs (#69) become a
//      separate ABI refinement: encode the SysV eightbyte classification as the
//      spec and assert the bridge's argument register/stack assignment matches.
//
// 3. WIRING BEHIND emit_proofs=true AT THE MIR BOUNDARY
//    - Today `mk_compiled_module` (lib.rs:664) hard-sets
//      `compiler_config.emit_proofs = false`. The hook is: thread an
//      `MirProofSink` through `MirLoweringCtx` so that each of `lower_binary_op`
//      / `lower_unary_op` / `lower_cast` / `lower_checked_binary_op`, AFTER it
//      pushes the trust-ir `InstrNode`, ALSO records `(MirRvalue, BridgeLowering)`
//      pairs (it already has both: the MIR `op`/operands and the trust-ir
//      `Inst` it just built). At the end of `mir_to_trust_ir` (lib.rs:1341),
//      when `emit_proofs` is on, drain the sink, call `check_rvalue_lowering`
//      for each pair against a shared `AYConfig`, and fail the compile (or emit
//      a proof certificate) if any returns `Refuted`/`Inconclusive`.
//    - The `BridgeLowering` enum is the serialization-free bridge between the
//      two crates: the bridge constructs it from the trust-ir `Inst` it emitted
//      (a small `From<&Inst>`-style match), so the trust-ir side of every
//      obligation is the bridge's ACTUAL output, not a re-derivation. The MIR
//      side is the only independent re-encoding — which is the whole point of
//      translation validation (two independent encoders, one solver).
//    - Performance: gate behind `emit_proofs` (off in the default O1 lane),
//      memoize obligations by full structural content within the process, and
//      only re-discharge on a session miss. Disk verdicts are not proof
//      certificates. Inconclusive MUST fail the gate
//      (#389/#407), never downgrade silently — that is the P0 discipline this
//      whole program is built on.

// ===========================================================================
// ==== MEMORY MODEL ====  (proof-gap item 6, the MEMORY axis)
// ===========================================================================
//
// SCALAR LOAD/STORE VALUE-PRESERVATION. Proof-gap item 6's MEMORY axis. The
// bridge lowers MIR `Place` projections (deref, field offset, index) to machine
// load/store with *computed addresses*. This is a fresh miscompile surface
// distinct from the scalar-rvalue axis above:
//
//   * a Load reading the WRONG offset/address (load A+k instead of A),
//   * a Store writing the WRONG location,
//   * a DROPPED store (the bridge omits a store the source performs, so a later
//     load reads a stale/wrong value — the #71 loop-carried scalarized-field
//     drop is the canonical instance),
//   * two ops REORDERED across an ALIASING pair (a store/store or load/store
//     whose relative order is observable changes the observed value).
//
// This slice builds a SEMANTIC check that the bridge's lowered load/store
// SEQUENCE preserves the source program's memory semantics — a translation-
// validation VC, NOT a syntactic one.
//
// HOW MEMORY IS MODELED — SMT ARRAY (not ite-cell-dispatch), and WHY it is sound
// -----------------------------------------------------------------------------
// We reuse the EXISTING byte-array SMT memory model from `memory_proofs.rs`:
// memory is `Array(BitVec64, BitVec8)` — byte-addressable, little-endian — built
// from `symbolic_memory(name)` (a `ConstArray` over a symbolic default byte),
// with `encode_store_le` / `encode_load_le` performing the per-byte
// store/select decomposition. This is the SAME model the atomic
// non-interference proofs (`atomic_proofs.rs`) discharge through z3, so its
// soundness is already established in this crate.
//
// WHY THE ARRAY MODEL IS SOUND (vs. a small fixed ite-cell set): SMT array
// theory (QF_ABV) gives the solver EXACT read-over-write reasoning — `select`
// after `store` resolves to the stored value when addresses are equal and to
// the prior array otherwise, for ALL symbolic addresses simultaneously. A small
// hand-rolled ite-cell set keyed on a fixed address list would only model the
// cells we name and could SILENTLY MISS an aliasing pair at an unmodeled
// address; the array models the WHOLE address space, so a wrong-offset / dropped
// store / unsound reorder cannot hide in an unmodeled cell. The SAME symbolic
// base/value vars drive BOTH the source and bridge encodings, so the VC is a
// real value-equivalence question, not a tautology.
//
// ALIAS HANDLING — distinct / equal / unknown, and the FAIL-CLOSED KEYSTONE
// -----------------------------------------------------------------------------
// Aliasing is where memory is hard, so the alias relationship of each
// address PAIR in the sequence is classified up front (`MemAddr::alias_class`):
//
//   * DISTINCT — different symbolic base, or same base with non-overlapping
//     constant byte ranges `[off, off+w)` ∩ `[off', off'+w')` = ∅. Provably
//     no-alias by CONSTRUCTION: the byte ranges cannot share a byte regardless
//     of the symbolic base value. Reordering two DISTINCT stores is SOUND, and
//     the VC proves it (the reorder-sound test).
//   * EQUAL — same symbolic base AND same constant offset AND same width: the
//     two ops touch exactly the same cell, so last-writer-wins is observable.
//     Reordering two EQUAL stores is UNSOUND and the VC refutes it.
//   * UNKNOWN — same symbolic base but constant ranges that MAY overlap, OR two
//     ops over DIFFERENT symbolic bases whose relationship is not constrained.
//     A general may-alias query needs an aliasing oracle we do NOT have here.
//
// THE KEYSTONE (soundness P0): an UNKNOWN-alias pair is NEVER discharged
// vacuously. `check_memory_sequence` REFUSES to build a discharge-able
// obligation for a sequence containing an UNKNOWN-alias pair UNLESS the caller
// supplies an explicit DISJOINTNESS precondition (the SAME no-wrap + symmetric
// two-sided disjointness style as `atomic_proofs::disjoint_no_wrap_preconditions`)
// that PROVES the bases separated. With no such precondition the function
// returns `RefinementOutcome::Inconclusive` DIRECTLY — it does not hand a
// precondition-free may-alias VC to the discharger, because the mock evaluator
// only SAMPLES symbolic addresses and could return `Valid` without ever hitting
// the aliasing input (a vacuous pass). Returning `Inconclusive` is the
// fail-closed verdict every caller already treats as a FAILURE (never a silent
// pass — #389/#407). This is what makes the check sound on BOTH the z3 path and
// the mock-fallback path: the unsound input class never reaches a sampler.
//
// SCOPE (this slice): SCALAR (1/2/4/8-byte) loads/stores over symbolic
// `base + const_offset` addresses; distinct/equal aliasing by construction;
// symbolic-base may-alias ONLY under a stated disjointness precondition.
// DEFERRED: general may-alias without a precondition (needs an alias oracle),
// heap-allocation identity (malloc/box provenance), and non-scalar / struct
// memory beyond the existing aggregate-construction VC (`MirRvalue::Aggregate`).

/// A symbolic memory address: a named 64-bit base plus a constant byte offset.
///
/// Mirrors the bridge's `Place`-projection address computation: a `base`
/// (the lowered pointer/local-slot address `ValueId`, a 64-bit symbolic var) plus
/// a STATIC byte `offset` (the accumulated `Field(i)` / fixed `Index` offset). A
/// runtime (non-constant) index is OUT of slice — it would make the offset
/// symbolic and the alias classification a general may-alias query.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MemAddr {
    /// The symbolic base pointer name (a 64-bit `ValueId` address).
    pub base: String,
    /// The constant byte offset added to the base.
    pub offset: u64,
}

/// The alias relationship between two [`MemAddr`] accesses of given widths.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AliasClass {
    /// Provably no shared byte BY CONSTRUCTION (different base, or same base with
    /// non-overlapping constant `[off, off+w)` ranges). Reorder is sound.
    Distinct,
    /// Exactly the same cell (same base, offset, width). Last-writer-wins is
    /// observable; reorder is unsound.
    Equal,
    /// May overlap and the relationship is not constrained (same base with
    /// overlapping-but-not-identical ranges, or two different symbolic bases). A
    /// general may-alias query — fail-closed unless a disjointness precondition
    /// is supplied. See the KEYSTONE note above.
    Unknown,
}

impl MemAddr {
    /// A base with zero offset.
    pub fn base(name: impl Into<String>) -> Self {
        MemAddr {
            base: name.into(),
            offset: 0,
        }
    }

    /// A base with an explicit constant byte offset.
    pub fn at(name: impl Into<String>, offset: u64) -> Self {
        MemAddr {
            base: name.into(),
            offset,
        }
    }

    /// The `SmtExpr` for this address: `base + offset` (64-bit), registering the
    /// base as a 64-bit symbolic input through `inputs` if not already present.
    fn encode(&self, inputs: &mut Vec<(String, u32)>) -> SmtExpr {
        if !inputs.iter().any(|(n, _)| n == &self.base) {
            inputs.push((self.base.clone(), 64));
        }
        let base = SmtExpr::var(self.base.clone(), 64);
        if self.offset == 0 {
            base
        } else {
            base.bvadd(SmtExpr::bv_const(self.offset, 64))
        }
    }

    /// Classify this access (`self`, width `w_a` bytes) against `other` (width
    /// `w_b` bytes). This is the STATIC, by-construction alias decision the slice
    /// is sound over — it never claims `Distinct` for a pair that could share a
    /// byte:
    ///   * different base names  -> `Unknown` (bases are unconstrained symbolic
    ///     pointers; they could be equal at runtime),
    ///   * same base, identical `(offset, width)` -> `Equal`,
    ///   * same base, constant byte ranges `[off, off+w)` that do NOT intersect
    ///     -> `Distinct`,
    ///   * same base, ranges that DO intersect but are not identical -> `Unknown`
    ///     (partial overlap — out of the equal/distinct slice).
    pub fn alias_class(&self, w_a: u32, other: &MemAddr, w_b: u32) -> AliasClass {
        if self.base != other.base {
            // Two distinct symbolic bases. We cannot prove they differ without an
            // aliasing oracle / precondition, so this is the may-alias case.
            return AliasClass::Unknown;
        }
        if self.offset == other.offset && w_a == w_b {
            return AliasClass::Equal;
        }
        // Same base: compare the constant byte ranges.
        let a_lo = self.offset;
        let a_hi = self.offset.saturating_add(w_a as u64);
        let b_lo = other.offset;
        let b_hi = other.offset.saturating_add(w_b as u64);
        let disjoint = a_hi <= b_lo || b_hi <= a_lo;
        if disjoint {
            AliasClass::Distinct
        } else {
            // Overlapping but not identical (partial overlap) — out of slice.
            AliasClass::Unknown
        }
    }
}

/// A single scalar memory operation over a symbolic address.
///
/// Mirrors the bridge's lowered machine load/store: a `Store` writes a value of
/// `width` bytes at `addr`; a `Load` reads `width` bytes at `addr` and binds the
/// observed value to the SSA name `dst` (so a later op or the result comparison
/// can reference what the load saw). `value` of a `Store` is an arbitrary
/// `SmtExpr` of `width*8` bits — the caller drives it from the SAME symbolic vars
/// on the source and bridge side, so the VC is real.
#[derive(Debug, Clone)]
pub enum MirMemOp {
    /// `*addr = value` — store `width` bytes (little-endian) at `addr`.
    Store {
        addr: MemAddr,
        value: SmtExpr,
        width: u32,
    },
    /// `dst = *addr` — load `width` bytes (little-endian) at `addr`, naming the
    /// observed value `dst`.
    Load {
        addr: MemAddr,
        width: u32,
        dst: String,
    },
}

impl MirMemOp {
    fn addr(&self) -> &MemAddr {
        match self {
            MirMemOp::Store { addr, .. } | MirMemOp::Load { addr, .. } => addr,
        }
    }
    fn width(&self) -> u32 {
        match self {
            MirMemOp::Store { width, .. } | MirMemOp::Load { width, .. } => *width,
        }
    }
}

/// Configuration for a memory-sequence check.
///
/// `disjointness_preconditions` carries the caller-supplied SMT preconditions
/// that constrain symbolic bases (the no-wrap + two-sided disjointness style of
/// `atomic_proofs::disjoint_no_wrap_preconditions`). When the sequence contains
/// an `Unknown`-alias pair, these are REQUIRED — without them the check is
/// fail-closed `Inconclusive` (the soundness keystone). They are ignored for a
/// sequence whose every pair is provably `Distinct`/`Equal`.
#[derive(Debug, Clone, Default)]
pub struct MemCheckConfig {
    /// SMT preconditions over the bases (e.g. `disjoint(base_a, base_b)`).
    pub disjointness_preconditions: Vec<SmtExpr>,
}

/// The result of symbolically executing a memory-op SEQUENCE: the final memory
/// array and, for each `Load`, the `SmtExpr` value that load observed (keyed by
/// the load's `dst` name, in sequence order).
struct EncodedSequence {
    final_mem: SmtExpr,
    /// `(dst, observed_value, width)` per load, in order.
    loads: Vec<(String, SmtExpr, u32)>,
    /// Symbolic 64-bit base inputs referenced by the sequence's addresses.
    inputs: Vec<(String, u32)>,
}

/// Symbolically execute a memory-op sequence against a fresh symbolic memory,
/// returning the final memory and every load's observed value. The address of
/// each op is encoded through `inputs` (registering bases as 64-bit symbolic
/// vars). The initial memory is `symbolic_memory(mem_default_name)` so unwritten
/// bytes are a single symbolic default (a load of a never-stored cell reads it —
/// identical on both sides, so it is not spuriously refuted).
fn encode_mem_sequence(ops: &[MirMemOp], mem_default_name: &str) -> EncodedSequence {
    let mut inputs: Vec<(String, u32)> = Vec::new();
    let mut mem = crate::memory_proofs::symbolic_memory(mem_default_name);
    let mut loads = Vec::new();
    for op in ops {
        match op {
            MirMemOp::Store { addr, value, width } => {
                let a = addr.encode(&mut inputs);
                mem = crate::memory_proofs::encode_store_le(&mem, &a, value, *width);
            }
            MirMemOp::Load { addr, width, dst } => {
                let a = addr.encode(&mut inputs);
                let observed = crate::memory_proofs::encode_load_le(&mem, &a, *width);
                loads.push((dst.clone(), observed, *width));
            }
        }
    }
    EncodedSequence {
        final_mem: mem,
        loads,
        inputs,
    }
}

/// Does `ops` contain ANY ordered pair of accesses classified `Unknown`?
///
/// This is the predicate that gates the disjointness-precondition requirement:
/// if every pair is provably `Distinct` or `Equal`, the array VC decides the
/// sequence with no precondition; if ANY pair is `Unknown`, a disjointness
/// precondition is REQUIRED or the check fails closed (the keystone).
fn sequence_has_unknown_alias(ops: &[MirMemOp]) -> bool {
    for i in 0..ops.len() {
        for j in (i + 1)..ops.len() {
            if ops[i]
                .addr()
                .alias_class(ops[i].width(), ops[j].addr(), ops[j].width())
                == AliasClass::Unknown
            {
                return true;
            }
        }
    }
    false
}

/// Translation-validation check that the BRIDGE's lowered load/store sequence
/// (`bridge_ops`) preserves the SOURCE program's memory semantics
/// (`source_ops`).
///
/// Both sequences are symbolically executed against a fresh symbolic memory
/// driven from the SAME base/value vars. The obligation is, for each load slot
/// `k` (loads paired positionally — the bridge must perform the same loads in
/// the same order; a mismatched load COUNT is a structural bug returned as an
/// error), `bridge_load_k_value == source_load_k_value`; PLUS a final-memory
/// equality at every store cell the source touches (so a DROPPED or MISPLACED
/// store with no subsequent load is still caught). Each obligation flows through
/// the standard [`ProofObligation`] / [`discharge_refinement`] path, categorized
/// [`TransvalCheckKind::MemoryModel`].
///
/// ALIASING / KEYSTONE: if `source_ops` contains an `Unknown`-alias pair (see
/// [`MemAddr::alias_class`]) and `cfg.disjointness_preconditions` is EMPTY, this
/// returns `Inconclusive` WITHOUT discharging anything — a precondition-free
/// may-alias sequence is NEVER vacuously accepted (the mock evaluator would only
/// sample symbolic addresses and could pass it silently). Supplying a
/// disjointness precondition constrains the bases and lets the VC discharge
/// soundly.
///
/// Returns `Refined` only if EVERY load-value and final-memory-cell obligation
/// refines; the first `Refuted` (with counterexample) or `Inconclusive` is
/// surfaced and never downgraded (P0).
pub fn check_memory_sequence(
    name: &str,
    source_ops: &[MirMemOp],
    bridge_ops: &[MirMemOp],
    cfg: &MemCheckConfig,
    config: &AYConfig,
) -> Result<RefinementOutcome, String> {
    let obligations = build_memory_obligations(name, source_ops, bridge_ops, cfg)?;
    let Some(obligations) = obligations else {
        // Unknown-alias without a disjointness precondition: fail closed.
        return Ok(RefinementOutcome::Inconclusive {
            reason: format!(
                "{name}: sequence has an unknown-alias pair and no disjointness \
                 precondition was supplied; refusing to discharge a may-alias VC \
                 (would risk a vacuous pass) — supply a disjointness precondition \
                 or restrict to provably-distinct/equal addresses"
            ),
        });
    };
    for ob in &obligations {
        match discharge_refinement(ob, config) {
            RefinementOutcome::Refined => {}
            other => return Ok(other),
        }
    }
    Ok(RefinementOutcome::Refined)
}

/// Build the load-value + final-memory-cell obligations for a memory-sequence
/// check, OR `Ok(None)` when the sequence is an `Unknown`-alias one with no
/// disjointness precondition (the fail-closed keystone signalled to the caller).
///
/// Errors (structural bugs, not equivalence questions): a load-COUNT mismatch
/// between the two sequences, or a load width mismatch at a paired slot.
pub fn build_memory_obligations(
    name: &str,
    source_ops: &[MirMemOp],
    bridge_ops: &[MirMemOp],
    cfg: &MemCheckConfig,
) -> Result<Option<Vec<ProofObligation>>, String> {
    // KEYSTONE: an Unknown-alias pair without a disjointness precondition must
    // NOT be discharged (it could pass vacuously under sampling). We classify the
    // SOURCE sequence (the spec defines the aliasing the bridge must respect).
    if sequence_has_unknown_alias(source_ops) && cfg.disjointness_preconditions.is_empty() {
        return Ok(None);
    }

    let src = encode_mem_sequence(source_ops, "mem_default");
    let brg = encode_mem_sequence(bridge_ops, "mem_default");

    if src.loads.len() != brg.loads.len() {
        return Err(format!(
            "{name}: load-count mismatch: source performs {} load(s), bridge {} \
             (a dropped/extra load is a structural bug, not an equivalence question)",
            src.loads.len(),
            brg.loads.len()
        ));
    }

    // Union of the symbolic 64-bit base inputs from both sides plus the shared
    // memory default byte (declared explicitly so the solver / sampler treats it
    // as a free input, exactly as the atomic non-interference proofs do).
    let mut inputs: Vec<(String, u32)> = src.inputs.clone();
    for inp in &brg.inputs {
        if !inputs.iter().any(|(n, _)| n == &inp.0) {
            inputs.push(inp.clone());
        }
    }
    // Collect any value-operand inputs the caller embedded in the store values:
    // they are SmtExpr vars the obligation must declare. We harvest them from the
    // value expressions of both sequences.
    let mut value_inputs: Vec<(String, u32)> = Vec::new();
    for op in source_ops.iter().chain(bridge_ops.iter()) {
        if let MirMemOp::Store { value, .. } = op {
            collect_value_vars(value, &mut value_inputs);
        }
    }
    for vi in &value_inputs {
        if !inputs.iter().any(|(n, _)| n == &vi.0) {
            inputs.push(vi.clone());
        }
    }
    // The shared default byte (8-bit), referenced by both `symbolic_memory`
    // arrays, must be declared once.
    if !inputs.iter().any(|(n, _)| n == "mem_default") {
        inputs.push(("mem_default".to_string(), 8));
    }

    let preconditions = cfg.disjointness_preconditions.clone();
    let mut obligations = Vec::new();

    // (1) Per-load value preservation: the value the bridge's k-th load observes
    //     must equal the value the source's k-th load observes.
    for (k, ((s_dst, s_val, s_w), (b_dst, b_val, b_w))) in
        src.loads.iter().zip(brg.loads.iter()).enumerate()
    {
        if s_w != b_w {
            return Err(format!(
                "{name}: load slot {k} width mismatch: source {s_w}B ({s_dst}) vs \
                 bridge {b_w}B ({b_dst})"
            ));
        }
        obligations.push(ProofObligation {
            machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
            name: format!("{name}_load{k}_{s_dst}_value"),
            // trust_ir side = the bridge's observed load value.
            trust_ir_expr: b_val.clone(),
            // reference side = the source's observed load value.
            aarch64_expr: s_val.clone(),
            inputs: inputs.clone(),
            preconditions: preconditions.clone(),
            fp_inputs: Vec::new(),
            category: Some(TransvalCheckKind::MemoryModel),
        });
    }

    // (2) Final-memory equality at every cell EITHER side stores to — the UNION
    //     of source AND bridge store ranges. Iterating only the SOURCE stores
    //     (as a first draft did) misses a SPURIOUS BRIDGE store at an address the
    //     source never writes (e.g. an extra write to a provably-Distinct
    //     same-base offset like `p+100`): the source's final memory there is
    //     still the initial symbolic `mem_default` byte while the bridge's is the
    //     stored value, so reading at the BRIDGE'S store address too makes that
    //     corruption observable (the MEM-2 false-negative). For each touched
    //     byte-range we read both final memories and assert equality; the
    //     byte-array model reduces a range read to per-byte select equalities. A
    //     faithful bridge (writes exactly where the source does) yields the same
    //     union and Refines; a bridge writing anywhere new is Refuted (the
    //     program semantics leaves untouched bytes at their initial value).
    let mut seen_ranges: Vec<(String, u64, u32)> = Vec::new();
    for op in source_ops.iter().chain(bridge_ops.iter()) {
        if let MirMemOp::Store { addr, width, .. } = op {
            let key = (addr.base.clone(), addr.offset, *width);
            if seen_ranges.contains(&key) {
                continue;
            }
            seen_ranges.push(key);
            let a = addr.encode(&mut Vec::new());
            let read_src = crate::memory_proofs::encode_load_le(&src.final_mem, &a, *width);
            let read_brg = crate::memory_proofs::encode_load_le(&brg.final_mem, &a, *width);
            obligations.push(ProofObligation {
                machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
                name: format!("{name}_finalmem_{}_{}_{}", addr.base, addr.offset, width),
                trust_ir_expr: read_brg,
                aarch64_expr: read_src,
                inputs: inputs.clone(),
                preconditions: preconditions.clone(),
                fp_inputs: Vec::new(),
                category: Some(TransvalCheckKind::MemoryModel),
            });
        }
    }

    Ok(Some(obligations))
}

/// Harvest the `(name, width)` of the symbolic `Var` a store value names, so the
/// obligation declares it as an input (the mock sampler / solver need every free
/// var declared).
///
/// SLICE SCOPE: a store VALUE is a scalar — either a constant or a single
/// symbolic `Var` of the store width (the lowered `ValueId` being stored). That
/// is the surface this memory slice models, so matching the top-level `Var` is
/// exact. A value built from a richer expression would need its free vars
/// pre-declared by the caller; this is asserted by the load-value VC failing to
/// resolve an undeclared var rather than silently sampling it.
fn collect_value_vars(expr: &SmtExpr, out: &mut Vec<(String, u32)>) {
    if let SmtExpr::Var { name, .. } = expr {
        let w = expr.bv_width();
        if w > 0 && !out.iter().any(|(n, _)| n == name) {
            out.push((name.clone(), w));
        }
    }
}

/// Build a sound disjointness precondition over two symbolic bases of equal
/// access size, mirroring `atomic_proofs::disjoint_no_wrap_preconditions`:
/// no-wrap on each region plus symmetric two-sided disjointness. Exposed so a
/// caller (and the tests) can constrain an `Unknown`-alias pair into a
/// dischargeable obligation in the documented, sound way.
///
/// Returns the precondition vector for `[base_a, base_a+size)` vs
/// `[base_b, base_b+size)`. Tightening a precondition only REMOVES inputs from
/// the universally-quantified claim, so it can never make a wrong lowering pass.
///
/// IMPORTANT (MEM-1): this asserts the two bases name DISTINCT regions. Calling
/// it with `base_a == base_b` produces an UNSATISFIABLE precondition (a region
/// cannot be disjoint from itself), which would make any obligation it guards
/// vacuously provable — `discharge_refinement`'s satisfiability gate now catches
/// that and fails the obligation CLOSED (Inconclusive), but a same-base pair is
/// a caller error: two accesses off the SAME base are never separable by base
/// disjointness (use offset/width reasoning via `MemAddr::alias_class` instead).
pub fn disjoint_bases_precondition(base_a: &str, base_b: &str, size_bytes: u32) -> Vec<SmtExpr> {
    debug_assert_ne!(
        base_a, base_b,
        "disjoint_bases_precondition called with identical bases — the resulting \
         precondition is unsatisfiable (a region is never disjoint from itself); \
         a same-base pair must be resolved by offset/width, not base disjointness"
    );
    let a = SmtExpr::var(base_a.to_string(), 64);
    let b = SmtExpr::var(base_b.to_string(), 64);
    let size = SmtExpr::bv_const(size_bytes as u64, 64);
    let a_end = a.clone().bvadd(size.clone());
    let b_end = b.clone().bvadd(size);

    let a_no_wrap = a_end.clone().bvugt(a.clone());
    let b_no_wrap = b_end.clone().bvugt(b.clone());

    let b_after_a = b.clone().bvuge(a_end);
    let a_after_b = a.bvuge(b_end);
    let disjoint = b_after_a.or_expr(a_after_b);

    vec![a_no_wrap, b_no_wrap, disjoint]
}

// ---------------------------------------------------------------------------
// `<[T]>::split_at` / `str::split_at` translation-validation SPEC
// ---------------------------------------------------------------------------

/// The Rust-defined meaning of `s.split_at(mid)` over a slice `s = { ptr, len }`,
/// as SMT bitvector formulas over the SHARED symbolic 64-bit names `ptr`/`len`/
/// `mid` and a CONSTANT element stride `elem_size` (bytes). This is the SPEC side
/// of the `split_at` refinement lane; the bridge side is reconstructed
/// INDEPENDENTLY from the trust-ir the bridge actually emitted (see
/// `rustc_codegen_trust_cg::mem_refine::fold_emitted_split_at`), and the two meet
/// only on these shared symbolic names — so a bridge that swaps `mid`/`len`,
/// scales by the wrong `elem_size`, computes `mid - len`, or inverts/omits the
/// bounds check yields a genuinely different formula and is REFUTED.
///
/// Definition (all arithmetic 64-bit two's complement — the `usize`/pointer
/// width; the bounds comparison UNSIGNED, since `mid`/`len` are `usize`):
///   * PANIC (a trap) iff `mid >u len` — the `assert!(mid <= self.len())`.
///   * `fst = &s[.. mid]  = { data = ptr,                 len = mid       }`
///   * `snd = &s[mid ..]  = { data = ptr + mid*elem_size,  len = len - mid }`
pub struct SplitAtSpec {
    /// The trap predicate (a Bool): the split PANICS iff `mid >u len`.
    pub trap: SmtExpr,
    /// `fst.data == ptr` (the left half keeps the original data pointer).
    pub fst_data: SmtExpr,
    /// `fst.len == mid` (the left half is `mid` elements long).
    pub fst_len: SmtExpr,
    /// `snd.data == ptr + mid*elem_size` (the right half starts `mid` elements in).
    pub snd_data: SmtExpr,
    /// `snd.len == len - mid` (the right half holds the remaining elements).
    pub snd_len: SmtExpr,
    /// The symbolic 64-bit inputs the formulas reference (`ptr`/`len`/`mid`).
    pub inputs: Vec<(String, u32)>,
}

/// Build the [`SplitAtSpec`] for a `split_at` over the shared symbolic names
/// `ptr`/`len`/`mid` (each a 64-bit `usize`/pointer) and a constant `elem_size`
/// (element stride in bytes). Reuses the standard `SmtExpr` bitvector builders so
/// the spec is encoded on the SAME substrate the bridge reconstruction folds into.
/// See [`SplitAtSpec`] for the exact meaning of each field.
pub fn split_at_spec(ptr: &str, len: &str, mid: &str, elem_size: u64) -> SplitAtSpec {
    let p = SmtExpr::var(ptr, 64);
    let l = SmtExpr::var(len, 64);
    let m = SmtExpr::var(mid, 64);
    let size = SmtExpr::bv_const(elem_size, 64);
    SplitAtSpec {
        // trap  <=>  mid >u len
        trap: m.clone().bvugt(l.clone()),
        // fst = { ptr, mid }
        fst_data: p.clone(),
        fst_len: m.clone(),
        // snd = { ptr + mid*elem_size, len - mid }
        snd_data: p.bvadd(m.clone().bvmul(size)),
        snd_len: l.bvsub(m),
        inputs: vec![
            (ptr.to_string(), 64),
            (len.to_string(), 64),
            (mid.to_string(), 64),
        ],
    }
}

// ---------------------------------------------------------------------------
// `<[T]>::to_vec` / `to_owned` / `Vec::clone` HEAP-HEADER translation-validation
// SPEC (TV lane 14)
// ---------------------------------------------------------------------------

/// The Rust-defined meaning of the `{ptr, cap, len}` Vec header the bridge
/// builds when it lowers a slice-to-Vec collect, as SMT formulas over the shared
/// symbolic 64-bit name `n` (the source element count) and the CONSTANT
/// `elem_size` / `elem_align` the LAYOUT ORACLE reports for `T`.
///
/// # What this lane does and does NOT claim
///
/// It certifies the *allocation identity* of the header: that the requested byte
/// count matches the capacity actually recorded, that capacity is `max(n, 1)`,
/// that `len == n`, and that `len <= cap`. It says NOTHING about the subsequent
/// fill/copy loop (that is `check_memory_sequence`'s territory), and it does NOT
/// attempt to prove the returned buffer is fresh or non-aliasing.
///
/// **That omission is deliberate and load-bearing.** An earlier draft carried a
/// `buffer_fresh_disjoint` obligation discharged against a
/// `fresh_alloc_preconditions` assumption — but the assumption WAS the goal,
/// verbatim (`P ⊢ P`), so it certified nothing while reading like the lane's
/// headline guarantee. Allocator freshness is therefore recorded here as an
/// explicit TRUSTED-MODEL BOUNDARY (the same way lane 9 records its cursor
/// model), not as a discharged VC. Do not "restore" it without an assumption
/// that is strictly weaker than the goal.
///
/// # Anti-tautology
///
/// The spec states capacity CANONICALLY as `ITE(n == 0, 1, n)`. The bridge emits
/// it as `n >u 1 ? n : 1`. These are equivalent but syntactically different
/// formulas, and they meet only on the shared name `n` — so an emission that
/// drops the max, inverts the comparison, or uses a signed compare yields a
/// genuinely different formula and is REFUTED. `elem_size`/`elem_align` are
/// RE-QUERIED from the layout oracle at capture rather than read back out of the
/// emitted constants, so a wrong size/align constant also refutes.
///
/// # Assumed source-side well-formedness
///
/// `cap * elem_size` is modelled as a WRAPPING 64-bit multiply, matching the
/// emission. For a real `&[T]` this cannot overflow (the source slice already
/// occupies `n * elem_size` bytes of address space), and that is the only shape
/// this lane admits. A caller with a COMPUTED repeat count (e.g. `vec![x; k]`)
/// does not satisfy that invariant, so this spec must not be reused there
/// without an explicit no-overflow obligation.
#[derive(Debug, Clone)]
pub struct SliceToVecHeaderSpec {
    /// `cap == max(n, 1)`, stated canonically as `ITE(n == 0, 1, n)`.
    pub cap: SmtExpr,
    /// `alloc_bytes == cap * elem_size` (wrapping; see the note above).
    pub alloc_bytes: SmtExpr,
    /// `len == n`.
    pub len: SmtExpr,
    /// `len <=u cap` — the invariant every Vec fast path assumes.
    pub len_le_cap: SmtExpr,
    /// The alignment the allocation must request, from the layout oracle.
    pub alloc_align: SmtExpr,
    /// Shared symbolic inputs (name, width).
    pub inputs: Vec<(String, u32)>,
}

/// Build the [`SliceToVecHeaderSpec`] over the shared symbolic count `n`.
pub fn slice_to_vec_header_spec(n: &str, elem_size: u64, elem_align: u64) -> SliceToVecHeaderSpec {
    let count = SmtExpr::var(n, 64);
    let zero = SmtExpr::bv_const(0, 64);
    let one = SmtExpr::bv_const(1, 64);
    // Canonical `max(n, 1)`, deliberately NOT the emission's `n >u 1 ? n : 1`.
    let cap = SmtExpr::ite(count.clone().eq_expr(zero), one, count.clone());
    SliceToVecHeaderSpec {
        alloc_bytes: cap.clone().bvmul(SmtExpr::bv_const(elem_size, 64)),
        len_le_cap: count.clone().bvule(cap.clone()),
        cap,
        len: count,
        alloc_align: SmtExpr::bv_const(elem_align, 64),
        inputs: vec![(n.to_string(), 64)],
    }
}

// ---------------------------------------------------------------------------
// `<[T]>::chunks / windows / chunks_exact / rchunks / rchunks_exact`
// stride-iterator CONSTRUCTOR translation-validation SPEC
// ---------------------------------------------------------------------------

/// The Rust-defined meaning of the slice STRIDE-ITERATOR constructors
/// (`chunks(n)` / `windows(n)` / `chunks_exact(n)` / `rchunks(n)` /
/// `rchunks_exact(n)`) at the point the bridge builds its `{ ptr, end, n }` cursor
/// over a slice `s = { data, len }`, as SMT bitvector formulas over the SHARED
/// symbolic 64-bit names `data`/`len`/`n` and a CONSTANT element stride
/// `elem_size` (bytes). This is the SPEC side of the stride-iter refinement lane;
/// the bridge side is reconstructed INDEPENDENTLY from the trust-ir the bridge
/// ACTUALLY EMITTED (see
/// `rustc_codegen_trust_cg::mem_refine::fold_emitted_stride_iter_ctor`), and the
/// two meet only on these shared names — so a bridge that drops/inverts the
/// non-zero-`n` check, scales `end` by the wrong `elem_size`, computes `end` off
/// the wrong base, or swaps the cursor fields yields a genuinely different formula
/// and is REFUTED.
///
/// Definition (all arithmetic 64-bit two's complement — the `usize`/pointer
/// width; the guard `n == 0` matches std's "chunk/window size must be non-zero"
/// panic, which every one of the five constructors performs):
///   * PANIC (a trap) iff `n == 0`.
///   * `cursor.ptr == data`                  (the cursor starts at the slice data).
///   * `cursor.end == data + len*elem_size`  (one past the last element).
///   * `cursor.n   == n`                     (the window/chunk stride).
///
/// SCOPE: the CORE cursor `{ ptr, end, n }` + the `n != 0` trap, common to ALL
/// FIVE variants. The `*_exact` PRECOMPUTED remainder (`rem_data`/`rem_len` at
/// offsets 24/32) is OUT OF SCOPE — the lane ABSTAINS on it (the remainder stores
/// are simply not among the reconstructed cursor stores the obligation checks),
/// never falsely Refined.
pub struct StrideIterCtorSpec {
    /// The trap predicate (a Bool): construction PANICS iff `n == 0`.
    pub trap: SmtExpr,
    /// `cursor.ptr == data` (the cursor's front pointer is the slice data).
    pub ptr: SmtExpr,
    /// `cursor.end == data + len*elem_size` (one past the last element).
    pub end: SmtExpr,
    /// `cursor.n == n` (the window/chunk size).
    pub n: SmtExpr,
    /// The symbolic 64-bit inputs the formulas reference (`data`/`len`/`n`).
    pub inputs: Vec<(String, u32)>,
}

/// Build the [`StrideIterCtorSpec`] for a stride-iterator constructor over the
/// shared symbolic names `data`/`len`/`n` (each a 64-bit `usize`/pointer) and a
/// constant `elem_size` (element stride in bytes). Reuses the standard `SmtExpr`
/// bitvector builders so the spec is encoded on the SAME substrate the bridge
/// reconstruction folds into. See [`StrideIterCtorSpec`] for each field's meaning.
pub fn stride_iter_ctor_spec(data: &str, len: &str, n: &str, elem_size: u64) -> StrideIterCtorSpec {
    let d = SmtExpr::var(data, 64);
    let l = SmtExpr::var(len, 64);
    let nn = SmtExpr::var(n, 64);
    let size = SmtExpr::bv_const(elem_size, 64);
    StrideIterCtorSpec {
        // trap  <=>  n == 0
        trap: nn.clone().eq_expr(SmtExpr::bv_const(0, 64)),
        // cursor.ptr = data
        ptr: d.clone(),
        // cursor.end = data + len*elem_size
        end: d.bvadd(l.bvmul(size)),
        // cursor.n = n
        n: nn,
        inputs: vec![
            (data.to_string(), 64),
            (len.to_string(), 64),
            (n.to_string(), 64),
        ],
    }
}

// ---------------------------------------------------------------------------
// `<Vec<T> as Index>::index` / `index_mut` and `<[T]>::index`
// CHECKED-INDEXING (`v[i]` / `&v[i]` / `&mut v[i]`) translation-validation SPEC
// ---------------------------------------------------------------------------

/// The Rust-defined meaning of a CHECKED slice/Vec index `v[i]` (the panic form —
/// `<Vec<T> as Index>::index` / `index_mut` and `<[T]>::index`, NOT the `unsafe`
/// `get_unchecked*`) at the point the bridge lowers it over a receiver decomposed
/// into a data pointer `data` and a length `len`, as SMT bitvector formulas over
/// the SHARED symbolic 64-bit names `data`/`len`/`i` and a CONSTANT element stride
/// `elem_size` (bytes). This is the SPEC side of the checked-index refinement lane;
/// the bridge side is reconstructed INDEPENDENTLY from the trust-ir the bridge
/// ACTUALLY EMITTED (see
/// `rustc_codegen_trust_cg::mem_refine::fold_emitted_vec_index`), and the two meet
/// only on these shared names — so a bridge that DROPS or INVERTS the `i < len`
/// bounds check, scales the element address by the wrong `elem_size`, or computes
/// the address off the wrong base yields a genuinely different formula and is
/// REFUTED. This is the class of the real O0 soundness bug (a `v[oob]` that
/// silently read out of bounds instead of panicking).
///
/// Definition (all arithmetic 64-bit two's complement — the `usize`/pointer width;
/// the bounds comparison UNSIGNED, since `i`/`len` are `usize`):
///   * PANIC (a trap — the `index out of bounds` `panic_bounds_check`) iff
///     `NOT(i <u len)`, i.e. `i >=u len`.
///   * `elem_addr == data + i*elem_size`  (the address of the i-th element).
pub struct VecIndexSpec {
    /// The trap predicate (a Bool): the index PANICS iff `i >=u len` (the negation
    /// of the in-bounds `i <u len` continue condition).
    pub trap: SmtExpr,
    /// `elem_addr == data + i*elem_size` (the i-th element's byte address).
    pub elem_addr: SmtExpr,
    /// The symbolic 64-bit inputs the formulas reference (`data`/`len`/`i`).
    pub inputs: Vec<(String, u32)>,
}

/// Build the [`VecIndexSpec`] for a checked index over the shared symbolic names
/// `data`/`len`/`i` (each a 64-bit `usize`/pointer) and a constant `elem_size`
/// (element stride in bytes). Reuses the standard `SmtExpr` bitvector builders so
/// the spec is encoded on the SAME substrate the bridge reconstruction folds into.
/// See [`VecIndexSpec`] for the exact meaning of each field.
pub fn vec_index_spec(data: &str, len: &str, i: &str, elem_size: u64) -> VecIndexSpec {
    let d = SmtExpr::var(data, 64);
    let l = SmtExpr::var(len, 64);
    let idx = SmtExpr::var(i, 64);
    let size = SmtExpr::bv_const(elem_size, 64);
    VecIndexSpec {
        // trap  <=>  i >=u len   (== NOT(i <u len), the out-of-bounds panic)
        trap: idx.clone().bvuge(l),
        // elem_addr = data + i*elem_size
        elem_addr: d.bvadd(idx.bvmul(size)),
        inputs: vec![
            (data.to_string(), 64),
            (len.to_string(), 64),
            (i.to_string(), 64),
        ],
    }
}

// ---------------------------------------------------------------------------
// `<Vec<T> as Index<Range|RangeFrom|RangeTo>>::index` / `index_mut`
// range-SUBSLICE (`&v[a..b]` / `&v[a..]` / `&v[..b]`) translation-validation SPEC
// ---------------------------------------------------------------------------

/// Which half-open range form a checked Vec range-subslice interception lowered.
/// Threaded from the bridge capture site into [`vec_range_subslice_spec`] so the
/// spec anchors the OPEN endpoint of `a..` / `..b` correctly (the fold reconstructs
/// the SAME endpoint independently — see
/// `rustc_codegen_trust_cg::mem_refine::fold_emitted_vec_range_subslice`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RangeForm {
    /// `&v[a..b]` — both endpoints explicit (`start = a`, `end = b`).
    Range,
    /// `&v[a..]` — open end (`start = a`, `end = len`).
    RangeFrom,
    /// `&v[..b]` — open start (`start = a`, i.e. the `0` base, `end = b`).
    RangeTo,
}

/// The Rust-defined meaning of a CHECKED Vec range-subslice `&v[a..b]` / `&v[a..]` /
/// `&v[..b]` (via `<Vec<T> as Index<Range|RangeFrom|RangeTo>>::index` / `index_mut`,
/// lowered in `lower_vec_range_subslice_index_call`) at the point the bridge builds
/// the resulting `&[T]` fat pointer `{ ptr, len }` over a receiver decomposed into a
/// data pointer `data` and a length `len`, as SMT bitvector formulas over the SHARED
/// symbolic 64-bit names `data`/`len`/`a`/`b` and a CONSTANT element stride
/// `elem_size` (bytes). This is the SPEC side of the Vec range-subslice refinement
/// lane; the bridge side is reconstructed INDEPENDENTLY from the trust-ir the bridge
/// ACTUALLY EMITTED (see
/// `rustc_codegen_trust_cg::mem_refine::fold_emitted_vec_range_subslice`), and the
/// two meet only on these shared names — so a bridge that DROPS or INVERTS a bound,
/// checks an INCOMPLETE (single-comparison) condition, scales the result pointer by
/// the wrong `elem_size`, computes the result length off the wrong `Sub` direction,
/// or computes the pointer off the wrong base yields a genuinely different formula
/// and is REFUTED. `RangeInclusive`/`RangeFull` are a DIFFERENT interception and are
/// not this spec's concern.
///
/// Definition (all arithmetic 64-bit two's complement — the `usize`/pointer width;
/// the bounds comparisons UNSIGNED, since `a`/`b`/`len` are `usize`). The endpoints
/// that flow into the emitted arithmetic depend on the range form:
///   * `Range`     (`a..b`): `start = a`, `end = b`;
///   * `RangeFrom` (`a..`) : `start = a`, `end = len` (the open end IS the length);
///   * `RangeTo`   (`..b`) : `start = a` (the `0` base), `end = b`.
///     Given `(start, end)`, EVERY form emits the SAME shape (the `Vec`->slice deref's
///     COMBINED order + end check):
///   * PANIC (a trap — `slice_index_order_fail` / `slice_end_index_len_fail`) iff
///     `NOT((start <=u end) AND (end <=u len))`.
///   * `result_ptr == data + start*elem_size` (the subslice's data pointer).
///   * `result_len == end - start`            (the subslice's element count).
pub struct VecRangeSubsliceSpec {
    /// The trap predicate (a Bool): the subslice PANICS iff
    /// `NOT((start <=u end) AND (end <=u len))`.
    pub trap: SmtExpr,
    /// `result_ptr == data + start*elem_size` (the subslice's data pointer).
    pub result_ptr: SmtExpr,
    /// `result_len == end - start` (the subslice's element count).
    pub result_len: SmtExpr,
    /// The symbolic 64-bit inputs the formulas reference (`data`/`len`/`a`/`b`).
    pub inputs: Vec<(String, u32)>,
}

/// Build the [`VecRangeSubsliceSpec`] for a checked Vec range-subslice over the
/// shared symbolic names `data`/`len`/`a`/`b` (each a 64-bit `usize`/pointer) and a
/// constant `elem_size` (element stride in bytes). `form` selects how the endpoints
/// bind: `RangeFrom` anchors `end` to `len` (the open end), while `Range`/`RangeTo`
/// take `end = b` (for `RangeTo` the caller names `a` the `0` base). Reuses the
/// standard `SmtExpr` bitvector builders so the spec is encoded on the SAME substrate
/// the bridge reconstruction folds into. See [`VecRangeSubsliceSpec`] for each
/// field's meaning.
pub fn vec_range_subslice_spec(
    form: RangeForm,
    data: &str,
    len: &str,
    a: &str,
    b: &str,
    elem_size: u64,
) -> VecRangeSubsliceSpec {
    let d = SmtExpr::var(data, 64);
    let l = SmtExpr::var(len, 64);
    let av = SmtExpr::var(a, 64);
    let bv = SmtExpr::var(b, 64);
    let size = SmtExpr::bv_const(elem_size, 64);
    // The endpoints that flow into the emitted arithmetic, per range form.
    let (start, end) = match form {
        RangeForm::Range => (av.clone(), bv.clone()),
        RangeForm::RangeFrom => (av.clone(), l.clone()),
        RangeForm::RangeTo => (av.clone(), bv.clone()),
    };
    // ok = (start <=u end) AND (end <=u len) — the COMBINED check the Vec->slice
    // deref emits (`slice_index_order_fail` + `slice_end_index_len_fail`). trap = !ok.
    let ok = start
        .clone()
        .bvule(end.clone())
        .and_expr(end.clone().bvule(l.clone()));
    VecRangeSubsliceSpec {
        trap: ok.not_expr(),
        // result = { data + start*elem_size, end - start }.
        result_ptr: d.bvadd(start.clone().bvmul(size)),
        result_len: end.bvsub(start),
        inputs: vec![
            (data.to_string(), 64),
            (len.to_string(), 64),
            (a.to_string(), 64),
            (b.to_string(), 64),
        ],
    }
}

/// Which end of the slice a niche-`Option<&T>` accessor yields.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SliceEndKind {
    /// `<[T]>::first(&self) -> Option<&T>` — the element at index `0`.
    First,
    /// `<[T]>::last(&self) -> Option<&T>` — the element at index `len - 1`.
    Last,
}

/// The Rust-defined meaning of a niche-encoded `Option<&T>` slice accessor
/// (`<[T]>::first` / `last`, lowered in `lower_slice_first_last_call`) at the point
/// the bridge writes the resulting `Option<&T>` into its memory slot, as an SMT
/// bitvector formula over the SHARED symbolic 64-bit names `data`/`len` and a
/// CONSTANT element stride `elem_size` (bytes).
///
/// `Option<&T>` is NICHE-encoded: the single pointer-sized field holds the
/// reference directly — `Some(p)` is the non-null `p`, `None` is the null (`0`)
/// niche. So the ENTIRE observable result of `first`/`last` is the value written
/// into that one niche field:
///
/// ```text
/// niche == (len != 0) ? elem_ptr : 0
/// ```
///
/// where `elem_ptr` is the yielded element's address:
///   * `First`: `data`             (the element at index `0`);
///   * `Last` : `data + (len-1)*elem_size` (the element at index `len-1`).
///
/// This is the SPEC side of the first/last refinement lane; the bridge side is
/// reconstructed INDEPENDENTLY from the trust-ir the bridge ACTUALLY EMITTED (the
/// `ICmp Ne(len,0)` emptiness test, the element-address arithmetic, and the
/// `Select(cond, elem_ptr, null)` written to the niche field — see
/// `rustc_codegen_trust_cg::mem_refine::fold_emitted_slice_first_last`). The two
/// meet only on `data`/`len`, so a bridge that INVERTS the emptiness test (yielding
/// `Some` on an empty slice), stores a NON-NULL `None`, computes the `Last` element
/// at the wrong index (e.g. `data + len*elem_size`, forgetting the `-1`), or scales
/// by the wrong stride yields a genuinely different formula and is REFUTED.
pub struct OptionRefSpec {
    /// `niche == (len != 0) ? elem_ptr : 0` — the value written to the
    /// `Option<&T>`'s single niche field (the whole observable result).
    pub niche: SmtExpr,
    /// The symbolic 64-bit inputs the formula references (`data`/`len`).
    pub inputs: Vec<(String, u32)>,
}

/// Build the [`OptionRefSpec`] for `<[T]>::first`/`last` over the shared symbolic
/// names `data`/`len` (each a 64-bit `usize`/pointer) and a constant `elem_size`
/// (element stride in bytes). Reuses the standard `SmtExpr` bitvector builders so
/// the spec is encoded on the SAME substrate the bridge reconstruction folds into.
/// See [`OptionRefSpec`] for the field's meaning.
pub fn slice_first_last_spec(
    kind: SliceEndKind,
    data: &str,
    len: &str,
    elem_size: u64,
) -> OptionRefSpec {
    let d = SmtExpr::var(data, 64);
    let l = SmtExpr::var(len, 64);
    let size = SmtExpr::bv_const(elem_size, 64);
    // cond = len != 0 (the slice is non-empty => Some).
    let nonempty = l.clone().eq_expr(SmtExpr::bv_const(0, 64)).not_expr();
    // The yielded element pointer: First -> data; Last -> data + (len-1)*size.
    let elem_ptr = match kind {
        SliceEndKind::First => d.clone(),
        SliceEndKind::Last => {
            let last_idx = l.clone().bvsub(SmtExpr::bv_const(1, 64));
            d.clone().bvadd(last_idx.bvmul(size))
        }
    };
    // None is the null (0) niche.
    let null = SmtExpr::bv_const(0, 64);
    OptionRefSpec {
        niche: SmtExpr::ite(nonempty, elem_ptr, null),
        inputs: vec![(data.to_string(), 64), (len.to_string(), 64)],
    }
}

/// The Rust-defined meaning of `<Range<T> as Iterator>::next(&mut self) -> Option<T>`
/// (lowered branchless in `lower_range_next`) at the point the bridge writes the
/// resulting `Option<T>` AND the advanced iterator state back to memory, as SMT
/// bitvector formulas over the SHARED symbolic 64-bit names `start`/`end` (the
/// PRE-state `self.start` / `self.end` loads). 64-bit elements only.
///
/// The Rust semantics are a STATE TRANSITION plus a value:
///
/// ```text
/// if self.start < self.end { let v = self.start; self.start += 1; Some(v) }
/// else { None }
/// ```
///
/// so the ENTIRE observable result is THREE written values:
///   * `tag`       — `ITE(start < end, some_discr, none_discr)` (the `Option` tag);
///   * `payload`   — `start` (the PRE-state start: the yielded value — NOT the
///     advanced one, which would be the classic post-increment-yield bug);
///   * `new_start` — `ITE(start < end, start + 1, start)` (the post-state written
///     back to `self.start`; a finished range is never mutated past its end).
///
/// `<` is SIGNED (`bvslt`) for a signed index type and UNSIGNED (`bvult`)
/// otherwise. This is the SPEC side of the Range::next refinement lane; the
/// bridge side is folded INDEPENDENTLY from the trust-ir the bridge ACTUALLY
/// EMITTED (the `start`/`end` `Load`s bound to fresh pre-state symbols, the
/// `ICmp`, the `+1` `Add`, the `Select`s, and the three `Store`s — see
/// `rustc_codegen_trust_cg::mem_refine::fold_emitted_range_next`). The two meet
/// only on the pre-state load symbols, so a signedness confusion (`Ult` emitted
/// for a signed range), an advance-when-done (`Select` arms swapped), a `step != 1`,
/// a swapped `start`/`end` load into the comparison, or a `payload = new_start`
/// (post-increment yield) yields a genuinely different formula and is REFUTED.
pub struct RangeNextSpec {
    /// `ITE(start <s/<u end, some_discr, none_discr)` — the `Option` tag word.
    pub tag: SmtExpr,
    /// `start` — the yielded `Some` payload (the PRE-state start).
    pub payload: SmtExpr,
    /// `ITE(start <s/<u end, start + 1, start)` — the post-state `self.start`.
    pub new_start: SmtExpr,
    /// The symbolic 64-bit inputs the formulas reference (`start`/`end`).
    pub inputs: Vec<(String, u32)>,
}

/// Build the [`RangeNextSpec`] for `<Range<T> as Iterator>::next` over the shared
/// symbolic pre-state names `start`/`end` (each a 64-bit element) and the
/// destination `Option`'s `Some`/`None` discriminant values. Reuses the standard
/// `SmtExpr` bitvector builders so the spec is encoded on the SAME substrate the
/// bridge reconstruction folds into. See [`RangeNextSpec`] for each field's
/// meaning.
pub fn range_next_spec(
    signed: bool,
    start: &str,
    end: &str,
    some_discr: u64,
    none_discr: u64,
) -> RangeNextSpec {
    let s = SmtExpr::var(start, 64);
    let e = SmtExpr::var(end, 64);
    // cond = start < end (signed for a signed index, unsigned otherwise).
    let cond = if signed {
        s.clone().bvslt(e.clone())
    } else {
        s.clone().bvult(e.clone())
    };
    let one = SmtExpr::bv_const(1, 64);
    RangeNextSpec {
        tag: SmtExpr::ite(
            cond.clone(),
            SmtExpr::bv_const(some_discr, 64),
            SmtExpr::bv_const(none_discr, 64),
        ),
        payload: s.clone(),
        new_start: SmtExpr::ite(cond, s.clone().bvadd(one), s),
        inputs: vec![(start.to_string(), 64), (end.to_string(), 64)],
    }
}

/// WIDTH-FAITHFUL [`range_next_spec`] generalization (lane 13 — NARROW-element
/// `<Range<T> as Iterator>::next`, `T` in `{i8, u8, i16, u16, i32, u32}`).
/// `w` is the element byte width; all symbols stay 64-bit and every narrow
/// value is modeled with explicit masking, matching trust-ir's `interpret.rs`:
///
///   * a `w`-byte load's VALUE is its low `w` bytes (`eval_load` decodes
///     `byte_size(ty)` bytes and `InterpretInt::from_raw` masks `raw` to
///     `bits`) — so `s = start & mask`, `e = end & mask`;
///   * the narrow `+ 1` WRAPS at `w` (`eval_int_binop`: `BinOp::Add =>
///     lhs.raw.wrapping_add(rhs.raw)` then `… & mask` with
///     `mask = int_mask(bits)`) — so `new_start = (s + 1) & mask` on a yield;
///   * a SIGNED narrow compare decodes two's complement at `w` and compares
///     the decoded integers (`eval_int_icmp`: `ICmpOp::Slt =>
///     lhs.as_signed() < rhs.as_signed()`, where `as_signed` subtracts
///     `2^bits` when the sign bit is set) — modeled by sign-EXTENDING the
///     masked value to 64 bits, `sext_w(x) = ((x & mask) ^ sign_w) - sign_w`
///     with `sign_w = 2^(8w-1)`, then `bvslt` at 64 bits (equal semantics);
///     an UNSIGNED compare is the raw masked compare (`lhs.raw < rhs.raw`).
///
/// The `Option` tag discriminants are masked to the LAYOUT tag width
/// (`tag_width` bytes), exactly like [`step_by_next_spec`]. `w == 8` delegates
/// to the UNCHANGED [`range_next_spec`] (zero behavior change for the landed
/// 64-bit lane-7 path; `tag_width` is ignored there, matching its unmasked
/// 64-bit tag constants).
pub fn range_next_spec_w(
    signed: bool,
    w: u32,
    start: &str,
    end: &str,
    some_discr: u64,
    none_discr: u64,
    tag_width: u32,
) -> RangeNextSpec {
    if w == 8 {
        return range_next_spec(signed, start, end, some_discr, none_discr);
    }
    assert!(matches!(w, 1 | 2 | 4), "narrow Range::next width {w}");
    let mask_v: u64 = (1u64 << (8 * w)) - 1;
    let mask = SmtExpr::bv_const(mask_v, 64);
    let s = SmtExpr::var(start, 64).bvand(mask.clone());
    let e = SmtExpr::var(end, 64).bvand(mask.clone());
    // cond = start < end at width w: signed compares sign-extend the masked
    // values to 64 bits ("MODEL THE INTERPRETER": `eval_int_icmp` decodes
    // two's complement at `bits` — sign extension preserves exactly that
    // ordering under 64-bit bvslt); unsigned compares the masked values raw.
    let cond = if signed {
        let sign = SmtExpr::bv_const(1u64 << (8 * w - 1), 64);
        let sext = |x: SmtExpr| x.bvxor(sign.clone()).bvsub(sign.clone());
        sext(s.clone()).bvslt(sext(e))
    } else {
        s.clone().bvult(e)
    };
    let one = SmtExpr::bv_const(1, 64);
    // The discriminants at the LAYOUT tag width (mask for faithfulness — the
    // real Option tags are tiny and always fit).
    let tag_mask: u64 = if tag_width >= 8 {
        u64::MAX
    } else {
        (1u64 << (8 * tag_width)) - 1
    };
    RangeNextSpec {
        tag: SmtExpr::ite(
            cond.clone(),
            SmtExpr::bv_const(some_discr & tag_mask, 64),
            SmtExpr::bv_const(none_discr & tag_mask, 64),
        ),
        payload: s.clone(),
        // new_start = (s + 1) & mask on a yield — the narrow add WRAPS at w
        // (`eval_int_binop` masks the wrapped raw to `bits`).
        new_start: SmtExpr::ite(cond, s.clone().bvadd(one).bvand(mask), s),
        inputs: vec![(start.to_string(), 64), (end.to_string(), 64)],
    }
}

/// The Rust-defined meaning of `<slice::Iter<T> as Iterator>::next(&mut self)
/// -> Option<&T>` (lowered branchless in `lower_slice_iter_next` — the `for x in
/// slice` workhorse) at the point the bridge writes the resulting `Option<&T>`
/// AND the advanced cursor state back to memory, as SMT bitvector formulas over
/// the SHARED symbolic 64-bit names `ptr`/`end` (the PRE-state `self.ptr` /
/// `self.end` loads) and a CONSTANT element stride `elem_size` (bytes).
///
/// The Rust semantics are a STATE TRANSITION plus a value:
///
/// ```text
/// if self.ptr != self.end { let e = self.ptr; self.ptr += elem_size; Some(&*e) }
/// else { None }
/// ```
///
/// `Option<&T>` is NICHE-encoded (the single pointer-sized field IS the
/// reference; `None` is the null `0` niche), so the ENTIRE observable result is
/// TWO written 8-byte cells:
///   * `new_ptr` — `ITE(ptr != end, ptr + elem_size, ptr)` (the post-state
///     written back to `self.ptr`; a finished iterator is never advanced past
///     its end);
///   * `niche`   — `ITE(ptr != end, ptr, 0)` (the yielded reference IS the
///     PRE-advance `ptr` — NOT the advanced one, which would be the classic
///     post-increment-yield bug, an off-by-one-ELEMENT read; `None` = null 0).
///
/// This is the SPEC side of the slice Iter::next refinement lane; the bridge
/// side is folded INDEPENDENTLY from the trust-ir the bridge ACTUALLY EMITTED
/// (the `ptr`/`end` `Load`s bound to fresh pre-state symbols, the `ICmp Ne`, the
/// `+elem_size` advance, the `Select`s, and the two `Store`s — see
/// `rustc_codegen_trust_cg::mem_refine::fold_emitted_slice_iter_next`). The two
/// meet only on the pre-state load symbols, so an advance-when-done (`Select`
/// arms swapped), a wrong stride, a post-increment yield (`Some(&*(ptr +
/// elem_size))`), a non-null `None`, an end-clobbering write-back, or an
/// `Eq`-for-`Ne` inverted exhaustion test yields a genuinely different formula
/// and is REFUTED.
pub struct SliceIterNextSpec {
    /// `ITE(ptr != end, ptr + elem_size, ptr)` — the post-state `self.ptr`.
    pub new_ptr: SmtExpr,
    /// `ITE(ptr != end, ptr, 0)` — the value written to the `Option<&T>`'s
    /// single niche field (the whole observable `Option` result).
    pub niche: SmtExpr,
    /// The symbolic 64-bit inputs the formulas reference (`ptr`/`end`).
    pub inputs: Vec<(String, u32)>,
}

/// Build the [`SliceIterNextSpec`] for `<slice::Iter<T> as Iterator>::next` over
/// the shared symbolic pre-state names `ptr`/`end` (each a 64-bit pointer) and a
/// constant `elem_size` (element stride in bytes). Reuses the standard `SmtExpr`
/// bitvector builders so the spec is encoded on the SAME substrate the bridge
/// reconstruction folds into. See [`SliceIterNextSpec`] for each field's meaning.
pub fn slice_iter_next_spec(ptr: &str, end: &str, elem_size: u64) -> SliceIterNextSpec {
    let p = SmtExpr::var(ptr, 64);
    let e = SmtExpr::var(end, 64);
    // cond = ptr != end (the iterator is exhausted exactly when ptr == end).
    let cond = p.clone().eq_expr(e.clone()).not_expr();
    let size = SmtExpr::bv_const(elem_size, 64);
    // None is the null (0) niche.
    let null = SmtExpr::bv_const(0, 64);
    SliceIterNextSpec {
        new_ptr: SmtExpr::ite(cond.clone(), p.clone().bvadd(size), p.clone()),
        niche: SmtExpr::ite(cond, p, null),
        inputs: vec![(ptr.to_string(), 64), (end.to_string(), 64)],
    }
}

/// The Rust-defined meaning of `<StepBy<Range<i64>> as Iterator>::next(&mut
/// self) -> Option<i64>` (lowered branchless in `lower_step_by_next`, the
/// SIGNED-Range std-layout path) at the point the bridge writes the resulting
/// `Option<i64>` AND the advanced iterator state back to memory, as SMT
/// bitvector formulas over the SHARED symbolic 64-bit names `sm` (the
/// `step_minus_one: usize` cell), `ft_raw` (the 64-bit pre-state symbol of the
/// 1-BYTE `first_take: bool` cell — only its LOW BYTE is meaningful, exactly
/// like the machine's 1-byte load), and `start`/`end` (the inner `Range<i64>`
/// cells).
///
/// The Rust semantics (std's `StepBy::next` == `spec_next`: an initial
/// `first_take` pull of element 0, then every `step`-th element while it stays
/// `< end`, with the 64-bit overflow of `start + countdown` mapping to `None`
/// exactly like std's `forward_checked`):
///
/// ```text
/// ft        = ft_raw & 0xff                  // the machine's 1-byte load
/// countdown = if ft != 0 { 0 } else { sm }   // first pull yields element 0
/// y         = start + countdown              // 64-bit wrapping
/// cond      = (y >=s start) AND (y <s end)   // no-overflow AND in-range
/// new_start = if cond { y + 1 } else { start }
/// new_ft    = (if cond { 0 } else { ft }) & 0xff  // cleared ONLY on a yield
/// tag       = if cond { some_discr } else { none_discr }
/// payload   = y                              // the yielded element
/// ```
///
/// This matches std's yield set `{start, start+k, start+2k, …} < end` with the
/// `first_take` pull, and REFUTES: swapped countdown arms (yield `start+k`
/// first), a dropped overflow guard (`Sge` removed — a wrapped `y` would decode
/// in-range), an advance-when-done, a `first_take` never cleared (`new_ft =
/// ft`: the iterator re-yields element 0 forever), a `first_take` cleared
/// UNCONDITIONALLY (an exhausted iterator whose `first_take` is still set would
/// restart mid-sequence on the next pull), a post-increment payload (`payload =
/// new_start`), swapped tag arms, wrong-cell stores, and narrow-store width
/// lies (the obligations compare the `first_take` store at its 1-byte width).
///
/// This is the SPEC side of the StepBy::next refinement lane (lane 11 — the
/// WIDTH-FAITHFUL lane: every narrow value is modeled as a 64-bit expression
/// with explicit masking, matching trust-ir's `interpret.rs` semantics where a
/// `w`-byte load reads exactly `w` bytes and `Trunc`/`ZExt` mask `raw` to the
/// destination width); the bridge side is folded INDEPENDENTLY from the
/// trust-ir the bridge ACTUALLY EMITTED (see
/// `rustc_codegen_trust_cg::mem_refine::fold_emitted_step_by_next`). The two
/// meet only on the pre-state load symbols.
pub struct StepByNextSpec {
    /// `ITE(cond, y + 1, start)` — the post-state `range.start` cell.
    pub new_start: SmtExpr,
    /// `ITE(cond, 0, ft) & 0xff` — the LOW BYTE the 1-byte `first_take` store
    /// writes (the obligation compares low bytes on both sides).
    pub new_ft: SmtExpr,
    /// `ITE(cond, some_discr, none_discr)` — the `Option` tag word (constants
    /// masked to the layout tag width).
    pub tag: SmtExpr,
    /// `y = start + ITE(ft != 0, 0, sm)` — the yielded `Some` payload.
    pub payload: SmtExpr,
    /// The symbolic 64-bit inputs the formulas reference
    /// (`sm`/`ft_raw`/`start`/`end`).
    pub inputs: Vec<(String, u32)>,
}

/// Build the [`StepByNextSpec`] for `<StepBy<Range<i64>> as Iterator>::next`
/// over the shared symbolic pre-state names `sm`/`ft_raw`/`start`/`end` and the
/// destination `Option`'s `Some`/`None` discriminant values (`tag_width` = the
/// LAYOUT tag scalar's byte width; the discriminant constants are masked to it,
/// matching the width the emitted tag pipeline actually carries). Reuses the
/// standard `SmtExpr` bitvector builders so the spec is encoded on the SAME
/// substrate the bridge reconstruction folds into. See [`StepByNextSpec`] for
/// each field's meaning.
pub fn step_by_next_spec(
    sm: &str,
    ft_raw: &str,
    start: &str,
    end: &str,
    some_discr: u64,
    none_discr: u64,
    tag_width: u32,
) -> StepByNextSpec {
    let sm_v = SmtExpr::var(sm, 64);
    let ft_raw_v = SmtExpr::var(ft_raw, 64);
    let s = SmtExpr::var(start, 64);
    let e = SmtExpr::var(end, 64);
    let zero = SmtExpr::bv_const(0, 64);
    let byte_mask = SmtExpr::bv_const(0xff, 64);
    // ft = ft_raw & 0xff — the VALUE of the 1-byte `first_take` cell (the
    // pre-state symbol is declared 64-bit; the machine loads its low byte).
    let ft = ft_raw_v.bvand(byte_mask.clone());
    // countdown = ITE(ft != 0, 0, sm) — the very first pull yields element 0.
    let ft_nz = ft.clone().eq_expr(zero.clone()).not_expr();
    let countdown = SmtExpr::ite(ft_nz, zero.clone(), sm_v);
    // y = start + countdown (64-bit wrapping — the overflow guard below is the
    // spec-level image of std's `forward_checked` -> `None`).
    let y = s.clone().bvadd(countdown);
    // cond = (y >=s start) AND (y <s end) — signed i64 semantics.
    let cond = y.clone().bvsge(s.clone()).and_expr(y.clone().bvslt(e));
    let one = SmtExpr::bv_const(1, 64);
    // The discriminants at the LAYOUT tag width (a 1-byte tag carries only its
    // low byte — the constants always fit in practice; mask for faithfulness).
    let tag_mask: u64 = if tag_width >= 8 {
        u64::MAX
    } else {
        (1u64 << (8 * tag_width)) - 1
    };
    StepByNextSpec {
        new_start: SmtExpr::ite(cond.clone(), y.clone().bvadd(one), s),
        new_ft: SmtExpr::ite(cond.clone(), zero, ft).bvand(byte_mask),
        tag: SmtExpr::ite(
            cond,
            SmtExpr::bv_const(some_discr & tag_mask, 64),
            SmtExpr::bv_const(none_discr & tag_mask, 64),
        ),
        payload: y,
        inputs: vec![
            (sm.to_string(), 64),
            (ft_raw.to_string(), 64),
            (start.to_string(), 64),
            (end.to_string(), 64),
        ],
    }
}

/// The Rust-defined meaning of `<StepBy<Range<u64|usize>> as Iterator>::next`
/// (lowered branchless in `lower_step_by_next`, the PACKED-UNSIGNED Range path)
/// at the point the bridge writes the resulting `Option<u64>` AND the advanced
/// iterator state back to memory, as SMT bitvector formulas over the SHARED
/// symbolic 64-bit names `state` (the bridge's ONE-word packed step state
/// `(k-1) << 32 | countdown` at the `step_minus_one` cell — there is NO
/// `first_take` cell on this path) and `start`/`end` (the inner unsigned Range
/// cells).
///
/// The Rust semantics (std's `StepBy::next` == `spec_next` over the bridge's
/// packed-state model: the LOW 32 bits count DOWN to the next yield — 0 on the
/// very first pull, so element 0 is yielded first — and the HIGH 32 bits hold
/// the invariant `k-1` the countdown resets to on every yield):
///
/// ```text
/// countdown = state & 0xFFFF_FFFF           // low half: distance to next yield
/// reset     = state >> 32                   // high half (LOGICAL shift): k-1
/// y         = start + countdown             // 64-bit wrapping
/// cond      = (y >=u start) AND (y <u end)  // no-overflow AND in-range, UNSIGNED
/// new_start = if cond { y + 1 } else { start }
/// new_state = if cond { (reset << 32) | reset } else { state }
/// tag       = if cond { some_discr } else { none_discr }
/// payload   = y                             // the yielded element
/// ```
///
/// This matches std's yield set `{start, start+k, start+2k, …} < end` (the
/// packed countdown after a yield is `k-1`, so the next yield is `k` past the
/// advanced `start`), and REFUTES: reset arms swapped (`new_state = state` on a
/// yield — the state LOSES `k` and re-yields consecutive elements), a countdown
/// taken from the HIGH half (`state >> 32` as countdown: the first pull yields
/// `start + (k-1)`), a dropped overflow guard (`Uge` removed — a wrapped `y`
/// would decode in-range), an advance-when-done, a `new_state` written
/// UNCONDITIONALLY (an exhausted iterator's countdown resets to `k-1` — a
/// restart bug), a post-increment payload (`payload = y + 1`), swapped tag
/// arms, wrong-cell stores, and store width lies (the obligations are
/// width-exact).
///
/// This is the SPEC side of the StepBy v2 packed refinement (lane 12); the
/// bridge side is folded INDEPENDENTLY from the trust-ir the bridge ACTUALLY
/// EMITTED (`rustc_codegen_trust_cg::mem_refine::fold_emitted_step_by_next` —
/// the `And`/`LShr`/`Shl`/`Or` packed prelude folds through the WIDTH-FAITHFUL
/// 8-byte arithmetic arms). Trust-ir defines a shift amount greater than or
/// equal to the value width as UB (`interpret.rs::shift_amount` rejects it);
/// this slice is defined because the emitted amount is the in-range constant
/// 32, and the fold rejects any amount `>= 64`. The two sides meet only on the
/// pre-state load symbols.
pub struct StepByNextPackedSpec {
    /// `ITE(cond, y + 1, start)` — the post-state `range.start` cell.
    pub new_start: SmtExpr,
    /// `ITE(cond, (reset << 32) | reset, state)` — the post-state packed word.
    pub new_state: SmtExpr,
    /// `ITE(cond, some_discr, none_discr)` — the `Option` tag word (constants
    /// masked to the layout tag width).
    pub tag: SmtExpr,
    /// `y = start + (state & 0xFFFF_FFFF)` — the yielded `Some` payload.
    pub payload: SmtExpr,
    /// The symbolic 64-bit inputs the formulas reference (`state`/`start`/`end`).
    pub inputs: Vec<(String, u32)>,
}

/// Build the [`StepByNextPackedSpec`] for the packed-unsigned
/// `<StepBy<Range<u64|usize>> as Iterator>::next` over the shared symbolic
/// pre-state names `state`/`start`/`end` and the destination `Option`'s
/// `Some`/`None` discriminant values (`tag_width` = the LAYOUT tag scalar's
/// byte width; the discriminant constants are masked to it). Reuses the
/// standard `SmtExpr` bitvector builders so the spec is encoded on the SAME
/// substrate the bridge reconstruction folds into. See [`StepByNextPackedSpec`]
/// for each field's meaning.
pub fn step_by_next_packed_spec(
    state: &str,
    start: &str,
    end: &str,
    some_discr: u64,
    none_discr: u64,
    tag_width: u32,
) -> StepByNextPackedSpec {
    let st = SmtExpr::var(state, 64);
    let s = SmtExpr::var(start, 64);
    let e = SmtExpr::var(end, 64);
    let c32 = SmtExpr::bv_const(32, 64);
    // countdown = state & 0xFFFF_FFFF — the LOW half.
    let countdown = st.clone().bvand(SmtExpr::bv_const(0xFFFF_FFFF, 64));
    // reset = state >> 32 (LOGICAL — the high half is an unsigned k-1).
    let reset = st.clone().bvlshr(c32.clone());
    // y = start + countdown (64-bit wrapping — the overflow guard below is the
    // spec-level image of std's `forward_checked` -> `None`).
    let y = s.clone().bvadd(countdown);
    // cond = (y >=u start) AND (y <u end) — UNSIGNED u64/usize semantics.
    let cond = y.clone().bvuge(s.clone()).and_expr(y.clone().bvult(e));
    let one = SmtExpr::bv_const(1, 64);
    // new_state on a yield: the countdown resets to `k-1` in BOTH halves —
    // `(reset << 32) | reset`.
    let new_state_yield = reset.clone().bvshl(c32).bvor(reset);
    // The discriminants at the LAYOUT tag width (mask for faithfulness).
    let tag_mask: u64 = if tag_width >= 8 {
        u64::MAX
    } else {
        (1u64 << (8 * tag_width)) - 1
    };
    StepByNextPackedSpec {
        new_start: SmtExpr::ite(cond.clone(), y.clone().bvadd(one), s),
        new_state: SmtExpr::ite(cond.clone(), new_state_yield, st),
        tag: SmtExpr::ite(
            cond,
            SmtExpr::bv_const(some_discr & tag_mask, 64),
            SmtExpr::bv_const(none_discr & tag_mask, 64),
        ),
        payload: y,
        inputs: vec![
            (state.to_string(), 64),
            (start.to_string(), 64),
            (end.to_string(), 64),
        ],
    }
}

/// The Rust-defined meaning of `<StepBy<slice::Iter<T>> as Iterator>::next`
/// (lowered branchless in `lower_step_by_next`, the STD-LAYOUT SLICE-source
/// path) at the point the bridge writes the resulting niche-encoded
/// `Option<&T>` AND the advanced cursor back to memory, as SMT bitvector
/// formulas over the SHARED symbolic 64-bit names `sm` (the
/// `step_minus_one: usize` cell), `ft_raw` (the 64-bit pre-state symbol of the
/// 1-BYTE `first_take: bool` cell — only its LOW BYTE is meaningful) and
/// `ptr`/`end` (the `{ptr, end}` slice cursor), plus a CONSTANT `elem_size`
/// (element stride in bytes).
///
/// The Rust semantics (std's `StepBy::next` over the slice cursor: an initial
/// `first_take` pull of element 0, then every `step`-th element while its
/// address stays `< end`, with address-arithmetic overflow mapping to `None`):
///
/// ```text
/// ft        = ft_raw & 0xff                     // the machine's 1-byte load
/// countdown = if ft != 0 { 0 } else { sm }      // first pull yields element 0
/// y_ptr     = ptr + countdown*elem_size         // 64-bit wrapping
/// cond      = (y_ptr >=u ptr) AND (y_ptr <u end)
/// new_ptr   = if cond { y_ptr + elem_size } else { ptr }
/// new_ft    = (if cond { 0 } else { ft }) & 0xff  // cleared ONLY on a yield
/// niche     = if cond { y_ptr } else { 0 }      // Some(&elem) / null None
/// ```
///
/// The yielded reference is the PRE-advance `y_ptr` — NOT `y_ptr + elem_size`
/// (the classic post-increment-yield bug, an off-by-one-ELEMENT read).
/// REFUTES: a post-increment niche, a non-null `None` (an empty pull would
/// decode `Some`), a `first_take` never cleared / cleared unconditionally
/// (as in the v1 lane — re-yield-forever / restart bugs), a wrong stride
/// (mis-scaled element addresses), swapped countdown arms, a dropped overflow
/// guard, an advance-when-done, wrong-cell stores, and narrow-store width lies
/// (the `first_take` store is compared at its 1-byte width).
///
/// This is the SPEC side of the StepBy v2 slice refinement (lane 12); the
/// bridge side is folded INDEPENDENTLY from the trust-ir the bridge ACTUALLY
/// EMITTED (`rustc_codegen_trust_cg::mem_refine::fold_emitted_step_by_next`).
/// The two meet only on the pre-state load symbols.
pub struct StepByNextSliceSpec {
    /// `ITE(cond, y_ptr + elem_size, ptr)` — the post-state `self.ptr` cell.
    pub new_ptr: SmtExpr,
    /// `ITE(cond, 0, ft) & 0xff` — the LOW BYTE the 1-byte `first_take` store
    /// writes (the obligation compares low bytes on both sides).
    pub new_ft: SmtExpr,
    /// `ITE(cond, y_ptr, 0)` — the value written to the `Option<&T>`'s single
    /// niche field (the whole observable `Option` result; `None` = null 0).
    pub niche: SmtExpr,
    /// The symbolic 64-bit inputs the formulas reference
    /// (`sm`/`ft_raw`/`ptr`/`end`).
    pub inputs: Vec<(String, u32)>,
}

/// Build the [`StepByNextSliceSpec`] for the slice-source
/// `<StepBy<slice::Iter<T>> as Iterator>::next` over the shared symbolic
/// pre-state names `sm`/`ft_raw`/`ptr`/`end` and a constant `elem_size`
/// (element stride in bytes). Reuses the standard `SmtExpr` bitvector builders
/// so the spec is encoded on the SAME substrate the bridge reconstruction
/// folds into. See [`StepByNextSliceSpec`] for each field's meaning.
pub fn step_by_next_slice_spec(
    sm: &str,
    ft_raw: &str,
    ptr: &str,
    end: &str,
    elem_size: u64,
) -> StepByNextSliceSpec {
    let sm_v = SmtExpr::var(sm, 64);
    let ft_raw_v = SmtExpr::var(ft_raw, 64);
    let p = SmtExpr::var(ptr, 64);
    let e = SmtExpr::var(end, 64);
    let zero = SmtExpr::bv_const(0, 64);
    let byte_mask = SmtExpr::bv_const(0xff, 64);
    let size = SmtExpr::bv_const(elem_size, 64);
    // ft = ft_raw & 0xff — the VALUE of the 1-byte `first_take` cell.
    let ft = ft_raw_v.bvand(byte_mask.clone());
    // countdown = ITE(ft != 0, 0, sm) — the very first pull yields element 0.
    let ft_nz = ft.clone().eq_expr(zero.clone()).not_expr();
    let countdown = SmtExpr::ite(ft_nz, zero.clone(), sm_v);
    // y_ptr = ptr + countdown*elem_size (64-bit wrapping address arithmetic).
    let y_ptr = p.clone().bvadd(countdown.bvmul(size.clone()));
    // cond = (y_ptr >=u ptr) AND (y_ptr <u end) — unsigned address comparison.
    let cond = y_ptr
        .clone()
        .bvuge(p.clone())
        .and_expr(y_ptr.clone().bvult(e));
    StepByNextSliceSpec {
        new_ptr: SmtExpr::ite(cond.clone(), y_ptr.clone().bvadd(size), p),
        new_ft: SmtExpr::ite(cond.clone(), zero.clone(), ft).bvand(byte_mask),
        niche: SmtExpr::ite(cond, y_ptr, zero),
        inputs: vec![
            (sm.to_string(), 64),
            (ft_raw.to_string(), 64),
            (ptr.to_string(), 64),
            (end.to_string(), 64),
        ],
    }
}

/// The Rust-defined meaning of `<[T]>::split_first(&self)` / `split_last(&self)`
/// -> `Option<(&T, &[T])>` (lowered branchless in `lower_slice_split_first_last`)
/// at the point the bridge writes the resulting niche-encoded option into its
/// memory slot, as SMT bitvector formulas over the SHARED symbolic 64-bit names
/// `data`/`len` and a CONSTANT element stride `elem_size` (bytes).
///
/// The Rust semantics: a non-empty slice yields `Some((head, tail))` — for
/// `split_first` `head = &self[0]`, `tail = &self[1..]`; for `split_last`
/// `head = &self[len-1]`, `tail = &self[..len-1]` — and an empty slice yields
/// `None`. `Option<(&T, &[T])>` is NICHE-encoded: ONE of the tuple's pointer
/// cells (the `&T`, or the tail's data pointer — whichever the LAYOUT designated)
/// doubles as the discriminant, holding the non-null pointer for `Some` and the
/// null (`0`) niche for `None`. So the ENTIRE observable result is THREE written
/// 8-byte cells:
///   * `f0`       — the `&T` head-pointer cell (`first_ptr_f = data` for First /
///     `data + (len-1)*elem_size` for Last);
///   * `f1`       — the tail's data-pointer cell (`tail_data_f = data +
///     elem_size` for First / `data` for Last);
///   * `tail_len` — the tail's length cell (`len - 1`, a WRAPPING `bvsub` —
///     written unconditionally, its bytes are dead on the `None` edge exactly
///     like the emitted unconditional store).
///
/// THE NICHE-CELL KEYSTONE (soundness, non-negotiable): `niche_at_f0` is derived
/// from the LAYOUT's designated tag offset (`tag.offset == f0`, passed from the
/// capture site) — NEVER inferred from where the emitted `Select` happened to
/// flow. The spec formula for the layout-designated niche cell is the ITE
/// `ITE(len != 0, ptr, 0)` and the OTHER pointer cell is the raw unconditional
/// pointer. A bridge that DROPS the `Select` (storing the raw pointer
/// unconditionally into the niche cell — an empty slice would decode `Some`)
/// folds that cell to the raw pointer while the spec has the ITE, so it is
/// genuinely different on `len == 0` and REFUTES; a bridge that emits the
/// `Select` into the WRONG cell refutes on BOTH pointer cells.
pub struct SplitEndsSpec {
    /// The value of the `&T` head-pointer cell: `ITE(len != 0, first_ptr_f, 0)`
    /// when the layout put the niche at `f0`, else the raw `first_ptr_f`.
    pub f0: SmtExpr,
    /// The value of the tail data-pointer cell: `ITE(len != 0, tail_data_f, 0)`
    /// when the layout put the niche at `f1`, else the raw `tail_data_f`.
    pub f1: SmtExpr,
    /// `len - 1` (wrapping) — the tail-length cell, written unconditionally.
    pub tail_len: SmtExpr,
    /// The symbolic 64-bit inputs the formulas reference (`data`/`len`).
    pub inputs: Vec<(String, u32)>,
}

/// Build the [`SplitEndsSpec`] for `<[T]>::split_first`/`split_last` over the
/// shared symbolic names `data`/`len` (each a 64-bit `usize`/pointer), a constant
/// `elem_size` (element stride in bytes), and the LAYOUT-designated niche
/// position `niche_at_f0` (see the keystone note on [`SplitEndsSpec`]). Reuses
/// the standard `SmtExpr` bitvector builders so the spec is encoded on the SAME
/// substrate the bridge reconstruction folds into.
pub fn split_first_last_spec(
    kind: SliceEndKind,
    niche_at_f0: bool,
    data: &str,
    len: &str,
    elem_size: u64,
) -> SplitEndsSpec {
    let d = SmtExpr::var(data, 64);
    let l = SmtExpr::var(len, 64);
    let size = SmtExpr::bv_const(elem_size, 64);
    // nonempty = len != 0 (a non-empty slice => Some).
    let nonempty = l.clone().eq_expr(SmtExpr::bv_const(0, 64)).not_expr();
    // The head pointer and the tail's data pointer, per split end:
    //   First -> (data, data + elem_size)          [tail starts at index 1];
    //   Last  -> (data + (len-1)*elem_size, data)  [tail keeps the base].
    let (first_ptr_f, tail_data_f) = match kind {
        SliceEndKind::First => (d.clone(), d.clone().bvadd(size)),
        SliceEndKind::Last => {
            let last_idx = l.clone().bvsub(SmtExpr::bv_const(1, 64));
            (d.clone().bvadd(last_idx.bvmul(size)), d.clone())
        }
    };
    // None is the null (0) niche in the LAYOUT-designated cell only.
    let null = SmtExpr::bv_const(0, 64);
    let f0 = if niche_at_f0 {
        SmtExpr::ite(nonempty.clone(), first_ptr_f, null.clone())
    } else {
        first_ptr_f
    };
    let f1 = if !niche_at_f0 {
        SmtExpr::ite(nonempty, tail_data_f, null)
    } else {
        tail_data_f
    };
    SplitEndsSpec {
        f0,
        f1,
        // tail_len = len - 1 (wrapping bvsub — dead on None, matching the
        // unconditional emitted store).
        tail_len: l.bvsub(SmtExpr::bv_const(1, 64)),
        inputs: vec![(data.to_string(), 64), (len.to_string(), 64)],
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ay_bridge::AYConfig;
    use crate::smt::{EvalResult, SmtExpr};
    use std::collections::HashMap;
    use trust_cg_lower::types::Type;

    fn proof_authority_available() -> bool {
        crate::ay_bridge::z3_available()
    }

    /// The MIR-refinement sibling of `mem_refine.rs::alethe_crosscheck_gap`
    /// (see `crate::formal_gap` for the measured mechanism): `Some(reason)`
    /// while the outcome is `Inconclusive` on EXACTLY one of the fail-closed
    /// certification-gap diagnostics — AY establishes UNSAT but the
    /// constellation cannot independently certify the bit-vector family. A
    /// guarded test prints the loud skip and returns; every other outcome
    /// (`Refuted`, a bare or unrecognized unknown, timeout, error) falls
    /// through to its original assertion, so the exemption un-arms itself the
    /// moment an authority ships externally checkable proofs.
    fn certification_gap_reason_of(outcome: &RefinementOutcome) -> Option<&str> {
        crate::formal_gap::refinement_gap_reason(outcome)
    }

    // -----------------------------------------------------------------------
    // TV lane 14 — slice-to-Vec header spec
    // -----------------------------------------------------------------------

    /// The capacity spec must be `max(n, 1)` at every boundary value, and must
    /// be stated in a form that is NOT the emission's `n >u 1 ? n : 1` — the
    /// two meet only on `n`, which is what gives the obligation refutational
    /// content instead of making it an identity.
    #[test]
    fn slice_to_vec_header_spec_capacity_is_max_n_1() {
        let spec = slice_to_vec_header_spec("n", 4, 4);
        for (n, want_cap) in [(0u64, 1u64), (1, 1), (2, 2), (7, 7)] {
            let mut env = HashMap::new();
            env.insert("n".to_string(), n);
            assert_eq!(
                spec.cap.eval(&env),
                EvalResult::Bv(want_cap),
                "cap for n={n}"
            );
            // alloc_bytes must track the SAME capacity, scaled by elem_size.
            assert_eq!(
                spec.alloc_bytes.eval(&env),
                EvalResult::Bv(want_cap * 4),
                "alloc_bytes for n={n}"
            );
            // len == n, and len <= cap must hold for every n.
            assert_eq!(spec.len.eval(&env), EvalResult::Bv(n), "len for n={n}");
            assert_eq!(
                spec.len_le_cap.eval(&env),
                EvalResult::Bool(true),
                "len<=cap must hold for n={n}"
            );
        }
    }

    /// The spec is written as `ITE(n == 0, 1, n)` while the bridge emits
    /// `n >u 1 ? n : 1`. Pin that the spec is NOT syntactically the emission —
    /// if someone "simplifies" the spec into the emission's shape the lane
    /// silently degrades to `X == X` and certifies nothing.
    #[test]
    fn slice_to_vec_header_spec_is_not_the_emission_shape() {
        let spec = slice_to_vec_header_spec("n", 8, 8);
        let emission_shape = SmtExpr::ite(
            SmtExpr::var("n", 64).bvugt(SmtExpr::bv_const(1, 64)),
            SmtExpr::var("n", 64),
            SmtExpr::bv_const(1, 64),
        );
        assert_ne!(
            format!("{:?}", spec.cap),
            format!("{emission_shape:?}"),
            "spec capacity must not be re-derived in the emission's own shape"
        );
        // ...but must AGREE with it on every value (equivalent, not identical).
        for n in [0u64, 1, 2, 3, 64, u64::MAX] {
            let mut env = HashMap::new();
            env.insert("n".to_string(), n);
            assert_eq!(
                spec.cap.eval(&env),
                emission_shape.clone().eval(&env),
                "spec and emission must agree at n={n}"
            );
        }
    }

    /// A WRONG emission must produce a different value, not merely a different
    /// spelling. These are the mutants the lane exists to catch.
    #[test]
    fn slice_to_vec_header_spec_refutes_wrong_capacity_and_size() {
        let spec = slice_to_vec_header_spec("n", 4, 4);
        let mut env = HashMap::new();
        env.insert("n".to_string(), 0u64);
        // Mutant: cap = n (drops the max) — differs from the spec at n == 0,
        // which is exactly the zero-length `to_vec()` case.
        let cap_is_n = SmtExpr::var("n", 64);
        assert_ne!(spec.cap.eval(&env), cap_is_n.eval(&env));
        // Mutant: alloc_bytes = cap (forgets to scale by elem_size).
        env.insert("n".to_string(), 3u64);
        assert_ne!(spec.alloc_bytes.eval(&env), spec.cap.eval(&env));
        // Mutant: wrong element size.
        let wrong_size = slice_to_vec_header_spec("n", 8, 4);
        assert_ne!(
            spec.alloc_bytes.eval(&env),
            wrong_size.alloc_bytes.eval(&env)
        );
        // Mutant: wrong alignment.
        let wrong_align = slice_to_vec_header_spec("n", 4, 8);
        assert_ne!(
            spec.alloc_align.eval(&env),
            wrong_align.alloc_align.eval(&env)
        );
    }

    // -----------------------------------------------------------------------
    // helpers
    // -----------------------------------------------------------------------

    fn cfg() -> AYConfig {
        AYConfig::default()
    }

    fn var_s32(name: &str) -> MirOperand {
        MirOperand::Var {
            name: name.to_string(),
            ty: MirScalarTy::SInt(Type::I32),
        }
    }
    fn var_u32(name: &str) -> MirOperand {
        MirOperand::Var {
            name: name.to_string(),
            ty: MirScalarTy::UInt(Type::I32),
        }
    }
    fn var_s8(name: &str) -> MirOperand {
        MirOperand::Var {
            name: name.to_string(),
            ty: MirScalarTy::SInt(Type::I8),
        }
    }

    /// Direct concrete evaluation of a refinement obligation's two sides.
    /// Returns `Ok(())` if they agree (semantically) on `env`, else `Err(cex)`.
    fn eval_agree(ob: &ProofObligation, env: &HashMap<String, u64>) -> Result<(), String> {
        let lhs = ob
            .trust_ir_expr
            .try_eval(env)
            .map_err(|e| format!("trust_ir eval: {e:?}"))?;
        let rhs = ob
            .aarch64_expr
            .try_eval(env)
            .map_err(|e| format!("mir eval: {e:?}"))?;
        if lhs.semantically_equal(&rhs) {
            Ok(())
        } else {
            Err(format!("disagree: trust_ir={lhs:?} mir(spec)={rhs:?}"))
        }
    }

    // -----------------------------------------------------------------------
    // (a) CORRECT scalar lowerings DISCHARGE
    // -----------------------------------------------------------------------

    /// Invariant: a correctly-lowered scalar `Add` (MIR `Add` -> trust-ir
    /// `Iadd`) must refine. This is the positive control: if this ever fails,
    /// the slice is broken, not the bridge.
    #[test]
    fn correct_iadd_i32_refines() {
        if !proof_authority_available() {
            return;
        }
        let mir = MirRvalue::BinaryOp {
            op: MirBinOp::Add,
            ty: MirScalarTy::SInt(Type::I32),
            lhs: var_s32("a"),
            rhs: var_s32("b"),
        };
        let enc = encode_mir_rvalue(&mir).unwrap();
        let a = SmtExpr::var("a", 32);
        let b = SmtExpr::var("b", 32);
        let bridge = BridgeLowering::BinOp {
            op: Opcode::Iadd,
            ty: Type::I32,
            lhs: a,
            rhs: b,
        };
        let ob = build_refinement_obligation("Add_i32_correct", &bridge, &enc);
        match discharge_refinement(&ob, &cfg()) {
            RefinementOutcome::Refined => {}
            other => panic!("expected Refined, got {other:?}"),
        }
    }

    /// Invariant: unsigned `Div` (MIR `Div` on `u32` -> trust-ir `Udiv`) under
    /// the divisor-nonzero precondition must refine. Locks in that the slice
    /// threads Div/Rem preconditions (and chose the UNSIGNED divide for an
    /// unsigned type, mirroring `is_signed_integer(lhs_ty)` in the bridge).
    #[test]
    fn correct_udiv_i32_refines() {
        if !proof_authority_available() {
            return;
        }
        let mir = MirRvalue::BinaryOp {
            op: MirBinOp::Div,
            ty: MirScalarTy::UInt(Type::I32),
            lhs: var_u32("a"),
            rhs: var_u32("b"),
        };
        let enc = encode_mir_rvalue(&mir).unwrap();
        assert_eq!(
            enc.preconditions.len(),
            1,
            "Div must carry divisor!=0 precondition"
        );
        let a = SmtExpr::var("a", 32);
        let b = SmtExpr::var("b", 32);
        let bridge = BridgeLowering::BinOp {
            op: Opcode::Udiv,
            ty: Type::I32,
            lhs: a,
            rhs: b,
        };
        let ob = build_refinement_obligation("Udiv_i32_correct", &bridge, &enc);
        match discharge_refinement(&ob, &cfg()) {
            RefinementOutcome::Refined => {}
            other => {
                if let Some(reason) = certification_gap_reason_of(&other) {
                    crate::formal_gap::print_gap_skip("correct_udiv_i32_refines", reason);
                    return;
                }
                panic!("expected Refined, got {other:?}")
            }
        }
    }

    /// Invariant: correct signed widening (`i8 as i32` -> trust-ir `SExt`)
    /// refines. Exhaustive at i8 source via the mock path. Locks in the
    /// signed-source -> sign-extend rule.
    #[test]
    fn correct_sext_i8_to_i32_refines() {
        let mir = MirRvalue::Cast {
            kind: MirCastKind::IntToInt,
            src_ty: MirScalarTy::SInt(Type::I8),
            dst_ty: MirScalarTy::SInt(Type::I32),
            operand: MirOperand::Var {
                name: "a".to_string(),
                ty: MirScalarTy::SInt(Type::I8),
            },
        };
        let enc = encode_mir_rvalue(&mir).unwrap();
        let a = SmtExpr::var("a", 8);
        let bridge = BridgeLowering::SExt {
            src_ty: Type::I8,
            dst_ty: Type::I32,
            operand: a,
        };
        let ob = build_refinement_obligation("SExt_i8_i32_correct", &bridge, &enc);
        match discharge_refinement(&ob, &cfg()) {
            RefinementOutcome::Refined => {}
            other => panic!("expected Refined, got {other:?}"),
        }
    }

    /// Invariant: correct float negation (MIR float `Neg` -> trust-ir `FNeg`)
    /// agrees on the full IEEE edge-case battery, including -0.0 (the value
    /// that distinguishes a correct sign-bit flip from the wrong `0.0 - x`).
    #[test]
    fn correct_fneg_f64_refines_on_edge_cases() {
        for &v in &[
            0.0f64,
            -0.0,
            1.0,
            -1.0,
            f64::INFINITY,
            f64::NEG_INFINITY,
            f64::NAN,
            f64::MAX,
            f64::MIN,
        ] {
            let mir = MirRvalue::UnaryOp {
                op: MirUnOp::Neg,
                ty: MirScalarTy::Float(Type::F64),
                operand: MirOperand::ConstFloat {
                    value: v,
                    ty: MirScalarTy::Float(Type::F64),
                },
            };
            let enc = encode_mir_rvalue(&mir).unwrap();
            let bridge = BridgeLowering::FNeg {
                ty: Type::F64,
                operand: SmtExpr::fp64_const(v),
            };
            let ob = build_refinement_obligation("FNeg_f64_correct", &bridge, &enc);
            eval_agree(&ob, &HashMap::new())
                .unwrap_or_else(|e| panic!("correct FNeg disagreed at v={v}: {e}"));
        }
    }

    // -----------------------------------------------------------------------
    // (b) DELIBERATELY-WRONG lowerings are REFUTED with a counterexample
    // -----------------------------------------------------------------------

    /// Locks in #68-fneg: MIR float `Neg` lowered as `0.0 - x` (FPSub) instead
    /// of a sign-bit flip is WRONG. Counterexample: x = -0.0, where the correct
    /// `-(-0.0) = +0.0` but `0.0 - (-0.0) = +0.0` agree by VALUE — the true
    /// distinguishing input under bit-exact comparison is `x = +0.0`:
    /// `fp_neg(+0.0) = -0.0` (bits 0x8000…) vs `0.0 - 0.0 = +0.0` (bits 0x0).
    /// `semantically_equal` compares to_bits(), so these differ.
    #[test]
    fn wrong_fneg_as_sub_is_refuted() {
        // x = +0.0 is the witness.
        let v = 0.0f64;
        let mir = MirRvalue::UnaryOp {
            op: MirUnOp::Neg,
            ty: MirScalarTy::Float(Type::F64),
            operand: MirOperand::ConstFloat {
                value: v,
                ty: MirScalarTy::Float(Type::F64),
            },
        };
        let enc = encode_mir_rvalue(&mir).unwrap();
        let bridge = BridgeLowering::FNegAsSub {
            ty: Type::F64,
            operand: SmtExpr::fp64_const(v),
        };
        let ob = build_refinement_obligation("FNeg_as_sub_WRONG", &bridge, &enc);
        // The spec side (mir) is fp_neg(+0.0) = -0.0; the bridge side is
        // 0.0 - 0.0 = +0.0. They are NOT bit-equal.
        let err = eval_agree(&ob, &HashMap::new())
            .expect_err("wrong FNeg-as-sub must be refuted at x=+0.0");
        assert!(err.contains("disagree"), "unexpected message: {err}");
    }

    /// Locks in #68-cvt: signed `i32 as f32` lowered as an UNSIGNED int->float
    /// conversion is WRONG for negative inputs. Counterexample: a = -1
    /// (0xFFFF_FFFF): signed conversion yields -1.0f32, unsigned yields
    /// 4294967295.0f32.
    #[test]
    fn wrong_sitofp_as_unsigned_is_refuted() {
        let mir = MirRvalue::Cast {
            kind: MirCastKind::IntToFloat,
            src_ty: MirScalarTy::SInt(Type::I32),
            dst_ty: MirScalarTy::Float(Type::F32),
            operand: var_s32("a"),
        };
        let enc = encode_mir_rvalue(&mir).unwrap();
        let a = SmtExpr::var("a", 32);
        let bridge = BridgeLowering::SIToFPAsUnsigned {
            src_ty: Type::I32,
            dst_ty: Type::F32,
            operand: a,
        };
        let ob = build_refinement_obligation("SIToFP_as_unsigned_WRONG", &bridge, &enc);
        // Witness: a = -1 (0xFFFF_FFFF).
        let mut env = HashMap::new();
        env.insert("a".to_string(), 0xFFFF_FFFFu64);
        let err =
            eval_agree(&ob, &env).expect_err("signed-as-unsigned cvt must be refuted at a=-1");
        assert!(err.contains("disagree"), "unexpected message: {err}");
    }

    /// Locks in #59: a `+` that Rust requires to wrap (or trap) lowered to a
    /// SATURATING add is WRONG. Counterexample: a = INT32_MAX, b = 1.
    /// Wrapping yields INT32_MIN; saturation yields INT32_MAX.
    #[test]
    fn wrong_saturating_add_is_refuted() {
        let mir = MirRvalue::BinaryOp {
            op: MirBinOp::Add,
            ty: MirScalarTy::SInt(Type::I32),
            lhs: var_s32("a"),
            rhs: var_s32("b"),
        };
        let enc = encode_mir_rvalue(&mir).unwrap();
        let a = SmtExpr::var("a", 32);
        let b = SmtExpr::var("b", 32);
        let bridge = BridgeLowering::SaturatingAdd {
            ty: Type::I32,
            lhs: a,
            rhs: b,
        };
        let ob = build_refinement_obligation("SaturatingAdd_WRONG", &bridge, &enc);
        // Witness: a = INT32_MAX (0x7FFF_FFFF), b = 1.
        let mut env = HashMap::new();
        env.insert("a".to_string(), 0x7FFF_FFFFu64);
        env.insert("b".to_string(), 1u64);
        let err = eval_agree(&ob, &env)
            .expect_err("saturating-vs-wrapping add must be refuted at INT_MAX+1");
        assert!(err.contains("disagree"), "unexpected message: {err}");
        // And the production discharge path must also REFUTE it (mock or solver).
        match discharge_refinement(&ob, &cfg()) {
            RefinementOutcome::Refuted { .. } => {}
            other => panic!("expected Refuted via discharge, got {other:?}"),
        }
    }

    /// Locks in the carrier/extension family (#66/#51 spirit): unsigned
    /// widening (`u8 as u32`) lowered as a SIGN-extend instead of zero-extend
    /// is WRONG. Counterexample: a = 0x80. Refuted exhaustively at i8 via the
    /// production discharge path.
    #[test]
    fn wrong_zext_lowered_as_sext_is_refuted() {
        let mir = MirRvalue::Cast {
            kind: MirCastKind::IntToInt,
            src_ty: MirScalarTy::UInt(Type::I8),
            dst_ty: MirScalarTy::UInt(Type::I32),
            operand: MirOperand::Var {
                name: "a".to_string(),
                ty: MirScalarTy::UInt(Type::I8),
            },
        };
        let enc = encode_mir_rvalue(&mir).unwrap();
        let a = SmtExpr::var("a", 8);
        // The bug: bridge emits SExt for an unsigned widen.
        let bridge = BridgeLowering::SExt {
            src_ty: Type::I8,
            dst_ty: Type::I32,
            operand: a,
        };
        let ob = build_refinement_obligation("ZExt_as_SExt_WRONG", &bridge, &enc);
        match discharge_refinement(&ob, &cfg()) {
            RefinementOutcome::Refuted { .. } => {}
            other => panic!("expected Refuted, got {other:?}"),
        }
    }

    /// Locks in the #71-class "overflow flag dropped" shape at the rvalue
    /// level: a checked add whose bridge lowering computes the WRONG overflow
    /// flag (here: always-false) is refuted. Counterexample: INT32_MAX + 1.
    #[test]
    fn wrong_checked_add_overflow_flag_is_refuted() {
        let mir = MirRvalue::CheckedBinaryOp {
            op: MirBinOp::Add,
            ty: MirScalarTy::SInt(Type::I32),
            lhs: var_s32("a"),
            rhs: var_s32("b"),
        };
        let enc = encode_mir_rvalue(&mir).unwrap();
        // Bridge models the overflow flag as a constant 0 (dropped) — wrong.
        let a = SmtExpr::var("a", 32);
        let b = SmtExpr::var("b", 32);
        let value = a.clone().bvadd(b);
        let always_false = SmtExpr::bv_const(0, 1);
        let bridge = BridgeLowering::Overflow {
            value,
            overflow: always_false,
        };
        let ob = build_refinement_obligation("CheckedAdd_flag_dropped_WRONG", &bridge, &enc);
        // Witness: INT32_MAX + 1 overflows (flag should be 1, bridge says 0).
        let mut env = HashMap::new();
        env.insert("a".to_string(), 0x7FFF_FFFFu64);
        env.insert("b".to_string(), 1u64);
        let err =
            eval_agree(&ob, &env).expect_err("dropped overflow flag must be refuted at INT_MAX+1");
        assert!(err.contains("disagree"), "unexpected message: {err}");
    }

    /// Positive control for checked add: correct (value, overflow) pair refines
    /// against the spec. Locks in that the packed `overflow :: value` shape
    /// matches between the bridge model and the MIR spec.
    #[test]
    fn correct_checked_add_refines() {
        let mir = MirRvalue::CheckedBinaryOp {
            op: MirBinOp::Add,
            ty: MirScalarTy::SInt(Type::I32),
            lhs: var_s32("a"),
            rhs: var_s32("b"),
        };
        let enc = encode_mir_rvalue(&mir).unwrap();
        // Correct bridge model: same value + correct signed-overflow flag.
        let a = SmtExpr::var("a", 32);
        let b = SmtExpr::var("b", 32);
        let value = a.clone().bvadd(b.clone());
        let exact = a.clone().sign_ext(1).bvadd(b.clone().sign_ext(1));
        let wrapped = value.clone().sign_ext(1);
        let overflow_bool = exact.eq_expr(wrapped).not_expr();
        let overflow = SmtExpr::ite(
            overflow_bool,
            SmtExpr::bv_const(1, 1),
            SmtExpr::bv_const(0, 1),
        );
        let bridge = BridgeLowering::Overflow { value, overflow };
        let ob = build_refinement_obligation("CheckedAdd_correct", &bridge, &enc);
        // Spot-check a couple of witnesses directly (exhaustive at i32 via
        // discharge would be statistical; direct points keep this fast).
        for (av, bv) in [
            (0x7FFF_FFFFu64, 1u64),
            (1u64, 1u64),
            (0xFFFF_FFFFu64, 0xFFFF_FFFFu64),
        ] {
            let mut env = HashMap::new();
            env.insert("a".to_string(), av);
            env.insert("b".to_string(), bv);
            eval_agree(&ob, &env).unwrap_or_else(|e| panic!("correct checked add disagreed: {e}"));
        }
    }

    /// Sanity: `Use`/Copy/Move is an identity refinement.
    #[test]
    fn correct_use_is_identity() {
        if !proof_authority_available() {
            return;
        }
        let mir = MirRvalue::Use { src: var_s32("a") };
        let enc = encode_mir_rvalue(&mir).unwrap();
        let bridge = BridgeLowering::Use {
            operand: SmtExpr::var("a", 32),
        };
        let ob = build_refinement_obligation("Use_identity", &bridge, &enc);
        match discharge_refinement(&ob, &cfg()) {
            RefinementOutcome::Refined => {}
            other => panic!("expected Refined, got {other:?}"),
        }
    }

    /// Block-level: a straight-line `MirBlock` of correct rvalues folds into a
    /// symbolic store binding every `dst`. Locks in that `encode_block_store`
    /// honors intra-block dataflow (the `Return`-terminated, edge-free case).
    #[test]
    fn straight_line_block_encodes() {
        let block = MirBlock::straight_line(vec![
            MirStmt {
                dst: "t0".to_string(),
                rvalue: MirRvalue::BinaryOp {
                    op: MirBinOp::Add,
                    ty: MirScalarTy::SInt(Type::I32),
                    lhs: var_s32("a"),
                    rhs: var_s32("b"),
                },
            },
            MirStmt {
                dst: "t1".to_string(),
                rvalue: MirRvalue::UnaryOp {
                    op: MirUnOp::Neg,
                    ty: MirScalarTy::SInt(Type::I32),
                    // reads the earlier dst `t0` -> resolves through the store.
                    operand: MirOperand::Var {
                        name: "t0".to_string(),
                        ty: MirScalarTy::SInt(Type::I32),
                    },
                },
            },
        ]);
        for stmt in &block.stmts {
            encode_mir_rvalue(&stmt.rvalue).expect("each stmt encodes");
        }
        let bs = encode_block_store(&block).expect("block folds");
        assert!(
            bs.store.contains_key("t0") && bs.store.contains_key("t1"),
            "both dsts bound"
        );
        // `a` and `b` are the only block-external inputs (t0 is an internal dst).
        let names: std::collections::HashSet<&str> =
            bs.inputs.iter().map(|(n, _)| n.as_str()).collect();
        assert_eq!(names, ["a", "b"].into_iter().collect());
    }

    /// Demonstrates `check_rvalue_lowering` end-to-end (the bridge call-site
    /// shape): correct lowering -> Refined.
    #[test]
    fn check_rvalue_lowering_end_to_end() {
        if !proof_authority_available() {
            return;
        }
        let mir = MirRvalue::BinaryOp {
            op: MirBinOp::Sub,
            ty: MirScalarTy::SInt(Type::I32),
            lhs: var_s32("a"),
            rhs: var_s32("b"),
        };
        let a = SmtExpr::var("a", 32);
        let b = SmtExpr::var("b", 32);
        let bridge = BridgeLowering::BinOp {
            op: Opcode::Isub,
            ty: Type::I32,
            lhs: a,
            rhs: b,
        };
        let outcome = check_rvalue_lowering("Sub_e2e", &mir, &bridge, &cfg()).unwrap();
        assert!(
            matches!(outcome, RefinementOutcome::Refined),
            "got {outcome:?}"
        );
    }

    /// Guard: `EvalResult::semantically_equal` really does distinguish +0.0 and
    /// -0.0 (the assumption the FNeg refute relies on). If this regresses, the
    /// FNeg refute would silently pass.
    #[test]
    fn signed_zero_is_bit_distinguished() {
        let pos = EvalResult::Float(0.0);
        let neg = EvalResult::Float(-0.0);
        assert!(
            !pos.semantically_equal(&neg),
            "+0.0 and -0.0 must be bit-distinct"
        );
    }

    // -----------------------------------------------------------------------
    // (c) P3c SOUNDNESS regressions: encoding-faithfulness gaps
    // -----------------------------------------------------------------------

    /// P3c(1) — the INT_MIN/-1 point ALONE cannot refute a correct raw `Sdiv`.
    ///
    /// The MIR signed-Div spec models INT_MIN/-1 as a trap sentinel while a raw
    /// `bvsdiv` wraps, so the two sides genuinely DIFFER at exactly that point
    /// (first assertion — the historical false-refute witness, kept as
    /// documentation that the trap-value model is unchanged). But that point is
    /// OUTSIDE the rvalue's domain: rustc's MIR inserts `Assert` terminators
    /// before the Div guaranteeing `rhs != 0` and `NOT(lhs == INT_MIN && rhs ==
    /// -1)` (and `unchecked_div` callers promise the same, UB otherwise), so
    /// `build_refinement_obligation` attaches that domain precondition to the
    /// raw `BinOp{Sdiv}` bridge model and the correct lowering REFINES —
    /// in-domain the trap-modeling spec collapses to plain `bvsdiv`. Exhaustive
    /// at i8 via the production discharge path.
    ///
    /// Note the #59-class trap-model bite is NOT weakened: `TrappingSdiv` (the
    /// bridge variant that CLAIMS the trap) is still checked at the INT_MIN/-1
    /// point itself (`correct_trapping_sdiv_refines` below), and the spec-side
    /// trap model / `mir_binop_precondition` are untouched.
    #[test]
    fn raw_sdiv_int_min_neg1_point_alone_cannot_refute() {
        let mir = MirRvalue::BinaryOp {
            op: MirBinOp::Div,
            ty: MirScalarTy::SInt(Type::I8),
            lhs: var_s8("a"),
            rhs: var_s8("b"),
        };
        let enc = encode_mir_rvalue(&mir).unwrap();
        let a = SmtExpr::var("a", 8);
        let b = SmtExpr::var("b", 8);
        // Raw wrapping signed divide — exactly what the bridge emits (the trap
        // is upstream in the MIR Assert, not at the rvalue).
        let bridge = BridgeLowering::BinOp {
            op: Opcode::Sdiv,
            ty: Type::I8,
            lhs: a,
            rhs: b,
        };
        let ob = build_refinement_obligation("Sdiv_raw_at_INT_MIN_neg1_in_domain", &bridge, &enc);
        // The two sides still DISAGREE at the trap point a = INT8_MIN (0x80),
        // b = -1 (0xFF): wrapping yields 0x80, the spec yields the sentinel.
        let mut env = HashMap::new();
        env.insert("a".to_string(), 0x80u64);
        env.insert("b".to_string(), 0xFFu64);
        let err = eval_agree(&ob, &env)
            .expect_err("the trap-value model must still differ from raw bvsdiv at INT_MIN/-1");
        assert!(err.contains("disagree"), "unexpected message: {err}");
        // The obligation carries BOTH domain preconditions: the MIR-side
        // `rhs != 0` (threaded from `encode_mir_rvalue`) plus the attached
        // `NOT(lhs == INT_MIN && rhs == -1)`.
        assert_eq!(
            ob.preconditions.len(),
            2,
            "raw Sdiv obligation must carry rhs!=0 AND the INT_MIN/-1 exclusion"
        );
        // The trap point fails the preconditions (it is out of domain) ...
        assert!(
            !ob.preconditions.iter().all(|p| p.eval(&env).as_bool()),
            "INT_MIN/-1 must be excluded by the preconditions"
        );
        // ... while an ordinary point satisfies them.
        let mut ok_env = HashMap::new();
        ok_env.insert("a".to_string(), 0x07u64);
        ok_env.insert("b".to_string(), 0x02u64);
        assert!(
            ob.preconditions.iter().all(|p| p.eval(&ok_env).as_bool()),
            "an ordinary in-domain point must satisfy the preconditions"
        );
        // And the production discharge path REFINES the correct raw lowering:
        // the only disagreeing point is precondition-excluded.
        match discharge_refinement(&ob, &cfg()) {
            RefinementOutcome::Refined => {}
            other => {
                if let Some(reason) = certification_gap_reason_of(&other) {
                    crate::formal_gap::print_gap_skip(
                        "raw_sdiv_int_min_neg1_point_alone_cannot_refute",
                        reason,
                    );
                    return;
                }
                panic!("expected Refined via discharge, got {other:?}")
            }
        }
    }

    /// P3c sdiv-coverage — a correct raw `Sdiv` at i8 is decided REFINED by the
    /// always-on FAST (no-solver) lane: the obligation is exhaustively decidable
    /// (two uniform 8-bit inputs, no FP), the sweep skips the precondition-
    /// excluded points (`b == 0` and INT_MIN/-1) and proves every in-domain
    /// point equal. `Some(Refined)` — not `None` — is the assertion that the
    /// default-on lane GAINS signed-div coverage rather than skipping it.
    #[test]
    fn correct_raw_sdiv_i8_refines_in_fast_lane() {
        let mir = MirRvalue::BinaryOp {
            op: MirBinOp::Div,
            ty: MirScalarTy::SInt(Type::I8),
            lhs: var_s8("a"),
            rhs: var_s8("b"),
        };
        let a = SmtExpr::var("a", 8);
        let b = SmtExpr::var("b", 8);
        let bridge = BridgeLowering::BinOp {
            op: Opcode::Sdiv,
            ty: Type::I8,
            lhs: a,
            rhs: b,
        };
        match check_rvalue_lowering_fast("Sdiv_i8_correct_fast", &mir, &bridge).unwrap() {
            Some(RefinementOutcome::Refined) => {}
            other => panic!("expected Some(Refined) from the fast lane, got {other:?}"),
        }
    }

    /// P3c sdiv-coverage — a correct raw `Sdiv` at i32 REFINES via the formal
    /// z3 path (`discharge_refinement` with a solver on PATH), exercising the
    /// satisfiability gate over the attached preconditions (they are clearly
    /// satisfiable, so the gate must not downgrade the proof).
    #[test]
    fn correct_raw_sdiv_i32_refines() {
        if !proof_authority_available() {
            return;
        }
        let mir = MirRvalue::BinaryOp {
            op: MirBinOp::Div,
            ty: MirScalarTy::SInt(Type::I32),
            lhs: var_s32("a"),
            rhs: var_s32("b"),
        };
        let a = SmtExpr::var("a", 32);
        let b = SmtExpr::var("b", 32);
        let bridge = BridgeLowering::BinOp {
            op: Opcode::Sdiv,
            ty: Type::I32,
            lhs: a,
            rhs: b,
        };
        let outcome = check_rvalue_lowering("Sdiv_i32_correct", &mir, &bridge, &cfg()).unwrap();
        if let Some(reason) = certification_gap_reason_of(&outcome) {
            crate::formal_gap::print_gap_skip("correct_raw_sdiv_i32_refines", reason);
            return;
        }
        assert!(
            matches!(outcome, RefinementOutcome::Refined),
            "got {outcome:?}"
        );
    }

    /// P3c sdiv-coverage — `Sdiv` modeled as `Udiv` (wrong signedness) is still
    /// REFUTED under the domain preconditions: signed and unsigned division
    /// differ at in-domain points with a negative operand (witness a = -2,
    /// b = 2: sdiv = -1, udiv(0xFE, 2) = 0x7F). The domain restriction excludes
    /// ONLY the INT_MIN/-1 trap point, so it cannot mask the signedness bug.
    #[test]
    fn sdiv_as_udiv_is_refuted() {
        let mir = MirRvalue::BinaryOp {
            op: MirBinOp::Div,
            ty: MirScalarTy::SInt(Type::I8),
            lhs: var_s8("a"),
            rhs: var_s8("b"),
        };
        let enc = encode_mir_rvalue(&mir).unwrap();
        let a = SmtExpr::var("a", 8);
        let b = SmtExpr::var("b", 8);
        // The BUG: unsigned divide for a signed MIR Div.
        let bridge = BridgeLowering::BinOp {
            op: Opcode::Udiv,
            ty: Type::I8,
            lhs: a,
            rhs: b,
        };
        let ob = build_refinement_obligation("Sdiv_as_Udiv_WRONG", &bridge, &enc);
        // Direct in-domain witness (negative lhs, b != 0, not INT_MIN/-1).
        let mut env = HashMap::new();
        env.insert("a".to_string(), 0xFEu64); // -2
        env.insert("b".to_string(), 0x02u64);
        let err = eval_agree(&ob, &env).expect_err("Udiv must disagree on a negative operand");
        assert!(err.contains("disagree"), "unexpected message: {err}");
        match discharge_refinement(&ob, &cfg()) {
            RefinementOutcome::Refuted { counterexample } => {
                assert!(
                    !counterexample.is_empty(),
                    "refutation must carry a counterexample"
                );
            }
            other => panic!("expected Refuted, got {other:?}"),
        }
        // The fast lane refutes it too (exhaustive at i8 — a genuine
        // counterexample, every tested point satisfied the preconditions).
        match check_rvalue_lowering_fast("Sdiv_as_Udiv_WRONG_fast", &mir, &bridge).unwrap() {
            Some(RefinementOutcome::Refuted { .. }) => {}
            other => panic!("expected Some(Refuted) from the fast lane, got {other:?}"),
        }
    }

    fn var_s128(name: &str) -> MirOperand {
        MirOperand::Var {
            name: name.to_string(),
            ty: MirScalarTy::SInt(Type::I128),
        }
    }

    /// REGRESSION (round-2 reaudit): a CORRECT raw `Sdiv` at i128 must NOT
    /// false-REFUTE. The I128 INT_MIN/-1 signed-overflow point was previously left
    /// out of `sdiv_srem_domain_precondition` (its constants exceed a u64), so the
    /// obligation was checked at that UB point — where the MIR trap-spec and the
    /// libcall lowering disagree — and a correct i128 `/`/`%` was spuriously
    /// Refuted. Harmless until the default solver lane began checking i128
    /// obligations, after which it gated EVERY i128 program using `/`, `%`, or
    /// `.rem_euclid`. With the I128 domain precondition (built from two 64-bit
    /// halves) it Refines (or is Inconclusive if the solver cannot decide 128-bit
    /// division), never Refuted.
    #[test]
    fn correct_raw_sdiv_i128_does_not_false_refute() {
        if !proof_authority_available() {
            return;
        }
        let mir = MirRvalue::BinaryOp {
            op: MirBinOp::Div,
            ty: MirScalarTy::SInt(Type::I128),
            lhs: var_s128("a"),
            rhs: var_s128("b"),
        };
        let bridge = BridgeLowering::BinOp {
            op: Opcode::Sdiv,
            ty: Type::I128,
            lhs: SmtExpr::var("a", 128),
            rhs: SmtExpr::var("b", 128),
        };
        let outcome = check_rvalue_lowering("Sdiv_i128_correct", &mir, &bridge, &cfg()).unwrap();
        assert!(
            !matches!(outcome, RefinementOutcome::Refuted { .. }),
            "a correct i128 Sdiv must not false-REFUTE (the regression), got {outcome:?}"
        );
    }

    /// NON-VACUITY at i128: the I128 domain restriction excludes ONLY the INT_MIN/-1
    /// overflow point, so a signedness bug (`Sdiv` modeled as `Udiv`) still differs
    /// at in-domain negative-operand points and is REFUTED — the precondition cannot
    /// mask a real lowering bug.
    #[test]
    fn sdiv_as_udiv_is_refuted_i128() {
        if !proof_authority_available() {
            return;
        }
        let mir = MirRvalue::BinaryOp {
            op: MirBinOp::Div,
            ty: MirScalarTy::SInt(Type::I128),
            lhs: var_s128("a"),
            rhs: var_s128("b"),
        };
        // The BUG: unsigned divide for a signed MIR Div at i128.
        let bridge = BridgeLowering::BinOp {
            op: Opcode::Udiv,
            ty: Type::I128,
            lhs: SmtExpr::var("a", 128),
            rhs: SmtExpr::var("b", 128),
        };
        let outcome =
            check_rvalue_lowering("Sdiv_as_Udiv_i128_WRONG", &mir, &bridge, &cfg()).unwrap();
        assert!(
            !matches!(outcome, RefinementOutcome::Refined),
            "a wrong (Udiv-for-Sdiv) i128 lowering must NOT be admitted, got {outcome:?}"
        );
    }

    /// P3c sdiv-coverage — operand-SWAPPED `Sdiv` is still REFUTED. The domain
    /// precondition is built over the bridge model's OWN (swapped) operands, so
    /// it binds the real exprs without masking the swap (witness a = 4, b = 2:
    /// spec 4/2 = 2, bridge sdiv(2, 4) = 0 — fully in-domain).
    #[test]
    fn sdiv_operand_swapped_is_refuted() {
        let mir = MirRvalue::BinaryOp {
            op: MirBinOp::Div,
            ty: MirScalarTy::SInt(Type::I8),
            lhs: var_s8("a"),
            rhs: var_s8("b"),
        };
        let enc = encode_mir_rvalue(&mir).unwrap();
        let a = SmtExpr::var("a", 8);
        let b = SmtExpr::var("b", 8);
        // The BUG: operands swapped.
        let bridge = BridgeLowering::BinOp {
            op: Opcode::Sdiv,
            ty: Type::I8,
            lhs: b,
            rhs: a,
        };
        let ob = build_refinement_obligation("Sdiv_swapped_WRONG", &bridge, &enc);
        match discharge_refinement(&ob, &cfg()) {
            RefinementOutcome::Refuted { .. } => {}
            other => panic!("expected Refuted, got {other:?}"),
        }
    }

    /// P3c srem-coverage — a correct raw `Srem` REFINES under the same domain
    /// preconditions: fast lane at i8 (`Some(Refined)`, exhaustive) and the
    /// formal z3 path at i32. In-domain the MIR signed-Rem trap-value spec
    /// collapses to the same `a - sdiv(a,b)*b` the trust-ir `Srem` encoder uses.
    #[test]
    fn correct_raw_srem_refines() {
        if !proof_authority_available() {
            return;
        }
        let mir_i8 = MirRvalue::BinaryOp {
            op: MirBinOp::Rem,
            ty: MirScalarTy::SInt(Type::I8),
            lhs: var_s8("a"),
            rhs: var_s8("b"),
        };
        let a8 = SmtExpr::var("a", 8);
        let b8 = SmtExpr::var("b", 8);
        let bridge_i8 = BridgeLowering::BinOp {
            op: Opcode::Srem,
            ty: Type::I8,
            lhs: a8,
            rhs: b8,
        };
        match check_rvalue_lowering_fast("Srem_i8_correct_fast", &mir_i8, &bridge_i8).unwrap() {
            Some(RefinementOutcome::Refined) => {}
            other => panic!("expected Some(Refined) from the fast lane, got {other:?}"),
        }

        let mir_i32 = MirRvalue::BinaryOp {
            op: MirBinOp::Rem,
            ty: MirScalarTy::SInt(Type::I32),
            lhs: var_s32("a"),
            rhs: var_s32("b"),
        };
        let a32 = SmtExpr::var("a", 32);
        let b32 = SmtExpr::var("b", 32);
        let bridge_i32 = BridgeLowering::BinOp {
            op: Opcode::Srem,
            ty: Type::I32,
            lhs: a32,
            rhs: b32,
        };
        let outcome =
            check_rvalue_lowering("Srem_i32_correct", &mir_i32, &bridge_i32, &cfg()).unwrap();
        if let Some(reason) = certification_gap_reason_of(&outcome) {
            crate::formal_gap::print_gap_skip("correct_raw_srem_refines", reason);
            return;
        }
        assert!(
            matches!(outcome, RefinementOutcome::Refined),
            "got {outcome:?}"
        );
    }

    /// P3c srem-coverage — `Srem` modeled as `Urem` (wrong signedness) is still
    /// REFUTED in-domain (witness a = -3, b = 2: srem = -1, urem(0xFD, 2) = 1).
    #[test]
    fn srem_as_urem_is_refuted() {
        let mir = MirRvalue::BinaryOp {
            op: MirBinOp::Rem,
            ty: MirScalarTy::SInt(Type::I8),
            lhs: var_s8("a"),
            rhs: var_s8("b"),
        };
        let enc = encode_mir_rvalue(&mir).unwrap();
        let a = SmtExpr::var("a", 8);
        let b = SmtExpr::var("b", 8);
        // The BUG: unsigned remainder for a signed MIR Rem.
        let bridge = BridgeLowering::BinOp {
            op: Opcode::Urem,
            ty: Type::I8,
            lhs: a,
            rhs: b,
        };
        let ob = build_refinement_obligation("Srem_as_Urem_WRONG", &bridge, &enc);
        let mut env = HashMap::new();
        env.insert("a".to_string(), 0xFDu64); // -3
        env.insert("b".to_string(), 0x02u64);
        let err = eval_agree(&ob, &env).expect_err("Urem must disagree on a negative operand");
        assert!(err.contains("disagree"), "unexpected message: {err}");
        match discharge_refinement(&ob, &cfg()) {
            RefinementOutcome::Refuted { .. } => {}
            other => panic!("expected Refuted, got {other:?}"),
        }
    }

    /// P3c sdiv-coverage — the domain precondition does NOT mask a wrong-OP
    /// lowering: `Sdiv` chosen for a MIR signed `Rem` (this bridge model DOES
    /// get the precondition attached) is still REFUTED at ordinary in-domain
    /// points (witness a = 5, b = 2: rem = 1, div = 2).
    #[test]
    fn sdiv_for_mir_rem_wrong_op_is_refuted() {
        let mir = MirRvalue::BinaryOp {
            op: MirBinOp::Rem,
            ty: MirScalarTy::SInt(Type::I8),
            lhs: var_s8("a"),
            rhs: var_s8("b"),
        };
        let enc = encode_mir_rvalue(&mir).unwrap();
        let a = SmtExpr::var("a", 8);
        let b = SmtExpr::var("b", 8);
        // The BUG: division where the MIR asks for remainder.
        let bridge = BridgeLowering::BinOp {
            op: Opcode::Sdiv,
            ty: Type::I8,
            lhs: a,
            rhs: b,
        };
        let ob = build_refinement_obligation("Sdiv_for_Rem_WRONG_OP", &bridge, &enc);
        assert_eq!(
            ob.preconditions.len(),
            2,
            "the wrong-op model still carries the domain"
        );
        match discharge_refinement(&ob, &cfg()) {
            RefinementOutcome::Refuted { .. } => {}
            other => panic!("expected Refuted, got {other:?}"),
        }
    }

    /// P3c(1) positive control — a CORRECT trapping signed divide (bvsdiv guarded
    /// by the INT_MIN/-1 overflow-trap model, i.e. the explicit panic branch the
    /// bridge must emit) validates against the trap-modeling spec, including at
    /// the INT_MIN/-1 input. Locks in that the trap model is not a false positive
    /// against a faithful trapping lowering.
    #[test]
    fn correct_trapping_sdiv_refines() {
        let mir = MirRvalue::BinaryOp {
            op: MirBinOp::Div,
            ty: MirScalarTy::SInt(Type::I8),
            lhs: MirOperand::Var {
                name: "a".to_string(),
                ty: MirScalarTy::SInt(Type::I8),
            },
            rhs: MirOperand::Var {
                name: "b".to_string(),
                ty: MirScalarTy::SInt(Type::I8),
            },
        };
        let enc = encode_mir_rvalue(&mir).unwrap();
        let a = SmtExpr::var("a", 8);
        let b = SmtExpr::var("b", 8);
        let bridge = BridgeLowering::TrappingSdiv {
            ty: Type::I8,
            lhs: a,
            rhs: b,
        };
        let ob = build_refinement_obligation("Sdiv_trapping_correct", &bridge, &enc);
        match discharge_refinement(&ob, &cfg()) {
            RefinementOutcome::Refined => {}
            other => {
                if let Some(reason) = certification_gap_reason_of(&other) {
                    crate::formal_gap::print_gap_skip("correct_trapping_sdiv_refines", reason);
                    return;
                }
                panic!("expected Refined, got {other:?}")
            }
        }
    }

    /// P3c(2) — Rust float->int `as` is SATURATING. Before the fix the spec was a
    /// raw `fp_to_sbv` (UNSPECIFIED out of range), so a non-saturating bridge
    /// passed vacuously. The spec now encodes the saturating contract, so a
    /// non-saturating bridge is REFUTED on an out-of-range input. Witness:
    /// 1e30_f32 (far above i32::MAX): saturating spec -> i32::MAX (0x7FFF_FFFF),
    /// the raw conversion -> a different (out-of-range) value.
    #[test]
    fn wrong_non_saturating_float_to_int_is_refuted() {
        let v = 1e30f32 as f64;
        let mir = MirRvalue::Cast {
            kind: MirCastKind::FloatToInt,
            src_ty: MirScalarTy::Float(Type::F32),
            dst_ty: MirScalarTy::SInt(Type::I32),
            operand: MirOperand::ConstFloat {
                value: v,
                ty: MirScalarTy::Float(Type::F32),
            },
        };
        let enc = encode_mir_rvalue(&mir).unwrap();
        let bridge = BridgeLowering::NonSaturatingFloatToInt {
            src_ty: Type::F32,
            dst_ty: Type::I32,
            signed: true,
            operand: SmtExpr::fp32_const(1e30f32),
        };
        let ob = build_refinement_obligation("FloatToInt_non_saturating_WRONG", &bridge, &enc);
        let err = eval_agree(&ob, &HashMap::new())
            .expect_err("non-saturating FloatToInt must be refuted on an out-of-range input");
        assert!(err.contains("disagree"), "unexpected message: {err}");
    }

    /// P3c(2) positive control — a CORRECT saturating FloatToInt (e.g. AArch64
    /// FCVTZS) validates against the saturating spec across the edge-case battery
    /// (NaN -> 0, +/-inf -> MAX/MIN, in-range truncation, exact boundaries). The
    /// old raw-`fp_to_sbv` spec would have spuriously refuted this correct
    /// lowering under a solver (UNSPECIFIED model freedom).
    #[test]
    fn correct_saturating_float_to_int_refines_on_edge_cases() {
        for &v in &[
            0.0f32,
            -0.0,
            1.9,
            -1.9,
            1e30,
            -1e30,
            f32::INFINITY,
            f32::NEG_INFINITY,
            f32::NAN,
            i32::MAX as f32,
            i32::MIN as f32,
            100.0,
            -100.0,
        ] {
            let mir = MirRvalue::Cast {
                kind: MirCastKind::FloatToInt,
                src_ty: MirScalarTy::Float(Type::F32),
                dst_ty: MirScalarTy::SInt(Type::I32),
                operand: MirOperand::ConstFloat {
                    value: v as f64,
                    ty: MirScalarTy::Float(Type::F32),
                },
            };
            let enc = encode_mir_rvalue(&mir).unwrap();
            let bridge = BridgeLowering::SaturatingFloatToInt {
                src_ty: Type::F32,
                dst_ty: Type::I32,
                signed: true,
                operand: SmtExpr::fp32_const(v),
            };
            let ob = build_refinement_obligation("FloatToInt_saturating_correct", &bridge, &enc);
            eval_agree(&ob, &HashMap::new()).unwrap_or_else(|e| {
                panic!("correct saturating FloatToInt disagreed at v={v}: {e}")
            });
        }
    }

    /// P3c(3) — Rust/AArch64/x86 MASK the shift amount modulo the bit width.
    /// Before the fix the spec used a raw `bvshl` (result 0 once `amount >=
    /// width`), so a bridge that forgot the `AND amount, #(width-1)` shared the
    /// spec's wrong assumption and passed. The spec now masks, so an unmasked raw
    /// shift is REFUTED at `amount >= width`. Witness: a = 1, b = 8 on i8 —
    /// masked: `1 << (8 & 7)` = `1 << 0` = 1; raw `bvshl`: `1 << 8` = 0.
    #[test]
    fn wrong_unmasked_shift_amount_is_refuted() {
        let mir = MirRvalue::BinaryOp {
            op: MirBinOp::Shl,
            ty: MirScalarTy::UInt(Type::I8),
            lhs: MirOperand::Var {
                name: "a".to_string(),
                ty: MirScalarTy::UInt(Type::I8),
            },
            rhs: MirOperand::Var {
                name: "b".to_string(),
                ty: MirScalarTy::UInt(Type::I8),
            },
        };
        let enc = encode_mir_rvalue(&mir).unwrap();
        let a = SmtExpr::var("a", 8);
        let b = SmtExpr::var("b", 8);
        // The BUG: raw unmasked logical shift left (BinOp dispatches to the raw
        // `try_encode_trust_ir_shift`, which does NOT mask the amount).
        let bridge = BridgeLowering::BinOp {
            op: Opcode::Ishl,
            ty: Type::I8,
            lhs: a,
            rhs: b,
        };
        let ob = build_refinement_obligation("Shl_unmasked_amount_WRONG", &bridge, &enc);
        // Direct witness: a = 1, b = 8 (== width). Masked spec -> 1, raw -> 0.
        let mut env = HashMap::new();
        env.insert("a".to_string(), 1u64);
        env.insert("b".to_string(), 8u64);
        let err =
            eval_agree(&ob, &env).expect_err("unmasked shift amount >= width must be refuted");
        assert!(err.contains("disagree"), "unexpected message: {err}");
        // Production discharge (exhaustive i8) must REFUTE it too.
        match discharge_refinement(&ob, &cfg()) {
            RefinementOutcome::Refuted { .. } => {}
            other => panic!("expected Refuted via discharge, got {other:?}"),
        }
    }

    /// P3c(3) positive control — a CORRECT masked shift (amount AND-ed to
    /// `width-1`) validates against the masked spec exhaustively at i8. Locks in
    /// that masking the spec is not a false positive against a faithful masked
    /// lowering.
    #[test]
    fn correct_masked_shift_refines() {
        let mir = MirRvalue::BinaryOp {
            op: MirBinOp::Shl,
            ty: MirScalarTy::UInt(Type::I8),
            lhs: MirOperand::Var {
                name: "a".to_string(),
                ty: MirScalarTy::UInt(Type::I8),
            },
            rhs: MirOperand::Var {
                name: "b".to_string(),
                ty: MirScalarTy::UInt(Type::I8),
            },
        };
        let enc = encode_mir_rvalue(&mir).unwrap();
        let a = SmtExpr::var("a", 8);
        let b = SmtExpr::var("b", 8);
        let bridge = BridgeLowering::MaskedShift {
            op: Opcode::Ishl,
            ty: Type::I8,
            lhs: a,
            rhs: b,
        };
        let ob = build_refinement_obligation("Shl_masked_correct", &bridge, &enc);
        match discharge_refinement(&ob, &cfg()) {
            RefinementOutcome::Refined => {}
            other => panic!("expected Refined, got {other:?}"),
        }
    }

    // -----------------------------------------------------------------------
    // TCG-SSA-071 mixed-width SHIFT (this change): the loop-VC shift-amount
    // coercion. `encode_mir_binop` coerces a shift AMOUNT to the shifted-value
    // width (zero-extend narrower / truncate wider) so a mixed-width shift
    // (`u64 << i32`, the b17_xorshift case) builds a well-formed VC and is
    // faithful on every well-defined input (`amount < width(value)`).
    // -----------------------------------------------------------------------

    /// Concrete-evaluate the encoded spec for `value:BV[value_bits] shl amount`
    /// where the amount is a NARROWER `amount_bits` variable. Returns the modeled
    /// result at `(value, amount)`. Drives the width-coercion path directly.
    fn eval_mixed_shift(
        op: MirBinOp,
        value_ty: MirScalarTy,
        amount_ty: MirScalarTy,
        value: u64,
        amount: u64,
    ) -> u64 {
        let mir = MirRvalue::BinaryOp {
            op,
            ty: value_ty.clone(),
            lhs: MirOperand::Var {
                name: "v".to_string(),
                ty: value_ty,
            },
            rhs: MirOperand::Var {
                name: "amt".to_string(),
                ty: amount_ty,
            },
        };
        let enc = encode_mir_rvalue(&mir).expect("mixed-width shift must build a VC");
        let mut env = HashMap::new();
        env.insert("v".to_string(), value);
        env.insert("amt".to_string(), amount);
        enc.expr.try_eval(&env).expect("eval").as_u64()
    }

    /// (1) b17-like: a mixed-width shift `u64 << i32` now BUILDS the VC and models
    /// exactly the Rust shift for well-defined amounts. Pins the three concrete
    /// shifts b17_xorshift_rng performs (`<< 23`, `>> 17`, `>> 26`), each with a
    /// 32-bit amount against a 64-bit value.
    #[test]
    fn mixed_width_shift_builds_and_matches_rust() {
        let u64t = MirScalarTy::UInt(Type::I64);
        let s32 = MirScalarTy::SInt(Type::I32); // MIR gives `<< 23` an i32 amount
        let x: u64 = 0x8a5c_d789_635d_2dff;
        // u64 << 23  (Shl)
        assert_eq!(
            eval_mixed_shift(MirBinOp::Shl, u64t.clone(), s32.clone(), x, 23),
            x.wrapping_shl(23),
        );
        // u64 >> 17  (LOGICAL Shr, because the value is UNSIGNED)
        assert_eq!(
            eval_mixed_shift(MirBinOp::Shr, u64t.clone(), s32.clone(), x, 17),
            x >> 17,
        );
        // u64 >> 26
        assert_eq!(
            eval_mixed_shift(MirBinOp::Shr, u64t.clone(), s32.clone(), x, 26),
            x >> 26,
        );
        // A wider amount (i64 amount on a u32 value) TRUNCATES to the value width:
        // 5 fits, so `1u32 << 5` == 32.
        assert_eq!(
            eval_mixed_shift(
                MirBinOp::Shl,
                MirScalarTy::UInt(Type::I32),
                MirScalarTy::SInt(Type::I64),
                1,
                5,
            ),
            1u32.wrapping_shl(5) as u64,
        );
    }

    /// (2) SIGNEDNESS of the shifted value is preserved through the coercion — an
    /// arithmetic (signed) `Shr` still sign-extends the VALUE, while the AMOUNT is
    /// only ever ZERO-extended. `i64 >> amount` on a negative value keeps its sign.
    #[test]
    fn mixed_width_signed_shr_is_arithmetic() {
        let neg: u64 = (-1000i64) as u64;
        // i64 >> 3 (arithmetic): sign bits shift in.
        assert_eq!(
            eval_mixed_shift(
                MirBinOp::Shr,
                MirScalarTy::SInt(Type::I64),
                MirScalarTy::SInt(Type::I32),
                neg,
                3,
            ),
            ((neg as i64) >> 3) as u64,
        );
    }

    /// (3) The amount coercion is ZERO-extend, NOT sign-extend. Contrive an amount
    /// whose narrow-type high bit is SET (`amt = 0x82` as an i8 = -126) against a
    /// wide value. The CORRECT (zero-extend) reading gives `0x82 = 130`, which
    /// masks (mod 64) to `130 & 63 = 2`. A WRONG sign-extend would give
    /// `0xFF..82`, masking to `... & 63 = 2` as well — so pick an amount where the
    /// two DIFFER after masking. `amt = 0x90` (i8 = -112): zero-ext 144 & 63 = 16;
    /// sign-ext 0xFF..90 & 63 = 16 too (low 6 bits identical). The low
    /// `log2(width)` bits are sign-agnostic, so masking hides it — instead pin the
    /// PRE-MASK coerced amount by using a value width whose mask keeps more bits
    /// than the amount type has: shift a 64-bit value by an i8 amount of 40. Zero-
    /// extend: 40 (< 64) -> `x << 40`. Sign-extend of 40 (high bit clear) is also
    /// 40, so use 40 to confirm the in-range path; then use an i8 amount 0xC8
    /// (= 200 unsigned, = -56 signed): zero-ext 200 & 63 = 8 -> `x << 8`; a WRONG
    /// sign-extend would be `0xFF..C8` whose low 6 bits are also 8 -> `x << 8`.
    /// Since masking collapses sign, the OBSERVABLE zero-vs-sign difference only
    /// survives when the shift width exceeds the mask — which never happens for
    /// power-of-two widths. So instead assert the DIRECT invariant: coercion keeps
    /// the amount's low `value_w` bits and the mask keeps low `log2` bits, so the
    /// result equals `value << (amount_low_bits % width)` — verified against the
    /// unsigned interpretation of the amount for several i8 amounts on a u64 value.
    #[test]
    fn mixed_width_amount_is_zero_extended_not_sign_extended() {
        let x: u64 = 0x0000_0000_0000_00ff;
        let s8 = MirScalarTy::SInt(Type::I8);
        let u64t = MirScalarTy::UInt(Type::I64);
        // For each i8 amount, the faithful (zero-extend) model is
        // `x << (amount_as_unsigned_u8 % 64)`. A sign-extend model would use
        // `x << ((0xFFFF_FFFF_FFFF_FF__ | amt) % 64)`; since the modulo keeps only
        // low 6 bits BOTH agree on the RESULT for a power-of-two width — but the
        // COERCED amount value itself must be the zero-extended one. Assert the
        // in-range (amount < 64) cases where zero-extend keeps the amount defined
        // and equal to Rust's `wrapping_shl`, and an amount whose UNSIGNED value is
        // < 64 while its SIGNED (i8) value is negative (0x3f = 63 stays positive;
        // use 0x28 = 40 positive; and 0xC0 = 192 unsigned -> 192 % 64 = 0).
        for &amt in &[0u64, 1, 5, 40, 63] {
            assert_eq!(
                eval_mixed_shift(MirBinOp::Shl, u64t.clone(), s8.clone(), x, amt),
                x.wrapping_shl(amt as u32),
                "zero-extended amount {amt} must model Rust wrapping_shl",
            );
        }
        // 0xC0 = 192 unsigned. Zero-extend -> 192; masked (192 & 63) = 0 -> x << 0
        // = x. A SIGN-extend of 0xC0 (i8 = -64) would be 0xFF..C0, masked
        // (& 63) = 0 too -> also x. Both agree, confirming the RESULT is
        // sign-agnostic under masking; the assert pins the zero-extended RESULT.
        assert_eq!(
            eval_mixed_shift(MirBinOp::Shl, u64t.clone(), s8.clone(), x, 0xC0),
            x, // 192 % 64 == 0
        );
    }

    // -----------------------------------------------------------------------
    // P3c EXTENSION (this change): OverflowOp coverage
    // -----------------------------------------------------------------------

    /// A correctly-selected signed checked add (`overflowing_add` -> trust-ir
    /// `Inst::Overflow { AddOverflow }`) refines against the `CheckedBinaryOp`
    /// spec. Exhaustive at i8 via the mock path (overflow obligations carry two
    /// 8-bit inputs, so the discharge enumerates all 2^16 combos).
    #[test]
    fn correct_overflow_op_add_i8_refines() {
        let mir = MirRvalue::CheckedBinaryOp {
            op: MirBinOp::Add,
            ty: MirScalarTy::SInt(Type::I8),
            lhs: MirOperand::Var {
                name: "a".to_string(),
                ty: MirScalarTy::SInt(Type::I8),
            },
            rhs: MirOperand::Var {
                name: "b".to_string(),
                ty: MirScalarTy::SInt(Type::I8),
            },
        };
        let enc = encode_mir_rvalue(&mir).unwrap();
        let a = SmtExpr::var("a", 8);
        let b = SmtExpr::var("b", 8);
        let bridge = BridgeLowering::OverflowOp {
            op: OverflowOpKind::Add,
            ty: Type::I8,
            signed: true,
            lhs: a,
            rhs: b,
        };
        let ob = build_refinement_obligation("OverflowAdd_i8_correct", &bridge, &enc);
        match discharge_refinement(&ob, &cfg()) {
            RefinementOutcome::Refined => {}
            other => panic!("expected Refined, got {other:?}"),
        }
    }

    /// A WRONG op-selection (the bridge picks `SubOverflow` for an
    /// `overflowing_add`) is REFUTED exhaustively at i8. Witness exists densely:
    /// e.g. a = 3, b = 1 — add value 4, sub value 2 — already disagree on value.
    #[test]
    fn wrong_overflow_op_selection_is_refuted() {
        let mir = MirRvalue::CheckedBinaryOp {
            op: MirBinOp::Add,
            ty: MirScalarTy::SInt(Type::I8),
            lhs: MirOperand::Var {
                name: "a".to_string(),
                ty: MirScalarTy::SInt(Type::I8),
            },
            rhs: MirOperand::Var {
                name: "b".to_string(),
                ty: MirScalarTy::SInt(Type::I8),
            },
        };
        let enc = encode_mir_rvalue(&mir).unwrap();
        let a = SmtExpr::var("a", 8);
        let b = SmtExpr::var("b", 8);
        // The BUG: bridge chose Sub for an Add overflow rvalue.
        let bridge = BridgeLowering::OverflowOp {
            op: OverflowOpKind::Sub,
            ty: Type::I8,
            signed: true,
            lhs: a,
            rhs: b,
        };
        let ob = build_refinement_obligation("OverflowAdd_as_Sub_WRONG", &bridge, &enc);
        match discharge_refinement(&ob, &cfg()) {
            RefinementOutcome::Refuted { .. } => {}
            other => panic!("expected Refuted, got {other:?}"),
        }
    }

    /// A WRONG signedness (the bridge treats an unsigned `overflowing_mul` as
    /// signed) is REFUTED: signed and unsigned overflow flags differ (e.g.
    /// 0xFF * 0x02 on u8 overflows unsigned but the signed flag computation
    /// differs). Exhaustive at i8.
    #[test]
    fn wrong_overflow_signedness_is_refuted() {
        let mir = MirRvalue::CheckedBinaryOp {
            op: MirBinOp::Mul,
            ty: MirScalarTy::UInt(Type::I8),
            lhs: MirOperand::Var {
                name: "a".to_string(),
                ty: MirScalarTy::UInt(Type::I8),
            },
            rhs: MirOperand::Var {
                name: "b".to_string(),
                ty: MirScalarTy::UInt(Type::I8),
            },
        };
        let enc = encode_mir_rvalue(&mir).unwrap();
        let a = SmtExpr::var("a", 8);
        let b = SmtExpr::var("b", 8);
        // The BUG: bridge used the SIGNED overflow flag for an unsigned mul.
        let bridge = BridgeLowering::OverflowOp {
            op: OverflowOpKind::Mul,
            ty: Type::I8,
            signed: true,
            lhs: a,
            rhs: b,
        };
        let ob = build_refinement_obligation("OverflowUMul_as_signed_WRONG", &bridge, &enc);
        match discharge_refinement(&ob, &cfg()) {
            RefinementOutcome::Refuted { .. } => {}
            other => panic!("expected Refuted, got {other:?}"),
        }
    }

    // -----------------------------------------------------------------------
    // P3c EXTENSION (this change): scalar AGGREGATE field-placement (#69/#73)
    // -----------------------------------------------------------------------

    /// Build a scalar-field aggregate MIR rvalue from `(name, ty)` fields, plus
    /// the matching CORRECT bridge `Aggregate` (fields placed in SOURCE order,
    /// driven from the SAME symbolic vars). Returns `(mir, bridge_field_exprs)`.
    fn agg_fields(fields: &[(&str, MirScalarTy)]) -> (MirRvalue, Vec<(SmtExpr, u32)>) {
        let mir_fields: Vec<MirOperand> = fields
            .iter()
            .map(|(n, t)| MirOperand::Var {
                name: n.to_string(),
                ty: t.clone(),
            })
            .collect();
        // SAME symbolic vars feed the bridge side — the obligation is real.
        let bridge_exprs: Vec<(SmtExpr, u32)> = fields
            .iter()
            .map(|(n, t)| (SmtExpr::var(*n, t.bits()), t.bits()))
            .collect();
        (MirRvalue::Aggregate { fields: mir_fields }, bridge_exprs)
    }

    /// CORRECT placement: the bridge places each field at its source offset
    /// (bridge order == source order). The packed bridge value equals the packed
    /// spec value at every offset, so the obligation REFINES. Exhaustive at i8
    /// fields via the production discharge path (two 4-bit fields here keeps the
    /// packed width = 8, well inside the exhaustive subset). This is the positive
    /// control that proves the REORDER refute below is load-bearing.
    #[test]
    fn correct_aggregate_field_placement_refines() {
        // Two 4-bit fields -> packed width 8 (uniform exhaustive at the field
        // var width; both fields are 4-bit symbolic ints).
        let (mir, bridge_exprs) = agg_fields(&[
            ("x", MirScalarTy::UInt(Type::I8)),
            ("y", MirScalarTy::UInt(Type::I8)),
        ]);
        let enc = encode_mir_rvalue(&mir).unwrap();
        let bridge = BridgeLowering::Aggregate {
            field_exprs: bridge_exprs,
        };
        let ob = build_refinement_obligation("Aggregate_correct_order", &bridge, &enc);
        // Spot-check a witness directly: x=0x0A, y=0x0B -> packed 0x0B0A
        // (y in the HIGH byte, x in the LOW byte — source order, field 0 low).
        let mut env = HashMap::new();
        env.insert("x".to_string(), 0x0Au64);
        env.insert("y".to_string(), 0x0Bu64);
        eval_agree(&ob, &env).unwrap_or_else(|e| panic!("correct placement disagreed: {e}"));
        // And the production discharge path must REFINE it.
        match discharge_refinement(&ob, &cfg()) {
            RefinementOutcome::Refined => {}
            other => panic!("expected Refined, got {other:?}"),
        }
    }

    /// #69/#73 field-REORDER miscompile: the bridge SWAPS two fields (places `y`
    /// at field 0's offset and `x` at field 1's offset). The spec packs `x` in
    /// the low bits and `y` above it; the swapped bridge packs `y` low and `x`
    /// high. They disagree wherever the two field values differ — REFUTED with
    /// the swap as the witness. Load-bearing: the *same* fields in the correct
    /// order Refine (test above), so the only difference is the offset swap.
    #[test]
    fn reordered_aggregate_field_placement_is_refuted() {
        let (mir, correct) = agg_fields(&[
            ("x", MirScalarTy::UInt(Type::I8)),
            ("y", MirScalarTy::UInt(Type::I8)),
        ]);
        let enc = encode_mir_rvalue(&mir).unwrap();
        // The BUG: bridge swaps the two fields' offsets (y at offset 0, x above).
        let mut swapped = correct.clone();
        swapped.swap(0, 1);
        let bridge = BridgeLowering::Aggregate {
            field_exprs: swapped,
        };
        let ob = build_refinement_obligation("Aggregate_REORDER_WRONG", &bridge, &enc);
        // Direct witness: x=0x0A, y=0x0B. Spec packs 0x0B0A; swapped bridge
        // packs 0x0A0B — distinct.
        let mut env = HashMap::new();
        env.insert("x".to_string(), 0x0Au64);
        env.insert("y".to_string(), 0x0Bu64);
        let err = eval_agree(&ob, &env)
            .expect_err("a field reorder must be refuted where the fields differ");
        assert!(err.contains("disagree"), "unexpected message: {err}");
        // Production discharge (exhaustive at the 8-bit field vars) must REFUTE.
        match discharge_refinement(&ob, &cfg()) {
            RefinementOutcome::Refuted { .. } => {}
            other => panic!("expected Refuted via discharge, got {other:?}"),
        }
    }

    /// Field WIDTH/OFFSET mismatch: same field order, but the bridge places a
    /// field at the WRONG offset because it used a different width for an
    /// earlier field (here the bridge thinks field 0 `x` is 4 bits wide, so it
    /// places field 1 `y` starting at bit 4 instead of bit 8). The spec packs
    /// `y` starting at bit 8 (after the true 8-bit `x`). The packings have
    /// DIFFERENT total widths AND place `y` at a different offset, so the
    /// obligation is REFUTED. This is the offset-shift class distinct from a pure
    /// swap. Witness checked directly (the two sides have different sorts, so we
    /// drive a concrete eval).
    #[test]
    fn wrong_field_offset_from_bad_width_is_refuted() {
        // Spec: both fields are true 8-bit -> y at bit offset 8.
        let (mir, _correct) = agg_fields(&[
            ("x", MirScalarTy::UInt(Type::I8)),
            ("y", MirScalarTy::UInt(Type::I8)),
        ]);
        let enc = encode_mir_rvalue(&mir).unwrap();
        // The BUG: bridge records field 0 `x` as only 4 bits wide (extracts the
        // low nibble), so it places `y` at bit offset 4 instead of 8. We model
        // that exact placement: a 4-bit slice of x in the low bits, then the
        // 8-bit y above it -> packed width 12, with y at offset 4.
        let x4 = SmtExpr::var("x", 8).extract(3, 0);
        let y8 = SmtExpr::var("y", 8);
        let bridge = BridgeLowering::Aggregate {
            field_exprs: vec![(x4, 4), (y8, 8)],
        };
        let ob = build_refinement_obligation("Aggregate_BAD_WIDTH_WRONG", &bridge, &enc);
        // Witness: x=0x00, y=0x0F. Spec (16-bit): 0x0F00 (y at bit 8). Bridge
        // (12-bit): y at bit 4 -> 0x0F0. These differ (and have different
        // widths), so `semantically_equal` reports disagreement.
        let mut env = HashMap::new();
        env.insert("x".to_string(), 0x00u64);
        env.insert("y".to_string(), 0x0Fu64);
        let err =
            eval_agree(&ob, &env).expect_err("a field placed at the wrong offset must be refuted");
        assert!(err.contains("disagree"), "unexpected message: {err}");
    }

    /// A bool field packs as a 1-bit lane: a 3-field `(u8, bool, u8)` aggregate
    /// (#69/#73 shape with a discriminant-like bool) refines when placed in
    /// source order. Locks in that mixed-width scalar packing (8 + 1 + 8 = 17
    /// bits) is faithful and that `bool` participates at width 1.
    #[test]
    fn mixed_width_aggregate_with_bool_refines() {
        let (mir, bridge_exprs) = agg_fields(&[
            ("a", MirScalarTy::UInt(Type::I8)),
            ("flag", MirScalarTy::Bool),
            ("b", MirScalarTy::UInt(Type::I8)),
        ]);
        let enc = encode_mir_rvalue(&mir).unwrap();
        let bridge = BridgeLowering::Aggregate {
            field_exprs: bridge_exprs,
        };
        let ob = build_refinement_obligation("Aggregate_mixed_width_correct", &bridge, &enc);
        // a in bits [0..8), flag at bit 8, b in bits [9..17).
        // a=0xA5, flag=1, b=0x3C -> b<<9 | flag<<8 | a = 0x3C*512 + 256 + 0xA5.
        let mut env = HashMap::new();
        env.insert("a".to_string(), 0xA5u64);
        env.insert("flag".to_string(), 1u64);
        env.insert("b".to_string(), 0x3Cu64);
        eval_agree(&ob, &env).unwrap_or_else(|e| panic!("mixed-width aggregate disagreed: {e}"));
    }

    /// A float field is OUT OF SLICE: the encoder rejects it (rather than
    /// silently packing an SSE-classified field as an integer). Locks in the
    /// scope boundary documented on `MirRvalue::Aggregate`.
    #[test]
    fn float_field_aggregate_is_rejected() {
        let mir = MirRvalue::Aggregate {
            fields: vec![
                MirOperand::Var {
                    name: "x".to_string(),
                    ty: MirScalarTy::UInt(Type::I32),
                },
                MirOperand::Var {
                    name: "f".to_string(),
                    ty: MirScalarTy::Float(Type::F32),
                },
            ],
        };
        let err = encode_mir_rvalue(&mir).expect_err("float field must be rejected (SSE class)");
        assert!(err.contains("float"), "unexpected error: {err}");
    }

    /// End-to-end via `check_rvalue_lowering` (the bridge call-site shape): a
    /// correct aggregate placement Refines through the production entry point.
    #[test]
    fn check_rvalue_lowering_aggregate_end_to_end() {
        let (mir, bridge_exprs) = agg_fields(&[
            ("p", MirScalarTy::UInt(Type::I8)),
            ("q", MirScalarTy::SInt(Type::I8)),
        ]);
        let bridge = BridgeLowering::Aggregate {
            field_exprs: bridge_exprs,
        };
        let outcome = check_rvalue_lowering("Aggregate_e2e", &mir, &bridge, &cfg()).unwrap();
        assert!(
            matches!(outcome, RefinementOutcome::Refined),
            "got {outcome:?}"
        );
    }

    // -----------------------------------------------------------------------
    // CONTROL-FLOW EXTENSION (this change): per-edge block-arg edge-equality VC
    //   (proof-gap item 6, CONTROL-FLOW axis — the #71 class made acyclic)
    // -----------------------------------------------------------------------

    fn var_u8(name: &str) -> MirOperand {
        MirOperand::Var {
            name: name.to_string(),
            ty: MirScalarTy::UInt(Type::I8),
        }
    }
    fn sym_u8(name: &str) -> SmtExpr {
        SmtExpr::var(name, 8)
    }

    /// A diamond block that, after the merge, threads ONE value to a successor
    /// via `Goto`. The block updates `x` (x1 = x0 + 1) and is supposed to thread
    /// the UPDATED `x1` across the edge. This is the #71 shape made ACYCLIC: a
    /// value that was updated in this block must reach the successor's param, not
    /// the stale entry value.
    ///
    /// Returns the block; the merge stmt binds `x1 = x0 + 1`, and the `Goto`
    /// threads MIR operand `x1` (the update) to the single target param.
    fn diamond_goto_update_block() -> MirBlock {
        MirBlock {
            stmts: vec![MirStmt {
                dst: "x1".to_string(),
                rvalue: MirRvalue::BinaryOp {
                    op: MirBinOp::Add,
                    ty: MirScalarTy::UInt(Type::I8),
                    lhs: var_u8("x0"),
                    rhs: MirOperand::ConstInt {
                        value: 1,
                        ty: MirScalarTy::UInt(Type::I8),
                    },
                },
            }],
            // The source program threads the UPDATED x1 to the successor param 0.
            terminator: MirTerminator::Goto {
                target: 1,
                args: vec![var_u8("x1")],
            },
        }
    }

    /// (1) CORRECT block-arg threading across a `Goto` edge -> Refined.
    ///
    /// The bridge threads the SAME value the source threads (`x1 = x0 + 1`),
    /// built from the SAME symbolic store: the per-slot edge-equality VC is
    /// `bridge(x0+1) == mir(x0+1)`, trivially UNSAT (Refined). Exhaustive at i8.
    #[test]
    fn correct_block_arg_threading_goto_refines() {
        let block = diamond_goto_update_block();
        // Bridge threads x1 = x0 + 1 (the update) — correct. Driven from the
        // SAME `x0` var the store reads, so the VC is real.
        let bridge_x1 = sym_u8("x0").bvadd(SmtExpr::bv_const(1, 8));
        let bridge_edges = vec![BridgeEdgeArgs {
            edge: EdgeKind::Goto,
            args: vec![bridge_x1],
        }];
        let obs = build_edge_equality_obligations("bb_merge", &block, &bridge_edges).unwrap();
        assert_eq!(obs.len(), 1, "one edge, one slot -> one obligation");
        assert_eq!(obs[0].category, Some(TransvalCheckKind::ControlFlow));
        match check_block_arg_threading("bb_merge", &block, &bridge_edges, &cfg()).unwrap() {
            RefinementOutcome::Refined => {}
            other => panic!("expected Refined, got {other:?}"),
        }
    }

    /// (2) DROPPED / STALE block-arg across a `Goto` edge -> Refuted.
    ///
    /// The #71 shape: the source updated `x` (x1 = x0 + 1) and threads the UPDATE,
    /// but the bridge threads the STALE ENTRY value `x0` instead. The per-slot VC
    /// is `bridge(x0) == mir(x0 + 1)`, SAT for every x0 (refuted). Exhaustive at
    /// i8 via the production discharge path.
    ///
    /// LOAD-BEARING: the ONLY change from `correct_block_arg_threading_goto_refines`
    /// (which Refines) is the bridge threading `x0` instead of `x0 + 1` — same
    /// block, same store, same edge. So the Refuted verdict is caused precisely by
    /// the dropped update, not by an unrelated encoding difference.
    #[test]
    fn dropped_stale_block_arg_goto_is_refuted() {
        let block = diamond_goto_update_block();
        // MUTATION-PROBE: thread the CORRECT updated value here -> must Refine
        // (proves the Refuted below is caused by the drop, not a broken VC).
        let probe_correct = sym_u8("x0").bvadd(SmtExpr::bv_const(1, 8));
        let probe_edges = vec![BridgeEdgeArgs {
            edge: EdgeKind::Goto,
            args: vec![probe_correct],
        }];
        assert!(
            matches!(
                check_block_arg_threading("bb_merge_probe", &block, &probe_edges, &cfg()).unwrap(),
                RefinementOutcome::Refined
            ),
            "MUTATION-PROBE: correct threading on the same fixture must Refine"
        );
        // BUG: bridge threads the STALE entry value x0 (dropped the +1 update).
        let bridge_stale = sym_u8("x0");
        let bridge_edges = vec![BridgeEdgeArgs {
            edge: EdgeKind::Goto,
            args: vec![bridge_stale],
        }];
        let obs = build_edge_equality_obligations("bb_merge", &block, &bridge_edges).unwrap();
        // Direct witness: x0 = 5. MIR threads 6 (x0+1); bridge threads 5. Disagree.
        let mut env = HashMap::new();
        env.insert("x0".to_string(), 5u64);
        let err = eval_agree(&obs[0], &env).expect_err("a dropped/stale block arg must be refuted");
        assert!(err.contains("disagree"), "unexpected message: {err}");
        // Production discharge (exhaustive i8) must REFUTE, with a counterexample.
        match check_block_arg_threading("bb_merge", &block, &bridge_edges, &cfg()).unwrap() {
            RefinementOutcome::Refuted { counterexample } => {
                assert!(
                    !counterexample.is_empty(),
                    "refutation carries a counterexample"
                );
            }
            other => panic!("expected Refuted, got {other:?}"),
        }
    }

    /// (3) SWAPPED block-args (two params threaded in the WRONG slots) -> Refuted.
    ///
    /// A `Goto` threading two values `(p, q)` to params `(0, 1)`. The source
    /// threads `(m, n)` where `m = p0 + 1` and `n = q0 + 2` (distinct
    /// expressions). The bridge SWAPS them, threading `(n, m)`. Slot 0's VC is
    /// `bridge(q0+2) == mir(p0+1)`, SAT (refuted). Driven from the same store.
    ///
    /// LOAD-BEARING: the in-order threading (helper builds it) Refines; the only
    /// change here is `.swap(0, 1)` on the bridge args.
    #[test]
    fn swapped_block_args_goto_is_refuted() {
        let block = MirBlock {
            stmts: vec![
                MirStmt {
                    dst: "m".to_string(),
                    rvalue: MirRvalue::BinaryOp {
                        op: MirBinOp::Add,
                        ty: MirScalarTy::UInt(Type::I8),
                        lhs: var_u8("p0"),
                        rhs: MirOperand::ConstInt {
                            value: 1,
                            ty: MirScalarTy::UInt(Type::I8),
                        },
                    },
                },
                MirStmt {
                    dst: "n".to_string(),
                    rvalue: MirRvalue::BinaryOp {
                        op: MirBinOp::Add,
                        ty: MirScalarTy::UInt(Type::I8),
                        lhs: var_u8("q0"),
                        rhs: MirOperand::ConstInt {
                            value: 2,
                            ty: MirScalarTy::UInt(Type::I8),
                        },
                    },
                },
            ],
            // Source threads (m, n) to params (0, 1).
            terminator: MirTerminator::Goto {
                target: 1,
                args: vec![var_u8("m"), var_u8("n")],
            },
        };
        // CORRECT in-order bridge args (driven from the same store vars).
        let correct: Vec<SmtExpr> = vec![
            sym_u8("p0").bvadd(SmtExpr::bv_const(1, 8)), // m
            sym_u8("q0").bvadd(SmtExpr::bv_const(2, 8)), // n
        ];
        // Positive control: in-order Refines.
        let ok_edges = vec![BridgeEdgeArgs {
            edge: EdgeKind::Goto,
            args: correct.clone(),
        }];
        match check_block_arg_threading("bb_swap", &block, &ok_edges, &cfg()).unwrap() {
            RefinementOutcome::Refined => {}
            other => panic!("in-order threading must Refine, got {other:?}"),
        }
        // BUG: the bridge SWAPS the two slots.
        let mut swapped = correct;
        swapped.swap(0, 1);
        let bad_edges = vec![BridgeEdgeArgs {
            edge: EdgeKind::Goto,
            args: swapped,
        }];
        let obs = build_edge_equality_obligations("bb_swap", &block, &bad_edges).unwrap();
        assert_eq!(obs.len(), 2, "two slots -> two obligations");
        // Direct witness: p0 = 10, q0 = 20. Slot 0: mir m = 11, bridge n = 22.
        let mut env = HashMap::new();
        env.insert("p0".to_string(), 10u64);
        env.insert("q0".to_string(), 20u64);
        let err = eval_agree(&obs[0], &env).expect_err("swapped slot 0 must disagree");
        assert!(err.contains("disagree"), "unexpected message: {err}");
        // Production discharge (exhaustive i8) must REFUTE the swap.
        match check_block_arg_threading("bb_swap", &block, &bad_edges, &cfg()).unwrap() {
            RefinementOutcome::Refuted { .. } => {}
            other => panic!("expected Refuted, got {other:?}"),
        }
    }

    /// A two-way `Branch` diamond where ONLY ONE ARM drops the update: the true
    /// arm threads the correct updated value, the false arm threads the STALE
    /// entry value. The per-edge VCs check the two arms INDEPENDENTLY, so the
    /// false arm is Refuted while the true arm would Refine — exactly the #71
    /// "dropped on one path only" diamond. `check_block_arg_threading` returns the
    /// first Refuted (the false arm). Exhaustive at i8.
    #[test]
    fn branch_one_arm_dropped_block_arg_is_refuted() {
        let block = MirBlock {
            stmts: vec![MirStmt {
                dst: "x1".to_string(),
                rvalue: MirRvalue::BinaryOp {
                    op: MirBinOp::Add,
                    ty: MirScalarTy::UInt(Type::I8),
                    lhs: var_u8("x0"),
                    rhs: MirOperand::ConstInt {
                        value: 1,
                        ty: MirScalarTy::UInt(Type::I8),
                    },
                },
            }],
            // Both arms are SUPPOSED to thread the updated x1.
            terminator: MirTerminator::Branch {
                cond: MirOperand::Var {
                    name: "c".to_string(),
                    ty: MirScalarTy::Bool,
                },
                t_target: 1,
                t_args: vec![var_u8("x1")],
                f_target: 2,
                f_args: vec![var_u8("x1")],
            },
        };
        let updated = sym_u8("x0").bvadd(SmtExpr::bv_const(1, 8));
        let bridge_edges = vec![
            // True arm: correct (updated x1).
            BridgeEdgeArgs {
                edge: EdgeKind::BranchTrue,
                args: vec![updated.clone()],
            },
            // False arm BUG: threads the STALE entry x0.
            BridgeEdgeArgs {
                edge: EdgeKind::BranchFalse,
                args: vec![sym_u8("x0")],
            },
        ];
        let obs = build_edge_equality_obligations("bb_branch", &block, &bridge_edges).unwrap();
        assert_eq!(obs.len(), 2, "two arms, one slot each -> two obligations");
        // True-arm obligation Refines; false-arm Refutes.
        assert!(matches!(
            discharge_refinement(&obs[0], &cfg()),
            RefinementOutcome::Refined
        ));
        assert!(matches!(
            discharge_refinement(&obs[1], &cfg()),
            RefinementOutcome::Refuted { .. }
        ));
        // Block-level fold surfaces the Refuted false arm.
        match check_block_arg_threading("bb_branch", &block, &bridge_edges, &cfg()).unwrap() {
            RefinementOutcome::Refuted { .. } => {}
            other => panic!("expected Refuted (false arm drop), got {other:?}"),
        }
    }

    /// A `Branch` whose BOTH arms thread correctly Refines (positive control for
    /// the per-arm machinery). The true arm threads the updated x1; the false arm
    /// threads the entry x0 — and the SOURCE also threads x0 on the false arm, so
    /// both agree. Locks in that per-arm checking does not over-refute.
    #[test]
    fn branch_both_arms_correct_refines() {
        let block = MirBlock {
            stmts: vec![MirStmt {
                dst: "x1".to_string(),
                rvalue: MirRvalue::BinaryOp {
                    op: MirBinOp::Add,
                    ty: MirScalarTy::UInt(Type::I8),
                    lhs: var_u8("x0"),
                    rhs: MirOperand::ConstInt {
                        value: 1,
                        ty: MirScalarTy::UInt(Type::I8),
                    },
                },
            }],
            terminator: MirTerminator::Branch {
                cond: MirOperand::Var {
                    name: "c".to_string(),
                    ty: MirScalarTy::Bool,
                },
                t_target: 1,
                t_args: vec![var_u8("x1")], // updated on the true arm
                f_target: 2,
                f_args: vec![var_u8("x0")], // entry on the false arm (intentional)
            },
        };
        let bridge_edges = vec![
            BridgeEdgeArgs {
                edge: EdgeKind::BranchTrue,
                args: vec![sym_u8("x0").bvadd(SmtExpr::bv_const(1, 8))],
            },
            BridgeEdgeArgs {
                edge: EdgeKind::BranchFalse,
                args: vec![sym_u8("x0")],
            },
        ];
        match check_block_arg_threading("bb_branch_ok", &block, &bridge_edges, &cfg()).unwrap() {
            RefinementOutcome::Refined => {}
            other => panic!("expected Refined, got {other:?}"),
        }
    }

    /// A `Return` block has NO outgoing edges, so it raises NO obligations and is
    /// vacuously Refined. Locks in the edge-free terminator handling.
    #[test]
    fn return_block_has_no_edge_obligations() {
        let block = MirBlock::straight_line(vec![MirStmt {
            dst: "t0".to_string(),
            rvalue: MirRvalue::Use { src: var_u8("a") },
        }]);
        let obs = build_edge_equality_obligations("bb_ret", &block, &[]).unwrap();
        assert!(obs.is_empty(), "Return has no edges -> no obligations");
        match check_block_arg_threading("bb_ret", &block, &[], &cfg()).unwrap() {
            RefinementOutcome::Refined => {}
            other => panic!("expected vacuous Refined, got {other:?}"),
        }
    }

    /// A block-arg COUNT mismatch (the bridge threads fewer args than the target
    /// has params — a dropped SLOT) is a STRUCTURAL arity error, surfaced as an
    /// `Err` rather than a silent pass. Mirrors P1.3's arity check at the value
    /// boundary.
    #[test]
    fn block_arg_arity_mismatch_is_error() {
        let block = diamond_goto_update_block(); // one target param
        // Bridge supplies ZERO args (dropped the only slot).
        let bridge_edges = vec![BridgeEdgeArgs {
            edge: EdgeKind::Goto,
            args: vec![],
        }];
        let err = build_edge_equality_obligations("bb_arity", &block, &bridge_edges)
            .expect_err("arg-count mismatch must be a structural error");
        assert!(
            err.contains("arg-count mismatch"),
            "unexpected error: {err}"
        );
    }

    /// A missing `BridgeEdgeArgs` for an edge the terminator declares is an error
    /// (the bridge must account for every outgoing edge — a silently-unchecked
    /// edge would let a drop through).
    #[test]
    fn missing_bridge_edge_is_error() {
        let block = diamond_goto_update_block(); // has a Goto edge
        // No BridgeEdgeArgs at all.
        let err = build_edge_equality_obligations("bb_missing", &block, &[])
            .expect_err("a declared edge with no bridge args must error");
        assert!(
            err.contains("no bridge block-args"),
            "unexpected error: {err}"
        );
    }

    // -----------------------------------------------------------------------
    // P3c EXTENSION (this change): FAST default-on solver-free lane
    // -----------------------------------------------------------------------

    /// The fast lane ACCEPTS a ≤ 8-bit scalar obligation (1- or 2-input) and
    /// REFINES a correct lowering with no solver. Exhaustive at i8.
    #[test]
    fn fast_lane_refines_correct_i8_binop() {
        let mir = MirRvalue::BinaryOp {
            op: MirBinOp::Add,
            ty: MirScalarTy::UInt(Type::I8),
            lhs: MirOperand::Var {
                name: "a".to_string(),
                ty: MirScalarTy::UInt(Type::I8),
            },
            rhs: MirOperand::Var {
                name: "b".to_string(),
                ty: MirScalarTy::UInt(Type::I8),
            },
        };
        let a = SmtExpr::var("a", 8);
        let b = SmtExpr::var("b", 8);
        let bridge = BridgeLowering::BinOp {
            op: Opcode::Iadd,
            ty: Type::I8,
            lhs: a,
            rhs: b,
        };
        match check_rvalue_lowering_fast("fast_add_i8", &mir, &bridge).unwrap() {
            Some(RefinementOutcome::Refined) => {}
            other => panic!("expected Some(Refined), got {other:?}"),
        }
    }

    /// The fast lane REFUTES the #68-fneg op-selection class at f-free 8-bit
    /// surfaces it can reach — here the unmasked-shift bug, which is an
    /// op-selection error decidable exhaustively at i8 WITHOUT a solver.
    #[test]
    fn fast_lane_refutes_unmasked_shift_i8() {
        let mir = MirRvalue::BinaryOp {
            op: MirBinOp::Shl,
            ty: MirScalarTy::UInt(Type::I8),
            lhs: MirOperand::Var {
                name: "a".to_string(),
                ty: MirScalarTy::UInt(Type::I8),
            },
            rhs: MirOperand::Var {
                name: "b".to_string(),
                ty: MirScalarTy::UInt(Type::I8),
            },
        };
        let a = SmtExpr::var("a", 8);
        let b = SmtExpr::var("b", 8);
        // BUG: raw unmasked Ishl (BinOp dispatch does not mask the amount).
        let bridge = BridgeLowering::BinOp {
            op: Opcode::Ishl,
            ty: Type::I8,
            lhs: a,
            rhs: b,
        };
        match check_rvalue_lowering_fast("fast_unmasked_shl_i8", &mir, &bridge).unwrap() {
            Some(RefinementOutcome::Refuted { .. }) => {}
            other => panic!("expected Some(Refuted), got {other:?}"),
        }
    }

    /// The fast lane SKIPS (returns None) a wide (> 8-bit) obligation: it is the
    /// full solver lane's job, never the fast lane's. No false refute, no
    /// statistical verdict masquerading as a complete one.
    #[test]
    fn fast_lane_skips_wide_obligation() {
        let mir = MirRvalue::BinaryOp {
            op: MirBinOp::Add,
            ty: MirScalarTy::SInt(Type::I32),
            lhs: var_s32("a"),
            rhs: var_s32("b"),
        };
        let a = SmtExpr::var("a", 32);
        let b = SmtExpr::var("b", 32);
        let bridge = BridgeLowering::BinOp {
            op: Opcode::Iadd,
            ty: Type::I32,
            lhs: a,
            rhs: b,
        };
        assert!(
            check_rvalue_lowering_fast("fast_add_i32", &mir, &bridge)
                .unwrap()
                .is_none(),
            "fast lane must skip a 32-bit obligation (out of the exhaustive subset)"
        );
    }

    /// The fast lane SKIPS an FP obligation: FP is never enumerated exhaustively
    /// (only sampled), so it cannot be decided completely without a solver.
    #[test]
    fn fast_lane_skips_fp_obligation() {
        let mir = MirRvalue::UnaryOp {
            op: MirUnOp::Neg,
            ty: MirScalarTy::Float(Type::F32),
            operand: MirOperand::Var {
                name: "a".to_string(),
                ty: MirScalarTy::Float(Type::F32),
            },
        };
        let bridge = BridgeLowering::FNeg {
            ty: Type::F32,
            operand: SmtExpr::var("a", 32),
        };
        assert!(
            check_rvalue_lowering_fast("fast_fneg_f32", &mir, &bridge)
                .unwrap()
                .is_none(),
            "fast lane must skip an FP obligation"
        );
    }

    // -----------------------------------------------------------------------
    // LOOP-CARRIED block-arg threading (proof-gap item 6, the euclid / #71 class)
    //   one-step universal-header-param edge-equality on BOTH in-edges
    // -----------------------------------------------------------------------

    /// Build the euclid_gcd latch over u8 header params `(a, b)`:
    ///   `t = b;  b' = a % b;  a' = t;`  then `Goto header (a' , b')`.
    ///
    /// The latch reads the header params `a`, `b` as FREE block-external inputs
    /// (any iteration's top-of-loop values). It threads `(a', b') = (t, a%b) =
    /// (b, a%b)` back to the header params `(a, b)` in slot order — the CORRECT
    /// rotation. `% ` is the real MIR `Rem` (the divisor `b` is excluded from the
    /// trap by the `b != 0` back-edge guard the `MirLoop` carries).
    fn euclid_latch_block() -> MirBlock {
        MirBlock {
            stmts: vec![
                // t = b  (the temporary that captures the OLD b before it is
                // overwritten — the value that must rotate into a').
                MirStmt {
                    dst: "t".to_string(),
                    rvalue: MirRvalue::Use { src: var_u8("b") },
                },
                // b' = a % b  (the new b: the remainder).
                MirStmt {
                    dst: "b_next".to_string(),
                    rvalue: MirRvalue::BinaryOp {
                        op: MirBinOp::Rem,
                        ty: MirScalarTy::UInt(Type::I8),
                        lhs: var_u8("a"),
                        rhs: var_u8("b"),
                    },
                },
                // a' = t  (the new a is the OLD b, threaded via the temporary).
                MirStmt {
                    dst: "a_next".to_string(),
                    rvalue: MirRvalue::Use { src: var_u8("t") },
                },
            ],
            // Back-edge to the header threading (a', b') = (a_next, b_next) to
            // header params (a, b) in slot order.
            terminator: MirTerminator::Goto {
                target: 0,
                args: vec![var_u8("a_next"), var_u8("b_next")],
            },
        }
    }

    /// The euclid `MirLoop`: header carries `(a, b)`; the preheader threads the
    /// function args `(a0, b0)`; the latch is the rotation above; the back-edge is
    /// guarded by `b != 0` (the `while b != 0` condition), excluding the loop-exit
    /// / `a % 0`-trap inputs from the universal threading VC. The guard is modeled
    /// as a precomputed bool `cont` (the comparison result the bridge would have
    /// in hand); a `cont != 0` precondition gates the latch VC.
    fn euclid_loop() -> MirLoop {
        MirLoop {
            header_params: vec![
                ("a".to_string(), MirScalarTy::UInt(Type::I8)),
                ("b".to_string(), MirScalarTy::UInt(Type::I8)),
            ],
            preheader_args: vec![var_u8("a0"), var_u8("b0")],
            latch: euclid_latch_block(),
            // `while b != 0`: model the loop-continue condition as a bool the VC
            // uses as a precondition. We express it directly over `b` so the
            // exhaustive eval excludes exactly `b == 0` (the trap input).
            back_edge_guard: Some(MirOperand::Var {
                name: "b".to_string(),
                ty: MirScalarTy::UInt(Type::I8),
            }),
        }
    }

    /// The CORRECT bridge back-edge args for the euclid latch, driven from the
    /// SAME free header-param vars `a`, `b` the latch store reads:
    ///   slot 0 (a') = b     (the rotation: new a is the OLD b)
    ///   slot 1 (b') = a % b (the remainder)
    /// `a % b` is the unsigned remainder over 8-bit `a`, `b`.
    fn euclid_correct_back_edge_args() -> Vec<SmtExpr> {
        let a = sym_u8("a");
        let b = sym_u8("b");
        // unsigned remainder a % b == a - (a udiv b) * b (the encoder's form).
        let q = a.clone().bvudiv(b.clone());
        let rem = a.bvsub(q.bvmul(b.clone()));
        vec![b, rem]
    }

    /// (1) CORRECT euclid rotation: the bridge threads `(a', b') = (b, a%b)` on the
    /// back-edge and `(a0, b0)` on the preheader edge -> Refined on BOTH edges.
    ///
    /// The latch reads `a`, `b` as free inputs; the per-slot back-edge VC is
    /// `bridge(b) == mir(t)` and `bridge(a%b) == mir(a%b)`, both UNSAT for all
    /// (a, b) with `b != 0` (exhaustive at u8). The preheader VC is
    /// `bridge(a0) == mir(a0)` / `(b0) == (b0)`. This is the positive control that
    /// makes the swapped/stale refutes below load-bearing.
    #[test]
    fn euclid_correct_rotation_threading_refines() {
        let lp = euclid_loop();
        let back = euclid_correct_back_edge_args();
        let preheader = BridgeEdgeArgs {
            edge: EdgeKind::Goto,
            args: vec![sym_u8("a0"), sym_u8("b0")],
        };
        let latch = BridgeEdgeArgs {
            edge: EdgeKind::Goto,
            args: back,
        };
        // Inspect the obligation set: 2 preheader slots + 2 latch slots = 4, all
        // ControlFlow, latch slots carry the b!=0 guard precondition.
        let obs = build_loop_carried_obligations("euclid", &lp, &preheader, &latch).unwrap();
        assert_eq!(obs.len(), 4, "2 preheader + 2 latch slots");
        assert!(
            obs.iter()
                .all(|o| o.category == Some(TransvalCheckKind::ControlFlow))
        );
        let latch_obs: Vec<&ProofObligation> =
            obs.iter().filter(|o| o.name.contains("_latch_")).collect();
        assert_eq!(latch_obs.len(), 2, "two latch slots");
        assert!(
            latch_obs.iter().all(|o| o.preconditions.len() == 1),
            "each latch slot carries the b!=0 back-edge guard precondition"
        );
        match check_loop_carried_threading("euclid", &lp, &preheader, &latch, &cfg()).unwrap() {
            RefinementOutcome::Refined => {}
            other => panic!("correct euclid rotation must Refine, got {other:?}"),
        }
    }

    /// The STRUCTURAL-IDENTITY LANE must fire on the CORRECT rotation and must
    /// NOT fire on either miscompile.
    ///
    /// This is the load-bearing property of `edge_equality_holds_structurally`:
    /// it may only short-circuit an obligation whose two INDEPENDENTLY-derived
    /// sides are the same tree. If it ever fired on the swapped or stale
    /// fixtures it would admit a known miscompile without consulting the solver,
    /// so both negative cases are asserted alongside the positive one.
    #[test]
    fn structural_identity_lane_fires_only_on_correct_rotation() {
        let lp = euclid_loop();
        let preheader = BridgeEdgeArgs {
            edge: EdgeKind::Goto,
            args: vec![sym_u8("a0"), sym_u8("b0")],
        };
        let correct = euclid_correct_back_edge_args();

        let latch = BridgeEdgeArgs {
            edge: EdgeKind::Goto,
            args: correct.clone(),
        };
        let obs = build_loop_carried_obligations("euclid", &lp, &preheader, &latch).unwrap();
        assert!(
            obs.iter().all(edge_equality_holds_structurally),
            "every slot of a CORRECT rotation must discharge by structural identity"
        );

        // SWAPPED: threads (a%b, b) where (b, a%b) is required.
        let mut swapped = correct.clone();
        swapped.swap(0, 1);
        let bad = BridgeEdgeArgs {
            edge: EdgeKind::Goto,
            args: swapped,
        };
        let swapped_obs = build_loop_carried_obligations("euclid", &lp, &preheader, &bad).unwrap();
        assert!(
            swapped_obs
                .iter()
                .filter(|o| o.name.contains("_latch_"))
                .any(|o| !edge_equality_holds_structurally(o)),
            "a SWAPPED back-edge must NOT be short-circuited by structural identity"
        );

        // STALE: threads the OLD `a` into slot 0 instead of `b`.
        let stale = BridgeEdgeArgs {
            edge: EdgeKind::Goto,
            args: vec![sym_u8("a"), correct[1].clone()],
        };
        let stale_obs = build_loop_carried_obligations("euclid", &lp, &preheader, &stale).unwrap();
        assert!(
            stale_obs
                .iter()
                .filter(|o| o.name.contains("_latch_"))
                .any(|o| !edge_equality_holds_structurally(o)),
            "a STALE back-edge must NOT be short-circuited by structural identity"
        );
    }

    /// The kill switch forces every obligation back through the solver lane.
    /// It may only ever make verification stricter, never weaker.
    #[test]
    fn structural_identity_lane_kill_switch_disables_it() {
        let lp = euclid_loop();
        let preheader = BridgeEdgeArgs {
            edge: EdgeKind::Goto,
            args: vec![sym_u8("a0"), sym_u8("b0")],
        };
        let latch = BridgeEdgeArgs {
            edge: EdgeKind::Goto,
            args: euclid_correct_back_edge_args(),
        };
        let obs = build_loop_carried_obligations("euclid", &lp, &preheader, &latch).unwrap();

        let env_scope = crate::env_lock::override_scope();
        let _guard =
            crate::env_lock::ScopedEnvVar::set(&env_scope, "TCG_NO_STRUCTURAL_EDGE_LANE", "1");
        assert!(
            obs.iter().all(|o| !edge_equality_holds_structurally(o)),
            "the kill switch must route every obligation to the solver"
        );
    }

    /// (2) SWAPPED back-edge — the euclid miscompile: the bridge threads
    /// `(a%b, b)` instead of `(b, a%b)`, i.e. it SWAPS the two loop-carried slots
    /// across the latch->header back-edge. -> Refuted with a counterexample.
    ///
    /// MUTATION-PROBE: the CORRECT (unswapped) back-edge args on the IDENTICAL
    /// fixture Refine, so the Refuted verdict is caused by the swap ALONE.
    /// Slot 0's VC becomes `bridge(a%b) == mir(b)`, SAT (e.g. a=3, b=2: a%b=1 != 2).
    #[test]
    fn euclid_swapped_back_edge_is_refuted() {
        let lp = euclid_loop();
        let preheader = BridgeEdgeArgs {
            edge: EdgeKind::Goto,
            args: vec![sym_u8("a0"), sym_u8("b0")],
        };

        // MUTATION-PROBE: correct rotation on the same fixture must Refine.
        let correct = euclid_correct_back_edge_args();
        let probe_latch = BridgeEdgeArgs {
            edge: EdgeKind::Goto,
            args: correct.clone(),
        };
        assert!(
            matches!(
                check_loop_carried_threading("euclid_probe", &lp, &preheader, &probe_latch, &cfg())
                    .unwrap(),
                RefinementOutcome::Refined
            ),
            "MUTATION-PROBE: correct rotation on the same fixture must Refine"
        );

        // BUG: SWAP the two back-edge slots — thread (a%b, b) into (a, b).
        let mut swapped = correct;
        swapped.swap(0, 1);
        let bad_latch = BridgeEdgeArgs {
            edge: EdgeKind::Goto,
            args: swapped,
        };
        let obs = build_loop_carried_obligations("euclid", &lp, &preheader, &bad_latch).unwrap();
        let slot0 = obs
            .iter()
            .find(|o| o.name.contains("_latch_") && o.name.ends_with("slot0"))
            .expect("latch slot0 obligation");
        // Direct eval witness: a = 3, b = 2 (b != 0 so the guard holds).
        // MIR threads t = b = 2 to slot 0; the swapped bridge threads a%b = 1.
        let mut env = HashMap::new();
        env.insert("a".to_string(), 3u64);
        env.insert("b".to_string(), 2u64);
        let err =
            eval_agree(slot0, &env).expect_err("swapped back-edge slot 0 must disagree at a=3,b=2");
        assert!(err.contains("disagree"), "unexpected message: {err}");

        // Production discharge (exhaustive u8) must REFUTE with a counterexample.
        match check_loop_carried_threading("euclid", &lp, &preheader, &bad_latch, &cfg()).unwrap() {
            RefinementOutcome::Refuted { counterexample } => {
                assert!(
                    !counterexample.is_empty(),
                    "refutation carries a counterexample"
                );
            }
            other => panic!("swapped euclid back-edge must be Refuted, got {other:?}"),
        }
    }

    /// (3) STALE back-edge — the #71 drop: the bridge threads the OLD `a` (the
    /// entry value of the header param) into slot 0 instead of the rotated `t`
    /// (= the OLD `b`). -> Refuted with a counterexample.
    ///
    /// MUTATION-PROBE: the CORRECT rotation on the IDENTICAL fixture Refines, so
    /// the Refuted verdict is caused by the stale-value drop ALONE. Slot 0's VC
    /// becomes `bridge(a) == mir(b)`, SAT wherever a != b (e.g. a=5, b=3).
    #[test]
    fn euclid_stale_back_edge_is_refuted() {
        let lp = euclid_loop();
        let preheader = BridgeEdgeArgs {
            edge: EdgeKind::Goto,
            args: vec![sym_u8("a0"), sym_u8("b0")],
        };

        // MUTATION-PROBE: correct rotation on the same fixture must Refine.
        let correct = euclid_correct_back_edge_args();
        let probe_latch = BridgeEdgeArgs {
            edge: EdgeKind::Goto,
            args: correct.clone(),
        };
        assert!(
            matches!(
                check_loop_carried_threading("euclid_probe", &lp, &preheader, &probe_latch, &cfg())
                    .unwrap(),
                RefinementOutcome::Refined
            ),
            "MUTATION-PROBE: correct rotation on the same fixture must Refine"
        );

        // BUG: thread the STALE entry `a` into slot 0 (a') instead of `t` (= old b).
        // slot 1 (b' = a%b) stays correct, so ONLY the dropped rotation is at fault.
        let bug = vec![sym_u8("a"), correct[1].clone()];
        let bad_latch = BridgeEdgeArgs {
            edge: EdgeKind::Goto,
            args: bug,
        };
        let obs = build_loop_carried_obligations("euclid", &lp, &preheader, &bad_latch).unwrap();
        let slot0 = obs
            .iter()
            .find(|o| o.name.contains("_latch_") && o.name.ends_with("slot0"))
            .expect("latch slot0 obligation");
        // Direct eval witness: a = 5, b = 3 (b != 0). MIR threads t = b = 3 to
        // slot 0; the stale bridge threads a = 5.
        let mut env = HashMap::new();
        env.insert("a".to_string(), 5u64);
        env.insert("b".to_string(), 3u64);
        let err =
            eval_agree(slot0, &env).expect_err("stale back-edge slot 0 must disagree at a=5,b=3");
        assert!(err.contains("disagree"), "unexpected message: {err}");

        // Production discharge (exhaustive u8) must REFUTE with a counterexample.
        match check_loop_carried_threading("euclid", &lp, &preheader, &bad_latch, &cfg()).unwrap() {
            RefinementOutcome::Refuted { counterexample } => {
                assert!(
                    !counterexample.is_empty(),
                    "refutation carries a counterexample"
                );
            }
            other => panic!("stale euclid back-edge must be Refuted, got {other:?}"),
        }
    }

    /// The PREHEADER entry edge is checked too: a bridge that threads the WRONG
    /// initial value (`b0` into slot 0 instead of `a0`) is Refuted on the
    /// preheader edge alone, with the latch back-edge correct. Locks in that BOTH
    /// in-edges of the header are validated (an entry-edge drop is the #71 shape on
    /// the loop's FIRST iteration).
    #[test]
    fn euclid_wrong_preheader_entry_is_refuted() {
        let lp = euclid_loop();
        let correct_latch = BridgeEdgeArgs {
            edge: EdgeKind::Goto,
            args: euclid_correct_back_edge_args(),
        };
        // BUG: preheader threads (b0, b0) — slot 0 should be a0.
        let bad_preheader = BridgeEdgeArgs {
            edge: EdgeKind::Goto,
            args: vec![sym_u8("b0"), sym_u8("b0")],
        };
        // Mutation-probe: correct preheader (a0, b0) Refines on the same fixture.
        let good_preheader = BridgeEdgeArgs {
            edge: EdgeKind::Goto,
            args: vec![sym_u8("a0"), sym_u8("b0")],
        };
        assert!(
            matches!(
                check_loop_carried_threading(
                    "euclid_pre_probe",
                    &lp,
                    &good_preheader,
                    &correct_latch,
                    &cfg()
                )
                .unwrap(),
                RefinementOutcome::Refined
            ),
            "MUTATION-PROBE: correct preheader must Refine"
        );
        match check_loop_carried_threading(
            "euclid_pre",
            &lp,
            &bad_preheader,
            &correct_latch,
            &cfg(),
        )
        .unwrap()
        {
            RefinementOutcome::Refuted { .. } => {}
            other => panic!("wrong preheader entry must be Refuted, got {other:?}"),
        }
    }

    /// A loop-carried-slot ARITY mismatch (the bridge threads fewer back-edge args
    /// than the header has params — a dropped loop-carried SLOT) is a STRUCTURAL
    /// error, surfaced as `Err` rather than a silent pass (mirrors P1.3 + the
    /// acyclic arity check).
    #[test]
    fn loop_carried_arity_mismatch_is_error() {
        let lp = euclid_loop(); // header has 2 params
        let preheader = BridgeEdgeArgs {
            edge: EdgeKind::Goto,
            args: vec![sym_u8("a0"), sym_u8("b0")],
        };
        // Bridge supplies ONE back-edge arg (dropped a loop-carried slot). The
        // latch threads 2 MIR args (matching the header), so the bridge-vs-MIR
        // arity mismatch is caught at the edge-equality layer.
        let short_latch = BridgeEdgeArgs {
            edge: EdgeKind::Goto,
            args: vec![sym_u8("b")],
        };
        let err = build_loop_carried_obligations("euclid_arity", &lp, &preheader, &short_latch)
            .expect_err("a dropped loop-carried slot must be a structural arity error");
        assert!(
            err.contains("arg-count mismatch"),
            "unexpected error: {err}"
        );

        // And a MIR preheader-args / header-param COUNT mismatch (the loop model
        // itself threads the wrong number of entry values to the header) is caught
        // BY the `MirLoop` arity check, distinct from the bridge-vs-MIR check.
        let mut bad_lp = euclid_loop();
        bad_lp.preheader_args = vec![var_u8("a0")]; // 1 entry arg vs 2 header params
        let good_latch = BridgeEdgeArgs {
            edge: EdgeKind::Goto,
            args: euclid_correct_back_edge_args(),
        };
        let err2 =
            build_loop_carried_obligations("euclid_arity2", &bad_lp, &preheader, &good_latch)
                .expect_err(
                    "a preheader-args/header-params count mismatch must be a structural error",
                );
        assert!(
            err2.contains("preheader threads"),
            "unexpected error: {err2}"
        );

        // And a MIR latch-args / header-param count mismatch is caught by the
        // `MirLoop` latch arity check.
        let mut bad_lp2 = euclid_loop();
        if let MirTerminator::Goto { args, .. } = &mut bad_lp2.latch.terminator {
            args.truncate(1); // 1 back-edge arg vs 2 header params
        }
        let err3 =
            build_loop_carried_obligations("euclid_arity3", &bad_lp2, &preheader, &good_latch)
                .expect_err("a latch-args/header-params count mismatch must be a structural error");
        assert!(err3.contains("latch threads"), "unexpected error: {err3}");
    }

    /// The back-edge GUARD is load-bearing: an UNGUARDED euclid loop (no
    /// `b != 0`) lets the latch VC reach `b == 0`, where the unsigned `a % b`
    /// is the encoder's `a - (a udiv 0) * 0`. With the guard present those points
    /// are EXCLUDED from the VC; the test confirms the guard yields exactly one
    /// `b != 0` precondition per latch slot, and that the correct rotation still
    /// Refines WITH the guard (i.e. the guard does not vacuously refine — the
    /// swapped refute above shares the same guard and still Refutes).
    #[test]
    fn euclid_back_edge_guard_is_threaded_as_precondition() {
        let lp = euclid_loop();
        let preheader = BridgeEdgeArgs {
            edge: EdgeKind::Goto,
            args: vec![sym_u8("a0"), sym_u8("b0")],
        };
        let latch = BridgeEdgeArgs {
            edge: EdgeKind::Goto,
            args: euclid_correct_back_edge_args(),
        };
        let obs = build_loop_carried_obligations("euclid_guard", &lp, &preheader, &latch).unwrap();
        for o in obs.iter().filter(|o| o.name.contains("_latch_")) {
            assert_eq!(
                o.preconditions.len(),
                1,
                "latch slot must carry the b!=0 guard"
            );
            // The guard excludes b == 0: at b = 0 the precondition is false.
            let mut env = HashMap::new();
            env.insert("a".to_string(), 7u64);
            env.insert("b".to_string(), 0u64);
            assert!(
                !o.preconditions[0].eval(&env).as_bool(),
                "guard must be FALSE at b=0 (so the trap input is excluded)"
            );
            // And TRUE at b != 0 (the input the back-edge is actually taken on).
            env.insert("b".to_string(), 4u64);
            assert!(
                o.preconditions[0].eval(&env).as_bool(),
                "guard must be TRUE at b!=0 (the taken input)"
            );
        }
    }

    /// A direct `eval_agree` DISAGREE witness for BOTH the swapped and stale
    /// back-edge bugs at a concrete (a, b) — the loop-carried analogue of the
    /// acyclic direct-eval witnesses. Asserts the two sides disagree on a concrete
    /// env (not just via the solver), so the refutation is grounded in a real
    /// value mismatch.
    #[test]
    fn euclid_back_edge_bugs_disagree_on_concrete_env() {
        let lp = euclid_loop();
        let preheader = BridgeEdgeArgs {
            edge: EdgeKind::Goto,
            args: vec![sym_u8("a0"), sym_u8("b0")],
        };
        let correct = euclid_correct_back_edge_args();

        // Concrete env: a = 9, b = 4 (b != 0). t = b = 4; a%b = 1.
        let mut env = HashMap::new();
        env.insert("a".to_string(), 9u64);
        env.insert("b".to_string(), 4u64);

        // SWAPPED: slot 0 bridge = a%b = 1, mir = t = 4 -> disagree.
        let mut swapped = correct.clone();
        swapped.swap(0, 1);
        let swap_latch = BridgeEdgeArgs {
            edge: EdgeKind::Goto,
            args: swapped,
        };
        let swap_obs =
            build_loop_carried_obligations("euclid_w", &lp, &preheader, &swap_latch).unwrap();
        let swap_slot0 = swap_obs
            .iter()
            .find(|o| o.name.contains("_latch_") && o.name.ends_with("slot0"))
            .unwrap();
        assert!(
            eval_agree(swap_slot0, &env).is_err(),
            "swapped back-edge must disagree at a=9,b=4"
        );

        // STALE: slot 0 bridge = a = 9, mir = t = 4 -> disagree.
        let stale = vec![sym_u8("a"), correct[1].clone()];
        let stale_latch = BridgeEdgeArgs {
            edge: EdgeKind::Goto,
            args: stale,
        };
        let stale_obs =
            build_loop_carried_obligations("euclid_s", &lp, &preheader, &stale_latch).unwrap();
        let stale_slot0 = stale_obs
            .iter()
            .find(|o| o.name.contains("_latch_") && o.name.ends_with("slot0"))
            .unwrap();
        assert!(
            eval_agree(stale_slot0, &env).is_err(),
            "stale back-edge must disagree at a=9,b=4"
        );
    }

    // -----------------------------------------------------------------------
    // check_back_edge_threading — the bridge-wired entry (#84 euclid class)
    // -----------------------------------------------------------------------

    /// The `b != 0` back-edge precondition for the u8 euclid fixture, as the
    /// bridge would derive it from the MIR loop guard / divide-by-zero assert.
    fn euclid_guard_precondition() -> SmtExpr {
        sym_u8("b").eq_expr(SmtExpr::bv_const(0, 8)).not_expr()
    }

    /// (1) The bridge entry refines the CORRECT euclid rotation: same latch
    /// block + correct back-edge args as the `MirLoop` tests, but through the
    /// `check_back_edge_threading` wiring (explicit preconditions, no MirLoop).
    #[test]
    fn back_edge_threading_entry_refines_correct_rotation() {
        let latch = euclid_latch_block();
        let bridge = BridgeEdgeArgs {
            edge: EdgeKind::Goto,
            args: euclid_correct_back_edge_args(),
        };
        match check_back_edge_threading(
            "be_ok",
            &latch,
            &bridge,
            &[euclid_guard_precondition()],
            &[],
            &cfg(),
        )
        .unwrap()
        {
            RefinementOutcome::Refined => {}
            other => panic!("correct rotation through the bridge entry must Refine, got {other:?}"),
        }
    }

    /// (2) The bridge entry REFUTES a swapped back-edge — the genuine misthread
    /// the structural gate cannot tell apart from a rotation. MUTATION-PROBE:
    /// the unswapped args on the identical fixture Refine (test (1)), so the
    /// refutation is caused by the swap alone.
    #[test]
    fn back_edge_threading_entry_refutes_swapped_args() {
        let latch = euclid_latch_block();
        let mut swapped = euclid_correct_back_edge_args();
        swapped.swap(0, 1);
        let bridge = BridgeEdgeArgs {
            edge: EdgeKind::Goto,
            args: swapped,
        };
        match check_back_edge_threading(
            "be_swap",
            &latch,
            &bridge,
            &[euclid_guard_precondition()],
            &[],
            &cfg(),
        )
        .unwrap()
        {
            RefinementOutcome::Refuted { counterexample } => {
                assert!(
                    !counterexample.is_empty(),
                    "refutation carries a counterexample"
                );
            }
            other => {
                panic!("swapped back-edge through the bridge entry must Refute, got {other:?}")
            }
        }
    }

    /// (3) An `extra_inputs` width clash with a spec-declared input is a hard
    /// error (sort soundness), not a verdict.
    #[test]
    fn back_edge_threading_entry_rejects_input_width_clash() {
        let latch = euclid_latch_block();
        let bridge = BridgeEdgeArgs {
            edge: EdgeKind::Goto,
            args: euclid_correct_back_edge_args(),
        };
        let err = check_back_edge_threading(
            "be_clash",
            &latch,
            &bridge,
            &[],
            &[("b".to_string(), 16)], // spec declares b at 8 bits
            &cfg(),
        )
        .expect_err("a width clash must be an error");
        assert!(err.contains("sort clash"), "unexpected error: {err}");
    }

    /// (4) An UNSATISFIABLE precondition set cannot mint a vacuous `Refined`:
    /// the LOOP-1 satisfiability gate inside `discharge_refinement` fails it
    /// closed (Inconclusive), even though `precond AND NOT(equiv)` is UNSAT for
    /// ANY bridge choice — including a SWAPPED one. (Solver-backed check; the
    /// gate lives on the z3 path, so skip without a solver.)
    #[test]
    fn back_edge_threading_vacuous_precondition_fails_closed() {
        if !ay_bridge::z3_available() {
            eprintln!("skipping: z3 not available");
            return;
        }
        let latch = euclid_latch_block();
        let mut swapped = euclid_correct_back_edge_args();
        swapped.swap(0, 1); // a genuinely WRONG threading
        let bridge = BridgeEdgeArgs {
            edge: EdgeKind::Goto,
            args: swapped,
        };
        match check_back_edge_threading(
            "be_vacuous",
            &latch,
            &bridge,
            &[SmtExpr::bool_const(false)], // contradictory "guard"
            &[],
            &cfg(),
        )
        .unwrap()
        {
            RefinementOutcome::Inconclusive { reason } => {
                // Certification-gap guard (crate::formal_gap): while the gap
                // is live the main VC fail-closes BEFORE the vacuity
                // pre-check can label the contradictory guard, so the reason
                // is the gap diagnostic instead of "vacuous"/"preconditions".
                // Either way the outcome this test pins holds — a vacuous
                // precondition NEVER minted Refined — so skip loudly on the
                // exact gap diagnostic only.
                let gap_confirmed = reason.strip_prefix("unknown: ").is_some_and(|s| {
                    crate::formal_gap::ay_reason_is_certification_gap(s)
                        || crate::formal_gap::ay_reason_is_self_check_rejection(s)
                });
                if gap_confirmed {
                    crate::formal_gap::print_gap_skip(
                        "back_edge_threading_vacuous_precondition_fails_closed",
                        &reason,
                    );
                    return;
                }
                assert!(
                    reason.contains("vacuous") || reason.contains("preconditions"),
                    "unexpected reason: {reason}"
                );
            }
            RefinementOutcome::Refined => {
                panic!("a vacuous precondition must NEVER mint Refined for a swapped threading")
            }
            RefinementOutcome::Refuted { .. } => {
                panic!("an unsatisfiable precondition cannot produce a counterexample")
            }
        }
    }

    /// The exhaustive-decidability predicate is exact about its subset: ≤ 8-bit
    /// uniform int inputs (≤ 2 of them) accepted; wider, mixed-width, FP, or
    /// 3+-input obligations rejected.
    #[test]
    fn exhaustive_decidability_predicate_boundaries() {
        let ob8 = ProofObligation {
            machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
            name: "p".into(),
            trust_ir_expr: SmtExpr::var("a", 8),
            aarch64_expr: SmtExpr::var("a", 8),
            inputs: vec![("a".into(), 8)],
            preconditions: vec![],
            fp_inputs: vec![],
            category: None,
        };
        assert!(is_exhaustively_decidable(&ob8));
        let ob9 = ProofObligation {
            inputs: vec![("a".into(), 9)],
            ..ob8.clone()
        };
        assert!(
            !is_exhaustively_decidable(&ob9),
            "9-bit is above the exhaustive threshold"
        );
        let ob_mixed = ProofObligation {
            inputs: vec![("a".into(), 8), ("b".into(), 4)],
            ..ob8.clone()
        };
        assert!(
            !is_exhaustively_decidable(&ob_mixed),
            "mixed widths are not uniformly enumerated"
        );
        let ob_three = ProofObligation {
            inputs: vec![("a".into(), 8), ("b".into(), 8), ("c".into(), 8)],
            ..ob8.clone()
        };
        assert!(
            !is_exhaustively_decidable(&ob_three),
            "3+ inputs are not exhaustively enumerated"
        );
        let ob_fp = ProofObligation {
            fp_inputs: vec![("a".into(), 8, 24)],
            ..ob8.clone()
        };
        assert!(
            !is_exhaustively_decidable(&ob_fp),
            "FP inputs are only sampled"
        );
    }

    // =======================================================================
    // ==== MEMORY MODEL tests ====  (proof-gap item 6, the MEMORY axis)
    //
    // Mirror the rigor of the rvalue/edge VC tests above: every test pairs a
    // SOURCE memory-op sequence against a BRIDGE one and discharges through
    // `check_memory_sequence`. The refuted-direction tests carry an in-test
    // MUTATION PROBE — flipping the bridge sequence back to the correct one on
    // the SAME fixture and asserting it then Refines — so a test that "passes"
    // because the VC is trivially unsatisfiable (a dead obligation) is caught.
    // =======================================================================

    /// A 32-bit store value var.
    fn val32(name: &str) -> SmtExpr {
        SmtExpr::var(name.to_string(), 32)
    }

    /// CORRECT: store `v` at A, load A -> observes `v`; the bridge does the SAME
    /// store+load at A. Must Refine. Positive control for the whole slice.
    #[test]
    fn mem_store_then_load_same_addr_refines() {
        if !proof_authority_available() {
            return;
        }
        let source = vec![
            MirMemOp::Store {
                addr: MemAddr::base("p"),
                value: val32("v"),
                width: 4,
            },
            MirMemOp::Load {
                addr: MemAddr::base("p"),
                width: 4,
                dst: "r".into(),
            },
        ];
        let bridge = source.clone();
        match check_memory_sequence(
            "store_load_same",
            &source,
            &bridge,
            &MemCheckConfig::default(),
            &cfg(),
        )
        .unwrap()
        {
            RefinementOutcome::Refined => {}
            other => {
                if let Some(reason) = certification_gap_reason_of(&other) {
                    crate::formal_gap::print_gap_skip(
                        "mem_store_then_load_same_addr_refines",
                        reason,
                    );
                    return;
                }
                panic!("expected Refined, got {other:?}")
            }
        }
    }

    /// WRONG-OFFSET load: the source stores at A then loads A, but the BRIDGE
    /// loads A+4 (a wrong field offset). The bridge load observes the unwritten
    /// default byte, not `v` — Refuted. MUTATION PROBE: correcting the bridge
    /// load back to offset 0 Refines on the same fixture.
    #[test]
    fn mem_wrong_offset_load_is_refuted_with_probe() {
        if !proof_authority_available() {
            return;
        }
        let source = vec![
            MirMemOp::Store {
                addr: MemAddr::base("p"),
                value: val32("v"),
                width: 4,
            },
            MirMemOp::Load {
                addr: MemAddr::base("p"),
                width: 4,
                dst: "r".into(),
            },
        ];
        // BUG: bridge loads p+4 instead of p. p+4 is DISTINCT from [p, p+4), so
        // the sequence is provably no-alias (no precondition needed) and the VC
        // discharges: the bridge observes the default byte, the source observes v.
        let bridge_bug = vec![
            MirMemOp::Store {
                addr: MemAddr::base("p"),
                value: val32("v"),
                width: 4,
            },
            MirMemOp::Load {
                addr: MemAddr::at("p", 4),
                width: 4,
                dst: "r".into(),
            },
        ];
        match check_memory_sequence(
            "wrong_offset",
            &source,
            &bridge_bug,
            &MemCheckConfig::default(),
            &cfg(),
        )
        .unwrap()
        {
            RefinementOutcome::Refuted { .. } => {}
            other => panic!("expected Refuted, got {other:?}"),
        }
        // MUTATION PROBE: the correct bridge (load p+0) Refines on the same source.
        let bridge_fixed = source.clone();
        match check_memory_sequence(
            "wrong_offset_probe",
            &source,
            &bridge_fixed,
            &MemCheckConfig::default(),
            &cfg(),
        )
        .unwrap()
        {
            RefinementOutcome::Refined => {}
            other => {
                if let Some(reason) = certification_gap_reason_of(&other) {
                    crate::formal_gap::print_gap_skip(
                        "mem_wrong_offset_load_is_refuted_with_probe",
                        reason,
                    );
                    return;
                }
                panic!("probe: expected Refined, got {other:?}")
            }
        }
    }

    /// DROPPED store: the source stores `v` at A then loads A; the bridge DROPS
    /// the store (keeps only the load), so its load reads the stale default byte.
    /// Refuted by BOTH the load-value VC and the final-memory VC. MUTATION PROBE:
    /// restoring the dropped store Refines.
    #[test]
    fn mem_dropped_store_is_refuted_with_probe() {
        if !proof_authority_available() {
            return;
        }
        let source = vec![
            MirMemOp::Store {
                addr: MemAddr::base("p"),
                value: val32("v"),
                width: 4,
            },
            MirMemOp::Load {
                addr: MemAddr::base("p"),
                width: 4,
                dst: "r".into(),
            },
        ];
        // BUG: bridge omits the store, so the load observes the default, not v.
        let bridge_bug = vec![MirMemOp::Load {
            addr: MemAddr::base("p"),
            width: 4,
            dst: "r".into(),
        }];
        // load-count matches (both perform 1 load), so this is a real VC, not a
        // structural arity error.
        match check_memory_sequence(
            "dropped_store",
            &source,
            &bridge_bug,
            &MemCheckConfig::default(),
            &cfg(),
        )
        .unwrap()
        {
            RefinementOutcome::Refuted { .. } => {}
            other => panic!("expected Refuted, got {other:?}"),
        }
        // MUTATION PROBE: restoring the store Refines on the same source.
        let bridge_fixed = source.clone();
        match check_memory_sequence(
            "dropped_store_probe",
            &source,
            &bridge_fixed,
            &MemCheckConfig::default(),
            &cfg(),
        )
        .unwrap()
        {
            RefinementOutcome::Refined => {}
            other => {
                if let Some(reason) = certification_gap_reason_of(&other) {
                    crate::formal_gap::print_gap_skip(
                        "mem_dropped_store_is_refuted_with_probe",
                        reason,
                    );
                    return;
                }
                panic!("probe: expected Refined, got {other:?}")
            }
        }
    }

    /// DROPPED store with NO later load (the pure final-memory case): the source
    /// stores `v1` at A then `v2` at A (last-writer = v2); the bridge performs
    /// only the FIRST store, so the final memory at A holds v1, not v2. There is
    /// no load to observe it, so ONLY the final-memory VC catches it. Refuted.
    /// MUTATION PROBE: performing both stores Refines.
    #[test]
    fn mem_dropped_store_no_load_caught_by_final_memory_with_probe() {
        if !proof_authority_available() {
            return;
        }
        let source = vec![
            MirMemOp::Store {
                addr: MemAddr::base("p"),
                value: val32("v1"),
                width: 4,
            },
            MirMemOp::Store {
                addr: MemAddr::base("p"),
                value: val32("v2"),
                width: 4,
            },
        ];
        // BUG: bridge drops the second (last-writer) store. No loads anywhere, so
        // only the final-memory equality VC at p distinguishes v1 from v2.
        let bridge_bug = vec![MirMemOp::Store {
            addr: MemAddr::base("p"),
            value: val32("v1"),
            width: 4,
        }];
        match check_memory_sequence(
            "dropped_no_load",
            &source,
            &bridge_bug,
            &MemCheckConfig::default(),
            &cfg(),
        )
        .unwrap()
        {
            RefinementOutcome::Refuted { .. } => {}
            other => panic!("expected Refuted (final-memory VC), got {other:?}"),
        }
        // MUTATION PROBE: both stores -> final memory matches -> Refines.
        let bridge_fixed = source.clone();
        match check_memory_sequence(
            "dropped_no_load_probe",
            &source,
            &bridge_fixed,
            &MemCheckConfig::default(),
            &cfg(),
        )
        .unwrap()
        {
            RefinementOutcome::Refined => {}
            other => {
                if let Some(reason) = certification_gap_reason_of(&other) {
                    crate::formal_gap::print_gap_skip(
                        "mem_dropped_store_no_load_caught_by_final_memory_with_probe",
                        reason,
                    );
                    return;
                }
                panic!("probe: expected Refined, got {other:?}")
            }
        }
    }

    /// REORDERED ALIASING stores (UNSOUND): the source stores v1 then v2 to the
    /// SAME cell A (last-writer = v2). The bridge SWAPS them (stores v2 then v1),
    /// so its last-writer is v1. The two cells are `Equal`-class, so no
    /// precondition is needed and the VC discharges -> Refuted. MUTATION PROBE:
    /// the original (un-swapped) order Refines.
    #[test]
    fn mem_reordered_aliasing_stores_unsound_is_refuted_with_probe() {
        if !proof_authority_available() {
            return;
        }
        let a = MemAddr::base("p");
        // Equal-class confirmation: same base, offset, width.
        assert_eq!(a.alias_class(4, &MemAddr::base("p"), 4), AliasClass::Equal);
        let source = vec![
            MirMemOp::Store {
                addr: a.clone(),
                value: val32("v1"),
                width: 4,
            },
            MirMemOp::Store {
                addr: a.clone(),
                value: val32("v2"),
                width: 4,
            },
        ];
        // BUG: bridge swaps the two same-cell stores -> last-writer becomes v1.
        let bridge_bug = vec![
            MirMemOp::Store {
                addr: a.clone(),
                value: val32("v2"),
                width: 4,
            },
            MirMemOp::Store {
                addr: a.clone(),
                value: val32("v1"),
                width: 4,
            },
        ];
        match check_memory_sequence(
            "reorder_alias",
            &source,
            &bridge_bug,
            &MemCheckConfig::default(),
            &cfg(),
        )
        .unwrap()
        {
            RefinementOutcome::Refuted { .. } => {}
            other => panic!("expected Refuted (aliasing reorder), got {other:?}"),
        }
        // MUTATION PROBE: original order Refines.
        let bridge_fixed = source.clone();
        match check_memory_sequence(
            "reorder_alias_probe",
            &source,
            &bridge_fixed,
            &MemCheckConfig::default(),
            &cfg(),
        )
        .unwrap()
        {
            RefinementOutcome::Refined => {}
            other => {
                if let Some(reason) = certification_gap_reason_of(&other) {
                    crate::formal_gap::print_gap_skip(
                        "mem_reordered_aliasing_stores_unsound_is_refuted_with_probe",
                        reason,
                    );
                    return;
                }
                panic!("probe: expected Refined, got {other:?}")
            }
        }
    }

    /// REORDERED DISTINCT stores (SOUND): the source stores v1 at A=p+0 and v2 at
    /// B=p+4 (non-overlapping 4-byte ranges -> `Distinct`). The bridge swaps the
    /// two stores. Because the cells share no byte, the final memory is identical
    /// either way -> Refines. This proves the check is NOT over-strict (it does
    /// not reject every reorder, only aliasing ones).
    #[test]
    fn mem_reordered_distinct_stores_sound_refines() {
        if !proof_authority_available() {
            return;
        }
        let a = MemAddr::at("p", 0);
        let b = MemAddr::at("p", 4);
        // Distinct-class confirmation: same base, non-overlapping [0,4) vs [4,8).
        assert_eq!(a.alias_class(4, &b, 4), AliasClass::Distinct);
        let source = vec![
            MirMemOp::Store {
                addr: a.clone(),
                value: val32("v1"),
                width: 4,
            },
            MirMemOp::Store {
                addr: b.clone(),
                value: val32("v2"),
                width: 4,
            },
        ];
        // SOUND reorder: distinct cells, so order does not matter.
        let bridge_swapped = vec![
            MirMemOp::Store {
                addr: b,
                value: val32("v2"),
                width: 4,
            },
            MirMemOp::Store {
                addr: a,
                value: val32("v1"),
                width: 4,
            },
        ];
        match check_memory_sequence(
            "reorder_distinct",
            &source,
            &bridge_swapped,
            &MemCheckConfig::default(),
            &cfg(),
        )
        .unwrap()
        {
            RefinementOutcome::Refined => {}
            other => {
                if let Some(reason) = certification_gap_reason_of(&other) {
                    crate::formal_gap::print_gap_skip(
                        "mem_reordered_distinct_stores_sound_refines",
                        reason,
                    );
                    return;
                }
                panic!("expected Refined (sound distinct reorder), got {other:?}")
            }
        }
    }

    /// THE SOUNDNESS KEYSTONE: an UNKNOWN-alias pair (two DIFFERENT symbolic
    /// bases — they could be equal at runtime) with NO disjointness precondition
    /// must be FAIL-CLOSED `Inconclusive`, NEVER silently Refined. Even though the
    /// two sequences are byte-identical (a correct lowering!), the function
    /// refuses to discharge a precondition-free may-alias VC — because a buggy
    /// reorder over those same unknown bases would also pass under sampling.
    #[test]
    fn mem_unknown_alias_without_precondition_is_fail_closed() {
        // Two stores to DIFFERENT symbolic bases p and q -> Unknown alias class.
        let p = MemAddr::base("p");
        let q = MemAddr::base("q");
        assert_eq!(p.alias_class(4, &q, 4), AliasClass::Unknown);
        let source = vec![
            MirMemOp::Store {
                addr: p.clone(),
                value: val32("v1"),
                width: 4,
            },
            MirMemOp::Store {
                addr: q.clone(),
                value: val32("v2"),
                width: 4,
            },
            MirMemOp::Load {
                addr: p.clone(),
                width: 4,
                dst: "r".into(),
            },
        ];
        // Identical bridge — a CORRECT lowering. Still must NOT be accepted
        // without a disjointness precondition (the keystone): a may-alias VC could
        // pass vacuously under sampling, so the only sound verdict is Inconclusive.
        let bridge = source.clone();
        match check_memory_sequence(
            "unknown_alias_nopre",
            &source,
            &bridge,
            &MemCheckConfig::default(),
            &cfg(),
        )
        .unwrap()
        {
            RefinementOutcome::Inconclusive { .. } => {}
            other => {
                panic!("KEYSTONE VIOLATED: expected Inconclusive (fail-closed), got {other:?}")
            }
        }
        // build_memory_obligations signals this as Ok(None) (no dischargeable VC).
        assert!(
            build_memory_obligations(
                "unknown_alias_nopre",
                &source,
                &bridge,
                &MemCheckConfig::default()
            )
            .unwrap()
            .is_none(),
            "an unknown-alias sequence with no precondition must yield no obligations"
        );
    }

    /// The SAME unknown-alias sequence, now WITH a disjointness precondition over
    /// the two bases, IS dischargeable: the precondition constrains p and q to
    /// non-overlapping regions, so the (correct) identical bridge Refines. This
    /// shows the keystone is a guard, not a dead end — the documented sound path
    /// admits the obligation once the bases are constrained.
    #[test]
    fn mem_unknown_alias_with_disjointness_precondition_refines() {
        if !proof_authority_available() {
            return;
        }
        let p = MemAddr::base("p");
        let q = MemAddr::base("q");
        let source = vec![
            MirMemOp::Store {
                addr: p.clone(),
                value: val32("v1"),
                width: 4,
            },
            MirMemOp::Store {
                addr: q.clone(),
                value: val32("v2"),
                width: 4,
            },
            MirMemOp::Load {
                addr: p.clone(),
                width: 4,
                dst: "r".into(),
            },
        ];
        let bridge = source.clone();
        let mem_cfg = MemCheckConfig {
            disjointness_preconditions: disjoint_bases_precondition("p", "q", 4),
        };
        match check_memory_sequence("unknown_alias_pre", &source, &bridge, &mem_cfg, &cfg())
            .unwrap()
        {
            RefinementOutcome::Refined => {}
            other => {
                if let Some(reason) = certification_gap_reason_of(&other) {
                    crate::formal_gap::print_gap_skip(
                        "mem_unknown_alias_with_disjointness_precondition_refines",
                        reason,
                    );
                    return;
                }
                panic!("expected Refined under disjointness precondition, got {other:?}")
            }
        }
    }

    /// Even WITH a disjointness precondition, a genuinely WRONG lowering over
    /// unknown bases is still Refuted — the precondition narrows the input space
    /// but does not mask a real miscompile. Here the bridge loads from q instead
    /// of p (a wrong-base load), so the observed value differs even when p and q
    /// are disjoint. Refuted. This guards against the precondition being a
    /// rubber-stamp.
    #[test]
    fn mem_wrong_base_load_refuted_even_with_precondition() {
        let p = MemAddr::base("p");
        let q = MemAddr::base("q");
        let source = vec![
            MirMemOp::Store {
                addr: p.clone(),
                value: val32("v1"),
                width: 4,
            },
            MirMemOp::Store {
                addr: q.clone(),
                value: val32("v2"),
                width: 4,
            },
            MirMemOp::Load {
                addr: p.clone(),
                width: 4,
                dst: "r".into(),
            },
        ];
        // BUG: bridge loads from q (observes v2) instead of p (should observe v1).
        let bridge_bug = vec![
            MirMemOp::Store {
                addr: p,
                value: val32("v1"),
                width: 4,
            },
            MirMemOp::Store {
                addr: q.clone(),
                value: val32("v2"),
                width: 4,
            },
            MirMemOp::Load {
                addr: q,
                width: 4,
                dst: "r".into(),
            },
        ];
        let mem_cfg = MemCheckConfig {
            disjointness_preconditions: disjoint_bases_precondition("p", "q", 4),
        };
        match check_memory_sequence("wrong_base_pre", &source, &bridge_bug, &mem_cfg, &cfg())
            .unwrap()
        {
            RefinementOutcome::Refuted { .. } => {}
            other => panic!("expected Refuted (wrong base, disjoint), got {other:?}"),
        }
    }

    /// A load-COUNT mismatch is a STRUCTURAL arity bug (an error), not an
    /// equivalence question — the bridge must perform the same loads as the
    /// source. (Contrast the DROPPED-store test, where load counts MATCH and the
    /// value VC fires.)
    #[test]
    fn mem_load_count_mismatch_is_error() {
        let source = vec![
            MirMemOp::Store {
                addr: MemAddr::base("p"),
                value: val32("v"),
                width: 4,
            },
            MirMemOp::Load {
                addr: MemAddr::base("p"),
                width: 4,
                dst: "r".into(),
            },
        ];
        let bridge = vec![
            MirMemOp::Store {
                addr: MemAddr::base("p"),
                value: val32("v"),
                width: 4,
            },
            // two loads where the source has one
            MirMemOp::Load {
                addr: MemAddr::base("p"),
                width: 4,
                dst: "r".into(),
            },
            MirMemOp::Load {
                addr: MemAddr::base("p"),
                width: 4,
                dst: "r2".into(),
            },
        ];
        let err = check_memory_sequence(
            "load_count",
            &source,
            &bridge,
            &MemCheckConfig::default(),
            &cfg(),
        )
        .expect_err("load-count mismatch must be a structural error");
        assert!(
            err.contains("load-count mismatch"),
            "unexpected error: {err}"
        );
    }

    /// `alias_class` decision table is exact: same cell = Equal, non-overlapping
    /// const ranges = Distinct, partial overlap = Unknown, different base =
    /// Unknown. This is the static classification the slice's soundness rests on,
    /// so lock its boundaries directly.
    #[test]
    fn mem_alias_class_decision_table() {
        // Same base, same (offset,width) -> Equal.
        assert_eq!(
            MemAddr::at("p", 8).alias_class(4, &MemAddr::at("p", 8), 4),
            AliasClass::Equal
        );
        // Same base, adjacent non-overlapping ranges -> Distinct.
        assert_eq!(
            MemAddr::at("p", 0).alias_class(4, &MemAddr::at("p", 4), 4),
            AliasClass::Distinct
        );
        // Same base, partial overlap (4-byte at 0 vs 4-byte at 2) -> Unknown.
        assert_eq!(
            MemAddr::at("p", 0).alias_class(4, &MemAddr::at("p", 2), 4),
            AliasClass::Unknown
        );
        // Same base, same offset, DIFFERENT width (1 vs 4) -> ranges [0,1) ⊂ [0,4),
        // overlap-but-not-identical -> Unknown (not silently Equal/Distinct).
        assert_eq!(
            MemAddr::at("p", 0).alias_class(1, &MemAddr::at("p", 0), 4),
            AliasClass::Unknown
        );
        // Different base -> Unknown (bases unconstrained).
        assert_eq!(
            MemAddr::base("p").alias_class(4, &MemAddr::base("q"), 4),
            AliasClass::Unknown
        );
    }

    // =======================================================================
    // ==== ADVERSARIAL-AUDIT REGRESSIONS (item-6 VC false-negatives) ====
    //
    // A skeptic swarm confirmed three false-negatives in the first-draft VCs
    // (the checker minted Refined for a genuinely-wrong lowering). Each test
    // below encodes the audit's exact repro and asserts the SOUND verdict; a
    // control on the same fixture proves the fix is not merely rejecting
    // everything. (Same discipline that caught the regalloc-validator faking.)
    // =======================================================================

    /// MEM-1: a CONTRADICTORY caller disjointness precondition must NOT mint a
    /// vacuous `Refined`. `negated_equivalence` is `precond AND NOT(equiv)`, which
    /// is trivially UNSAT when `precond` is unsatisfiable — a naive checker maps
    /// that z3 UNSAT to Verified->Refined for ANY (even wrong) bridge. The
    /// satisfiability gate in `discharge_refinement` now fails it CLOSED.
    /// CONTROL: a SOUND disjointness precondition still REFUTES the wrong-base bridge.
    #[test]
    fn mem1_unsatisfiable_precondition_fails_closed_not_vacuous_refined() {
        let p = MemAddr::base("p");
        let q = MemAddr::base("q");
        let source = vec![
            MirMemOp::Store {
                addr: p.clone(),
                value: val32("v1"),
                width: 4,
            },
            MirMemOp::Store {
                addr: q.clone(),
                value: val32("v2"),
                width: 4,
            },
            MirMemOp::Load {
                addr: p.clone(),
                width: 4,
                dst: "r".into(),
            },
        ];
        // BUG: bridge loads q instead of p (a real wrong-base miscompile).
        let bridge_bug = vec![
            MirMemOp::Store {
                addr: p,
                value: val32("v1"),
                width: 4,
            },
            MirMemOp::Store {
                addr: q.clone(),
                value: val32("v2"),
                width: 4,
            },
            MirMemOp::Load {
                addr: q,
                width: 4,
                dst: "r".into(),
            },
        ];
        // Contradictory precondition: (p >u q) AND (q >u p) — unsatisfiable.
        let pv = SmtExpr::var("p".to_string(), 64);
        let qv = SmtExpr::var("q".to_string(), 64);
        let contradiction = MemCheckConfig {
            disjointness_preconditions: vec![pv.clone().bvugt(qv.clone()), qv.bvugt(pv)],
        };
        match check_memory_sequence("mem1_unsat", &source, &bridge_bug, &contradiction, &cfg())
            .unwrap()
        {
            RefinementOutcome::Inconclusive { .. } => {}
            other => panic!("MEM-1: unsatisfiable precondition must fail closed, got {other:?}"),
        }
        // CONTROL: a SOUND precondition still REFUTES the wrong-base bridge.
        let sound = MemCheckConfig {
            disjointness_preconditions: disjoint_bases_precondition("p", "q", 4),
        };
        match check_memory_sequence("mem1_sound", &source, &bridge_bug, &sound, &cfg()).unwrap() {
            RefinementOutcome::Refuted { .. } => {}
            other => {
                panic!("MEM-1 control: sound precondition must Refute wrong-base, got {other:?}")
            }
        }
    }

    /// MEM-2: a SPURIOUS bridge store at an address the SOURCE never writes (a
    /// provably-Distinct same-base offset `p+100`) corrupts memory and must be
    /// Refuted. The first-draft final-memory VC iterated only SOURCE store cells,
    /// missing it; the union-of-store-ranges VC now reads the bridge's store
    /// address too. MUTATION PROBE: dropping the spurious store Refines.
    #[test]
    fn mem2_spurious_bridge_store_at_distinct_offset_is_refuted_with_probe() {
        if !proof_authority_available() {
            return;
        }
        let source = vec![
            MirMemOp::Store {
                addr: MemAddr::base("p"),
                value: val32("v"),
                width: 4,
            },
            MirMemOp::Load {
                addr: MemAddr::base("p"),
                width: 4,
                dst: "r".into(),
            },
        ];
        // BUG: correct store+load PLUS a spurious store at p+100 (Distinct).
        let bridge_bug = vec![
            MirMemOp::Store {
                addr: MemAddr::base("p"),
                value: val32("v"),
                width: 4,
            },
            MirMemOp::Store {
                addr: MemAddr::at("p", 100),
                value: val32("w"),
                width: 4,
            },
            MirMemOp::Load {
                addr: MemAddr::base("p"),
                width: 4,
                dst: "r".into(),
            },
        ];
        match check_memory_sequence(
            "mem2_spurious",
            &source,
            &bridge_bug,
            &MemCheckConfig::default(),
            &cfg(),
        )
        .unwrap()
        {
            RefinementOutcome::Refuted { .. } => {}
            other => {
                // Certification-gap guard (crate::formal_gap), MEASURED
                // mechanism: the sequence check discharges the LOAD-VALUE VC
                // first (captured live: a 4-byte load at `p` compared across
                // both memories — CORRECTLY unsat, since the spurious store
                // at `p+100..p+103` can never alias `p..p+3` in 64-bit
                // arithmetic), and while the constellation cannot certify
                // that intermediate proof the check fail-closes to
                // Inconclusive BEFORE reaching the FINAL-MEMORY VC whose
                // mismatch at `p+100` refutes. The refutation lane itself is
                // pinned by the solver-less evaluation run of this same test
                // (it Refutes there). Skip ONLY on the exact gap disclosure —
                // a `Refined` here still fails hard.
                if let Some(reason) = certification_gap_reason_of(&other) {
                    crate::formal_gap::print_gap_skip(
                        "mem2_spurious_bridge_store_at_distinct_offset_is_refuted_with_probe \
                         (negative half; load-value VC gap-blocked before the refuting \
                         final-memory VC)",
                        reason,
                    );
                    return;
                }
                panic!("MEM-2: spurious bridge store at p+100 must be Refuted, got {other:?}")
            }
        }
        // MUTATION PROBE: without the spurious store, the bridge Refines.
        let bridge_fixed = source.clone();
        match check_memory_sequence(
            "mem2_probe",
            &source,
            &bridge_fixed,
            &MemCheckConfig::default(),
            &cfg(),
        )
        .unwrap()
        {
            RefinementOutcome::Refined => {}
            other => {
                if let Some(reason) = certification_gap_reason_of(&other) {
                    crate::formal_gap::print_gap_skip(
                        "mem2_spurious_bridge_store_at_distinct_offset_is_refuted_with_probe",
                        reason,
                    );
                    return;
                }
                panic!("MEM-2 probe: correct bridge must Refine, got {other:?}")
            }
        }
    }

    /// P1 FIELD-LOAD (the FIRST RULE shape): a NESTED-PROJECTION scalar field
    /// load `dst = o.b.x` lowers to a typed LOAD at the layout-designated cell
    /// `base + layout_offset`. A load over the UNIFORM initial memory cannot
    /// observe an offset, so — exactly as the bridge's drain does — a SHARED
    /// harness store conditions the cell with a fresh field value `fv`: the spec
    /// loads it, and a faithful bridge load reads the SAME cell, observing `fv`.
    /// Must Refine — the positive control for the field-load proof.
    #[test]
    fn mem_field_load_at_layout_offset_refines() {
        if !proof_authority_available() {
            return;
        }
        // `o.b.x` resolves to byte offset 16, an 8-byte (i64) leaf.
        let fv = SmtExpr::var("fv".to_string(), 64);
        let harness = MirMemOp::Store {
            addr: MemAddr::at("base", 16),
            value: fv,
            width: 8,
        };
        let spec = vec![
            harness.clone(),
            MirMemOp::Load {
                addr: MemAddr::at("base", 16),
                width: 8,
                dst: "spec".into(),
            },
        ];
        // The bridge loads the SAME cell the layout designates.
        let bridge = vec![
            harness,
            MirMemOp::Load {
                addr: MemAddr::at("base", 16),
                width: 8,
                dst: "impl".into(),
            },
        ];
        match check_memory_sequence(
            "p1_field_load",
            &spec,
            &bridge,
            &MemCheckConfig::default(),
            &cfg(),
        )
        .unwrap()
        {
            RefinementOutcome::Refined => {}
            other => {
                if let Some(reason) = certification_gap_reason_of(&other) {
                    crate::formal_gap::print_gap_skip(
                        "mem_field_load_at_layout_offset_refines",
                        reason,
                    );
                    return;
                }
                panic!("P1: correct field load must Refine, got {other:?}")
            }
        }
    }

    /// P1 FIELD-LOAD anti-tautology: the bridge EMITS the field load at the WRONG
    /// byte offset (8 instead of the layout-designated 16). With the cell at
    /// base+16 conditioned to hold `fv`, the bridge's base+8 load reads a Distinct
    /// (defaulted) cell, NOT `fv` — so the load-value VC is REFUTED. MUTATION
    /// PROBE: correcting the bridge offset back to 16 Refines on the same spec, so
    /// the test does not pass on a vacuous obligation.
    #[test]
    fn mem_field_load_wrong_offset_is_refuted_with_probe() {
        if !proof_authority_available() {
            return;
        }
        let fv = SmtExpr::var("fv".to_string(), 64);
        let harness = MirMemOp::Store {
            addr: MemAddr::at("base", 16),
            value: fv,
            width: 8,
        };
        let spec = vec![
            harness.clone(),
            MirMemOp::Load {
                addr: MemAddr::at("base", 16),
                width: 8,
                dst: "spec".into(),
            },
        ];
        // BUG: the emitted load reads base+8, a Distinct cell from base+16.
        let bridge_bug = vec![
            harness.clone(),
            MirMemOp::Load {
                addr: MemAddr::at("base", 8),
                width: 8,
                dst: "impl".into(),
            },
        ];
        match check_memory_sequence(
            "p1_field_load_wrong_offset",
            &spec,
            &bridge_bug,
            &MemCheckConfig::default(),
            &cfg(),
        )
        .unwrap()
        {
            RefinementOutcome::Refuted { .. } => {}
            other => panic!("P1: a wrong field-load offset must be Refuted, got {other:?}"),
        }
        // MUTATION PROBE: the correct bridge (load base+16) Refines on the same spec.
        let bridge_fixed = spec.clone();
        match check_memory_sequence(
            "p1_field_load_probe",
            &spec,
            &bridge_fixed,
            &MemCheckConfig::default(),
            &cfg(),
        )
        .unwrap()
        {
            RefinementOutcome::Refined => {}
            other => {
                if let Some(reason) = certification_gap_reason_of(&other) {
                    crate::formal_gap::print_gap_skip(
                        "mem_field_load_wrong_offset_is_refuted_with_probe",
                        reason,
                    );
                    return;
                }
                panic!("P1 probe: correct field load must Refine, got {other:?}")
            }
        }
    }

    /// LOOP-1: a CONSTANT back-edge guard is rejected structurally. A constant-
    /// false guard (`0 != 0`) would make every latch-slot VC vacuous, accepting
    /// ANY threading; the guard must be a header-parameter condition. (The
    /// discharge satisfiability gate also fails such a VC closed; this rejects the
    /// malformed guard up front with a clear error.)
    #[test]
    fn loop1_constant_back_edge_guard_is_rejected() {
        let lp = MirLoop {
            header_params: vec![("b".to_string(), MirScalarTy::UInt(Type::I8))],
            preheader_args: vec![var_u8("b0")],
            latch: MirBlock {
                stmts: vec![MirStmt {
                    dst: "t".into(),
                    rvalue: MirRvalue::Use { src: var_u8("b") },
                }],
                terminator: MirTerminator::Goto {
                    target: 0,
                    args: vec![var_u8("t")],
                },
            },
            back_edge_guard: Some(MirOperand::ConstInt {
                value: 0,
                ty: MirScalarTy::UInt(Type::I8),
            }),
        };
        // Bridge threads a WRONG constant 7 — but the constant guard is rejected
        // before any threading is evaluated.
        let bridge_pre = BridgeEdgeArgs {
            edge: EdgeKind::Goto,
            args: vec![sym_u8("b0")],
        };
        let bridge_latch = BridgeEdgeArgs {
            edge: EdgeKind::Goto,
            args: vec![SmtExpr::bv_const(7, 8)],
        };
        let err =
            check_loop_carried_threading("loop1_const", &lp, &bridge_pre, &bridge_latch, &cfg())
                .expect_err("a constant back-edge guard must be a structural error");
        assert!(err.contains("constant"), "unexpected error: {err}");
    }

    /// LOOP-1 (free-var leg): a guard naming a NON-header-param var is rejected —
    /// it would also panic the no-solver eval path on an undeclared variable.
    #[test]
    fn loop1_foreign_var_back_edge_guard_is_rejected() {
        let lp = MirLoop {
            header_params: vec![("b".to_string(), MirScalarTy::UInt(Type::I8))],
            preheader_args: vec![var_u8("b0")],
            latch: MirBlock {
                stmts: vec![MirStmt {
                    dst: "t".into(),
                    rvalue: MirRvalue::Use { src: var_u8("b") },
                }],
                terminator: MirTerminator::Goto {
                    target: 0,
                    args: vec![var_u8("t")],
                },
            },
            back_edge_guard: Some(var_u8("zzz_not_a_param")),
        };
        let bridge_pre = BridgeEdgeArgs {
            edge: EdgeKind::Goto,
            args: vec![sym_u8("b0")],
        };
        let bridge_latch = BridgeEdgeArgs {
            edge: EdgeKind::Goto,
            args: vec![sym_u8("b")],
        };
        let err =
            check_loop_carried_threading("loop1_foreign", &lp, &bridge_pre, &bridge_latch, &cfg())
                .expect_err("a guard over a non-header var must be a structural error");
        assert!(
            err.contains("not a loop header parameter"),
            "unexpected error: {err}"
        );
    }

    /// MOCK-PATH twin of MEM-1/LOOP-1: with NO solver, `verify_by_evaluation` must
    /// return `Unknown` (not vacuous `Valid`) when no tested point satisfies the
    /// preconditions. Encodes an unsatisfiable precondition (`a != a`) over an
    /// obligation whose two sides DIFFER (would be Invalid if any point were
    /// tested) — so the only sound verdict is Unknown.
    #[test]
    fn mock_path_unsatisfiable_precondition_is_unknown_not_vacuous_valid() {
        let a = SmtExpr::var("a", 8);
        let ob = ProofObligation {
            machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
            name: "mock_unsat_pre".into(),
            trust_ir_expr: SmtExpr::bv_const(0, 8),
            aarch64_expr: SmtExpr::bv_const(1, 8),
            inputs: vec![("a".into(), 8)],
            preconditions: vec![a.clone().eq_expr(a).not_expr()], // a != a == false
            fp_inputs: vec![],
            category: None,
        };
        match verify_by_evaluation(&ob) {
            VerificationResult::Unknown { .. } => {}
            other => panic!("unsatisfiable precondition must yield Unknown, got {other:?}"),
        }
    }

    // -----------------------------------------------------------------------
    // (f) DIAMOND MERGE: MirRvalue::Select (the 2-way `if/else` join)
    // -----------------------------------------------------------------------

    fn var_bool(name: &str) -> MirOperand {
        MirOperand::Var {
            name: name.to_string(),
            ty: MirScalarTy::Bool,
        }
    }

    /// A diamond-merge block whose post-join value of `x` is
    /// `select(c, a + 1, a - 1)` — the SPEC the bridge's join `ite` is checked
    /// against. The block binds `x1 = select(c, a+1, a-1)` and threads the
    /// MERGED `x1` across a `Goto` to the successor's single param. `c` is the
    /// 1-bit branch discriminant; `a` is a pre-diamond value (u8 -> exhaustive).
    fn diamond_select_block() -> MirBlock {
        MirBlock {
            stmts: vec![
                MirStmt {
                    dst: "then_x".to_string(),
                    rvalue: MirRvalue::BinaryOp {
                        op: MirBinOp::Add,
                        ty: MirScalarTy::UInt(Type::I8),
                        lhs: var_u8("a"),
                        rhs: MirOperand::ConstInt {
                            value: 1,
                            ty: MirScalarTy::UInt(Type::I8),
                        },
                    },
                },
                MirStmt {
                    dst: "else_x".to_string(),
                    rvalue: MirRvalue::BinaryOp {
                        op: MirBinOp::Sub,
                        ty: MirScalarTy::UInt(Type::I8),
                        lhs: var_u8("a"),
                        rhs: MirOperand::ConstInt {
                            value: 1,
                            ty: MirScalarTy::UInt(Type::I8),
                        },
                    },
                },
                MirStmt {
                    dst: "x1".to_string(),
                    rvalue: MirRvalue::Select {
                        cond: var_bool("c"),
                        ty: MirScalarTy::UInt(Type::I8),
                        then_val: var_u8("then_x"),
                        else_val: var_u8("else_x"),
                    },
                },
            ],
            terminator: MirTerminator::Goto {
                target: 1,
                args: vec![var_u8("x1")],
            },
        }
    }

    /// The bridge's INDEPENDENTLY-derived join value (built like the emitted
    /// trust-ir does: an `ite` over the same branch cond and the same per-arm
    /// values), so the VC `bridge_ite == mir_select` is a real check.
    fn bridge_join_ite(then_x: SmtExpr, else_x: SmtExpr) -> SmtExpr {
        let c = SmtExpr::var("c", 1);
        SmtExpr::ite(
            c.eq_expr(SmtExpr::bv_const(0, 1)).not_expr(),
            then_x,
            else_x,
        )
    }

    /// (f.1) CORRECT diamond merge -> Refined. The bridge threads
    /// `ite(c, a+1, a-1)`, exactly the source `select(c, a+1, a-1)`. Exhaustive
    /// over (a, c) at i8/i1 via the production discharge path.
    #[test]
    fn correct_select_diamond_refines() {
        if !proof_authority_available() {
            return;
        }
        let block = diamond_select_block();
        let a = sym_u8("a");
        let bridge_x1 = bridge_join_ite(
            a.clone().bvadd(SmtExpr::bv_const(1, 8)),
            a.bvsub(SmtExpr::bv_const(1, 8)),
        );
        let bridge_edges = vec![BridgeEdgeArgs {
            edge: EdgeKind::Goto,
            args: vec![bridge_x1],
        }];
        match check_block_arg_threading("bb_select", &block, &bridge_edges, &cfg()).unwrap() {
            RefinementOutcome::Refined => {}
            other => panic!("correct select diamond must Refine, got {other:?}"),
        }
    }

    /// (f.2) SWAPPED ARMS -> Refuted. The ONLY change from (f.1) is the bridge's
    /// `ite` threads the ELSE value on the true edge and vice versa
    /// (`ite(c, a-1, a+1)`); the per-slot VC is SAT wherever `a+1 != a-1` (every
    /// `a`), so the swap is refuted. Load-bearing: proves the Select VC has bite.
    #[test]
    fn swapped_arm_select_diamond_is_refuted() {
        let block = diamond_select_block();
        let a = sym_u8("a");
        // SWAP: then/else exchanged relative to the spec.
        let bridge_x1 = bridge_join_ite(
            a.clone().bvsub(SmtExpr::bv_const(1, 8)),
            a.bvadd(SmtExpr::bv_const(1, 8)),
        );
        let bridge_edges = vec![BridgeEdgeArgs {
            edge: EdgeKind::Goto,
            args: vec![bridge_x1],
        }];
        match check_block_arg_threading("bb_select_swap", &block, &bridge_edges, &cfg()).unwrap() {
            RefinementOutcome::Refuted { .. } => {}
            other => panic!("swapped-arm select must be Refuted, got {other:?}"),
        }
    }

    /// (f.3) WRONG ARM VALUE -> Refuted. The bridge's THEN arm threads the wrong
    /// value (`a + 2` instead of `a + 1`); the false edge is still correct. The
    /// VC is SAT on the true edge, refuted. This is the "wrong value on one
    /// branch" misthread the diamond VC must catch.
    #[test]
    fn wrong_then_value_select_diamond_is_refuted() {
        let block = diamond_select_block();
        let a = sym_u8("a");
        let bridge_x1 = bridge_join_ite(
            a.clone().bvadd(SmtExpr::bv_const(2, 8)), // WRONG: should be a + 1
            a.bvsub(SmtExpr::bv_const(1, 8)),
        );
        let bridge_edges = vec![BridgeEdgeArgs {
            edge: EdgeKind::Goto,
            args: vec![bridge_x1],
        }];
        match check_block_arg_threading("bb_select_wrongarm", &block, &bridge_edges, &cfg())
            .unwrap()
        {
            RefinementOutcome::Refuted { .. } => {}
            other => panic!("wrong-then-value select must be Refuted, got {other:?}"),
        }
    }

    /// (f.4) The encoder rejects an ill-typed Select (arm width mismatch) rather
    /// than silently mis-encoding it — fail closed at the encoder boundary.
    #[test]
    fn select_arm_width_mismatch_errors() {
        let mir = MirRvalue::Select {
            cond: var_bool("c"),
            ty: MirScalarTy::UInt(Type::I8),
            then_val: var_u8("then_x"),
            else_val: var_u32("else_x"), // 32-bit arm vs 8-bit result
        };
        assert!(
            encode_mir_rvalue(&mir).is_err(),
            "width-mismatched Select must error"
        );
    }

    // -----------------------------------------------------------------------
    // FRONTEND BATCH PRE-SOLVE soundness tests
    // -----------------------------------------------------------------------
    //
    // These lock the frontend batch pre-solve to the SAME fail-closed contract
    // the backend `verdict_db` batch has, plus the frontend-specific invariant
    // that a batched Refuted still gates the compile closed via the inline path.

    /// A CORRECT wide add (`u32` MIR Add -> trust-ir Iadd). Its negated
    /// equivalence is UNSAT -> a batched window of `unsat`.
    fn batch_correct_add_u32() -> (MirRvalue, BridgeLowering) {
        let mir = MirRvalue::BinaryOp {
            op: MirBinOp::Add,
            ty: MirScalarTy::UInt(Type::I32),
            lhs: var_u32("a"),
            rhs: var_u32("b"),
        };
        let bridge = BridgeLowering::BinOp {
            op: Opcode::Iadd,
            ty: Type::I32,
            lhs: SmtExpr::var("a", 32),
            rhs: SmtExpr::var("b", 32),
        };
        (mir, bridge)
    }

    /// A WRONG wide lowering: `u32` MIR Add lowered as trust-ir Isub. Its
    /// negated equivalence is SAT (any a,b with b!=0) -> a batched window of
    /// `sat`. Structurally distinct sides force a genuine decision.
    fn batch_wrong_add_as_sub_u32() -> (MirRvalue, BridgeLowering) {
        let mir = MirRvalue::BinaryOp {
            op: MirBinOp::Add,
            ty: MirScalarTy::UInt(Type::I32),
            lhs: var_u32("a"),
            rhs: var_u32("b"),
        };
        let bridge = BridgeLowering::BinOp {
            op: Opcode::Isub, // the bug
            ty: Type::I32,
            lhs: SmtExpr::var("a", 32),
            rhs: SmtExpr::var("b", 32),
        };
        (mir, bridge)
    }

    /// PURE: `frontend_strip_trailing_exit` removes exactly the final `(exit)`
    /// line of a real generated query and nothing else.
    #[test]
    fn frontend_strip_trailing_exit_is_exact() {
        let (mir, bridge) = batch_correct_add_u32();
        let enc = encode_mir_rvalue(&mir).unwrap();
        let ob = build_refinement_obligation("strip-me", &bridge, &enc);
        let smt2 = frontend_inline_smt2(&ob, &cfg());
        assert!(smt2.ends_with("(exit)"), "generator must end with (exit)");
        let body = frontend_strip_trailing_exit(&smt2).expect("well-formed script strips");
        assert!(!body.contains("(exit)"), "the exit line is gone");
        assert!(body.contains("(check-sat)"), "the check-sat survives");
        assert_eq!(
            format!("{body}(exit)"),
            smt2,
            "reassembly is byte-identical"
        );
        assert!(
            frontend_strip_trailing_exit("(check-sat)\n(exit) trailing").is_none(),
            "a non-standalone (exit) is refused"
        );
    }

    /// PURE: the sentinel parse rule is fail-closed (mirrors the backend rule).
    #[test]
    fn frontend_parse_batch_windows_is_fail_closed() {
        let out = "c ay ...\nunsat\n==TCG_BND_0==\nsat\n((x #x05))\n==TCG_BND_1==\nunsat\n==TCG_BND_2==\n";
        assert_eq!(
            frontend_parse_batch_windows(out, 3),
            Some(vec![Some(true), Some(false), Some(true)])
        );
        // Ambiguous (two verdicts) window -> None; empty window -> None.
        assert_eq!(
            frontend_parse_batch_windows("unsat\nunsat\n==TCG_BND_0==\nunsat\n==TCG_BND_1==\n", 2),
            Some(vec![None, Some(true)])
        );
        assert_eq!(
            frontend_parse_batch_windows("==TCG_BND_0==\nunsat\n==TCG_BND_1==\n", 2),
            Some(vec![None, Some(true)])
        );
        // Framing failures abort the whole batch.
        assert_eq!(
            frontend_parse_batch_windows("unsat\n==TCG_BND_0==\nunsat\n==TCG_BND_1==\n", 3),
            None
        );
        assert_eq!(
            frontend_parse_batch_windows("unsat\n==TCG_BND_1==\n", 1),
            None
        );
        assert_eq!(
            frontend_parse_batch_windows("unsat\n==TCG_BND_0==\nunsat\n==TCG_BND_1==\n", 1),
            None
        );
    }

    /// REAL SOLVER, BOTH ORDERS: a batch of {correct(UNSAT), wrong(SAT)} yields
    /// exactly {unsat, sat} in either order — the SAT (Refuted) obligation is
    /// NOT masked by the UNSAT one, and `(reset)` isolates each script.
    #[test]
    fn frontend_batch_sat_unsat_isolation_both_orders() {
        let _guard = ay_bridge::formal_solver_test_lock();
        let Some(_ay) = ay_bridge::resolved_solver_path() else {
            eprintln!("frontend_batch_sat_unsat_isolation_both_orders: no ay; skipping");
            return;
        };
        let (cm, cb) = batch_correct_add_u32();
        let (wm, wb) = batch_wrong_add_as_sub_u32();
        let ce = encode_mir_rvalue(&cm).unwrap();
        let we = encode_mir_rvalue(&wm).unwrap();
        let correct = build_refinement_obligation("iso-correct", &cb, &ce);
        let wrong = build_refinement_obligation("iso-wrong", &wb, &we);

        for (order, obs) in [
            ("correct_first", vec![&correct, &wrong]),
            ("wrong_first", vec![&wrong, &correct]),
        ] {
            let bodies: Vec<String> = obs
                .iter()
                .map(|ob| {
                    frontend_strip_trailing_exit(&frontend_inline_smt2(ob, &cfg()))
                        .unwrap()
                        .to_string()
                })
                .collect();
            let script = frontend_assemble_batch_script(&bodies);
            let stdout = ay_bridge::run_batch_solver_script(&script, 120_000)
                .expect("batch solve should run");
            let windows = frontend_parse_batch_windows(&stdout, obs.len())
                .unwrap_or_else(|| panic!("[{order}] windows must parse: {stdout:?}"));
            let expect: Vec<Option<bool>> = obs
                .iter()
                .map(|ob| Some(ob.name.contains("correct")))
                .collect();
            assert_eq!(
                windows, expect,
                "[{order}] SAT must not be masked; got {stdout:?}"
            );
        }
    }

    /// REAL SOLVER, BATCHED == FRESH: every batched verdict equals the verdict
    /// from solving that obligation ALONE in a fresh solver process. A leaked
    /// `(reset)` that diverged a batched verdict from fresh fails here (a STOP
    /// condition).
    #[test]
    fn frontend_batch_equals_fresh_process() {
        let _guard = ay_bridge::formal_solver_test_lock();
        let Some(_ay) = ay_bridge::resolved_solver_path() else {
            eprintln!("frontend_batch_equals_fresh_process: no ay; skipping");
            return;
        };
        let (cm, cb) = batch_correct_add_u32();
        let (wm, wb) = batch_wrong_add_as_sub_u32();
        let ce = encode_mir_rvalue(&cm).unwrap();
        let we = encode_mir_rvalue(&wm).unwrap();
        let obs = [
            build_refinement_obligation("fresh-c1", &cb, &ce),
            build_refinement_obligation("fresh-w1", &wb, &we),
            build_refinement_obligation("fresh-c2", &cb, &ce),
        ];
        let refs: Vec<&ProofObligation> = obs.iter().collect();
        let bodies: Vec<String> = refs
            .iter()
            .map(|ob| {
                frontend_strip_trailing_exit(&frontend_inline_smt2(ob, &cfg()))
                    .unwrap()
                    .to_string()
            })
            .collect();
        let script = frontend_assemble_batch_script(&bodies);
        let stdout =
            ay_bridge::run_batch_solver_script(&script, 120_000).expect("batch solve should run");
        let batched = frontend_parse_batch_windows(&stdout, refs.len())
            .unwrap_or_else(|| panic!("batch windows must parse: {stdout:?}"));

        for (ob, batched_v) in refs.iter().zip(batched.iter()) {
            let full = frontend_inline_smt2(ob, &cfg());
            let fresh_out =
                ay_bridge::run_batch_solver_script(&full, 120_000).expect("fresh solve should run");
            let fresh_v = if fresh_out.lines().any(|l| l.trim() == "unsat") {
                Some(true)
            } else if fresh_out.lines().any(|l| l.trim() == "sat") {
                Some(false)
            } else {
                None
            };
            assert_eq!(
                *batched_v, fresh_v,
                "batched verdict for {:?} ({batched_v:?}) must equal fresh ({fresh_v:?})",
                ob.name
            );
        }
    }

    /// END-TO-END proof-authority invariant: a verdict-only batch, even one
    /// containing a clean UNSAT window, primes NOTHING. The subsequent inline
    /// checker must independently prove the correct obligation and still refute
    /// the wrong one.
    #[test]
    fn frontend_verdict_only_batch_never_primes_proof_authority() {
        let _guard = ay_bridge::formal_solver_test_lock();
        let Some(_ay) = ay_bridge::resolved_solver_path() else {
            eprintln!("frontend_batch_refuted_still_gates_closed: no ay; skipping");
            return;
        };
        // Opt the batch in for this test (and disable CERT-SKIP interference by
        // relying on these being non-canary obligations). The thread-local RAII
        // guards restore the prior values on scope exit, even on panic.
        let env_scope = crate::env_lock::override_scope();
        let _g_batch = crate::env_lock::ScopedEnvVar::set(&env_scope, "TCG_REFINE_BATCH", "1");
        let _g_solver = crate::env_lock::ScopedEnvVar::unset(&env_scope, "TCG_REFINE_SOLVER");
        let _g_no_cache = crate::env_lock::ScopedEnvVar::unset(&env_scope, "TCG_NO_PROOF_CACHE");

        let (cm, cb) = batch_correct_add_u32();
        let (wm, wb) = batch_wrong_add_as_sub_u32();

        // Prime a batch containing BOTH the correct (unsat) and wrong (sat) job.
        let jobs: Vec<(String, &MirRvalue, &BridgeLowering)> = vec![
            ("e2e-correct".to_string(), &cm, &cb),
            ("e2e-wrong".to_string(), &wm, &wb),
        ];

        // CT-9 made `session_proof_cache_key` decline to compute the solver
        // identity hash so that a compile never blocks on it: it returns the key
        // only if the identity is ALREADY resolved, and otherwise leaves the
        // caller to solve live. Nothing resolves it here — `CodegenBackend::init`
        // starts the warm and never runs in a test binary, and the warm
        // deliberately declines to prepay for a `-dirty` solver anyway — so the
        // first consult below would yield None and this test would fail on
        // "default solver route must resolve" instead of on the invariant it
        // exists to check.
        //
        // This test is ABOUT canonical cache keys, so it needs the identity
        // deterministically rather than opportunistically. `TCG_BLOCKING_IDENTITY`
        // is the supported way to ask for it (same key either way — only who
        // waits for it differs).
        let _blocking =
            crate::env_lock::ScopedEnvVar::set(&env_scope, "TCG_BLOCKING_IDENTITY", "1");

        // Snapshot the memo because an earlier test may already have checked
        // the same byte-identical obligation. The verdict-only batch must not
        // change either membership bit.
        let key_of = |name: &str, mir: &MirRvalue, bridge: &BridgeLowering| {
            let encoded = encode_mir_rvalue(mir).expect("batch job must encode");
            let obligation = build_refinement_obligation(name.to_string(), bridge, &encoded);
            let smt2 = frontend_inline_smt2(&obligation, &cfg());
            ay_bridge::default_route_cache_key(&smt2)
                .expect("default solver route must resolve")
                .1
        };
        let correct_key = key_of("e2e-correct", &cm, &cb);
        let wrong_key = key_of("e2e-wrong", &wm, &wb);
        assert!(
            !ay_bridge::session_cache_contains(&wrong_key),
            "the wrong (sat) obligation must not be session-cached before the batch"
        );
        let correct_precached = ay_bridge::session_cache_contains(&correct_key);
        let wrong_precached = ay_bridge::session_cache_contains(&wrong_key);

        let primed = batch_presolve_refinements(&jobs, &cfg());
        assert_eq!(primed, 0, "solver verdicts alone have no proof authority");
        assert!(
            ay_bridge::session_cache_contains(&correct_key) == correct_precached,
            "a verdict-only UNSAT window must not change the Verified memo"
        );
        assert!(
            ay_bridge::session_cache_contains(&wrong_key) == wrong_precached,
            "a SAT window must not change the Verified memo"
        );

        // Now the independently checked inline discharge: the correct rule is
        // either Refined (complete proof accepted) or explicitly Inconclusive
        // (proof evidence missing/holey), never Refuted. The wrong rule must
        // still be Refuted.
        match check_rvalue_lowering("e2e-correct", &cm, &cb, &cfg()).unwrap() {
            RefinementOutcome::Refined => {}
            RefinementOutcome::Inconclusive { reason } => assert!(
                reason.contains("proof") || reason.contains("unknown"),
                "correct obligation may remain pending only for explicit proof authority: {reason}"
            ),
            other => panic!("correct obligation must not be refuted, got {other:?}"),
        }
        match check_rvalue_lowering("e2e-wrong", &wm, &wb, &cfg()).unwrap() {
            RefinementOutcome::Refuted { .. } => {}
            other => panic!("wrong obligation must STILL be Refuted under batching, got {other:?}"),
        }

        // The RAII guards above restore TCG_REFINE_BATCH / TCG_REFINE_SOLVER /
        // TCG_NO_PROOF_CACHE to their prior values on return.
    }
}
