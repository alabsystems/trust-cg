// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! Make representation-preserving reinterpretation explicit before SSA checks.
//!
//! Copy requires exact operand/result type agreement. A pointer address extracted
//! from a typed reference must instead use PtrToPtr with its original source
//! type. This pass grants no lifetime, allocation, aliasing or access authority.
//! Fat-pointer metadata and function/Rc/handle carriers are outside this repair.

use std::collections::HashMap;
use trust_ir::{BlockId, CastOp, Constant, Function, Inst, InstrNode, Module, Ty, ValueId};

use crate::pointer_casts::can_retype_thin_address;

/// Rewrite every reinterpreting `Copy` into the explicit cast it is, and give
/// every branch argument that carries an address into a block parameter of a
/// different thin-pointer type an explicit `PtrToPtr` on the edge, and one that
/// carries an integer into a parameter of the same width and the other
/// signedness an explicit `Bitcast` ([`edge_reinterpretation`]).
///
/// A block parameter is typed as the local it joins (`&T` for a reference
/// local), while the value a predecessor binds to that local may be a computed
/// address (`Ptr`, an `inttoptr` result). trust-ir requires every branch
/// argument to have exactly its parameter's type, so such an edge is re-typed
/// in the predecessor, just before its terminator. `fresh` allocates the new
/// values from the function's own counter.
///
/// `module`, when given, types every value the listed instructions below do
/// not (a call result, a `GlobalAddr`, an aggregate read, ...) by its declared
/// result type (`InstrNode::result_tys`), so a reinterpreting `Copy` of such a
/// value is made explicit too (WS7.3-pre). A value whose type cannot be read is
/// left as it was.
pub(crate) fn canonicalize_reinterpret_copies(
    func: &mut Function,
    module: Option<&Module>,
    mut fresh: impl FnMut() -> ValueId,
) {
    let val_ty = value_types(func, module);
    for block in &mut func.blocks {
        for node in &mut block.body {
            if let Inst::Copy { ty, operand } = &node.inst {
                let declared = ty.clone();
                let operand = *operand;
                if let Some(op_ty) = val_ty.get(&operand.index()) {
                    if op_ty != &declared
                        && declared.is_integer()
                        && op_ty.is_integer()
                        && declared.bit_width().is_some()
                        && declared.bit_width() == op_ty.bit_width()
                    {
                        node.inst = Inst::Cast {
                            op: CastOp::Bitcast,
                            src_ty: op_ty.clone(),
                            dst_ty: declared,
                            operand,
                        };
                    } else if op_ty != &declared && can_retype_thin_address(op_ty, &declared) {
                        node.inst = Inst::Cast {
                            op: CastOp::PtrToPtr,
                            src_ty: op_ty.clone(),
                            dst_ty: declared,
                            operand,
                        };
                    }
                }
            }
        }
    }
    reinterpret_integer_operands(func, &val_ty, &mut fresh);
    retype_pointer_cast_sources(func, &val_ty, &mut fresh);
    // LD-48's integer edges are re-spelled in the MODULE-level pass only
    // (`abi_edges::legalize_module`, on the module the compiler receives,
    // after every bridge gate): the per-function pass (`module: None`) runs
    // before the lane's own field-store and SSA / loop-completeness gates,
    // which therefore still judge the lane's own spelling. LD-48's stored
    // addresses are re-typed by [`retype_stored_and_selected_values`], which
    // `legalize_module` runs right after this pass, for the same reason.
    let module_level = module.is_some();
    // A reinterpreting `Copy` above now has its declared type as its result's
    // type, which `val_ty` already records; block parameter types are fixed.
    let param_tys: HashMap<BlockId, Vec<Ty>> = func
        .blocks
        .iter()
        .map(|block| {
            (
                block.id,
                block.params.iter().map(|(_, ty)| ty.clone()).collect(),
            )
        })
        .collect();
    for block in &mut func.blocks {
        let Some(terminator) = block.body.last_mut() else {
            continue;
        };
        // A value the terminator itself defines (an `Invoke`'s result) cannot
        // be re-spelled before it; such an edge is left for the validator.
        let own_results = terminator.results.clone();
        let mut retypes: Vec<(ValueId, CastOp, Ty, Ty, ValueId)> = Vec::new();
        for (target, args) in edge_args_mut(&mut terminator.inst) {
            let Some(params) = param_tys.get(&target) else {
                continue;
            };
            for (arg, param_ty) in args.iter_mut().zip(params) {
                let Some(arg_ty) = val_ty.get(&arg.index()) else {
                    continue;
                };
                if arg_ty == param_ty || own_results.contains(arg) {
                    continue;
                }
                let Some(op) = edge_reinterpretation(arg_ty, param_ty, module_level) else {
                    continue;
                };
                let existing = retypes
                    .iter()
                    .find(|(source, _, _, dst_ty, _)| source == arg && dst_ty == param_ty)
                    .map(|(_, _, _, _, result)| *result);
                let result = existing.unwrap_or_else(|| {
                    let result = fresh();
                    retypes.push((*arg, op, arg_ty.clone(), param_ty.clone(), result));
                    result
                });
                *arg = result;
            }
        }
        if retypes.is_empty() {
            continue;
        }
        let terminator = block.body.pop().expect("terminator checked above");
        for (operand, op, src_ty, dst_ty, result) in retypes {
            block.body.push(
                InstrNode::new(Inst::Cast {
                    op,
                    src_ty,
                    dst_ty,
                    operand,
                })
                .with_result(result),
            );
        }
        block.body.push(terminator);
    }
    compare_addresses_as_ptr(func, &mut fresh);
    spell_constants_at_their_types(func, &mut fresh);
}

/// The type of every value `func` defines that the canonicalization reads: a
/// block parameter's declared type, and the result type of the instructions
/// listed below. `module`, when given, types the rest by their declared result
/// types (`InstrNode::result_tys`); a value whose type cannot be read is absent.
fn value_types(func: &Function, module: Option<&Module>) -> HashMap<u32, Ty> {
    let mut val_ty: HashMap<u32, Ty> = HashMap::new();
    for block in &func.blocks {
        for (vid, ty) in &block.params {
            val_ty.insert(vid.index(), ty.clone());
        }
        for node in &block.body {
            let ty = match &node.inst {
                Inst::Copy { ty, .. }
                | Inst::Const { ty, .. }
                | Inst::BinOp { ty, .. }
                | Inst::UnOp { ty, .. }
                | Inst::Load { ty, .. } => Some(ty.clone()),
                // Alloca's result is the opaque address carrier, regardless
                // of the stored element type. A subsequent typed raw-pointer
                // Copy therefore needs the same explicit PtrToPtr repair as
                // a pointer parameter does.
                Inst::Alloca { .. } => Some(Ty::Ptr),
                // A GEP's result is the same opaque address carrier (the
                // wasm32 lowering's in-bounds addresses, `wasm32_inbounds`).
                Inst::GEP { .. } => Some(Ty::Ptr),
                Inst::Cast { dst_ty, .. } => Some(dst_ty.clone()),
                _ => None,
            };
            // Nested rather than a let-chain: this crate is edition 2021,
            // where `&& let` is a parse error. Do not let a clippy
            // `collapsible_if` suggestion re-collapse these.
            // EDITION 2021: this crate is `edition = "2021"`, where clippy's
            // suggested `&& let` chain is a PARSE ERROR. Taking that suggestion
            // once already made this crate unbuildable (4d50932d0, reverted by
            // 39d3cc125). The nesting stays until the crate moves to 2024.
            #[allow(clippy::collapsible_if)]
            if let Some(ty) = ty {
                if let Some(result) = node.results.first() {
                    val_ty.insert(result.index(), ty);
                }
            } else if let Some(module) = module {
                // A self-call's callee is not in the module yet; its results
                // stay untyped here (`result_tys` answers none for it).
                for (result, ty) in node.results.iter().zip(node.result_tys(module)) {
                    val_ty.insert(result.index(), ty);
                }
            }
        }
    }
    val_ty
}

/// Re-type each `Store` value and `Select` arm that has the declared type's
/// representation but another type ([`reinterpret_stored_and_selected_values`]).
///
/// Only [`crate::abi_edges::legalize_module`] runs this, on the merged module
/// and after [`canonicalize_reinterpret_copies`]. It is kept out of the
/// per-function canonicalization on purpose: the bridge's field-store gate
/// (`check_field_store_value_types`, [TCG-FIELD-STORE-TYPE]) runs between the
/// two and must judge each recorded field store's value as the lane lowered
/// it. Re-typed first, a thin pointer of another type or a same-width integer
/// of the other signedness would reach the gate already cast to the field's
/// type and pass it.
pub(crate) fn retype_stored_and_selected_values(
    func: &mut Function,
    module: Option<&Module>,
    mut fresh: impl FnMut() -> ValueId,
) {
    let val_ty = value_types(func, module);
    reinterpret_stored_and_selected_values(func, &val_ty, &mut fresh);
}

/// How a branch argument of type `have` is re-spelled for a block parameter of
/// type `want` (`have != want`), if at all: a thin address re-typed by
/// `PtrToPtr` ([`can_retype_thin_address`]), or an integer of the SAME fixed
/// width and the other signedness re-labelled by `Bitcast` — the same bits, as
/// [`reinterpret_integer_operands`] does for `binop` / `icmp` operands. Both
/// are [`representation_cast_op`], the one rule stores and select arms use
/// too. The second arm is LD-48: the lane carries a `ControlFlow` / `Option`
/// payload lane as its `i64` / `i32` / `i8` word, while the loop-carried
/// accumulator's block parameter has the Rust type (`u64` / `u32` / `u8`), so
/// the lane's back edge was `BranchArgTypeMismatch`, which every ingestion
/// entry refuses since WS7.3; it applies only when `integers` (the
/// module-level pass). Any other pair (a width change, a float, a fat pointer)
/// is left for the validator.
fn edge_reinterpretation(have: &Ty, want: &Ty, integers: bool) -> Option<CastOp> {
    representation_cast_op(have, want).filter(|op| integers || *op == CastOp::PtrToPtr)
}

/// WS7.3-pre: an integer `binop` / `icmp` whose operand is an integer of the
/// SAME width but the other signedness (`icmp ult i64 %u64_len, %i64_bound`,
/// `mul i64 %u64_index, %size` — the lane puns a `usize` onto its `I64` word)
/// takes an explicit same-width `Bitcast` of that operand, exactly as a
/// reinterpreting `Copy` does above: the same bits, compared or combined by
/// the same signedness-carrying opcode. Any other operand mismatch is left for
/// the validator to report.
fn reinterpret_integer_operands(
    func: &mut Function,
    val_ty: &HashMap<u32, Ty>,
    fresh: &mut impl FnMut() -> ValueId,
) {
    let reinterpret = |operand: ValueId, declared: &Ty| -> Option<Ty> {
        let have = val_ty.get(&operand.index())?;
        (have != declared
            && have.is_integer()
            && declared.is_integer()
            && have.bit_width().is_some()
            && have.bit_width() == declared.bit_width())
        .then(|| have.clone())
    };
    for block in &mut func.blocks {
        let body = std::mem::take(&mut block.body);
        let mut out = Vec::with_capacity(body.len());
        for mut node in body {
            if let Inst::BinOp { ty, lhs, rhs, .. } | Inst::ICmp { ty, lhs, rhs, .. } =
                &mut node.inst
            {
                for operand in [&mut *lhs, &mut *rhs] {
                    if let Some(src_ty) = reinterpret(*operand, ty) {
                        let result = fresh();
                        out.push(
                            InstrNode::new(Inst::Cast {
                                op: CastOp::Bitcast,
                                src_ty,
                                dst_ty: ty.clone(),
                                operand: *operand,
                            })
                            .with_result(result),
                        );
                        *operand = result;
                    }
                }
            }
            out.push(node);
        }
        block.body = out;
    }
}

/// The cast that re-spells a value of type `have` as the `declared` type of the
/// same representation, by the two rules this pass applies everywhere: a thin
/// address of another thin-pointer type takes a `PtrToPtr`
/// ([`can_retype_thin_address`]), and an integer of the same width but the
/// other signedness a `Bitcast`. `None` when the types agree, and for anything
/// else (a width change, an address read as an integer, an aggregate), which is
/// left for the validator to report. Branch arguments
/// ([`edge_reinterpretation`]) and stored / selected values
/// ([`representation_retype`]) both decide by this one function.
fn representation_cast_op(have: &Ty, declared: &Ty) -> Option<CastOp> {
    if have == declared {
        return None;
    }
    if can_retype_thin_address(have, declared) {
        return Some(CastOp::PtrToPtr);
    }
    (have.is_integer()
        && declared.is_integer()
        && have.bit_width().is_some()
        && have.bit_width() == declared.bit_width())
    .then_some(CastOp::Bitcast)
}

/// The explicit cast that makes `operand: have` the value of type `declared` it
/// already is ([`representation_cast_op`]); `None` where that gives none.
fn representation_retype(operand: ValueId, have: &Ty, declared: &Ty) -> Option<Inst> {
    Some(Inst::Cast {
        op: representation_cast_op(have, declared)?,
        src_ty: have.clone(),
        dst_ty: declared.clone(),
        operand,
    })
}

/// WS7.3: a `Store` whose value, or a `Select` whose arm, has a type other than
/// the one the instruction declares, where the two are the same representation
/// (trust-ir's `OperandTypeMismatch` "store value type mismatch: expected
/// &mut T, got ptr", "select else type mismatch: expected ptr, got &mut T",
/// "expected i64, got u64"). The lane computes a reference as a plain address
/// (`Ptr`, from its byte-address arithmetic, or the base pointer's own type)
/// and stores or selects it where the Rust type of the place names the
/// reference; it reinterprets a `usize` word as its `I64` lane. The value is
/// re-typed to the declared type by [`representation_retype`] just before the
/// instruction: the same eight (or `width`) bytes are stored, the same register
/// selected (`PtrToPtr` and a same-width `Bitcast` lower to a register move),
/// so nothing a store writes or a select yields changes. A value of any other
/// type (a wider or narrower integer, an address stored as an integer) is left
/// for the validator to report. This is also LD-48's store half, measured on
/// the Linux bridge lane: `store *const i32 %p` of the `ptr` a `Box::new`
/// allocation returned, and `store &mut () %a` of an `alloca`'s `ptr` into a
/// captured-reference slot.
fn reinterpret_stored_and_selected_values(
    func: &mut Function,
    val_ty: &HashMap<u32, Ty>,
    fresh: &mut impl FnMut() -> ValueId,
) {
    for block in &mut func.blocks {
        let body = std::mem::take(&mut block.body);
        let mut out = Vec::with_capacity(body.len());
        for mut node in body {
            let (declared, operands): (Ty, Vec<&mut ValueId>) = match &mut node.inst {
                Inst::Store { ty, value, .. } => (ty.clone(), vec![value]),
                Inst::Select {
                    ty,
                    then_val,
                    else_val,
                    ..
                } => (ty.clone(), vec![then_val, else_val]),
                _ => {
                    out.push(node);
                    continue;
                }
            };
            for operand in operands {
                let Some(inst) = val_ty
                    .get(&operand.index())
                    .and_then(|have| representation_retype(*operand, have, &declared))
                else {
                    continue;
                };
                let result = fresh();
                out.push(InstrNode::new(inst).with_result(result));
                *operand = result;
            }
            out.push(node);
        }
        block.body = out;
    }
}

/// WS7.3-pre: a pointer cast whose operand is a thin pointer of another type
/// than the cast declares (the CGU merge re-binds a call to one unified
/// declaration, so `realloc`'s result is `ptr` where its lowering read the
/// Rust `*mut u8`): a `ptrtoptr` takes the operand's own type as its source,
/// and a `ptrtoint` (whose source is the bare `Ptr` carrier) gets an explicit
/// `PtrToPtr` to `Ptr` first. The same address either way. Any other operand
/// mismatch is left for the validator.
fn retype_pointer_cast_sources(
    func: &mut Function,
    val_ty: &HashMap<u32, Ty>,
    fresh: &mut impl FnMut() -> ValueId,
) {
    for block in &mut func.blocks {
        let body = std::mem::take(&mut block.body);
        let mut out = Vec::with_capacity(body.len());
        for mut node in body {
            if let Inst::Cast {
                op,
                src_ty,
                dst_ty,
                operand,
            } = &mut node.inst
            {
                // Two statements, not nested `if`s: this file also compiles
                // as edition 2021 (this crate), where the let-chain a
                // collapsed `if` needs does not exist.
                let have = val_ty
                    .get(&operand.index())
                    .filter(|have| *have != src_ty && can_retype_thin_address(have, src_ty));
                if let Some(have) = have {
                    match op {
                        CastOp::PtrToPtr if can_retype_thin_address(have, dst_ty) => {
                            *src_ty = have.clone();
                        }
                        CastOp::PtrToInt if *src_ty == Ty::Ptr => {
                            let result = fresh();
                            out.push(
                                InstrNode::new(Inst::Cast {
                                    op: CastOp::PtrToPtr,
                                    src_ty: have.clone(),
                                    dst_ty: Ty::Ptr,
                                    operand: *operand,
                                })
                                .with_result(result),
                            );
                            *operand = result;
                        }
                        _ => {}
                    }
                }
            }
            out.push(node);
        }
        block.body = out;
    }
}

/// The `(signed, bits)` of a fixed-width integer type (`Isize` / `Usize`,
/// whose width is the target's, are not rewritten here).
fn fixed_int_shape(ty: &Ty) -> Option<(bool, u32)> {
    Some(match ty {
        Ty::I8 => (true, 8),
        Ty::I16 => (true, 16),
        Ty::I32 => (true, 32),
        Ty::I64 => (true, 64),
        Ty::U8 => (false, 8),
        Ty::U16 => (false, 16),
        Ty::U32 => (false, 32),
        Ty::U64 => (false, 64),
        _ => return None,
    })
}

/// The same `bits`-wide bit pattern as `value`, spelled in the range of the
/// `signed` / unsigned integer type of that width, when `value` lies in the
/// range of the OTHER signedness of that width; `None` otherwise.
fn same_bits_in_range(value: i128, signed: bool, bits: u32) -> Option<i128> {
    let modulus = 1i128 << bits;
    let signed_min = -(1i128 << (bits - 1));
    let signed_max = (1i128 << (bits - 1)) - 1;
    let unsigned_max = modulus - 1;
    if signed {
        (value > signed_max && value <= unsigned_max).then(|| value - modulus)
    } else {
        (value < 0 && value >= signed_min).then(|| value + modulus)
    }
}

/// WS7.3-pre: spell every function-body constant the lane emits in the form
/// trust-ir admits at its declared type (`ConstTypeMismatch` otherwise). Each
/// rewrite denotes the same bits the adapter materialized before:
///
/// * an integer whose value is outside its fixed-width type's range but inside
///   the other signedness's range of that width (`const i64 10^19`, a `u64`
///   value on the `I64` lane) — the same bit pattern, in range;
/// * `Int(0)` / `Int(1)` at `Bool` — `Bool(false)` / `Bool(true)`;
/// * an integer at a TYPED thin pointer (`const *mut u8 8`, a dangling
///   well-aligned address; `const &() 1`) — the integer at `Ptr`, the one
///   pointer type an integer constant inhabits, then an explicit `PtrToPtr` to
///   the declared type;
/// * the empty aggregate at `Unit` (a zero-sized constant,
///   `ConstValue::ZeroSized`) — `PhantomData`, the constant trust-ir admits at
///   `Unit`. The adapter still refuses `PhantomData` by name, so a function
///   that ever reaches this form is REFUSED rather than compiled from invalid
///   IR (none of the measured corpus does).
///
/// Anything else is left as it was, for the validator to report.
fn spell_constants_at_their_types(func: &mut Function, fresh: &mut impl FnMut() -> ValueId) {
    for block in &mut func.blocks {
        let body = std::mem::take(&mut block.body);
        let mut out = Vec::with_capacity(body.len());
        for mut node in body {
            if let Inst::Const { ty, value } = &node.inst {
                let (ty, value) = (ty.clone(), value.clone());
                match (&ty, &value) {
                    (Ty::Bool, Constant::Int(bit @ (0 | 1))) => {
                        node.inst = Inst::Const {
                            ty: ty.clone(),
                            value: Constant::Bool(*bit == 1),
                        };
                    }
                    (_, Constant::Int(integer)) => {
                        if let Some((signed, bits)) = fixed_int_shape(&ty) {
                            if let Some(wrapped) = same_bits_in_range(*integer, signed, bits) {
                                node.inst = Inst::Const {
                                    ty: ty.clone(),
                                    value: Constant::Int(wrapped),
                                };
                            }
                        } else if ty != Ty::Ptr && can_retype_thin_address(&Ty::Ptr, &ty) {
                            let address = fresh();
                            out.push(
                                InstrNode::new(Inst::Const {
                                    ty: Ty::Ptr,
                                    value: Constant::Int(*integer),
                                })
                                .with_result(address),
                            );
                            node.inst = Inst::Cast {
                                op: CastOp::PtrToPtr,
                                src_ty: Ty::Ptr,
                                dst_ty: ty.clone(),
                                operand: address,
                            };
                        }
                    }
                    (Ty::Unit, Constant::Aggregate(fields)) if fields.is_empty() => {
                        node.inst = Inst::Const {
                            ty: ty.clone(),
                            value: Constant::PhantomData,
                        };
                    }
                    _ => {}
                }
            }
            out.push(node);
        }
        block.body = out;
    }
}

/// WS7.3-pre: an `icmp` at a TYPED thin pointer (`icmp eq *mut T %a, %b`, the
/// lowering of a Rust raw-pointer / reference comparison) compares two
/// addresses, but trust-ir admits `icmp` only at integer types and the bare
/// `Ptr` carrier (`ICmpRequiresIntegerOrPtr`). Each operand is re-typed to
/// `Ptr` by an explicit `PtrToPtr` from the comparison's declared type, and the
/// comparison is made at `Ptr`: the same two addresses, compared the same way
/// (the adapter lowers `PtrToPtr` to a register move). An operand whose own type
/// is not the declared one is not hidden: the `PtrToPtr`'s operand check
/// reports it exactly as the `icmp` did.
fn compare_addresses_as_ptr(func: &mut Function, fresh: &mut impl FnMut() -> ValueId) {
    for block in &mut func.blocks {
        if !block.body.iter().any(|node| {
            matches!(&node.inst, Inst::ICmp { ty, .. } if *ty != Ty::Ptr && can_retype_thin_address(ty, &Ty::Ptr))
        }) {
            continue;
        }
        let body = std::mem::take(&mut block.body);
        let mut out = Vec::with_capacity(body.len() + 2);
        for mut node in body {
            if let Inst::ICmp { ty, lhs, rhs, .. } = &mut node.inst {
                // Two statements, as in `retype_pointer_cast_sources`: no
                // let-chain in this crate's edition 2021.
                let retype = *ty != Ty::Ptr && can_retype_thin_address(ty, &Ty::Ptr);
                if retype {
                    for operand in [&mut *lhs, &mut *rhs] {
                        let result = fresh();
                        out.push(
                            InstrNode::new(Inst::Cast {
                                op: CastOp::PtrToPtr,
                                src_ty: ty.clone(),
                                dst_ty: Ty::Ptr,
                                operand: *operand,
                            })
                            .with_result(result),
                        );
                        *operand = result;
                    }
                    *ty = Ty::Ptr;
                }
            }
            out.push(node);
        }
        block.body = out;
    }
}

/// The `(target, arguments)` of every edge a terminator passes block
/// arguments on.
fn edge_args_mut(inst: &mut Inst) -> Vec<(BlockId, &mut Vec<ValueId>)> {
    match inst {
        Inst::Br { target, args } => vec![(*target, args)],
        Inst::CondBr {
            then_target,
            then_args,
            else_target,
            else_args,
            ..
        } => vec![(*then_target, then_args), (*else_target, else_args)],
        Inst::Switch {
            default,
            default_args,
            cases,
            ..
        } => std::iter::once((*default, default_args))
            .chain(cases.iter_mut().map(|case| (case.target, &mut case.args)))
            .collect(),
        Inst::Invoke {
            normal_dest,
            normal_args,
            ..
        } => vec![(*normal_dest, normal_args)],
        _ => Vec::new(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use trust_ir::{Block, FuncId, FuncTyId};

    fn alloca(result: u32) -> InstrNode {
        InstrNode::new(Inst::Alloca {
            ty: Ty::I32,
            count: None,
            align: None,
        })
        .with_result(ValueId::new(result))
    }

    fn ref_i32() -> Ty {
        Ty::Ref(Box::new(Ty::I32))
    }

    /// `bb0: %1 = alloca; <terminator>`, `bb1(%2: &i32)` and `bb2(%3: &i32)`,
    /// both returning.
    fn two_ref_param_blocks(terminator: Inst) -> Function {
        let mut func = Function::new(FuncId::new(0), "t", FuncTyId::new(0), BlockId::new(0));
        let mut entry = Block::new(BlockId::new(0));
        entry.body.push(alloca(1));
        entry.body.push(InstrNode::new(terminator));
        let mut blocks = vec![entry];
        for (id, param) in [(1, 2), (2, 3)] {
            let mut block = Block::new(BlockId::new(id));
            block.params.push((ValueId::new(param), ref_i32()));
            block
                .body
                .push(InstrNode::new(Inst::Return { values: Vec::new() }));
            blocks.push(block);
        }
        func.blocks = blocks;
        func
    }

    fn counter(start: u32) -> impl FnMut() -> ValueId {
        let mut next = start;
        move || {
            let value = ValueId::new(next);
            next += 1;
            value
        }
    }

    /// An address carried into a reference-typed block parameter is re-typed
    /// on the edge, in the predecessor, just before its terminator.
    #[test]
    fn edge_address_into_reference_param_gets_ptr_to_ptr() {
        let mut func = two_ref_param_blocks(Inst::Br {
            target: BlockId::new(1),
            args: vec![ValueId::new(1)],
        });
        canonicalize_reinterpret_copies(&mut func, None, counter(10));
        let entry = &func.blocks[0];
        assert_eq!(entry.body.len(), 3);
        assert_eq!(
            entry.body[1].inst,
            Inst::Cast {
                op: CastOp::PtrToPtr,
                src_ty: Ty::Ptr,
                dst_ty: ref_i32(),
                operand: ValueId::new(1),
            }
        );
        assert_eq!(entry.body[1].results, vec![ValueId::new(10)]);
        assert_eq!(
            entry.body[2].inst,
            Inst::Br {
                target: BlockId::new(1),
                args: vec![ValueId::new(10)],
            }
        );
    }

    /// One value passed to two parameters of the same type on the two edges of
    /// a conditional branch is re-typed once.
    #[test]
    fn one_retype_serves_every_edge_of_a_terminator() {
        let mut func = two_ref_param_blocks(Inst::CondBr {
            cond: ValueId::new(1),
            then_target: BlockId::new(1),
            then_args: vec![ValueId::new(1)],
            else_target: BlockId::new(2),
            else_args: vec![ValueId::new(1)],
        });
        canonicalize_reinterpret_copies(&mut func, None, counter(10));
        let entry = &func.blocks[0];
        assert_eq!(entry.body.len(), 3);
        let Inst::CondBr {
            then_args,
            else_args,
            ..
        } = &entry.body[2].inst
        else {
            panic!("terminator moved");
        };
        assert_eq!(then_args, &vec![ValueId::new(10)]);
        assert_eq!(else_args, &vec![ValueId::new(10)]);
    }

    /// An argument that already has its parameter's type, and one whose type is
    /// not a thin pointer, are left alone.
    #[test]
    fn matching_and_non_address_arguments_are_untouched() {
        let mut func = two_ref_param_blocks(Inst::Br {
            target: BlockId::new(1),
            args: vec![ValueId::new(1)],
        });
        func.blocks[1].params[0].1 = Ty::Ptr;
        canonicalize_reinterpret_copies(&mut func, None, counter(10));
        assert_eq!(func.blocks[0].body.len(), 2);

        let mut func = two_ref_param_blocks(Inst::Br {
            target: BlockId::new(1),
            args: vec![ValueId::new(1)],
        });
        func.blocks[1].params[0].1 = Ty::I64;
        canonicalize_reinterpret_copies(&mut func, None, counter(10));
        assert_eq!(func.blocks[0].body.len(), 2);
    }

    /// A `Copy` that re-types an address as a reference becomes the explicit
    /// `PtrToPtr` it is.
    #[test]
    fn reference_retyping_copy_becomes_ptr_to_ptr() {
        let mut func = two_ref_param_blocks(Inst::Return { values: Vec::new() });
        func.blocks[0].body.insert(
            1,
            InstrNode::new(Inst::Copy {
                ty: ref_i32(),
                operand: ValueId::new(1),
            })
            .with_result(ValueId::new(5)),
        );
        canonicalize_reinterpret_copies(&mut func, None, counter(10));
        assert_eq!(
            func.blocks[0].body[1].inst,
            Inst::Cast {
                op: CastOp::PtrToPtr,
                src_ty: Ty::Ptr,
                dst_ty: ref_i32(),
                operand: ValueId::new(1),
            }
        );
    }

    /// WS7.3-pre: a comparison of two typed raw pointers is made at `Ptr`, each
    /// operand re-typed by an explicit `PtrToPtr`; an integer comparison is
    /// untouched.
    #[test]
    fn typed_pointer_comparison_is_made_at_ptr() {
        let ptr_mut = Ty::PtrMut(Box::new(Ty::U64));
        let icmp = |ty: Ty| {
            InstrNode::new(Inst::ICmp {
                op: trust_ir::ICmpOp::Eq,
                ty,
                lhs: ValueId::new(1),
                rhs: ValueId::new(2),
            })
            .with_result(ValueId::new(3))
        };
        let mut func = two_ref_param_blocks(Inst::Return { values: Vec::new() });
        func.blocks[0].body.insert(1, icmp(ptr_mut.clone()));
        canonicalize_reinterpret_copies(&mut func, None, counter(10));
        let body = &func.blocks[0].body;
        for (index, operand, result) in [(1, 1, 10), (2, 2, 11)] {
            assert_eq!(
                body[index].inst,
                Inst::Cast {
                    op: CastOp::PtrToPtr,
                    src_ty: ptr_mut.clone(),
                    dst_ty: Ty::Ptr,
                    operand: ValueId::new(operand),
                }
            );
            assert_eq!(body[index].results, vec![ValueId::new(result)]);
        }
        assert_eq!(
            body[3].inst,
            Inst::ICmp {
                op: trust_ir::ICmpOp::Eq,
                ty: Ty::Ptr,
                lhs: ValueId::new(10),
                rhs: ValueId::new(11),
            }
        );

        let mut func = two_ref_param_blocks(Inst::Return { values: Vec::new() });
        func.blocks[0].body.insert(1, icmp(Ty::I64));
        canonicalize_reinterpret_copies(&mut func, None, counter(10));
        assert_eq!(func.blocks[0].body[1], icmp(Ty::I64));
    }

    /// WS7.3-pre: an integer comparison over a same-width operand of the other
    /// signedness re-types that operand by an explicit `Bitcast`.
    #[test]
    fn same_width_integer_operand_is_bitcast() {
        let mut func = two_ref_param_blocks(Inst::Return { values: Vec::new() });
        let body = &mut func.blocks[0].body;
        body.insert(
            1,
            InstrNode::new(Inst::Const {
                ty: Ty::U64,
                value: Constant::Int(4),
            })
            .with_result(ValueId::new(5)),
        );
        body.insert(
            2,
            InstrNode::new(Inst::Const {
                ty: Ty::I64,
                value: Constant::Int(9),
            })
            .with_result(ValueId::new(6)),
        );
        body.insert(
            3,
            InstrNode::new(Inst::ICmp {
                op: trust_ir::ICmpOp::Ult,
                ty: Ty::I64,
                lhs: ValueId::new(5),
                rhs: ValueId::new(6),
            })
            .with_result(ValueId::new(7)),
        );
        canonicalize_reinterpret_copies(&mut func, None, counter(10));
        let body = &func.blocks[0].body;
        assert_eq!(
            body[3].inst,
            Inst::Cast {
                op: CastOp::Bitcast,
                src_ty: Ty::U64,
                dst_ty: Ty::I64,
                operand: ValueId::new(5),
            }
        );
        assert_eq!(
            body[4].inst,
            Inst::ICmp {
                op: trust_ir::ICmpOp::Ult,
                ty: Ty::I64,
                lhs: ValueId::new(10),
                rhs: ValueId::new(6),
            }
        );
    }

    /// WS7.3-pre: a `ptrtoptr` declaring another source type than its operand
    /// has takes the operand's type; a `ptrtoint` of a typed pointer gets an
    /// explicit `PtrToPtr` to `Ptr` first.
    #[test]
    fn pointer_cast_sources_follow_their_operand() {
        let ptr_mut = Ty::PtrMut(Box::new(Ty::U8));
        // %1 is an `alloca` (a `Ptr`).
        let mut func = two_ref_param_blocks(Inst::Return { values: Vec::new() });
        func.blocks[0].body.insert(
            1,
            InstrNode::new(Inst::Cast {
                op: CastOp::PtrToPtr,
                src_ty: ptr_mut.clone(),
                dst_ty: ref_i32(),
                operand: ValueId::new(1),
            })
            .with_result(ValueId::new(5)),
        );
        canonicalize_reinterpret_copies(&mut func, None, counter(10));
        assert_eq!(
            func.blocks[0].body[1].inst,
            Inst::Cast {
                op: CastOp::PtrToPtr,
                src_ty: Ty::Ptr,
                dst_ty: ref_i32(),
                operand: ValueId::new(1),
            }
        );

        // %2 is a `&i32` block parameter of bb1.
        let mut func = two_ref_param_blocks(Inst::Return { values: Vec::new() });
        func.blocks[1].body.insert(
            0,
            InstrNode::new(Inst::Cast {
                op: CastOp::PtrToInt,
                src_ty: Ty::Ptr,
                dst_ty: Ty::I64,
                operand: ValueId::new(2),
            })
            .with_result(ValueId::new(5)),
        );
        canonicalize_reinterpret_copies(&mut func, None, counter(10));
        let body = &func.blocks[1].body;
        assert_eq!(
            body[0].inst,
            Inst::Cast {
                op: CastOp::PtrToPtr,
                src_ty: ref_i32(),
                dst_ty: Ty::Ptr,
                operand: ValueId::new(2),
            }
        );
        assert_eq!(
            body[1].inst,
            Inst::Cast {
                op: CastOp::PtrToInt,
                src_ty: Ty::Ptr,
                dst_ty: Ty::I64,
                operand: ValueId::new(10),
            }
        );
    }

    /// WS7.3-pre: constants are spelled as trust-ir admits them at their
    /// declared types; an in-range constant is untouched.
    #[test]
    fn constants_are_spelled_at_their_declared_types() {
        let constant = |ty: Ty, value: Constant| {
            InstrNode::new(Inst::Const { ty, value }).with_result(ValueId::new(7))
        };
        let run = |node: InstrNode| {
            let mut func = two_ref_param_blocks(Inst::Return { values: Vec::new() });
            func.blocks[0].body.insert(1, node);
            canonicalize_reinterpret_copies(&mut func, None, counter(10));
            func.blocks[0].body.clone()
        };
        // A u64 value on the I64 lane: the same 64 bits, in range.
        let body = run(constant(Ty::I64, Constant::Int(10_000_000_000_000_000_000)));
        assert_eq!(
            body[1],
            constant(
                Ty::I64,
                Constant::Int(10_000_000_000_000_000_000 - (1i128 << 64))
            )
        );
        // A negative value at an unsigned type.
        let body = run(constant(Ty::U8, Constant::Int(-1)));
        assert_eq!(body[1], constant(Ty::U8, Constant::Int(255)));
        // Out of both ranges: left for the validator.
        let body = run(constant(Ty::I8, Constant::Int(300)));
        assert_eq!(body[1], constant(Ty::I8, Constant::Int(300)));
        // In range: untouched.
        let body = run(constant(Ty::I64, Constant::Int(-5)));
        assert_eq!(body[1], constant(Ty::I64, Constant::Int(-5)));
        // Bool.
        let body = run(constant(Ty::Bool, Constant::Int(1)));
        assert_eq!(body[1], constant(Ty::Bool, Constant::Bool(true)));
        let body = run(constant(Ty::Bool, Constant::Int(2)));
        assert_eq!(body[1], constant(Ty::Bool, Constant::Int(2)));
        // An integer address at a typed pointer: at `Ptr`, then re-typed.
        let ptr_mut = Ty::PtrMut(Box::new(Ty::U8));
        let body = run(constant(ptr_mut.clone(), Constant::Int(8)));
        assert_eq!(
            body[1],
            InstrNode::new(Inst::Const {
                ty: Ty::Ptr,
                value: Constant::Int(8),
            })
            .with_result(ValueId::new(10))
        );
        assert_eq!(
            body[2],
            InstrNode::new(Inst::Cast {
                op: CastOp::PtrToPtr,
                src_ty: Ty::Ptr,
                dst_ty: ptr_mut,
                operand: ValueId::new(10),
            })
            .with_result(ValueId::new(7))
        );
        // The empty aggregate at Unit.
        let body = run(constant(Ty::Unit, Constant::Aggregate(Vec::new())));
        assert_eq!(body[1], constant(Ty::Unit, Constant::PhantomData));
    }

    /// A GEP's result is a `Ptr` like an `alloca`'s: a `Copy` re-typing it as
    /// a reference becomes a `PtrToPtr`, and so does the edge carrying it into
    /// a reference-typed parameter.
    #[test]
    fn gep_result_is_retyped_like_an_address() {
        let gep = || {
            InstrNode::new(Inst::GEP {
                pointee_ty: Ty::U8,
                base: ValueId::new(1),
                indices: vec![ValueId::new(1)],
                inbounds: true,
            })
            .with_result(ValueId::new(4))
        };
        let mut func = two_ref_param_blocks(Inst::Return { values: Vec::new() });
        func.blocks[0].body.insert(1, gep());
        func.blocks[0].body.insert(
            2,
            InstrNode::new(Inst::Copy {
                ty: ref_i32(),
                operand: ValueId::new(4),
            })
            .with_result(ValueId::new(5)),
        );
        canonicalize_reinterpret_copies(&mut func, None, counter(10));
        assert_eq!(
            func.blocks[0].body[2].inst,
            Inst::Cast {
                op: CastOp::PtrToPtr,
                src_ty: Ty::Ptr,
                dst_ty: ref_i32(),
                operand: ValueId::new(4),
            }
        );

        let mut func = two_ref_param_blocks(Inst::Br {
            target: BlockId::new(1),
            args: vec![ValueId::new(4)],
        });
        func.blocks[0].body.insert(1, gep());
        canonicalize_reinterpret_copies(&mut func, None, counter(10));
        assert_eq!(
            func.blocks[0].body[2].inst,
            Inst::Cast {
                op: CastOp::PtrToPtr,
                src_ty: Ty::Ptr,
                dst_ty: ref_i32(),
                operand: ValueId::new(4),
            }
        );
    }

    /// WS7.3: a `Store` of an address at a reference type (`store &i32 %ptr`,
    /// the lane's `Rc` / `Weak` drop glue and aggregate fields), and a `Select`
    /// arm of another thin-pointer type, take a `PtrToPtr` to the declared type
    /// just before the instruction; a same-width integer of the other
    /// signedness takes a `Bitcast`. A narrower or wider integer, and an address
    /// stored as an integer, are left as they were for the validator.
    #[test]
    fn stored_and_selected_values_take_the_declared_representation() {
        let store = |ty: Ty, value: u32| {
            InstrNode::new(Inst::Store {
                ty,
                ptr: ValueId::new(1),
                value: ValueId::new(value),
                volatile: false,
                align: None,
            })
        };
        let konst = |ty: Ty, value: i128, result: u32| {
            InstrNode::new(Inst::Const {
                ty,
                value: Constant::Int(value),
            })
            .with_result(ValueId::new(result))
        };
        // %1 = alloca (a `Ptr`); %4: u64; %5: i64; %6: bool.
        let mut func = two_ref_param_blocks(Inst::Return { values: Vec::new() });
        let body = &mut func.blocks[0].body;
        body.insert(1, konst(Ty::U64, 4, 4));
        body.insert(2, konst(Ty::I64, 9, 5));
        body.insert(
            3,
            InstrNode::new(Inst::ICmp {
                op: trust_ir::ICmpOp::Eq,
                ty: Ty::I64,
                lhs: ValueId::new(5),
                rhs: ValueId::new(5),
            })
            .with_result(ValueId::new(6)),
        );
        body.insert(4, store(ref_i32(), 1));
        body.insert(5, store(Ty::I64, 4));
        body.insert(6, store(Ty::I8, 5));
        body.insert(7, store(Ty::I64, 1));
        body.insert(
            8,
            InstrNode::new(Inst::Select {
                ty: ref_i32(),
                cond: ValueId::new(6),
                then_val: ValueId::new(1),
                else_val: ValueId::new(1),
            })
            .with_result(ValueId::new(7)),
        );
        // The per-function canonicalization leaves every store and select as
        // the lane lowered it: the field-store gate runs after it.
        let lowered = func.clone();
        canonicalize_reinterpret_copies(&mut func, None, counter(10));
        assert_eq!(func, lowered);
        retype_stored_and_selected_values(&mut func, None, counter(10));
        let body: Vec<&Inst> = func.blocks[0].body.iter().map(|node| &node.inst).collect();
        let retype = |op, src_ty, dst_ty, operand: u32| Inst::Cast {
            op,
            src_ty,
            dst_ty,
            operand: ValueId::new(operand),
        };
        assert_eq!(*body[4], retype(CastOp::PtrToPtr, Ty::Ptr, ref_i32(), 1));
        assert_eq!(*body[5], store(ref_i32(), 10).inst);
        assert_eq!(*body[6], retype(CastOp::Bitcast, Ty::U64, Ty::I64, 4));
        assert_eq!(*body[7], store(Ty::I64, 11).inst);
        // Width changes and an address read as an integer: untouched.
        assert_eq!(*body[8], store(Ty::I8, 5).inst);
        assert_eq!(*body[9], store(Ty::I64, 1).inst);
        assert_eq!(*body[10], retype(CastOp::PtrToPtr, Ty::Ptr, ref_i32(), 1));
        assert_eq!(*body[11], retype(CastOp::PtrToPtr, Ty::Ptr, ref_i32(), 1));
        assert_eq!(
            *body[12],
            Inst::Select {
                ty: ref_i32(),
                cond: ValueId::new(6),
                then_val: ValueId::new(12),
                else_val: ValueId::new(13),
            }
        );
    }

    /// LD-48: in the module-level pass, an integer carried into a block
    /// parameter of the same width and the other signedness (the `i64` lane of
    /// a `ControlFlow` payload into a `u64` accumulator) is re-labelled by a
    /// `Bitcast` on the edge; a width change is left for the validator, and the
    /// per-function pass (no module) leaves the edge to the lane's own gates.
    #[test]
    fn same_width_integer_edge_argument_is_bitcast() {
        let module = Module::new("t");
        let constant = |ty: Ty| {
            InstrNode::new(Inst::Const {
                ty,
                value: trust_ir::Constant::Int(5),
            })
            .with_result(ValueId::new(4))
        };
        let with_param = |arg_ty: Ty, param_ty: Ty| {
            let mut func = two_ref_param_blocks(Inst::Br {
                target: BlockId::new(1),
                args: vec![ValueId::new(4)],
            });
            func.blocks[0].body.insert(1, constant(arg_ty));
            func.blocks[1].params[0].1 = param_ty;
            func
        };
        let mut func = with_param(Ty::I64, Ty::U64);
        canonicalize_reinterpret_copies(&mut func, Some(&module), counter(10));
        let entry = &func.blocks[0].body;
        assert_eq!(
            entry[2].inst,
            Inst::Cast {
                op: CastOp::Bitcast,
                src_ty: Ty::I64,
                dst_ty: Ty::U64,
                operand: ValueId::new(4),
            }
        );
        assert_eq!(entry[2].results, vec![ValueId::new(10)]);
        assert_eq!(
            entry[3].inst,
            Inst::Br {
                target: BlockId::new(1),
                args: vec![ValueId::new(10)],
            }
        );

        let mut func = with_param(Ty::I32, Ty::U64);
        canonicalize_reinterpret_copies(&mut func, Some(&module), counter(10));
        assert_eq!(
            func.blocks[0].body.len(),
            3,
            "a width change is not re-labelled"
        );

        let mut func = with_param(Ty::I64, Ty::U64);
        canonicalize_reinterpret_copies(&mut func, None, counter(10));
        assert_eq!(func.blocks[0].body.len(), 3, "the per-function pass");
    }

    /// LD-48: in the module-level pass, a `store` of an address at another
    /// thin-pointer type than the value's own takes a `PtrToPtr` of the value
    /// to the declared type; an address stored as an integer is left for the
    /// validator, and the per-function pass (no module) leaves the store to the
    /// lane's own gates. The module-level pass is the sequence
    /// `abi_edges::legalize_module` runs: the copy canonicalization, then
    /// [`retype_stored_and_selected_values`], which re-types the store.
    #[test]
    fn stored_address_is_retyped_to_the_declared_pointer() {
        let module = Module::new("t");
        let module_level = |func: &mut Function| {
            let mut fresh = counter(10);
            canonicalize_reinterpret_copies(func, Some(&module), &mut fresh);
            retype_stored_and_selected_values(func, Some(&module), &mut fresh);
        };
        let declared = Ty::PtrConst(Box::new(Ty::I32));
        let store = |ty: Ty| {
            InstrNode::new(Inst::Store {
                ty,
                ptr: ValueId::new(2),
                value: ValueId::new(1),
                volatile: false,
                align: None,
            })
        };
        let mut func = two_ref_param_blocks(Inst::Return { values: Vec::new() });
        func.blocks[0].body.insert(1, alloca(2));
        func.blocks[0].body.insert(2, store(declared.clone()));
        module_level(&mut func);
        let body = &func.blocks[0].body;
        assert_eq!(
            body[2].inst,
            Inst::Cast {
                op: CastOp::PtrToPtr,
                src_ty: Ty::Ptr,
                dst_ty: declared.clone(),
                operand: ValueId::new(1),
            }
        );
        assert_eq!(body[2].results, vec![ValueId::new(10)]);
        assert_eq!(
            body[3].inst,
            Inst::Store {
                ty: declared.clone(),
                ptr: ValueId::new(2),
                value: ValueId::new(10),
                volatile: false,
                align: None,
            }
        );

        let mut func = two_ref_param_blocks(Inst::Return { values: Vec::new() });
        func.blocks[0].body.insert(1, alloca(2));
        func.blocks[0].body.insert(2, store(Ty::I64));
        let before = func.blocks[0].body.clone();
        module_level(&mut func);
        assert_eq!(func.blocks[0].body, before);

        let mut func = two_ref_param_blocks(Inst::Return { values: Vec::new() });
        func.blocks[0].body.insert(1, alloca(2));
        func.blocks[0].body.insert(2, store(declared.clone()));
        let before = func.blocks[0].body.clone();
        canonicalize_reinterpret_copies(&mut func, None, counter(10));
        assert_eq!(func.blocks[0].body, before, "the per-function pass");
    }
}
