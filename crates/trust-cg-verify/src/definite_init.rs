// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Definite-initialization / no-uninitialized-read checker over a
//! `trust_ir::Function`.
//!
//! This is a *structural* well-formedness gate that runs on the trust-ir
//! `Function` produced by a frontend (notably the rustc bridge) **before** it is
//! lowered to machine IR. Like [`crate::ssa_loop_complete`], it is independent of
//! *how* the IR was built, so it catches bugs in the producer's own memory
//! reasoning rather than in any individual instruction.
//!
//! # The #99 class
//!
//! #99 was a SILENT MISCOMPILE: a celled function parameter's value was never
//! stored into its `Alloca` cell, so `&param` (a niche `Option<&T>` payload)
//! dereferenced *uninitialized stack* and returned input-independent garbage. The
//! per-instruction SMT proofs did not catch it — every emitted instruction was
//! individually a correct lowering; the bug was a MISSING store, so the produced
//! trust-ir was already a wrong translation of the MIR. No scalar-rvalue,
//! carrier-hygiene, regalloc-validator or loop-completeness gate validates memory
//! *initialization*. This checker closes that perimeter gap.
//!
//! # The property (simple, near-zero-false-positive)
//!
//! For every stack cell — the result `ValueId` of an [`Inst::Alloca`] — consider
//! every pointer that **definitely derives** from that Alloca (the Alloca result
//! itself, and any value produced by feeding a derived pointer through `Copy`,
//! `GEP`, a pointer-preserving `Cast` (`PtrToPtr` / `Bitcast` / `Transmute`), or
//! `PtrData`). If any [`Inst::Load`] reads through a derived pointer (a LOAD of
//! the cell) but there is **no** [`Inst::Store`] through *any* derived pointer (a
//! STORE into the cell), the cell is read while definitely uninitialized — the
//! #99 signature — and we **fail closed**.
//!
//! # Soundness: provenance and escape (the crux)
//!
//! The whole gate hinges on never flagging a load whose pointer might in fact be
//! initialized somewhere we did not model. We are deliberately conservative on
//! every axis:
//!
//! * **Provenance is forward-only and exact.** A pointer is "derived from cell
//!   `c`" only if it is `c` itself or is produced by an instruction whose pointer
//!   *input* is already known to derive from `c`, through one of the
//!   address-preserving ops above. A value we cannot trace to a *specific single*
//!   Alloca (a function argument, `HeapAlloc`, `GlobalAddr`, `NullPtr`, an
//!   `IntToPtr`, the result of a `Load`, or a block parameter / phi that merges
//!   pointers of different origin) is NOT an Alloca cell pointer — a load through
//!   it is never flagged.
//!
//! * **A pointer that merges two origins is poisoned.** If any derived-pointer
//!   propagation step would attribute a value to two *different* Allocas, that
//!   value is dropped from all provenance sets. We only ever flag a load whose
//!   pointer derives from exactly one Alloca. Block parameters never receive an
//!   origin at all (a phi merging pointers must not be attributed).
//!
//! * **Escape ⇒ never flag.** If a cell's pointer (or any derived pointer) is
//!   used as anything *other* than the pointer operand of a Load / Store / GEP /
//!   address-preserving Cast / PtrData — e.g. it is passed as a `Call` argument,
//!   used as the *value* operand of a `Store`, returned, used in pointer
//!   arithmetic, compared, or threaded as a branch argument — then the cell MAY
//!   be initialized through that escaped pointer by code this structural gate
//!   cannot see. Such a cell is removed from consideration entirely.
//!
//! The net effect: a flagged cell is one that is (a) an `Alloca`, (b) read by at
//! least one Load through a pointer that definitely and *only* derives from it,
//! (c) never written through *any* derived pointer, and (d) never escapes to any
//! context that could write it. That is exactly the #99 shape, and nothing a
//! correct producer emits.

use std::collections::{BTreeSet, HashMap, HashSet};

use trust_ir::{CastOp, Function, Inst, ValueId};

/// A single definite-initialization violation.
///
/// `Serialize` is derived purely for the AI-usability diagnostics layer
/// (`crate::diag`): it lets a fail-closed event emit its typed fields as JSON.
/// The derive is additive — it changes no field and no gate decision.
#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize)]
pub enum InitViolation {
    /// A stack cell (an `Alloca` result) is read by a Load through a pointer that
    /// definitely derives from it, but is never written by any Store through any
    /// derived pointer, and never escapes to a context that could write it. This
    /// is the #99 signature: an uninitialized stack read. Failing closed rather
    /// than miscompiling.
    UninitializedCellRead {
        /// The `Alloca` result value naming the cell.
        cell: ValueId,
        /// A representative pointer value through which the uninitialized cell is
        /// loaded, for diagnostics.
        load_ptr: ValueId,
    },
}

impl InitViolation {
    /// Single-line diagnostic suitable for a fail-closed `Err(String)`.
    pub fn message(&self) -> String {
        match self {
            InitViolation::UninitializedCellRead { cell, load_ptr } => format!(
                "uninitialized stack cell read: alloca {cell:?} is loaded (through {load_ptr:?}) \
                 but never stored to and never escapes — failing closed rather than miscompiling, \
                 #99-class"
            ),
        }
    }
}

/// Result of running the checker. `Ok(())` when every loaded stack cell is
/// definitely written (or escapes); `Err(violations)` (non-empty) otherwise.
pub type InitCheckResult = Result<(), Vec<InitViolation>>;

/// Run the definite-initialization checker on a trust-ir function.
pub fn check_function(function: &Function) -> InitCheckResult {
    let prov = Provenance::compute(function);

    // For each Alloca cell, tally: was it loaded through a derived pointer, was it
    // stored through a derived pointer, did it escape?
    #[derive(Default, Clone, Copy)]
    struct CellState {
        loaded_through: Option<ValueId>,
        stored: bool,
        escaped: bool,
    }
    let mut state: HashMap<ValueId, CellState> = prov
        .cells
        .iter()
        .map(|c| (*c, CellState::default()))
        .collect();

    // Mark escapes first: any *use* of a derived pointer that is not a recognized
    // load/store/GEP/cast/PtrData pointer-position use is an escape for that
    // pointer's cell.
    for block in &function.blocks {
        for node in &block.body {
            mark_pointer_escapes(&node.inst, &prov, &mut |cell| {
                if let Some(s) = state.get_mut(&cell) {
                    s.escaped = true;
                }
            });
            // Terminator edge arguments and scrutinees are escapes if they carry a
            // derived pointer (a branch arg threads the pointer to a block param —
            // its origin is then merged/lost; a Switch/CondBr/Return operand
            // likewise leaves load/store/GEP context).
            if node.is_terminator() {
                for v in terminator_operands(&node.inst) {
                    if let Some(cell) = prov.cell_of(v)
                        && let Some(s) = state.get_mut(&cell)
                    {
                        s.escaped = true;
                    }
                }
            }
        }
    }

    // Now tally loads and stores through derived pointers.
    for block in &function.blocks {
        for node in &block.body {
            match &node.inst {
                Inst::Load { ptr, .. } | Inst::AtomicLoad { ptr, .. } => {
                    if let Some(cell) = prov.cell_of(*ptr)
                        && let Some(s) = state.get_mut(&cell)
                        && s.loaded_through.is_none()
                    {
                        s.loaded_through = Some(*ptr);
                    }
                }
                Inst::Store { ptr, .. }
                | Inst::AtomicStore { ptr, .. }
                | Inst::AtomicRMW { ptr, .. }
                | Inst::CmpXchg { ptr, .. } => {
                    if let Some(cell) = prov.cell_of(*ptr)
                        && let Some(s) = state.get_mut(&cell)
                    {
                        s.stored = true;
                    }
                }
                _ => {}
            }
        }
    }

    let mut violations = Vec::new();
    // Deterministic order: by cell value id.
    let mut cells: Vec<ValueId> = prov.cells.iter().copied().collect();
    cells.sort_by_key(|c| c.index());
    for cell in cells {
        let s = state.get(&cell).copied().unwrap_or(CellState {
            loaded_through: None,
            stored: false,
            escaped: false,
        });
        if s.escaped || s.stored {
            continue;
        }
        if let Some(load_ptr) = s.loaded_through {
            violations.push(InitViolation::UninitializedCellRead { cell, load_ptr });
        }
    }

    if violations.is_empty() {
        Ok(())
    } else {
        Err(violations)
    }
}

/// Convenience wrapper that collapses all violations into a single fail-closed
/// `Err(String)`, matching the bridge's `Result<_, String>` lowering contract.
pub fn check_function_fail_closed(function: &Function) -> Result<(), String> {
    check_function(function).map_err(|violations| {
        violations
            .first()
            .map(InitViolation::message)
            .unwrap_or_else(|| "definite-initialization check failed".to_owned())
    })
}

// ---------------------------------------------------------------------------
// Provenance: which Alloca cell does each pointer value derive from?
// ---------------------------------------------------------------------------

/// Forward provenance map. `cell_of(v)` is `Some(c)` iff value `v` *definitely*
/// derives from exactly one Alloca `c` (the cell itself, or a value produced by
/// an address-preserving op on a value already known to derive from `c`). A value
/// whose provenance is ambiguous, broken, or unknown is absent (and `cell_of`
/// returns `None`).
struct Provenance {
    /// The set of Alloca result values (the stack cells).
    cells: BTreeSet<ValueId>,
    /// For each pointer value that definitely derives from a single cell, that
    /// cell. The cell itself maps to itself. A value that could derive from more
    /// than one cell is *removed* from the map (poisoned), so a poisoned pointer
    /// is treated as un-attributable (`None`).
    origin: HashMap<ValueId, ValueId>,
}

impl Provenance {
    fn cell_of(&self, v: ValueId) -> Option<ValueId> {
        self.origin.get(&v).copied()
    }

    fn compute(function: &Function) -> Self {
        let mut cells: BTreeSet<ValueId> = BTreeSet::new();
        let mut origin: HashMap<ValueId, ValueId> = HashMap::new();
        // Values that have been seen to merge >1 origin; never attributable.
        let mut poisoned: HashSet<ValueId> = HashSet::new();

        // Seed: every Alloca result is its own cell.
        for block in &function.blocks {
            for node in &block.body {
                if let Inst::Alloca { .. } = node.inst
                    && let Some(r) = node.results.first()
                {
                    cells.insert(*r);
                    origin.insert(*r, *r);
                }
            }
        }

        // Propagate forward to a fixpoint. Address-preserving ops carry their
        // single pointer input's origin to their result. If a result already has
        // a *different* recorded origin, it merges two cells and is poisoned
        // (removed from `origin`). Block parameters are never given an origin
        // (a phi merging pointers of different cells must not be attributed) —
        // this is the conservative "merge ⇒ unknown" rule.
        let mut changed = true;
        while changed {
            changed = false;
            for block in &function.blocks {
                for node in &block.body {
                    let Some(input) = address_preserving_input(&node.inst) else {
                        continue;
                    };
                    if poisoned.contains(&input) {
                        // Propagating an unknown/poisoned origin: the result is
                        // not attributable to a single cell. Poison the result so
                        // a later, different attribution cannot resurrect it.
                        for r in &node.results {
                            if origin.remove(r).is_some() {
                                changed = true;
                            }
                            if poisoned.insert(*r) {
                                changed = true;
                            }
                        }
                        continue;
                    }
                    let Some(src) = origin.get(&input).copied() else {
                        continue;
                    };
                    for r in &node.results {
                        if poisoned.contains(r) {
                            continue;
                        }
                        match origin.get(r).copied() {
                            None => {
                                origin.insert(*r, src);
                                changed = true;
                            }
                            Some(existing) if existing == src => {}
                            Some(_) => {
                                // Two different cells reach this result: poison it.
                                origin.remove(r);
                                poisoned.insert(*r);
                                changed = true;
                            }
                        }
                    }
                }
            }
        }

        Provenance { cells, origin }
    }
}

/// If `inst` produces a pointer that address-preservingly derives from a single
/// pointer *input*, return that input. These are the ops through which a stack
/// cell's address flows without changing which allocation it points into:
///
/// * `Copy` of a pointer,
/// * `GEP` (offset within the same allocation — `inbounds` or not, the base's
///   allocation is preserved; an out-of-bounds GEP is UB, not a re-attribution),
/// * a pointer-preserving `Cast` (`PtrToPtr` / `Bitcast` / `Transmute`),
/// * `PtrData` (extract the data lane of a fat pointer — same allocation).
///
/// `PtrToInt` / `IntToPtr` deliberately break provenance (the int could be
/// stored/recombined anywhere), so they are NOT address-preserving here: an
/// `IntToPtr` result has no cell origin, and a `PtrToInt` *use* of a cell pointer
/// is an escape (handled in `mark_pointer_escapes`).
fn address_preserving_input(inst: &Inst) -> Option<ValueId> {
    match inst {
        Inst::Copy { operand, .. } => Some(*operand),
        Inst::GEP { base, .. } => Some(*base),
        Inst::Cast {
            op: CastOp::PtrToPtr | CastOp::Bitcast | CastOp::Transmute,
            operand,
            ..
        } => Some(*operand),
        Inst::PtrData { ptr, .. } => Some(*ptr),
        // The metadata lane of a fat pointer is not the address; `Borrow`/
        // `BorrowMut` re-borrow but their result is a fresh borrow value whose
        // address-identity we conservatively do NOT propagate (so a load through a
        // re-borrow is never flagged — sound). Everything else is not
        // address-preserving.
        _ => None,
    }
}

/// Invoke `escape(cell)` for every cell whose derived pointer ESCAPES through
/// `inst` — i.e. is used as anything other than the pointer operand of a
/// load/store/GEP/address-preserving-cast/PtrData.
///
/// This is the soundness backstop: if a derived pointer reaches a `Call` arg, a
/// `Store` *value* slot, a comparison, pointer arithmetic, `PtrToInt`,
/// `PtrFromParts`, a frame bind, a `Borrow`, etc., the cell may be written
/// through that alias by code this structural gate cannot see, so the cell must
/// not be flagged.
fn mark_pointer_escapes(inst: &Inst, prov: &Provenance, escape: &mut impl FnMut(ValueId)) {
    // The pointer-position operand(s) that do NOT escape (they keep the value in
    // load/store/GEP/cast/PtrData provenance context). Every OTHER value operand
    // that carries a cell origin is an escape.
    let non_escaping: &[ValueId] = match inst {
        Inst::Load { ptr, .. } | Inst::AtomicLoad { ptr, .. } => std::slice::from_ref(ptr),
        Inst::Store { ptr, .. } | Inst::AtomicStore { ptr, .. } | Inst::AtomicRMW { ptr, .. } => {
            // The pointer is non-escaping; the VALUE operand (handled below as a
            // generic use) IS an escape if it carries a cell origin.
            std::slice::from_ref(ptr)
        }
        Inst::CmpXchg { ptr, .. } => std::slice::from_ref(ptr),
        Inst::GEP { base, .. } => std::slice::from_ref(base),
        Inst::Cast {
            op: CastOp::PtrToPtr | CastOp::Bitcast | CastOp::Transmute,
            operand,
            ..
        } => std::slice::from_ref(operand),
        Inst::PtrData { ptr, .. } | Inst::PtrMetadata { ptr, .. } => std::slice::from_ref(ptr),
        _ => &[],
    };

    for used in crate::ssa_loop_complete::non_terminator_value_uses(inst) {
        if non_escaping.contains(&used) {
            continue;
        }
        if let Some(cell) = prov.cell_of(used) {
            escape(cell);
        }
    }
}

/// Operands that a terminator threads as edge arguments or uses as a scrutinee /
/// return value. A cell pointer reaching any of these leaves load/store context,
/// so it is treated as an escape.
fn terminator_operands(inst: &Inst) -> Vec<ValueId> {
    match inst {
        Inst::Br { args, .. } => args.clone(),
        Inst::CondBr {
            cond,
            then_args,
            else_args,
            ..
        } => {
            let mut v = vec![*cond];
            v.extend(then_args.iter().copied());
            v.extend(else_args.iter().copied());
            v
        }
        Inst::Switch {
            value,
            default_args,
            cases,
            ..
        } => {
            let mut v = vec![*value];
            v.extend(default_args.iter().copied());
            for c in cases {
                v.extend(c.args.iter().copied());
            }
            v
        }
        Inst::Return { values } => values.clone(),
        _ => Vec::new(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use trust_ir::inst::AllocOrigin;
    use trust_ir::{Block, BlockId, FuncId, FuncTyId, Function, Inst, InstrNode, Ty, ValueId};

    fn v(n: u32) -> ValueId {
        ValueId::new(n)
    }
    fn b(n: u32) -> BlockId {
        BlockId::new(n)
    }
    fn empty_fn() -> Function {
        Function::new(FuncId::new(0), "test", FuncTyId::new(0), b(0))
    }

    /// The #99 PRE-FIX shape (uninitialized cell read).
    ///
    /// Models `fn f(x: i64) -> i64 { let o: Option<&i64> = Some(&x); *o.payload }`
    /// where the bridge celled `x` (to take `&x` for the niche payload) but FORGOT
    /// to store the incoming param value into the cell:
    ///
    ///   bb0(%x:i64):
    ///       %cell = alloca i64          ; the celled parameter `x`
    ///       ; (BUG: no `store %cell, %x` — cell left uninitialized)
    ///       %addr = gep %cell           ; &x (the niche payload pointer)
    ///       %val  = load i64, %addr     ; later `*p` reads uninitialized stack
    ///       return %val
    ///
    /// The cell is loaded, never stored, never escaped => FAIL CLOSED.
    fn uninitialized_cell() -> Function {
        let mut f = empty_fn();
        let mut bb0 = Block::new(b(0)).with_param(v(0), Ty::I64); // %x
        bb0.body.push(
            InstrNode::new(Inst::Alloca {
                ty: Ty::I64,
                count: None,
                align: None,
            })
            .with_result(v(1)), // %cell
        );
        // NO store into %cell — the #99 bug.
        bb0.body.push(
            InstrNode::new(Inst::GEP {
                pointee_ty: Ty::I64,
                base: v(1),
                indices: vec![],
                inbounds: true,
            })
            .with_result(v(2)), // %addr derived from %cell
        );
        bb0.body.push(
            InstrNode::new(Inst::Load {
                ty: Ty::I64,
                ptr: v(2),
                volatile: false,
                align: None,
            })
            .with_result(v(3)), // %val = load uninitialized
        );
        bb0.body
            .push(InstrNode::new(Inst::Return { values: vec![v(3)] }));
        f.blocks = vec![bb0];
        f
    }

    /// The POSITIVE CONTROL: the #99 POST-FIX shape — identical, but WITH the
    /// store of the incoming param into the cell (the fix). Must pass.
    fn initialized_cell() -> Function {
        let mut f = empty_fn();
        let mut bb0 = Block::new(b(0)).with_param(v(0), Ty::I64); // %x
        bb0.body.push(
            InstrNode::new(Inst::Alloca {
                ty: Ty::I64,
                count: None,
                align: None,
            })
            .with_result(v(1)), // %cell
        );
        // THE FIX: store the incoming param value into the cell.
        bb0.body.push(InstrNode::new(Inst::Store {
            ty: Ty::I64,
            ptr: v(1),
            value: v(0),
            volatile: false,
            align: None,
        }));
        bb0.body.push(
            InstrNode::new(Inst::GEP {
                pointee_ty: Ty::I64,
                base: v(1),
                indices: vec![],
                inbounds: true,
            })
            .with_result(v(2)),
        );
        bb0.body.push(
            InstrNode::new(Inst::Load {
                ty: Ty::I64,
                ptr: v(2),
                volatile: false,
                align: None,
            })
            .with_result(v(3)),
        );
        bb0.body
            .push(InstrNode::new(Inst::Return { values: vec![v(3)] }));
        f.blocks = vec![bb0];
        f
    }

    #[test]
    fn catches_99_uninitialized_read() {
        let f = uninitialized_cell();
        let result = check_function(&f);
        assert!(
            result.is_err(),
            "#99 uninitialized cell read must fail closed"
        );
        let violations = result.unwrap_err();
        assert_eq!(violations.len(), 1);
        assert!(matches!(
            violations[0],
            InitViolation::UninitializedCellRead { cell, .. } if cell == v(1)
        ));
    }

    #[test]
    fn positive_control_initialized_read_ok() {
        let f = initialized_cell();
        assert!(
            check_function(&f).is_ok(),
            "a stored-then-loaded cell must pass"
        );
    }

    /// A store through a GEP-DERIVED pointer (not the bare Alloca) still counts as
    /// initialization.
    #[test]
    fn store_through_derived_pointer_counts() {
        let mut f = empty_fn();
        let mut bb0 = Block::new(b(0)).with_param(v(0), Ty::I64);
        bb0.body.push(
            InstrNode::new(Inst::Alloca {
                ty: Ty::I64,
                count: None,
                align: None,
            })
            .with_result(v(1)),
        );
        bb0.body.push(
            InstrNode::new(Inst::GEP {
                pointee_ty: Ty::I64,
                base: v(1),
                indices: vec![],
                inbounds: true,
            })
            .with_result(v(2)),
        );
        bb0.body.push(InstrNode::new(Inst::Store {
            ty: Ty::I64,
            ptr: v(2), // store through the DERIVED pointer
            value: v(0),
            volatile: false,
            align: None,
        }));
        bb0.body.push(
            InstrNode::new(Inst::Load {
                ty: Ty::I64,
                ptr: v(1), // load through the bare alloca
                volatile: false,
                align: None,
            })
            .with_result(v(3)),
        );
        bb0.body
            .push(InstrNode::new(Inst::Return { values: vec![v(3)] }));
        f.blocks = vec![bb0];
        assert!(
            check_function(&f).is_ok(),
            "a store through a derived pointer initializes the cell"
        );
    }

    /// A cell whose pointer ESCAPES (passed to a Call) is never flagged, even with
    /// no visible store: the callee may write it through the escaped pointer.
    #[test]
    fn escaped_cell_not_flagged() {
        let mut f = empty_fn();
        let mut bb0 = Block::new(b(0));
        bb0.body.push(
            InstrNode::new(Inst::Alloca {
                ty: Ty::I64,
                count: None,
                align: None,
            })
            .with_result(v(1)),
        );
        // Pass &cell to a call (escape — callee may initialize it).
        bb0.body.push(InstrNode::new(Inst::Call {
            callee: FuncId::new(1),
            args: vec![v(1)],
        }));
        bb0.body.push(
            InstrNode::new(Inst::Load {
                ty: Ty::I64,
                ptr: v(1),
                volatile: false,
                align: None,
            })
            .with_result(v(3)),
        );
        bb0.body
            .push(InstrNode::new(Inst::Return { values: vec![v(3)] }));
        f.blocks = vec![bb0];
        assert!(
            check_function(&f).is_ok(),
            "an escaped (call-passed) cell may be initialized by the callee — not flagged"
        );
    }

    /// A cell whose address is used as a STORE VALUE (stored into other memory)
    /// escapes and is not flagged.
    #[test]
    fn cell_stored_as_value_escapes() {
        let mut f = empty_fn();
        let mut bb0 = Block::new(b(0));
        // cell A (the one we load), cell B (somewhere we stash A's address).
        bb0.body.push(
            InstrNode::new(Inst::Alloca {
                ty: Ty::I64,
                count: None,
                align: None,
            })
            .with_result(v(1)), // A
        );
        bb0.body.push(
            InstrNode::new(Inst::Alloca {
                ty: Ty::Ptr,
                count: None,
                align: None,
            })
            .with_result(v(2)), // B
        );
        // store A's address into B: A escapes.
        bb0.body.push(InstrNode::new(Inst::Store {
            ty: Ty::Ptr,
            ptr: v(2),
            value: v(1), // A as the VALUE => escape
            volatile: false,
            align: None,
        }));
        bb0.body.push(
            InstrNode::new(Inst::Load {
                ty: Ty::I64,
                ptr: v(1),
                volatile: false,
                align: None,
            })
            .with_result(v(3)),
        );
        bb0.body
            .push(InstrNode::new(Inst::Return { values: vec![v(3)] }));
        f.blocks = vec![bb0];
        // A escaped (stored as a value) -> not flagged. B is stored to (init) and
        // never loaded -> not flagged.
        assert!(
            check_function(&f).is_ok(),
            "a cell stored as a value escapes"
        );
    }

    /// A function arg / heap pointer / global is NOT an Alloca cell: a load
    /// through it is never flagged (no cell to attribute).
    #[test]
    fn non_alloca_loads_never_flagged() {
        let mut f = empty_fn();
        let mut bb0 = Block::new(b(0)).with_param(v(0), Ty::Ptr); // a pointer param
        // load through the param (not an alloca).
        bb0.body.push(
            InstrNode::new(Inst::Load {
                ty: Ty::I64,
                ptr: v(0),
                volatile: false,
                align: None,
            })
            .with_result(v(1)),
        );
        // load through a heap allocation (not an alloca cell).
        bb0.body.push(
            InstrNode::new(Inst::HeapAlloc {
                ty: Ty::I64,
                count: None,
                align: None,
                origin: AllocOrigin::RustHeap,
            })
            .with_result(v(2)),
        );
        bb0.body.push(
            InstrNode::new(Inst::Load {
                ty: Ty::I64,
                ptr: v(2),
                volatile: false,
                align: None,
            })
            .with_result(v(3)),
        );
        bb0.body
            .push(InstrNode::new(Inst::Return { values: vec![v(1)] }));
        f.blocks = vec![bb0];
        assert!(
            check_function(&f).is_ok(),
            "loads through non-alloca pointers are never flagged"
        );
    }

    /// A cell that is allocated and loaded but whose pointer is threaded as a
    /// branch arg (so its provenance merges into a block param) escapes — never
    /// flagged.
    #[test]
    fn branch_threaded_pointer_escapes() {
        let mut f = empty_fn();
        let mut bb0 = Block::new(b(0));
        bb0.body.push(
            InstrNode::new(Inst::Alloca {
                ty: Ty::I64,
                count: None,
                align: None,
            })
            .with_result(v(1)),
        );
        // thread the cell pointer to bb1 as an arg (escape: origin lost at the
        // block param).
        bb0.body.push(InstrNode::new(Inst::Br {
            target: b(1),
            args: vec![v(1)],
        }));
        let mut bb1 = Block::new(b(1)).with_param(v(2), Ty::Ptr);
        bb1.body.push(
            InstrNode::new(Inst::Load {
                ty: Ty::I64,
                ptr: v(2), // load through the block param (no single cell origin)
                volatile: false,
                align: None,
            })
            .with_result(v(3)),
        );
        bb1.body
            .push(InstrNode::new(Inst::Return { values: vec![v(3)] }));
        f.blocks = vec![bb0, bb1];
        assert!(
            check_function(&f).is_ok(),
            "a pointer threaded through a block param has no single cell origin"
        );
    }

    /// Multiple cells: one initialized, one not. Only the uninitialized one is
    /// flagged.
    #[test]
    fn flags_only_the_uninitialized_cell() {
        let mut f = empty_fn();
        let mut bb0 = Block::new(b(0)).with_param(v(0), Ty::I64);
        bb0.body.push(
            InstrNode::new(Inst::Alloca {
                ty: Ty::I64,
                count: None,
                align: None,
            })
            .with_result(v(1)), // good cell
        );
        bb0.body.push(
            InstrNode::new(Inst::Alloca {
                ty: Ty::I64,
                count: None,
                align: None,
            })
            .with_result(v(2)), // bad cell (never stored)
        );
        bb0.body.push(InstrNode::new(Inst::Store {
            ty: Ty::I64,
            ptr: v(1),
            value: v(0),
            volatile: false,
            align: None,
        }));
        bb0.body.push(
            InstrNode::new(Inst::Load {
                ty: Ty::I64,
                ptr: v(1),
                volatile: false,
                align: None,
            })
            .with_result(v(3)),
        );
        bb0.body.push(
            InstrNode::new(Inst::Load {
                ty: Ty::I64,
                ptr: v(2),
                volatile: false,
                align: None,
            })
            .with_result(v(4)),
        );
        bb0.body.push(InstrNode::new(Inst::Return {
            values: vec![v(3), v(4)],
        }));
        f.blocks = vec![bb0];
        let violations = check_function(&f).unwrap_err();
        assert_eq!(violations.len(), 1);
        assert!(matches!(
            violations[0],
            InitViolation::UninitializedCellRead { cell, .. } if cell == v(2)
        ));
    }

    /// A cell that is allocated and stored but never loaded passes (write-only is
    /// fine — no uninitialized READ).
    #[test]
    fn write_only_cell_ok() {
        let mut f = empty_fn();
        let mut bb0 = Block::new(b(0)).with_param(v(0), Ty::I64);
        bb0.body.push(
            InstrNode::new(Inst::Alloca {
                ty: Ty::I64,
                count: None,
                align: None,
            })
            .with_result(v(1)),
        );
        bb0.body.push(InstrNode::new(Inst::Store {
            ty: Ty::I64,
            ptr: v(1),
            value: v(0),
            volatile: false,
            align: None,
        }));
        bb0.body
            .push(InstrNode::new(Inst::Return { values: vec![v(0)] }));
        f.blocks = vec![bb0];
        assert!(check_function(&f).is_ok());
    }

    /// A cell that is neither loaded nor stored (allocated, address never used for
    /// a load) passes — there is no uninitialized READ to catch.
    #[test]
    fn unused_cell_ok() {
        let mut f = empty_fn();
        let mut bb0 = Block::new(b(0));
        bb0.body.push(
            InstrNode::new(Inst::Alloca {
                ty: Ty::I64,
                count: None,
                align: None,
            })
            .with_result(v(1)),
        );
        bb0.body
            .push(InstrNode::new(Inst::Return { values: vec![] }));
        f.blocks = vec![bb0];
        assert!(check_function(&f).is_ok());
    }

    /// A pointer-preserving cast then load, with a store through the cast: still
    /// initialized.
    #[test]
    fn store_through_bitcast_counts() {
        let mut f = empty_fn();
        let mut bb0 = Block::new(b(0)).with_param(v(0), Ty::I64);
        bb0.body.push(
            InstrNode::new(Inst::Alloca {
                ty: Ty::I64,
                count: None,
                align: None,
            })
            .with_result(v(1)),
        );
        bb0.body.push(
            InstrNode::new(Inst::Cast {
                op: CastOp::Bitcast,
                src_ty: Ty::Ptr,
                dst_ty: Ty::Ptr,
                operand: v(1),
            })
            .with_result(v(2)),
        );
        bb0.body.push(InstrNode::new(Inst::Store {
            ty: Ty::I64,
            ptr: v(2),
            value: v(0),
            volatile: false,
            align: None,
        }));
        bb0.body.push(
            InstrNode::new(Inst::Load {
                ty: Ty::I64,
                ptr: v(2),
                volatile: false,
                align: None,
            })
            .with_result(v(3)),
        );
        bb0.body
            .push(InstrNode::new(Inst::Return { values: vec![v(3)] }));
        f.blocks = vec![bb0];
        assert!(check_function(&f).is_ok());
    }
}
