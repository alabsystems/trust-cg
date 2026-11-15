// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! Constant-offset addresses Rust guarantees in bounds, as trust-ir GEPs on
//! wasm32.
//!
//! The MIR lowering forms `base + k` as the integer chain
//! `inttoptr(ptrtoint(base) + k)` ([`emit_element_addr`]). In trust-ir that
//! `add` wraps at the word width and `inttoptr` of the wrapped integer is
//! defined, so the chain states nothing about `base + k` staying inside the
//! address space, and the wasm lane never folds `k` into a memarg offset
//! (decision record OD-125, ruling 6). A trust-ir `gep u8 base, [k]` is
//! undefined behaviour when its byte offset is negative or overflows, or, on
//! a 32-bit target, when its result passes `2^32 - 1` (the reference
//! interpreter's `eval_gep`, WS2.16); the lane claims a single-index GEP's
//! addition and the emission pass folds it under that premise (OD-125).
//!
//! In a wasm32 session whose backend level (`-C opt-level`, or the bridge's
//! `opt-level` knob when set) is O1 or above ([`place_geps_enabled`]) the entries
//! below spell exactly the addresses Rust guarantees in bounds as
//! `gep inbounds u8 base, [k]`, each under the rule its name states:
//!
//! * [`projection_addr`]: `k` is the static offset of a `Field` /
//!   `ConstantIndex` projection chain of a place the statement reads, writes
//!   or borrows, through a local, a reference or a raw pointer. The
//!   Rust Reference makes "a place projection that violates the requirements
//!   of in-bounds pointer arithmetic" undefined behaviour (a field, tuple
//!   index or array/slice index expression), and rustc's `codegen_ssa`
//!   lowers each such step to `getelementptr inbounds`. A `Downcast` adds no
//!   offset and a variant's fields lie inside the enum; a packed struct's
//!   fields lie inside the struct (packing changes alignment, not the rule).
//! * [`accessed_place_addr`] and [`accessed_place_byte_ptr`]: `base + k` is
//!   a byte of a place (or of a field of the place at `base`) that the same
//!   statement reads or writes whole, lane by lane, right after forming the
//!   address: a typed copy the lowering decomposes. Accessing a place that
//!   is dangling is undefined behaviour, and a pointer is dangling unless
//!   all the bytes it points to lie in one live allocation (the Reference's
//!   "Behavior considered undefined").
//! * [`vtable_slot_addr`]: a method slot of the vtable a `dyn Trait`
//!   pointer's metadata names. That metadata must point to a vtable for the
//!   trait (the validity invariant of a wide pointer), the slot lies inside
//!   that compiler-built allocation, and rustc reads it through
//!   `getelementptr inbounds`.
//!
//! Each rule places `base + k` inside (or one past) one allocated object, and
//! an allocated object's addresses satisfy `base + size <= usize::MAX`
//! (`core::ptr`, "Allocated object"), so on wasm32 the result is at most
//! `2^32 - 1` and the byte offset is non-negative: every case satisfies
//! trust-ir's GEP rule, which asks less than `inbounds` does. The `inbounds`
//! flag records the stronger Rust guarantee; trust-ir gives it no run-time
//! effect.
//!
//! What stays an integer chain: `ptr::wrapping_add` / `arith_offset`
//! (no in-bounds requirement), integer address arithmetic, an `Index` by a
//! runtime value (strength reduction reads its chain), a constant offset
//! past `i32::MAX` (the word legalization gives a GEP index the wasm32 width
//! and trust-ir reads a negative signed index as undefined), every address
//! the lowering forms inside its own models of library types, and
//! `Offset(p, c)` (`ptr::add`, `ptr::offset`). The last is in bounds by the
//! intrinsic's contract, but it is the step of a slice iterator: once the
//! mid-end fully unrolls the loop, the last copy's step is dead, and the
//! dead-code table removes a dead integer chain (decision record OD-117) but
//! not a dead GEP of a pointer that is not rooted at an `alloca` or a global,
//! so the lane would emit it. The `Box<dyn Fn>` call's vtable slot also
//! keeps its chain: the vtable rule covers it, but no wasm32 execution
//! differential reaches that call (the wasm32 test sysroot has no `alloc`).
//! A slice pattern's elements on a `&[T]` are read by the slice element
//! path, which keeps its chain.
//!
//! Off the GEP lane every entry emits the chain its call site emitted
//! before, instruction for instruction, so native targets and O0 are
//! unchanged. `-Ztrust-ir-cg-args=no-wasm32-place-gep` restores the chains on
//! wasm32 at every level.

use super::*;

/// Whether this session spells in-bounds constant-offset addresses as GEPs:
/// a wasm32 session whose backend level is O1 or above, without the
/// `no-wasm32-place-gep` kill switch. The level is the one the wasm lane runs
/// at, [`backend_opt_level`] of `-C opt-level` (the bridge's `opt-level` knob
/// overrides it), so `-C opt-level=2` with the knob `opt-level=0` keeps every
/// chain and `-C opt-level=0` with `opt-level=2` emits the GEPs. The wasm
/// lane is the only consumer of the premise, and at O0 the emission pass
/// that folds under it does not run.
pub(super) fn place_geps_enabled(tcx: TyCtxt<'_>) -> bool {
    session_is_wasm32(tcx)
        && backend_opt_level(session_rustc_opt_level(tcx)) != OptLevel::O0
        && !crate::knobs::is_enabled(crate::knobs::NO_WASM32_PLACE_GEP)
}

/// The address of the sub-place `offset` bytes into the place at `base`,
/// reached by a `Field` / `ConstantIndex` projection chain (module docs,
/// the projection rule). Off the GEP lane: `emit_i64_const` of the offset,
/// then [`emit_element_addr`] at stride 1.
pub(super) fn projection_addr(
    ctx: &mut MirLoweringCtx<'_>,
    block: &mut Block,
    base: ValueId,
    offset: u64,
) -> ValueId {
    byte_addr(ctx, block, base, offset)
}

/// The address of the byte `offset` into a place the caller reads or writes
/// whole right after (module docs, the accessed-place rule). Off the GEP
/// lane: `emit_i64_const` of the offset, then [`emit_element_addr`] at
/// stride 1.
pub(super) fn accessed_place_addr(
    ctx: &mut MirLoweringCtx<'_>,
    block: &mut Block,
    base: ValueId,
    offset: u64,
) -> ValueId {
    byte_addr(ctx, block, base, offset)
}

/// [`accessed_place_addr`] for a caller that needs a plain `Ptr` even at
/// offset 0: off the GEP lane it is [`slot_byte_ptr`], which casts through
/// the integer chain at every offset; on it, offset 0 is the `copy ptr` of
/// `base` ([`byte_gep`]).
pub(super) fn accessed_place_byte_ptr(
    ctx: &mut MirLoweringCtx<'_>,
    block: &mut Block,
    base: ValueId,
    offset: u64,
) -> ValueId {
    if ctx.place_geps {
        if let Some(addr) = byte_gep(ctx, block, base, offset) {
            return addr;
        }
    }
    slot_byte_ptr(ctx, block, base, offset)
}

/// The address of method slot `slot` (of `slot_size` bytes) of the vtable at
/// `vtable` (module docs, the vtable rule). Off the GEP lane:
/// `emit_i64_const` of the slot, then [`emit_element_addr`] at `slot_size`.
pub(super) fn vtable_slot_addr(
    ctx: &mut MirLoweringCtx<'_>,
    block: &mut Block,
    vtable: ValueId,
    slot: u64,
    slot_size: u64,
) -> ValueId {
    if let (true, Some(offset)) = (ctx.place_geps, slot.checked_mul(slot_size)) {
        if let Some(addr) = byte_gep(ctx, block, vtable, offset) {
            return addr;
        }
    }
    let index = emit_i64_const(ctx, block, i128::from(slot));
    emit_element_addr(ctx, block, vtable, index, slot_size)
}

/// The shared body of [`projection_addr`] and [`accessed_place_addr`].
fn byte_addr(
    ctx: &mut MirLoweringCtx<'_>,
    block: &mut Block,
    base: ValueId,
    offset: u64,
) -> ValueId {
    if ctx.place_geps {
        if let Some(addr) = byte_gep(ctx, block, base, offset) {
            return addr;
        }
    }
    let index = emit_i64_const(ctx, block, i128::from(offset));
    emit_element_addr(ctx, block, base, index, 1)
}

/// `gep inbounds u8 base, [offset]`, the base normalized to a plain `Ptr` as
/// the lane's operand gate requires (the chain's `PtrToInt` source is the
/// same normalized value); offset 0 is that normalized base itself. `None`
/// for an offset past `i32::MAX`: the word legalization narrows the `i64`
/// index to the wasm32 word, where it would read as negative.
fn byte_gep(
    ctx: &mut MirLoweringCtx<'_>,
    block: &mut Block,
    base: ValueId,
    offset: u64,
) -> Option<ValueId> {
    let offset = i32::try_from(offset).ok()?;
    let base_ptr = coerce_to_plain_ptr(ctx, block, base);
    if offset == 0 {
        return Some(base_ptr);
    }
    let index = emit_i64_const(ctx, block, i128::from(offset));
    let addr = ctx.fresh_value();
    block.body.push(
        InstrNode::new(Inst::GEP {
            pointee_ty: TrustIrTy::U8,
            base: base_ptr,
            indices: vec![index],
            inbounds: true,
        })
        .with_result(addr),
    );
    Some(addr)
}
